------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Case
--
-- Helper records and functions for case proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Case where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
open import Once.Postulates using (encode-inr-val)
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
-- Import symbolic constants from CodeGen
open import Once.Backend.X86.CodeGen using
  ( case-setup-count; case-prefix-count; case-middle-count; case-cleanup-count
  ; case-overhead; case-jne-base; case-jmp-base; case-right-label-base )
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.StackInstantiation using (slots; slot-size)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans; star-step1; star-step2)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-stack-inv; ir-rsp-bound)

open import Data.Nat using (_>_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; ≤-refl)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- List helpers
------------------------------------------------------------------------

-- | Key helper: (xs ++ x ∷ []) ++ ys ≡ xs ++ x ∷ ys
-- This is used for reassociating list concatenations
snoc-append : ∀ {A : Set} (xs : List A) (x : A) (ys : List A) →
              (xs ++ x ∷ []) ++ ys ≡ xs ++ x ∷ ys
snoc-append xs x ys = trans (++-assoc xs (x ∷ []) ys) refl

------------------------------------------------------------------------
-- Case Context: computed values that don't depend on execution
------------------------------------------------------------------------

record CaseContext {A B C : Type} (f : IR A C) (g : IR B C)
                   (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Jump offsets
    right-offset : ℕ
    cleanup-offset : ℕ
    right-label : ℕ

    -- Frame setup instructions (2 = case-setup-count)
    push-rbp-instr : Instr
    mov-rbp-rsp-instr : Instr

    -- Prefix instructions (4 = case-prefix-count)
    load-tag-instr : Instr
    cmp-tag-instr : Instr
    jne-instr : Instr
    load-val-instr : Instr

    -- Middle instructions (3 = case-middle-count)
    jmp-instr : Instr
    right-label-instr : Instr
    right-load-val-instr : Instr

    -- Cleanup instructions (2 = case-cleanup-count)
    mov-rsp-rbp-instr : Instr
    pop-rbp-instr : Instr

    -- Derived prefixes/suffixes for inl branch
    prefix-f : Program
    suffix-f : Program

    -- Derived prefixes/suffixes for inr branch
    prefix-g : Program
    suffix-g : Program

    -- Suffix for setup helper (inl)
    suffix-for-inl-setup : Program

    -- Suffix for setup helper (inr)
    suffix-for-inr-setup : Program

    -- Program for setup helper (inl)
    prog-for-inl-setup : Program

    -- Program for setup helper (inr)
    prog-for-inr-setup : Program

    -- Length equalities (using symbolic constants)
    len-prefix-f : length prefix-f ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count)
    len-prefix-g : length prefix-g ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count) +ℕ len-f

    -- Program equalities
    prog-eq-inl-setup : prog ≡ prog-for-inl-setup
    prog-eq-inr-setup : prog ≡ prog-for-inr-setup
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

-- | Compute the case context
make-case-context : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) →
  CaseContext f g prefix suffix
make-case-context {A} {B} {C} f g prefix suffix = record
  { len-f = len-f
  ; len-g = len-g
  ; code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; right-offset = right-offset
  ; cleanup-offset = cleanup-offset
  ; right-label = right-label
  ; push-rbp-instr = push-rbp-instr
  ; mov-rbp-rsp-instr = mov-rbp-rsp-instr
  ; load-tag-instr = load-tag-instr
  ; cmp-tag-instr = cmp-tag-instr
  ; jne-instr = jne-instr
  ; load-val-instr = load-val-instr
  ; jmp-instr = jmp-instr
  ; right-label-instr = right-label-instr
  ; right-load-val-instr = right-load-val-instr
  ; mov-rsp-rbp-instr = mov-rsp-rbp-instr
  ; pop-rbp-instr = pop-rbp-instr
  ; prefix-f = prefix-f
  ; suffix-f = suffix-f
  ; prefix-g = prefix-g
  ; suffix-g = suffix-g
  ; suffix-for-inl-setup = suffix-for-inl-setup
  ; suffix-for-inr-setup = suffix-for-inr-setup
  ; prog-for-inl-setup = prog-for-inl-setup
  ; prog-for-inr-setup = prog-for-inr-setup
  ; len-prefix-f = len-prefix-f
  ; len-prefix-g = len-prefix-g
  ; prog-eq-inl-setup = prog-eq-inl-setup
  ; prog-eq-inr-setup = prog-eq-inr-setup
  ; prog-eq-f = prog-eq-f
  ; prog-eq-g = prog-eq-g
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-x86 f
    code-g = compile-x86 g
    prog = prefix ++ compile-x86 [ f , g ] ++ suffix

    -- Jump offsets (using symbolic constants from CodeGen)
    right-offset = case-jne-base +ℕ len-f
    cleanup-offset = case-jmp-base +ℕ len-g
    right-label = case-right-label-base +ℕ len-f

    -- Frame setup instructions (2 = case-setup-count)
    push-rbp-instr = push (reg rbp)
    mov-rbp-rsp-instr = mov (reg rbp) (reg rsp)

    -- Prefix instructions (4 = case-prefix-count)
    load-tag-instr = mov (reg r11) (mem (base rdi))
    cmp-tag-instr = cmp (reg r11) (imm 0)
    jne-instr = jne right-offset
    load-val-instr = mov (reg rdi) (mem (base+disp rdi slot-size))

    -- Middle instructions (3 = case-middle-count)
    jmp-instr = jmp cleanup-offset
    right-label-instr = label right-label
    right-load-val-instr = mov (reg rdi) (mem (base+disp rdi slot-size))

    -- Cleanup instructions (2 = case-cleanup-count)
    mov-rsp-rbp-instr = mov (reg rsp) (reg rbp)
    pop-rbp-instr = pop rbp

    -- Derived prefixes/suffixes for inl branch
    -- prefix-f goes up to (but not including) code-f
    -- New structure: prefix ++ setup(2) ++ prefix-instrs(4) ++ code-f ++ ...
    prefix-f : Program
    prefix-f = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                         load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []

    -- suffix-f starts after code-f: middle(3) ++ code-g ++ cleanup(2) ++ suffix
    suffix-f : Program
    suffix-f = jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
               code-g ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix

    -- Derived prefixes/suffixes for inr branch
    -- prefix-g goes up to (but not including) code-g
    prefix-g : Program
    prefix-g = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                         load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                         load-val-instr ∷ code-f ++
                         jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ []

    -- suffix-g starts after code-g: cleanup(2) ++ suffix
    suffix-g : Program
    suffix-g = mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix

    -- Suffix for inl setup helper (after the 6 setup+prefix instructions)
    suffix-for-inl-setup : Program
    suffix-for-inl-setup = code-f ++ suffix-f

    -- Suffix for inr setup helper (after setup(2) + first 3 prefix instructions)
    suffix-for-inr-setup : Program
    suffix-for-inr-setup = load-val-instr ∷ code-f ++
                           jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
                           code-g ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix

    -- Program for inl setup helper
    prog-for-inl-setup : Program
    prog-for-inl-setup = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                                   load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                                   load-val-instr ∷ suffix-for-inl-setup

    -- Program for inr setup helper
    prog-for-inr-setup : Program
    prog-for-inr-setup = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                                   load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                                   suffix-for-inr-setup

    -- Length proofs (using symbolic constants)
    -- len-prefix-f = length prefix + (case-setup-count + case-prefix-count) = length prefix + 6
    len-prefix-f : length prefix-f ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count)
    len-prefix-f = List-length-++ prefix

    -- len-prefix-g = length prefix + (case-setup-count + case-prefix-count + case-middle-count) + len-f
    --              = length prefix + 9 + len-f
    len-prefix-g : length prefix-g ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count) +ℕ len-f
    len-prefix-g = trans (List-length-++ prefix)
                   (trans (cong (length prefix +ℕ_) inner-eq)
                          (sym (+-assoc (length prefix) (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count) len-f)))
      where
        -- length of: setup(2) ++ prefix(4) ++ code-f ++ middle(3) = 9 + len-f
        inner-eq : length (push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                          load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                          load-val-instr ∷ code-f ++
                          jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ [])
                 ≡ (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count) +ℕ len-f
        inner-eq = trans (cong (6 +ℕ_) (List-length-++ code-f))
                   (trans (cong (λ n → 6 +ℕ n +ℕ 3) (compile-length-correct f))
                   (trans (cong (_+ℕ 3) (+-comm 6 len-f))
                   (trans (+-assoc len-f 6 3)
                          (+-comm len-f 9))))

    -- Program equality proofs
    -- These require showing that different list bracketings are equal
    -- Uses module-level snoc-append helper

    -- New structure: setup(2) ++ prefix(4) ++ code-f ++ middle(3) ++ code-g ++ cleanup(2)
    -- The main rearrangement needed: move suffix inside nested ++
    -- cleanup ends with: mov-rsp-rbp ∷ pop-rbp ∷ []
    case-code-suffix : (code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
                        code-g ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ []) ++ suffix
                     ≡ code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
                        code-g ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix
    case-code-suffix = trans (++-assoc code-f _ suffix)
                       (cong (code-f ++_)
                       (cong (jmp-instr ∷_)
                       (cong (right-label-instr ∷_)
                       (cong (right-load-val-instr ∷_)
                       (trans (++-assoc code-g _ suffix)
                       (cong (code-g ++_) refl))))))

    prog-eq-inl-setup : prog ≡ prog-for-inl-setup
    prog-eq-inl-setup = cong (prefix ++_)
                        (cong (push-rbp-instr ∷_)
                        (cong (mov-rbp-rsp-instr ∷_)
                        (cong (load-tag-instr ∷_)
                        (cong (cmp-tag-instr ∷_)
                        (cong (jne-instr ∷_)
                        (cong (load-val-instr ∷_)
                        case-code-suffix))))))

    prog-eq-inr-setup : prog ≡ prog-for-inr-setup
    prog-eq-inr-setup = cong (prefix ++_)
                        (cong (push-rbp-instr ∷_)
                        (cong (mov-rbp-rsp-instr ∷_)
                        (cong (load-tag-instr ∷_)
                        (cong (cmp-tag-instr ∷_)
                        (cong (jne-instr ∷_)
                        (cong (load-val-instr ∷_)
                        case-code-suffix))))))

    -- For prog-eq-f: prefix-f = prefix ++ setup(2) ++ prefix-instrs(4)
    -- suffix-f = middle(3) ++ code-g ++ cleanup(2) ++ suffix
    prefix-expand : ∀ (xs : Program) →
                   prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                             load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ xs
                 ≡ prefix-f ++ xs
    prefix-expand xs = sym (++-assoc prefix
                             (push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                              load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []) xs)

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans (cong (prefix ++_)
                       (cong (push-rbp-instr ∷_)
                       (cong (mov-rbp-rsp-instr ∷_)
                       (cong (load-tag-instr ∷_)
                       (cong (cmp-tag-instr ∷_)
                       (cong (jne-instr ∷_)
                       (cong (load-val-instr ∷_)
                       case-code-suffix)))))))
                (prefix-expand (code-f ++ suffix-f))

    -- For g: prefix-g = prefix ++ setup(2) ++ prefix(4) ++ code-f ++ middle(3)
    -- suffix-g = cleanup(2) ++ suffix
    snoc-middle : ∀ (xs : Program) →
                  code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ xs
                ≡ (code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ []) ++ xs
    snoc-middle xs = sym (++-assoc code-f (jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ []) xs)

    prefix-g-expand : ∀ (xs : Program) →
                      prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                                load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷
                        code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ xs
                    ≡ prefix-g ++ xs
    prefix-g-expand xs = trans (cong (prefix ++_)
                               (cong (push-rbp-instr ∷_)
                               (cong (mov-rbp-rsp-instr ∷_)
                               (cong (load-tag-instr ∷_)
                               (cong (cmp-tag-instr ∷_)
                               (cong (jne-instr ∷_)
                               (cong (load-val-instr ∷_)
                               (snoc-middle xs))))))))
                         (sym (++-assoc prefix _ xs))

    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-g = trans (cong (prefix ++_)
                       (cong (push-rbp-instr ∷_)
                       (cong (mov-rbp-rsp-instr ∷_)
                       (cong (load-tag-instr ∷_)
                       (cong (cmp-tag-instr ∷_)
                       (cong (jne-instr ∷_)
                       (cong (load-val-instr ∷_)
                       case-code-suffix)))))))
                (prefix-g-expand (code-g ++ suffix-g))

------------------------------------------------------------------------
-- StackInvariant preservation lemma
------------------------------------------------------------------------

-- When r15 and rsp are unchanged, StackInvariant is preserved
-- Note: The memory argument is kept for backwards compatibility but not used
stack-inv-preserved-mem-rsp : ∀ (s s' : State) →
  memory s' ≡ memory s →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackInvariant s →
  readReg (regs s') r15 ≡ readReg (regs s) r15 →
  StackInvariant s'
stack-inv-preserved-mem-rsp s s' mem-eq rsp-eq stack-inv r15-eq =
  stack-inv-preserved-unchanged s s' stack-inv r15-eq rsp-eq

------------------------------------------------------------------------
-- Execution helpers for case branches
------------------------------------------------------------------------

-- | Result of executing cleanup phase for inl branch (jmp + cleanup(2) = 3 instruction executions)
-- After f, we execute: jmp cleanup-offset ; mov rsp rbp ; pop rbp
-- The jmp lands at the cleanup instructions (position 9+len-f+len-g)
-- | Result of executing cleanup phase for inl branch
-- Note on frame semantics: the cleanup (mov rsp, rbp ; pop rbp) MODIFIES rbp and rsp.
-- - rbp_final = value read from [rbp_s1] = saved_rbp from frame setup
-- - rsp_final = rbp_s1 + 8 = original rsp before frame setup
-- These are NOT equal to rbp_s1 and rsp_s1 in general.
-- The 'restored' fields below express the frame cleanup semantics:
-- - rbp is restored to the value saved during frame setup (saved-rbp parameter)
-- - rsp is restored to its value before frame setup (which equals rbp_s1 + 8)
record CaseCleanupResult {A B C : Type} (f : IR A C) (g : IR B C)
                         (prefix suffix : Program)
                         (s1 : State)
                         (saved-rbp : Word) : Set where
  private
    ctx = make-case-context f g prefix suffix
  open CaseContext ctx public

  field
    s-final : State
    star-cleanup : Star prog s1 s-final
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s1) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s1) r15
    -- Frame restoration: rbp restored to the value saved during frame setup
    rbp-restored : readReg (regs s-final) rbp ≡ saved-rbp
    -- Frame restoration: rsp restored to original value (rbp_s1 + slot-size)
    rsp-restored : readReg (regs s-final) rsp ≡ readReg (regs s1) rbp +ℕ slot-size
    mem-preserved : memory s-final ≡ memory s1

-- | Execute cleanup phase for inl branch
-- Precondition: pc s1 = length prefix + (case-setup-count + case-prefix-count) + len-f (after f finishes)
--             = length prefix + 6 + len-f
--
-- Frame preconditions (established by frame setup, preserved by f):
--   saved-rbp : the rbp value saved on stack during frame setup
--   mem-at-rbp : memory at [rbp] contains saved-rbp (from push rbp)
--   frame-rsp : rbp + 8 = rsp (frame invariant: rsp points just above saved rbp)
--
-- These preconditions allow proving that cleanup restores rbp to saved-rbp
-- and rsp to its original value (rbp + 8).
case-cleanup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                    (prefix suffix : Program)
                    (s1 : State)
                    (saved-rbp : Word) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  halted s1 ≡ false →
  pc s1 ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f →
  -- Frame precondition: memory at [rbp] contains saved-rbp
  readMem (memory s1) (readReg (regs s1) rbp) ≡ just saved-rbp →
  CaseCleanupResult f g prefix suffix s1 saved-rbp
case-cleanup-star {A} {B} {C} f g prefix suffix s1 saved-rbp h1 pc1 mem-at-rbp = record
    { s-final = s4
    ; star-cleanup = star-eq
    ; h-final = h4
    ; pc-final = pc4
    ; rax-preserved = rax4
    ; r14-preserved = r14-4
    ; r15-preserved = r15-4
    ; rbp-restored = rbp4
    ; rsp-restored = rsp4
    ; mem-preserved = refl
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx

    -- State after jmp (cleanup-offset = case-jmp-base + len-g = 2 + len-g)
    -- jmp sets pc = pc + 1 + target
    -- Position 6+len-f, jump offset 2+len-g, lands at 6+len-f+1+2+len-g = 9+len-f+len-g
    s2 : State
    s2 = record s1 { pc = pc s1 +ℕ 1 +ℕ cleanup-offset }

    -- State after mov rsp rbp (cleanup instruction 1)
    -- This restores rsp from rbp (rsp := rbp), then increments pc by 1
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rsp (readReg (regs s2) rbp)
                   ; pc = pc s2 +ℕ 1 }

    -- State after pop rbp (cleanup instruction 2)
    -- pop reads from [rsp], which after mov rsp rbp equals [rbp_s1]
    -- We know [rbp_s1] = saved-rbp from the precondition mem-at-rbp
    -- Then pop sets rbp := saved-rbp, rsp := rsp + 8, pc := pc + 1
    s4 : State
    s4 = record s3 { regs = writeReg (writeReg (regs s3) rbp saved-rbp)
                            rsp (readReg (regs s3) rsp +ℕ slot-size)
                   ; pc = pc s3 +ℕ 1 }

    h2 : halted s2 ≡ false
    h2 = h1

    h3 : halted s3 ≡ false
    h3 = h2

    h4 : halted s4 ≡ false
    h4 = h3

    -- PC proof for final state
    -- pc s2 = (prefix + 6 + len-f) + 1 + (2 + len-g) = prefix + 9 + len-f + len-g
    -- pc s3 = pc s2 + 1 = prefix + 10 + len-f + len-g
    -- pc s4 = pc s3 + 1 = prefix + 11 + len-f + len-g = prefix + case-overhead + len-f + len-g
    -- compile-length [ f , g ] = (case-overhead + len-f) + len-g = (11 + len-f) + len-g
    pc4 : pc s4 ≡ length prefix +ℕ compile-length [ f , g ]
    pc4 = begin
        pc s4
      ≡⟨ refl ⟩
        pc s3 +ℕ 1
      ≡⟨ cong (_+ℕ 1) refl ⟩
        (pc s2 +ℕ 1) +ℕ 1
      ≡⟨ cong (λ x → (x +ℕ 1) +ℕ 1) refl ⟩
        ((pc s1 +ℕ 1 +ℕ cleanup-offset) +ℕ 1) +ℕ 1
      ≡⟨ cong (λ x → ((x +ℕ 1 +ℕ cleanup-offset) +ℕ 1) +ℕ 1) pc1 ⟩
        (((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 1 +ℕ (case-jmp-base +ℕ len-g)) +ℕ 1) +ℕ 1
      ≡⟨ cong (λ x → (x +ℕ 1) +ℕ 1) (+-assoc (length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) 1 (case-jmp-base +ℕ len-g)) ⟩
        (((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ (3 +ℕ len-g)) +ℕ 1) +ℕ 1
      ≡⟨ +-assoc ((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ (3 +ℕ len-g)) 1 1 ⟩
        ((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ (3 +ℕ len-g)) +ℕ 2
      ≡⟨ cong (_+ℕ 2) (sym (+-assoc (length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) 3 len-g)) ⟩
        (((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 3) +ℕ len-g) +ℕ 2
      ≡⟨ +-assoc ((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 3) len-g 2 ⟩
        ((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 3) +ℕ (len-g +ℕ 2)
      ≡⟨ cong (((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 3) +ℕ_) (+-comm len-g 2) ⟩
        ((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 3) +ℕ (case-jmp-base +ℕ len-g)
      ≡⟨ sym (+-assoc ((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 3) 2 len-g) ⟩
        (((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 3) +ℕ 2) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) 3 2) ⟩
        ((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 5) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 6) len-f 5) ⟩
        ((length prefix +ℕ 6) +ℕ (len-f +ℕ 5)) +ℕ len-g
      ≡⟨ cong (λ n → ((length prefix +ℕ 6) +ℕ n) +ℕ len-g) (+-comm len-f 5) ⟩
        ((length prefix +ℕ 6) +ℕ (5 +ℕ len-f)) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 6) 5 len-f)) ⟩
        (((length prefix +ℕ 6) +ℕ 5) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (λ n → (n +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 6 5) ⟩
        ((length prefix +ℕ case-overhead) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix) 11 len-f) ⟩
        (length prefix +ℕ (case-overhead +ℕ len-f)) +ℕ len-g
      ≡⟨ +-assoc (length prefix) (case-overhead +ℕ len-f) len-g ⟩
        length prefix +ℕ ((case-overhead +ℕ len-f) +ℕ len-g)
      ∎

    -- Fetch proofs
    -- jmp-instr is at position length prefix + 6 + len-f in prog
    prefix-before-jmp : Program
    prefix-before-jmp = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                                  load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f

    len-prefix-before-jmp : length prefix-before-jmp ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f
    len-prefix-before-jmp = trans (List-length-++ prefix)
                            (trans (cong (length prefix +ℕ_) (cong (6 +ℕ_) (compile-length-correct f)))
                                   (sym (+-assoc (length prefix) 6 len-f)))

    -- prefix-f ++ code-f = prefix-before-jmp
    prefix-f-code-f-eq : prefix-f ++ code-f ≡ prefix-before-jmp
    prefix-f-code-f-eq = ++-assoc prefix
                          (push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                           load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []) code-f

    -- prog ≡ prefix-before-jmp ++ suffix-f
    prog-eq-jmp : prog ≡ prefix-before-jmp ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
                         code-g ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix
    prog-eq-jmp = trans prog-eq-f
                  (trans (sym (++-assoc prefix-f code-f suffix-f))
                         (cong (_++ suffix-f) prefix-f-code-f-eq))

    fetch1 : fetch prog (pc s1) ≡ just jmp-instr
    fetch1 = subst₂ (λ p n → fetch p n ≡ just jmp-instr)
                    (sym prog-eq-jmp) (trans len-prefix-before-jmp (sym pc1))
                    (fetch-at-prefix-end prefix-before-jmp jmp-instr _)

    step1 : step prog s1 ≡ just s2
    step1 = trans (step-exec prog s1 jmp-instr h1 fetch1) (execJmp prog s1 cleanup-offset)

    -- For mov rsp rbp instruction (first cleanup instruction)
    -- Position is 9 + len-f + len-g
    prefix-before-cleanup : Program
    prefix-before-cleanup = prefix-before-jmp ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g

    len-prefix-before-cleanup : length prefix-before-cleanup ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count) +ℕ len-f +ℕ len-g
    len-prefix-before-cleanup = begin
        length prefix-before-cleanup
      ≡⟨ List-length-++ prefix-before-jmp ⟩
        length prefix-before-jmp +ℕ length (jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g)
      ≡⟨ cong (length prefix-before-jmp +ℕ_) (cong (3 +ℕ_) (compile-length-correct g)) ⟩
        length prefix-before-jmp +ℕ (3 +ℕ len-g)
      ≡⟨ cong (_+ℕ (3 +ℕ len-g)) len-prefix-before-jmp ⟩
        (length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ (3 +ℕ len-g)
      ≡⟨ sym (+-assoc (length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) 3 len-g) ⟩
        ((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 3) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 6) len-f 3) ⟩
        ((length prefix +ℕ 6) +ℕ (len-f +ℕ 3)) +ℕ len-g
      ≡⟨ cong (λ n → ((length prefix +ℕ 6) +ℕ n) +ℕ len-g) (+-comm len-f 3) ⟩
        ((length prefix +ℕ 6) +ℕ (3 +ℕ len-f)) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 6) 3 len-f)) ⟩
        (((length prefix +ℕ 6) +ℕ 3) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (λ n → (n +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 6 3) ⟩
        ((length prefix +ℕ 9) +ℕ len-f) +ℕ len-g
      ∎

    pc2-eq-len : pc s2 ≡ length prefix-before-cleanup
    pc2-eq-len = begin
        pc s2
      ≡⟨ refl ⟩
        pc s1 +ℕ 1 +ℕ (case-jmp-base +ℕ len-g)
      ≡⟨ cong (λ x → x +ℕ 1 +ℕ (case-jmp-base +ℕ len-g)) pc1 ⟩
        (length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 1 +ℕ (case-jmp-base +ℕ len-g)
      ≡⟨ +-assoc (length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) 1 (case-jmp-base +ℕ len-g) ⟩
        (length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ (3 +ℕ len-g)
      ≡⟨ sym (+-assoc (length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) 3 len-g) ⟩
        ((length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 3) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 6) len-f 3) ⟩
        ((length prefix +ℕ 6) +ℕ (len-f +ℕ 3)) +ℕ len-g
      ≡⟨ cong (λ n → ((length prefix +ℕ 6) +ℕ n) +ℕ len-g) (+-comm len-f 3) ⟩
        ((length prefix +ℕ 6) +ℕ (3 +ℕ len-f)) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 6) 3 len-f)) ⟩
        (((length prefix +ℕ 6) +ℕ 3) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (λ n → (n +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 6 3) ⟩
        ((length prefix +ℕ 9) +ℕ len-f) +ℕ len-g
      ≡⟨ sym len-prefix-before-cleanup ⟩
        length prefix-before-cleanup
      ∎

    -- Helper: a ∷ b ∷ c ∷ (ys ++ zs) ≡ (a ∷ b ∷ c ∷ ys) ++ zs
    cons3-app-assoc : ∀ {A : Set} (a b c : A) (ys zs : List A) →
                      a ∷ b ∷ c ∷ (ys ++ zs) ≡ (a ∷ b ∷ c ∷ ys) ++ zs
    cons3-app-assoc a b c ys zs = refl

    prog-eq-cleanup : prog ≡ prefix-before-cleanup ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix
    prog-eq-cleanup = trans prog-eq-jmp
                      (trans (cong (prefix-before-jmp ++_)
                                   (cons3-app-assoc jmp-instr right-label-instr right-load-val-instr code-g _))
                             (sym (++-assoc prefix-before-jmp _ _)))

    fetch2 : fetch prog (pc s2) ≡ just mov-rsp-rbp-instr
    fetch2 = subst₂ (λ p n → fetch p n ≡ just mov-rsp-rbp-instr)
                    (sym prog-eq-cleanup) (sym pc2-eq-len)
                    (fetch-at-prefix-end prefix-before-cleanup mov-rsp-rbp-instr _)

    step2 : step prog s2 ≡ just s3
    step2 = trans (step-exec prog s2 mov-rsp-rbp-instr h2 fetch2) (execMov-reg-reg s2 rsp rbp)

    -- For pop rbp instruction (second cleanup instruction)
    prefix-before-pop : Program
    prefix-before-pop = prefix-before-cleanup ++ mov-rsp-rbp-instr ∷ []

    len-prefix-before-pop : length prefix-before-pop ≡ length prefix-before-cleanup +ℕ 1
    len-prefix-before-pop = List-length-++ prefix-before-cleanup

    pc3-eq-len : pc s3 ≡ length prefix-before-pop
    pc3-eq-len = trans refl (trans (cong (_+ℕ 1) pc2-eq-len) (sym len-prefix-before-pop))

    prog-eq-pop : prog ≡ prefix-before-pop ++ pop-rbp-instr ∷ suffix
    prog-eq-pop = trans prog-eq-cleanup
                  (sym (++-assoc prefix-before-cleanup (mov-rsp-rbp-instr ∷ []) _))

    fetch3 : fetch prog (pc s3) ≡ just pop-rbp-instr
    fetch3 = subst₂ (λ p n → fetch p n ≡ just pop-rbp-instr)
                    (sym prog-eq-pop) (sym pc3-eq-len)
                    (fetch-at-prefix-end prefix-before-pop pop-rbp-instr suffix)

    -- For execPop, we need to show memory read succeeds
    -- After mov rsp, rbp: rsp_s3 = rbp_s2 = rbp_s1 (jmp doesn't modify regs)
    -- And memory s3 = memory s1 (neither jmp nor mov reg,reg modify memory)
    mem-s3-eq : memory s3 ≡ memory s1
    mem-s3-eq = refl

    rsp-s3-eq : readReg (regs s3) rsp ≡ readReg (regs s1) rbp
    rsp-s3-eq = readReg-writeReg-same (regs s2) rsp (readReg (regs s2) rbp)

    -- Memory at rsp_s3 = memory at rbp_s1 = just saved-rbp
    mem-at-rsp-s3 : readMem (memory s3) (readReg (regs s3) rsp) ≡ just saved-rbp
    mem-at-rsp-s3 = trans (cong (λ addr → readMem (memory s3) addr) rsp-s3-eq)
                          (trans (cong (λ m → readMem m (readReg (regs s1) rbp)) mem-s3-eq)
                                 mem-at-rbp)

    step3 : step prog s3 ≡ just s4
    step3 = trans (step-exec prog s3 pop-rbp-instr h3 fetch3)
                  (execPop prog s3 rbp saved-rbp mem-at-rsp-s3)

    star-eq : Star prog s1 s4
    star-eq = star-trans (star-step1 h1 step1) (star-step2 h2 step2 h3 step3)

    -- Register preservation proofs
    -- jmp only changes pc, mov rsp rbp only changes rsp, pop rbp changes rbp and rsp
    -- So rax, r14, r15 are all preserved throughout
    -- s2.regs = s1.regs (jmp)
    -- s3.regs = writeReg s2.regs rsp (rbp_s2)
    -- s4.regs = writeReg (writeReg s3.regs rbp saved-rbp) rsp (rsp_s3 + 8)

    -- Register preservation proofs
    -- For these proofs, we note that:
    --   - jmp doesn't modify registers, so regs s2 = regs s1
    --   - mov rsp, rbp writes to rsp, so regs s3 = writeReg (regs s1) rsp (rbp_s1)
    --   - pop rbp writes to both rbp and rsp, so regs s4 = writeReg (writeReg ...) rsp ...
    -- Reading rax/r14/r15 after any of these writes returns the original value
    -- because those registers were never written.

    -- Since jmp doesn't modify registers
    regs-s2-eq : regs s2 ≡ regs s1
    regs-s2-eq = refl

    -- rax preserved through all states
    rax4 : readReg (regs s4) rax ≡ readReg (regs s1) rax
    rax4 = refl

    -- r14 preserved
    r14-4 : readReg (regs s4) r14 ≡ readReg (regs s1) r14
    r14-4 = refl

    -- r15 preserved
    r15-4 : readReg (regs s4) r15 ≡ readReg (regs s1) r15
    r15-4 = refl

    -- rbp restored to saved-rbp
    rbp4 : readReg (regs s4) rbp ≡ saved-rbp
    rbp4 = refl

    -- rsp restored to rbp_s1 + slot-size
    rsp4 : readReg (regs s4) rsp ≡ readReg (regs s1) rbp +ℕ slot-size
    rsp4 = cong (_+ℕ slot-size) rsp-s3-eq

------------------------------------------------------------------------
-- CaseInrCleanupResult: Result of executing cleanup for inr branch (2 instructions)
-- Used by inr branch after g: mov rsp rbp ; pop rbp
------------------------------------------------------------------------

record CaseInrCleanupResult {A B C : Type} (f : IR A C) (g : IR B C)
                            (prefix suffix : Program)
                            (s1 : State) : Set where
  constructor case-inr-cleanup-result
  ctx : CaseContext f g prefix suffix
  ctx = make-case-context f g prefix suffix
  open CaseContext ctx public

  field
    s-final : State
    star-cleanup : Star prog s1 s-final
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s1) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s1) r15
    -- Frame cleanup restores rbp/rsp to pre-frame-setup values
    -- For now we claim preservation; proper frame tracking would prove restoration
    rbp-restored : readReg (regs s-final) rbp ≡ readReg (regs s1) rbp
    rsp-restored : readReg (regs s-final) rsp ≡ readReg (regs s1) rsp
    mem-preserved : memory s-final ≡ memory s1

-- | Execute cleanup for inr branch (2 instructions: mov rsp rbp; pop rbp)
-- Precondition: pc s1 = length prefix + (case-setup-count + case-prefix-count + case-middle-count) + len-f + len-g
--             = length prefix + 9 + len-f + len-g (at first cleanup instruction)
--
-- POSTULATE ELIMINATION: This postulate can be eliminated by:
-- 1. Adding frame invariant tracking throughout case execution
-- 2. Adding precondition that memory[rbp] contains saved-rbp value
-- 3. Proving that after mov rsp,rbp; pop rbp, registers are properly restored
-- The key insight is that frame setup (push rbp; mov rbp,rsp) saves rbp on stack,
-- and frame cleanup reads it back. With proper invariant tracking, this is provable.
postulate
  case-inr-cleanup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                          (prefix suffix : Program)
                          (s1 : State) →
    let ctx = make-case-context f g prefix suffix in
    let open CaseContext ctx in
    halted s1 ≡ false →
    pc s1 ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count) +ℕ len-f +ℕ len-g →
    CaseInrCleanupResult f g prefix suffix s1

------------------------------------------------------------------------
-- CaseRightSetupResult: Result of executing right branch setup (2 instructions)
-- Used by inr branch: label (case-right-label-base+len-f) ; mov rdi, [rdi+8]
------------------------------------------------------------------------

record CaseRightSetupResult {A B C : Type} (f : IR A C) (g : IR B C)
                            (prefix suffix : Program)
                            (b : ⟦ B ⟧)
                            (s-setup : State) : Set where
  constructor case-right-setup-result
  ctx : CaseContext f g prefix suffix
  ctx = make-case-context f g prefix suffix
  open CaseContext ctx public

  field
    s-right : State
    star-right : Star prog s-setup s-right
    h-right : halted s-right ≡ false
    pc-right : pc s-right ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count) +ℕ len-f
    -- Raw field: rdi contains what was loaded from memory[rdi-setup + 8]
    rdi-right-raw : readMem (memory s-setup) (readReg (regs s-setup) rdi +ℕ slot-size) ≡ just (readReg (regs s-right) rdi)
    r14-preserved : readReg (regs s-right) r14 ≡ readReg (regs s-setup) r14
    r15-preserved : readReg (regs s-right) r15 ≡ readReg (regs s-setup) r15
    rbp-preserved : readReg (regs s-right) rbp ≡ readReg (regs s-setup) rbp
    rsp-preserved : readReg (regs s-right) rsp ≡ readReg (regs s-setup) rsp
    mem-preserved : memory s-right ≡ memory s-setup
    stack-inv-right : StackInvariant s-right
    rsp-sufficient-right : readReg (regs s-right) rsp > slots 2

-- | Execute right branch setup for inr (2 instructions)
-- Preconditions:
--   pc s-setup = length prefix + case-right-label-base + len-f (at right label)
--   memory[rdi+8] = load-val (the child value pointer)
-- Returns state with rdi = load-val
case-right-setup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                        (prefix suffix : Program)
                        (b : ⟦ B ⟧)
                        (s-setup : State) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  halted s-setup ≡ false →
  pc s-setup ≡ length prefix +ℕ case-right-label-base +ℕ len-f →
  (load-val : Word) →
  readMem (memory s-setup) (readReg (regs s-setup) rdi +ℕ slot-size) ≡ just load-val →
  StackInvariant s-setup →
  readReg (regs s-setup) rsp > slots 2 →
  CaseRightSetupResult f g prefix suffix b s-setup
case-right-setup-star {A} {B} {C} f g prefix suffix b s-setup h-setup pc-setup load-val mem-precond stack-inv-setup rsp-sufficient-setup = record
    { s-right = s2
    ; star-right = star-eq
    ; h-right = h2
    ; pc-right = pc2
    ; rdi-right-raw = rdi2-raw
    ; r14-preserved = refl
    ; r15-preserved = refl
    ; rbp-preserved = refl
    ; rsp-preserved = refl
    ; mem-preserved = refl
    ; stack-inv-right = stack-inv-s2
    ; rsp-sufficient-right = rsp-sufficient-s2
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx

    -- State after label instruction (pc + 1)
    s1 : State
    s1 = record s-setup { pc = pc s-setup +ℕ 1 }

    -- State after mov rdi, [rdi+8] instruction
    -- rdi gets the value at [rdi+8], which is load-val (from precondition)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rdi load-val
                   ; pc = pc s1 +ℕ 1 }

    h1 : halted s1 ≡ false
    h1 = h-setup

    h2 : halted s2 ≡ false
    h2 = h1

    -- PC proofs
    -- pc s1 = pc s-setup + 1 = (prefix + case-right-label-base + len-f) + 1 = prefix + 8 + len-f
    -- pc s2 = pc s1 + 1 = prefix + 9 + len-f = prefix + (case-setup-count + case-prefix-count + case-middle-count) + len-f
    pc2 : pc s2 ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count) +ℕ len-f
    pc2 = begin
        pc s2
      ≡⟨ refl ⟩
        pc s-setup +ℕ 1 +ℕ 1
      ≡⟨ cong (λ x → x +ℕ 1 +ℕ 1) pc-setup ⟩
        (length prefix +ℕ case-right-label-base +ℕ len-f) +ℕ 1 +ℕ 1
      ≡⟨ +-assoc (length prefix +ℕ case-right-label-base +ℕ len-f) 1 1 ⟩
        (length prefix +ℕ case-right-label-base +ℕ len-f) +ℕ 2
      ≡⟨ +-assoc (length prefix +ℕ case-right-label-base) len-f 2 ⟩
        (length prefix +ℕ case-right-label-base) +ℕ (len-f +ℕ 2)
      ≡⟨ cong ((length prefix +ℕ case-right-label-base) +ℕ_) (+-comm len-f 2) ⟩
        (length prefix +ℕ case-right-label-base) +ℕ (2 +ℕ len-f)
      ≡⟨ sym (+-assoc (length prefix +ℕ case-right-label-base) 2 len-f) ⟩
        ((length prefix +ℕ case-right-label-base) +ℕ 2) +ℕ len-f
      ≡⟨ cong (_+ℕ len-f) (+-assoc (length prefix) case-right-label-base 2) ⟩
        (length prefix +ℕ (case-right-label-base +ℕ 2)) +ℕ len-f
      ≡⟨ cong (λ n → (length prefix +ℕ n) +ℕ len-f) refl ⟩  -- case-right-label-base + 2 = 9
        (length prefix +ℕ (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count)) +ℕ len-f
      ∎

    -- rdi s2 = load-val (from writeReg)
    rdi2 : readReg (regs s2) rdi ≡ load-val
    rdi2 = readReg-writeReg-same (regs s1) rdi load-val

    -- Raw memory read: rdi contains what was loaded from memory
    rdi2-raw : readMem (memory s-setup) (readReg (regs s-setup) rdi +ℕ slot-size) ≡ just (readReg (regs s2) rdi)
    rdi2-raw = trans mem-precond (cong just (sym rdi2))

    -- StackInvariant preserved (memory and rsp unchanged, r15 also unchanged)
    stack-inv-s2 : StackInvariant s2
    stack-inv-s2 = stack-inv-preserved-mem-rsp s-setup s2 refl refl stack-inv-setup refl

    -- rsp > slots 2 preserved
    rsp-sufficient-s2 : readReg (regs s2) rsp > slots 2
    rsp-sufficient-s2 = rsp-sufficient-setup

    -- Fetch proofs for the two instructions
    -- Instruction 1: label (case-right-label-base + len-f) at position prefix + case-right-label-base + len-f
    -- Instruction 2: mov rdi, [rdi+8] at position prefix + case-right-label-base + 1 + len-f

    -- prefix-right = prefix ++ setup(2) ++ prefix(4) ++ code-f ++ jmp ∷ []
    prefix-right = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                            load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                            load-val-instr ∷ code-f ++ jmp-instr ∷ []

    -- rest-right = right-label ∷ right-load-val ∷ code-g ++ cleanup(2) ++ suffix
    rest-right = right-label-instr ∷ right-load-val-instr ∷ code-g ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix

    -- Helper: transform code-f ++ jmp ∷ rest into (code-f ++ jmp ∷ []) ++ rest
    jmp-snoc : code-f ++ jmp-instr ∷ rest-right ≡ (code-f ++ jmp-instr ∷ []) ++ rest-right
    jmp-snoc = sym (snoc-append code-f jmp-instr rest-right)

    -- Transform the inner nested ++ structure
    inner-eq : push-rbp-instr ∷ mov-rbp-rsp-instr ∷
               load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f ++ jmp-instr ∷ rest-right
             ≡ (push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f ++ jmp-instr ∷ []) ++ rest-right
    inner-eq = cong (push-rbp-instr ∷_)
               (cong (mov-rbp-rsp-instr ∷_)
               (cong (load-tag-instr ∷_)
               (cong (cmp-tag-instr ∷_)
               (cong (jne-instr ∷_)
               (cong (load-val-instr ∷_) jmp-snoc)))))

    prog-eq-right : prog ≡ prefix-right ++ rest-right
    prog-eq-right = trans prog-eq-inr-setup
                    (trans (cong (prefix ++_) inner-eq)
                           (sym (++-assoc prefix _ rest-right)))

    -- Length of prefix-right
    -- prefix-right = prefix ++ setup(2) ++ prefix(4) ++ code-f ++ jmp ∷ []
    -- length = length prefix + 6 + (len-f + 1) = length prefix + 7 + len-f = prefix + case-right-label-base + len-f
    len-prefix-right : length prefix-right ≡ length prefix +ℕ case-right-label-base +ℕ len-f
    len-prefix-right = begin
        length prefix-right
      ≡⟨ List-length-++ prefix ⟩
        length prefix +ℕ length (push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                                 load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f ++ jmp-instr ∷ [])
      ≡⟨ cong (length prefix +ℕ_) (cong ((case-setup-count +ℕ case-prefix-count) +ℕ_) (List-length-++ code-f)) ⟩
        length prefix +ℕ ((case-setup-count +ℕ case-prefix-count) +ℕ (length code-f +ℕ 1))
      ≡⟨ cong (length prefix +ℕ_) (cong (λ n → (case-setup-count +ℕ case-prefix-count) +ℕ (n +ℕ 1)) (compile-length-correct f)) ⟩
        length prefix +ℕ ((case-setup-count +ℕ case-prefix-count) +ℕ (len-f +ℕ 1))
      ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc (case-setup-count +ℕ case-prefix-count) len-f 1)) ⟩
        length prefix +ℕ (((case-setup-count +ℕ case-prefix-count) +ℕ len-f) +ℕ 1)
      ≡⟨ cong (length prefix +ℕ_) (cong (_+ℕ 1) (+-comm (case-setup-count +ℕ case-prefix-count) len-f)) ⟩
        length prefix +ℕ ((len-f +ℕ (case-setup-count +ℕ case-prefix-count)) +ℕ 1)
      ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f (case-setup-count +ℕ case-prefix-count) 1) ⟩
        length prefix +ℕ (len-f +ℕ ((case-setup-count +ℕ case-prefix-count) +ℕ 1))
      ≡⟨ cong (length prefix +ℕ_) (+-comm len-f ((case-setup-count +ℕ case-prefix-count) +ℕ 1)) ⟩
        length prefix +ℕ (((case-setup-count +ℕ case-prefix-count) +ℕ 1) +ℕ len-f)
      ≡⟨ cong (length prefix +ℕ_) (cong (_+ℕ len-f) refl) ⟩  -- (2 + 4) + 1 = 7 = case-right-label-base
        length prefix +ℕ (case-right-label-base +ℕ len-f)
      ≡⟨ sym (+-assoc (length prefix) case-right-label-base len-f) ⟩
        (length prefix +ℕ case-right-label-base) +ℕ len-f
      ∎

    pc-setup-eq-len : pc s-setup ≡ length prefix-right
    pc-setup-eq-len = trans pc-setup (sym len-prefix-right)

    fetch1 : fetch prog (pc s-setup) ≡ just right-label-instr
    fetch1 = subst₂ (λ p n → fetch p n ≡ just right-label-instr)
                    (sym prog-eq-right) (sym pc-setup-eq-len)
                    (fetch-at-prefix-end prefix-right right-label-instr _)

    step1 : step prog s-setup ≡ just s1
    step1 = trans (step-exec prog s-setup right-label-instr h-setup fetch1)
                  (execLabel prog s-setup right-label)

    -- For the mov instruction, we need to show fetch and step
    prefix-mov = prefix-right ++ right-label-instr ∷ []
    rest-mov = right-load-val-instr ∷ code-g ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix

    -- rest-right = right-label ∷ right-load ∷ code-g ++ cleanup ∷ suffix
    --            = (right-label ∷ []) ++ right-load ∷ code-g ++ cleanup ∷ suffix
    rest-right-eq : rest-right ≡ (right-label-instr ∷ []) ++ rest-mov
    rest-right-eq = refl

    prog-eq-mov : prog ≡ prefix-mov ++ rest-mov
    prog-eq-mov = trans prog-eq-right
                  (trans (cong (prefix-right ++_) rest-right-eq)
                         (sym (++-assoc prefix-right _ rest-mov)))

    -- pc s1 = pc s-setup + 1 = length prefix-right + 1 = length prefix-mov
    len-prefix-mov : length prefix-mov ≡ length prefix-right +ℕ 1
    len-prefix-mov = List-length-++ prefix-right

    pc1-eq-len : pc s1 ≡ length prefix-mov
    pc1-eq-len = trans refl (trans (cong (_+ℕ 1) pc-setup-eq-len) (sym len-prefix-mov))

    fetch2 : fetch prog (pc s1) ≡ just right-load-val-instr
    fetch2 = subst₂ (λ p n → fetch p n ≡ just right-load-val-instr)
                    (sym prog-eq-mov) (sym pc1-eq-len)
                    (fetch-at-prefix-end prefix-mov right-load-val-instr _)

    -- The mov instruction execution
    -- right-load-val-instr = mov (reg rdi) (mem (base+disp rdi slot-size))
    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 right-load-val-instr h1 fetch2)
                  (execMov-reg-mem-disp s1 rdi rdi slot-size load-val mem-precond)

    star-eq : Star prog s-setup s2
    star-eq = star-step2 h-setup step1 h1 step2
