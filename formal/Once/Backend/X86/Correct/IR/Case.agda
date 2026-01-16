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
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.StackInstantiation
  using (slots; slot-size; StackCapacity; capacity-preserved-rsp-unchanged)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.FrameRestore
  using (frame-cleanup-count;
         FrameRestoreResult; frame-restore-exec;
         JumpToCleanupResult; jump-to-cleanup-exec)
  renaming (restore-rsp-instr to fr-restore-rsp-instr; pop-rbp-instr to fr-pop-rbp-instr)
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

    -- Frame setup instructions (new)
    push-rbp-instr : Instr
    mov-rbp-rsp-instr : Instr

    -- Setup instructions
    load-tag-instr : Instr
    cmp-tag-instr : Instr
    jne-instr : Instr
    load-val-instr : Instr
    jmp-instr : Instr
    right-label-instr : Instr
    right-load-val-instr : Instr

    -- Frame cleanup instructions (new)
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

    -- Length equalities using symbolic constants from CodeGen
    -- pos-before-f = case-setup-count + case-prefix-count (6)
    -- pos-before-g = case-setup-count + case-prefix-count + case-middle-count (9)
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

    -- Jump offsets (from CodeGen constants)
    right-offset = case-jne-base +ℕ len-f
    cleanup-offset = case-jmp-base +ℕ len-g
    right-label = case-right-label-base +ℕ len-f

    -- Frame setup instructions
    push-rbp-instr = push (reg rbp)
    mov-rbp-rsp-instr = mov (reg rbp) (reg rsp)

    -- Instructions
    load-tag-instr = mov (reg r11) (mem (base rdi))
    cmp-tag-instr = cmp (reg r11) (imm 0)
    jne-instr = jne right-offset
    load-val-instr = mov (reg rdi) (mem (base+disp rdi slot-size))
    jmp-instr = jmp cleanup-offset
    right-label-instr = label right-label
    right-load-val-instr = mov (reg rdi) (mem (base+disp rdi slot-size))

    -- Frame cleanup instructions
    mov-rsp-rbp-instr = mov (reg rsp) (reg rbp)
    pop-rbp-instr = pop rbp

    -- Derived prefixes/suffixes for inl
    -- prefix-f includes setup (2) + prefix (4) = 6 instructions before f
    prefix-f : Program
    prefix-f = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
               load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []

    -- suffix-f includes middle (3) + g + cleanup (2) + suffix
    suffix-f : Program
    suffix-f = jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
               code-g ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix

    -- Derived prefixes/suffixes for inr
    -- prefix-g includes setup (2) + prefix (4) + f + middle (3) = 9 + len-f instructions before g
    prefix-g : Program
    prefix-g = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
               load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
               load-val-instr ∷ code-f ++
               jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ []

    -- suffix-g includes cleanup (2) + suffix
    suffix-g : Program
    suffix-g = mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix

    -- Suffix for inl setup helper
    suffix-for-inl-setup : Program
    suffix-for-inl-setup = code-f ++ suffix-f

    -- Suffix for inr setup helper
    suffix-for-inr-setup : Program
    suffix-for-inr-setup = load-val-instr ∷ code-f ++
                           jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
                           code-g ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix

    -- Program for inl setup helper (after setup instructions)
    prog-for-inl-setup : Program
    prog-for-inl-setup = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                         load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ suffix-for-inl-setup

    -- Program for inr setup helper
    prog-for-inr-setup : Program
    prog-for-inr-setup = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                         load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ suffix-for-inr-setup

    -- Shorthand for common sums
    setup+prefix : ℕ
    setup+prefix = case-setup-count +ℕ case-prefix-count

    setup+prefix+middle : ℕ
    setup+prefix+middle = case-setup-count +ℕ case-prefix-count +ℕ case-middle-count

    -- Length proofs using symbolic constants
    -- prefix-f has setup + prefix instructions before f
    len-prefix-f : length prefix-f ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count)
    len-prefix-f = List-length-++ prefix

    -- prefix-g has setup + prefix + f + middle instructions before g
    len-prefix-g : length prefix-g ≡ length prefix +ℕ setup+prefix+middle +ℕ len-f
    len-prefix-g = trans (List-length-++ prefix)
                   (trans (cong (length prefix +ℕ_) inner-eq)
                          (sym (+-assoc (length prefix) setup+prefix+middle len-f)))
      where
        inner-eq : length (push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                          load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                          load-val-instr ∷ code-f ++
                          jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ [])
                 ≡ setup+prefix+middle +ℕ len-f
        inner-eq = trans (cong (setup+prefix +ℕ_) (List-length-++ code-f))
                   (trans (cong (λ n → setup+prefix +ℕ n +ℕ case-middle-count) (compile-length-correct f))
                   (trans (cong (_+ℕ case-middle-count) (+-comm setup+prefix len-f))
                   (trans (+-assoc len-f setup+prefix case-middle-count)
                          (+-comm len-f setup+prefix+middle))))

    -- Program equality proofs
    -- These require showing that different list bracketings are equal
    -- Uses module-level snoc-append helper

    -- The main rearrangement needed: move suffix inside nested ++
    -- New structure: code-f ++ middle(3) ++ code-g ++ cleanup(2) ++ suffix
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
                       (cong (code-g ++_)
                       (cong (mov-rsp-rbp-instr ∷_)
                       (cong (pop-rbp-instr ∷_) refl))))))))

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

    -- For prog-eq-f and prog-eq-g, we need to rearrange the ++ associations
    -- With stack frame, prefix-f = prefix ++ setup(2) ++ prefix(4)

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

-- | Result of executing jump-to-cleanup phase for inl branch
-- After f, we execute: jmp (2+len-g) ; mov rsp,rbp ; pop rbp
-- This restores the stack frame before returning.
record CaseJumpResult {A B C : Type} (f : IR A C) (g : IR B C)
                      (prefix suffix : Program)
                      (s1 : State)
                      (saved-rbp : Word)
                      (original-rsp : Word) : Set where
  private
    ctx = make-case-context f g prefix suffix
  open CaseContext ctx public

  field
    s-final : State
    star-jump : Star prog s1 s-final
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    rdi-preserved : readReg (regs s-final) rdi ≡ readReg (regs s1) rdi
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s1) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s1) r15
    -- RSP and RBP are restored, not preserved
    rsp-restored : readReg (regs s-final) rsp ≡ original-rsp
    rbp-restored : readReg (regs s-final) rbp ≡ saved-rbp
    mem-preserved : memory s-final ≡ memory s1

-- | Execute jump-to-cleanup phase for inl branch
-- Precondition: pc s1 = length prefix + 6 + len-f (after f finishes)
-- The jump skips: right-label, right-load-val, code-g
-- Then executes cleanup: mov rsp,rbp ; pop rbp
case-jump-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                 (prefix suffix : Program)
                 (s1 : State)
                 (saved-rbp : Word)
                 (original-rsp : Word) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  halted s1 ≡ false →
  pc s1 ≡ length prefix +ℕ 6 +ℕ len-f →
  -- Frame preconditions: memory[rbp] = saved-rbp, rbp + 8 = original-rsp
  readMem (memory s1) (readReg (regs s1) rbp) ≡ just saved-rbp →
  readReg (regs s1) rbp +ℕ slot-size ≡ original-rsp →
  CaseJumpResult f g prefix suffix s1 saved-rbp original-rsp
case-jump-star {A} {B} {C} f g prefix suffix s1 saved-rbp original-rsp h1 pc1 mem-rbp rbp-eq = record
    { s-final = JumpToCleanupResult.s-final jump-result
    ; star-jump = JumpToCleanupResult.star jump-result
    ; h-final = JumpToCleanupResult.h-final jump-result
    ; pc-final = pc-final-proof
    ; rax-preserved = JumpToCleanupResult.rax-preserved jump-result
    ; rdi-preserved = JumpToCleanupResult.rdi-preserved jump-result
    ; r14-preserved = JumpToCleanupResult.r14-preserved jump-result
    ; r15-preserved = JumpToCleanupResult.r15-preserved jump-result
    ; rsp-restored = JumpToCleanupResult.rsp-final jump-result
    ; rbp-restored = JumpToCleanupResult.rbp-final jump-result
    ; mem-preserved = JumpToCleanupResult.mem-preserved jump-result
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx

    -- Program structure for jump-to-cleanup:
    -- prefix-jmp = prefix ++ [setup(2) + prefix(4)] ++ code-f
    -- skipped = right-label ∷ right-load-val ∷ code-g
    -- cleanup = mov-rsp-rbp ∷ pop-rbp ∷ suffix

    prefix-jmp : Program
    prefix-jmp = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                 load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f

    skipped : Program
    skipped = right-label-instr ∷ right-load-val-instr ∷ code-g

    -- length skipped = 2 + len-g = cleanup-offset (case-jmp-base = 2)
    len-skipped : length skipped ≡ cleanup-offset
    len-skipped = cong (2 +ℕ_) (compile-length-correct g)

    -- Program structure equality for jump-to-cleanup
    prog-eq-for-jump : prog ≡ prefix-jmp ++ jmp-instr ∷ skipped ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix
    prog-eq-for-jump = trans prog-eq-f
                       (trans (sym (++-assoc prefix-f code-f suffix-f))
                              (cong (_++ suffix-f) prefix-f-eq))
      where
        prefix-f-eq : prefix-f ++ code-f ≡ prefix-jmp
        prefix-f-eq = ++-assoc prefix _ code-f

    -- Length of prefix-jmp = prefix + setup+prefix + len-f
    len-prefix-jmp : length prefix-jmp ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count) +ℕ len-f
    len-prefix-jmp = trans (List-length-++ prefix)
                     (trans (cong (length prefix +ℕ_) (cong ((case-setup-count +ℕ case-prefix-count) +ℕ_) (compile-length-correct f)))
                            (sym (+-assoc (length prefix) (case-setup-count +ℕ case-prefix-count) len-f)))

    -- PC at jmp position
    pc-eq-jmp : pc s1 ≡ length prefix-jmp
    pc-eq-jmp = trans pc1 (sym len-prefix-jmp)

    -- jmp-offset = cleanup-offset = 2 + len-g = length skipped
    offset-eq : cleanup-offset ≡ length skipped
    offset-eq = sym len-skipped

    -- Use jump-to-cleanup-exec from FrameRestore
    jump-result : JumpToCleanupResult prog s1 saved-rbp original-rsp
    jump-result = jump-to-cleanup-exec prog prefix-jmp skipped suffix s1 cleanup-offset
                                       saved-rbp original-rsp
                                       h1 prog-eq-for-jump pc-eq-jmp offset-eq mem-rbp rbp-eq

    -- Final PC proof
    -- PC from jump-to-cleanup = prefix-jmp + 1 + cleanup-offset + 2
    --                         = (prefix + 6 + len-f) + 1 + (2 + len-g) + 2
    --                         = prefix + 6 + len-f + 3 + len-g + 2
    --                         = prefix + 11 + len-f + len-g
    --                         = prefix + (11 + len-f) + len-g
    --                         = prefix + compile-length [ f , g ]
    pc-final-proof : pc (JumpToCleanupResult.s-final jump-result) ≡ length prefix +ℕ compile-length [ f , g ]
    pc-final-proof = trans (JumpToCleanupResult.pc-final-eq jump-result)
                     (begin
                       length prefix-jmp +ℕ 1 +ℕ cleanup-offset +ℕ frame-cleanup-count
                     ≡⟨ cong (λ n → n +ℕ 1 +ℕ cleanup-offset +ℕ frame-cleanup-count) len-prefix-jmp ⟩
                       (length prefix +ℕ 6 +ℕ len-f) +ℕ 1 +ℕ cleanup-offset +ℕ 2
                     ≡⟨ cong (λ n → (length prefix +ℕ 6 +ℕ len-f) +ℕ 1 +ℕ n +ℕ 2) refl ⟩
                       (length prefix +ℕ 6 +ℕ len-f) +ℕ 1 +ℕ (2 +ℕ len-g) +ℕ 2
                     ≡⟨ cong (_+ℕ 2) (+-assoc (length prefix +ℕ 6 +ℕ len-f) 1 (2 +ℕ len-g)) ⟩
                       ((length prefix +ℕ 6 +ℕ len-f) +ℕ (3 +ℕ len-g)) +ℕ 2
                     ≡⟨ +-assoc (length prefix +ℕ 6 +ℕ len-f) (3 +ℕ len-g) 2 ⟩
                       (length prefix +ℕ 6 +ℕ len-f) +ℕ (3 +ℕ len-g +ℕ 2)
                     ≡⟨ cong ((length prefix +ℕ 6 +ℕ len-f) +ℕ_) (+-assoc 3 len-g 2) ⟩
                       (length prefix +ℕ 6 +ℕ len-f) +ℕ (3 +ℕ (len-g +ℕ 2))
                     ≡⟨ cong (λ n → (length prefix +ℕ 6 +ℕ len-f) +ℕ (3 +ℕ n)) (+-comm len-g 2) ⟩
                       (length prefix +ℕ 6 +ℕ len-f) +ℕ (3 +ℕ (2 +ℕ len-g))
                     ≡⟨ cong ((length prefix +ℕ 6 +ℕ len-f) +ℕ_) (sym (+-assoc 3 2 len-g)) ⟩
                       (length prefix +ℕ 6 +ℕ len-f) +ℕ (5 +ℕ len-g)
                     ≡⟨ sym (+-assoc (length prefix +ℕ 6 +ℕ len-f) 5 len-g) ⟩
                       ((length prefix +ℕ 6 +ℕ len-f) +ℕ 5) +ℕ len-g
                     ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 6) len-f 5) ⟩
                       ((length prefix +ℕ 6) +ℕ (len-f +ℕ 5)) +ℕ len-g
                     ≡⟨ cong (λ n → ((length prefix +ℕ 6) +ℕ n) +ℕ len-g) (+-comm len-f 5) ⟩
                       ((length prefix +ℕ 6) +ℕ (5 +ℕ len-f)) +ℕ len-g
                     ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 6) 5 len-f)) ⟩
                       (((length prefix +ℕ 6) +ℕ 5) +ℕ len-f) +ℕ len-g
                     ≡⟨ cong (λ n → (n +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 6 5) ⟩
                       ((length prefix +ℕ 11) +ℕ len-f) +ℕ len-g
                     ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix) 11 len-f) ⟩
                       (length prefix +ℕ (11 +ℕ len-f)) +ℕ len-g
                     ≡⟨ +-assoc (length prefix) (11 +ℕ len-f) len-g ⟩
                       length prefix +ℕ ((11 +ℕ len-f) +ℕ len-g)
                     ∎)

------------------------------------------------------------------------
-- CaseCleanupResult: Result of executing frame cleanup (2 instructions)
-- Used by inr branch to execute: mov rsp,rbp ; pop rbp
------------------------------------------------------------------------

record CaseCleanupResult {A B C : Type} (f : IR A C) (g : IR B C)
                         (prefix suffix : Program)
                         (s1 : State)
                         (saved-rbp : Word)
                         (original-rsp : Word) : Set where
  constructor case-cleanup-result
  ctx : CaseContext f g prefix suffix
  ctx = make-case-context f g prefix suffix
  open CaseContext ctx public

  field
    s-final : State
    star-cleanup : Star prog s1 s-final
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    rdi-preserved : readReg (regs s-final) rdi ≡ readReg (regs s1) rdi
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s1) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s1) r15
    -- RSP and RBP are restored, not preserved
    rsp-restored : readReg (regs s-final) rsp ≡ original-rsp
    rbp-restored : readReg (regs s-final) rbp ≡ saved-rbp
    mem-preserved : memory s-final ≡ memory s1

-- | Execute frame cleanup for inr branch (2 instructions)
-- Precondition: pc s1 = length prefix + 9 + len-f + len-g (at cleanup)
-- Executes: mov rsp,rbp ; pop rbp
case-cleanup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                    (prefix suffix : Program)
                    (s1 : State)
                    (saved-rbp : Word)
                    (original-rsp : Word) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  halted s1 ≡ false →
  pc s1 ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g →
  -- Frame preconditions: memory[rbp] = saved-rbp, rbp + 8 = original-rsp
  readMem (memory s1) (readReg (regs s1) rbp) ≡ just saved-rbp →
  readReg (regs s1) rbp +ℕ slot-size ≡ original-rsp →
  CaseCleanupResult f g prefix suffix s1 saved-rbp original-rsp
case-cleanup-star {A} {B} {C} f g prefix suffix s1 saved-rbp original-rsp h1 pc1 mem-rbp rbp-eq = record
    { s-final = FrameRestoreResult.s-final cleanup-result
    ; star-cleanup = FrameRestoreResult.star cleanup-result
    ; h-final = FrameRestoreResult.h-final cleanup-result
    ; pc-final = pc-final-proof
    ; rax-preserved = FrameRestoreResult.rax-preserved cleanup-result
    ; rdi-preserved = FrameRestoreResult.rdi-preserved cleanup-result
    ; r14-preserved = FrameRestoreResult.r14-preserved cleanup-result
    ; r15-preserved = FrameRestoreResult.r15-preserved cleanup-result
    ; rsp-restored = FrameRestoreResult.rsp-final cleanup-result
    ; rbp-restored = FrameRestoreResult.rbp-final cleanup-result
    ; mem-preserved = FrameRestoreResult.mem-preserved cleanup-result
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx

    -- Cleanup prefix: everything before the cleanup instructions
    cleanup-prefix : Program
    cleanup-prefix = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                     load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                     load-val-instr ∷ code-f ++
                     jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g

    -- Length of cleanup-prefix = prefix + 9 + len-f + len-g
    len-cleanup-prefix : length cleanup-prefix ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
    len-cleanup-prefix = trans (List-length-++ prefix)
                         (trans (cong (length prefix +ℕ_) inner-len)
                                (sym (+-assoc (length prefix) 9 (len-f +ℕ len-g))))
      where
        inner-len : length (push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                           load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                           load-val-instr ∷ code-f ++
                           jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g)
                  ≡ 9 +ℕ (len-f +ℕ len-g)
        inner-len = trans (cong (6 +ℕ_) (List-length-++ code-f))
                    (trans (cong (λ n → 6 +ℕ n +ℕ (3 +ℕ length code-g)) (compile-length-correct f))
                    (trans (cong (λ n → 6 +ℕ len-f +ℕ (3 +ℕ n)) (compile-length-correct g))
                    (trans (cong (6 +ℕ_) (sym (+-assoc len-f 3 len-g)))
                    (trans (cong (6 +ℕ_) (cong (_+ℕ len-g) (+-comm len-f 3)))
                    (trans (cong (6 +ℕ_) (+-assoc 3 len-f len-g))
                           (sym (+-assoc 6 3 (len-f +ℕ len-g))))))))

    -- Program structure for cleanup
    prog-eq-cleanup : prog ≡ cleanup-prefix ++ mov-rsp-rbp-instr ∷ pop-rbp-instr ∷ suffix
    prog-eq-cleanup = trans prog-eq-g
                      (trans (sym (++-assoc prefix-g code-g suffix-g))
                             (cong (_++ suffix-g) prefix-g-code-g-eq))
      where
        prefix-g-code-g-eq : prefix-g ++ code-g ≡ cleanup-prefix
        prefix-g-code-g-eq = trans (++-assoc prefix _ code-g)
                             (cong (prefix ++_)
                             (cong (push-rbp-instr ∷_)
                             (cong (mov-rbp-rsp-instr ∷_)
                             (cong (load-tag-instr ∷_)
                             (cong (cmp-tag-instr ∷_)
                             (cong (jne-instr ∷_)
                             (cong (load-val-instr ∷_)
                             (trans (sym (++-assoc code-f _ code-g))
                                    (cong (_++ code-g) (sym (++-assoc code-f _ [])))))))))))

    -- PC at cleanup position
    pc-eq-cleanup : pc s1 ≡ length cleanup-prefix
    pc-eq-cleanup = trans pc1 (sym len-cleanup-prefix)

    -- Use frame-restore-exec from FrameRestore
    cleanup-result : FrameRestoreResult prog s1 saved-rbp original-rsp
    cleanup-result = frame-restore-exec prog cleanup-prefix suffix s1 saved-rbp original-rsp
                                        h1 prog-eq-cleanup pc-eq-cleanup mem-rbp rbp-eq

    -- Final PC proof
    -- PC after cleanup = cleanup-prefix + 2
    --                  = (prefix + 9 + len-f + len-g) + 2
    --                  = prefix + 11 + len-f + len-g
    --                  = prefix + (11 + len-f) + len-g
    --                  = prefix + compile-length [ f , g ]
    pc-final-proof : pc (FrameRestoreResult.s-final cleanup-result) ≡ length prefix +ℕ compile-length [ f , g ]
    pc-final-proof = trans (FrameRestoreResult.pc-final cleanup-result)
                     (begin
                       pc s1 +ℕ frame-cleanup-count
                     ≡⟨ cong (_+ℕ frame-cleanup-count) pc1 ⟩
                       (length prefix +ℕ 9 +ℕ len-f +ℕ len-g) +ℕ 2
                     ≡⟨ +-assoc (length prefix +ℕ 9 +ℕ len-f) len-g 2 ⟩
                       (length prefix +ℕ 9 +ℕ len-f) +ℕ (len-g +ℕ 2)
                     ≡⟨ cong ((length prefix +ℕ 9 +ℕ len-f) +ℕ_) (+-comm len-g 2) ⟩
                       (length prefix +ℕ 9 +ℕ len-f) +ℕ (2 +ℕ len-g)
                     ≡⟨ sym (+-assoc (length prefix +ℕ 9 +ℕ len-f) 2 len-g) ⟩
                       ((length prefix +ℕ 9 +ℕ len-f) +ℕ 2) +ℕ len-g
                     ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 9) len-f 2) ⟩
                       ((length prefix +ℕ 9) +ℕ (len-f +ℕ 2)) +ℕ len-g
                     ≡⟨ cong (λ n → ((length prefix +ℕ 9) +ℕ n) +ℕ len-g) (+-comm len-f 2) ⟩
                       ((length prefix +ℕ 9) +ℕ (2 +ℕ len-f)) +ℕ len-g
                     ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 9) 2 len-f)) ⟩
                       (((length prefix +ℕ 9) +ℕ 2) +ℕ len-f) +ℕ len-g
                     ≡⟨ cong (λ n → (n +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 9 2) ⟩
                       ((length prefix +ℕ 11) +ℕ len-f) +ℕ len-g
                     ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix) 11 len-f) ⟩
                       (length prefix +ℕ (11 +ℕ len-f)) +ℕ len-g
                     ≡⟨ +-assoc (length prefix) (11 +ℕ len-f) len-g ⟩
                       length prefix +ℕ ((11 +ℕ len-f) +ℕ len-g)
                     ∎)

------------------------------------------------------------------------
-- CaseRightSetupResult: Result of executing right branch setup (2 instructions)
-- Used by inr branch: label (5+len-f) ; mov rdi, [rdi+8]
------------------------------------------------------------------------

record CaseRightSetupResult {A B C : Type} (f : IR A C) (g : IR B C)
                            (prefix suffix : Program)
                            (b : ⟦ B ⟧)
                            (s-setup : State)
                            (cap-req : ℕ) : Set where
  constructor case-right-setup-result
  ctx : CaseContext f g prefix suffix
  ctx = make-case-context f g prefix suffix
  open CaseContext ctx public

  field
    s-right : State
    star-right : Star prog s-setup s-right
    h-right : halted s-right ≡ false
    -- After 2 instructions: label + mov rdi, [rdi+8]
    -- Position = prefix + setup + prefix + middle + len-f = prefix + 9 + len-f
    pc-right : pc s-right ≡ length prefix +ℕ (case-setup-count +ℕ case-prefix-count +ℕ case-middle-count) +ℕ len-f
    -- Raw field: rdi contains what was loaded from memory[rdi-setup + 8]
    rdi-right-raw : readMem (memory s-setup) (readReg (regs s-setup) rdi +ℕ slot-size) ≡ just (readReg (regs s-right) rdi)
    r14-preserved : readReg (regs s-right) r14 ≡ readReg (regs s-setup) r14
    r15-preserved : readReg (regs s-right) r15 ≡ readReg (regs s-setup) r15
    rbp-preserved : readReg (regs s-right) rbp ≡ readReg (regs s-setup) rbp
    rsp-preserved : readReg (regs s-right) rsp ≡ readReg (regs s-setup) rsp
    mem-preserved : memory s-right ≡ memory s-setup
    stack-inv-right : StackInvariant s-right
    cap-right : StackCapacity s-right cap-req

-- | Execute right branch setup for inr (2 instructions)
-- Preconditions:
--   pc s-setup = length prefix + case-right-label-base + len-f (at right label)
--   memory[rdi+8] = load-val (the child value pointer)
-- Returns state with rdi = load-val
case-right-setup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                        (prefix suffix : Program)
                        (b : ⟦ B ⟧)
                        (s-setup : State)
                        (cap-req : ℕ) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  halted s-setup ≡ false →
  pc s-setup ≡ length prefix +ℕ case-right-label-base +ℕ len-f →
  (load-val : Word) →
  readMem (memory s-setup) (readReg (regs s-setup) rdi +ℕ slot-size) ≡ just load-val →
  StackInvariant s-setup →
  StackCapacity s-setup cap-req →
  CaseRightSetupResult f g prefix suffix b s-setup cap-req
case-right-setup-star {A} {B} {C} f g prefix suffix b s-setup cap-req h-setup pc-setup load-val mem-precond stack-inv-setup cap-setup = record
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
    ; cap-right = cap-s2
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

    -- PC proofs using symbolic constants
    -- pc s1 = pc s-setup + 1 = (prefix + case-right-label-base + len-f) + 1
    -- pc s2 = pc s1 + 1 = prefix + (case-right-label-base + 2) + len-f
    --                   = prefix + (setup + prefix + middle) + len-f
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

    -- StackCapacity preserved (rsp unchanged)
    cap-s2 : StackCapacity s2 cap-req
    cap-s2 = capacity-preserved-rsp-unchanged s-setup s2 cap-req cap-setup refl

    -- Fetch proofs for the two instructions
    -- Instruction 1: label (5 + len-f) at position prefix + 5 + len-f
    -- Instruction 2: mov rdi, [rdi+8] at position prefix + 6 + len-f

    -- prefix-right includes: setup (2) + prefix (4, but only first 3 + f + jmp for inr path)
    -- Actually for inr: setup + load-tag + cmp + jne jumps to right-label
    -- So prefix-right = prefix ++ setup + prefix-before-jne + f + jmp
    prefix-right = prefix ++ push-rbp-instr ∷ mov-rbp-rsp-instr ∷
                   load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                   load-val-instr ∷ code-f ++ jmp-instr ∷ []

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
    -- length = length prefix + 6 + length (code-f ++ jmp ∷ [])
    --        = length prefix + 6 + (len-f + 1)
    --        = length prefix + 7 + len-f = length prefix + case-right-label-base + len-f
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
      ≡⟨ sym (+-assoc (length prefix) ((case-setup-count +ℕ case-prefix-count) +ℕ 1) len-f) ⟩
        (length prefix +ℕ ((case-setup-count +ℕ case-prefix-count) +ℕ 1)) +ℕ len-f
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
    -- right-load-val-instr = mov (reg rdi) (mem (base+disp rdi 8))
    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 right-load-val-instr h1 fetch2)
                  (execMov-reg-mem-disp s1 rdi rdi 8 load-val mem-precond)

    star-eq : Star prog s-setup s2
    star-eq = star-step2 h-setup step1 h1 step2
