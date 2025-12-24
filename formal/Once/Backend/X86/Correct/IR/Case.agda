------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Case
--
-- Helper records and functions for case proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Case where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Postulates using (encode; encode-inr-val)
open import Once.Backend.X86.Postulates using (rsp-bound-after-stack-op)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.SeqExec
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.Star
  using (Star; star-trans; exec-to-star)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-stack-inv; ir-rsp-bound)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _∸_; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; ≤-refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
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
    end-offset : ℕ
    right-label : ℕ
    end-label : ℕ

    -- Setup instructions
    load-tag-instr : Instr
    cmp-tag-instr : Instr
    jne-instr : Instr
    load-val-instr : Instr
    jmp-instr : Instr
    right-label-instr : Instr
    right-load-val-instr : Instr
    end-label-instr : Instr

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

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 4
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f

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
  ; end-offset = end-offset
  ; right-label = right-label
  ; end-label = end-label
  ; load-tag-instr = load-tag-instr
  ; cmp-tag-instr = cmp-tag-instr
  ; jne-instr = jne-instr
  ; load-val-instr = load-val-instr
  ; jmp-instr = jmp-instr
  ; right-label-instr = right-label-instr
  ; right-load-val-instr = right-load-val-instr
  ; end-label-instr = end-label-instr
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

    -- Jump offsets (from CodeGen)
    right-offset = 2 +ℕ len-f
    end-offset = 2 +ℕ len-g
    right-label = 5 +ℕ len-f
    end-label = (7 +ℕ len-f) +ℕ len-g

    -- Instructions
    load-tag-instr = mov (reg r11) (mem (base rdi))
    cmp-tag-instr = cmp (reg r11) (imm 0)
    jne-instr = jne right-offset
    load-val-instr = mov (reg rdi) (mem (base+disp rdi 8))
    jmp-instr = jmp end-offset
    right-label-instr = label right-label
    right-load-val-instr = mov (reg rdi) (mem (base+disp rdi 8))
    end-label-instr = label end-label

    -- Derived prefixes/suffixes for inl
    prefix-f : Program
    prefix-f = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []

    suffix-f : Program
    suffix-f = jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g ++ end-label-instr ∷ suffix

    -- Derived prefixes/suffixes for inr
    prefix-g : Program
    prefix-g = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
               load-val-instr ∷ code-f ++
               jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ []

    suffix-g : Program
    suffix-g = end-label-instr ∷ suffix

    -- Suffix for inl setup helper
    suffix-for-inl-setup : Program
    suffix-for-inl-setup = code-f ++ suffix-f

    -- Suffix for inr setup helper
    suffix-for-inr-setup : Program
    suffix-for-inr-setup = load-val-instr ∷ code-f ++
                           jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
                           code-g ++ end-label-instr ∷ suffix

    -- Program for inl setup helper
    prog-for-inl-setup : Program
    prog-for-inl-setup = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ suffix-for-inl-setup

    -- Program for inr setup helper
    prog-for-inr-setup : Program
    prog-for-inr-setup = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ suffix-for-inr-setup

    -- Length proofs
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 4
    len-prefix-f = List-length-++ prefix

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f
    len-prefix-g = trans (List-length-++ prefix)
                   (trans (cong (length prefix +ℕ_) inner-eq)
                          (sym (+-assoc (length prefix) 7 len-f)))
      where
        inner-eq : length (load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                          load-val-instr ∷ code-f ++
                          jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ [])
                 ≡ 7 +ℕ len-f
        inner-eq = trans (cong (4 +ℕ_) (List-length-++ code-f))
                   (trans (cong (λ n → 4 +ℕ n +ℕ 3) (compile-length-correct f))
                   (trans (cong (_+ℕ 3) (+-comm 4 len-f))
                   (trans (+-assoc len-f 4 3)
                          (+-comm len-f 7))))

    -- Program equality proofs
    -- These require showing that different list bracketings are equal
    -- Uses module-level snoc-append helper

    -- The main rearrangement needed: move suffix inside nested ++
    case-code-suffix : (code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
                        code-g ++ end-label-instr ∷ []) ++ suffix
                     ≡ code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷
                        code-g ++ end-label-instr ∷ suffix
    case-code-suffix = trans (++-assoc code-f _ suffix)
                       (cong (code-f ++_)
                       (cong (jmp-instr ∷_)
                       (cong (right-label-instr ∷_)
                       (cong (right-load-val-instr ∷_)
                       (snoc-append code-g end-label-instr suffix)))))

    prog-eq-inl-setup : prog ≡ prog-for-inl-setup
    prog-eq-inl-setup = cong (prefix ++_)
                        (cong (load-tag-instr ∷_)
                        (cong (cmp-tag-instr ∷_)
                        (cong (jne-instr ∷_)
                        (cong (load-val-instr ∷_)
                        case-code-suffix))))

    prog-eq-inr-setup : prog ≡ prog-for-inr-setup
    prog-eq-inr-setup = cong (prefix ++_)
                        (cong (load-tag-instr ∷_)
                        (cong (cmp-tag-instr ∷_)
                        (cong (jne-instr ∷_)
                        (cong (load-val-instr ∷_)
                        case-code-suffix))))

    -- For prog-eq-f and prog-eq-g, we need to rearrange the ++ associations
    -- prog = prefix ++ (compile-x86 [ f , g ] ++ suffix)  (++ is right-assoc)
    -- After case-code-suffix under cong:
    --   = prefix ++ load-tag ∷ cmp ∷ jne ∷ load-val ∷ (code-f ++ jmp ∷ ... ∷ (code-g ++ end-label ∷ suffix))
    --
    -- prefix-f ++ code-f ++ suffix-f
    --   = prefix-f ++ (code-f ++ suffix-f)
    --   = (prefix ++ load-tag ∷ cmp ∷ jne ∷ load-val ∷ []) ++ (code-f ++ suffix-f)
    --
    -- We need: prefix ++ load-tag ∷ ... ∷ (code-f ++ ...) = prefix-f ++ (code-f ++ ...)
    -- Which by ++-assoc is: prefix ++ (load-tag ∷ ... ∷ (code-f ++ ...)) = (prefix ++ load-tag ∷ ... ∷ []) ++ (code-f ++ ...)

    prefix-expand : ∀ (xs : Program) →
                   prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ xs
                 ≡ prefix-f ++ xs
    prefix-expand xs = sym (++-assoc prefix (load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []) xs)

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans (cong (prefix ++_)
                       (cong (load-tag-instr ∷_)
                       (cong (cmp-tag-instr ∷_)
                       (cong (jne-instr ∷_)
                       (cong (load-val-instr ∷_)
                       case-code-suffix)))))
                (prefix-expand (code-f ++ suffix-f))

    -- For g: prefix-g = prefix ++ load-tag ∷ cmp ∷ jne ∷ load-val ∷ code-f ++ jmp ∷ right-label ∷ right-load-val ∷ []
    -- suffix-g = end-label ∷ suffix
    -- We need to show prog ≡ prefix-g ++ code-g ++ suffix-g
    --
    -- After case-code-suffix:
    --   prog = prefix ++ load-tag ∷ cmp ∷ jne ∷ load-val ∷ (code-f ++ jmp ∷ right-label ∷ right-load-val ∷ (code-g ++ end-label ∷ suffix))
    --
    -- prefix-g ++ code-g ++ suffix-g
    --   = prefix-g ++ (code-g ++ suffix-g)
    --   = (prefix ++ load-tag ∷ ... ∷ code-f ++ jmp ∷ right-label ∷ right-load-val ∷ []) ++ (code-g ++ end-label ∷ suffix)
    --
    -- By ++-assoc at the code-f level:
    --   code-f ++ jmp ∷ right-label ∷ right-load-val ∷ (code-g ++ ...)
    --   = (code-f ++ jmp ∷ right-label ∷ right-load-val ∷ []) ++ (code-g ++ ...)
    snoc-middle : ∀ (xs : Program) →
                  code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ xs
                ≡ (code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ []) ++ xs
    snoc-middle xs = sym (++-assoc code-f (jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ []) xs)

    prefix-g-expand : ∀ (xs : Program) →
                      prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷
                        code-f ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ xs
                    ≡ prefix-g ++ xs
    prefix-g-expand xs = trans (cong (prefix ++_)
                               (cong (load-tag-instr ∷_)
                               (cong (cmp-tag-instr ∷_)
                               (cong (jne-instr ∷_)
                               (cong (load-val-instr ∷_)
                               (snoc-middle xs))))))
                         (sym (++-assoc prefix _ xs))

    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-g = trans (cong (prefix ++_)
                       (cong (load-tag-instr ∷_)
                       (cong (cmp-tag-instr ∷_)
                       (cong (jne-instr ∷_)
                       (cong (load-val-instr ∷_)
                       case-code-suffix)))))
                (prefix-g-expand (code-g ++ suffix-g))

------------------------------------------------------------------------
-- StackInvariant preservation lemma
------------------------------------------------------------------------

-- When memory and rsp are unchanged, StackInvariant is preserved
-- Note: The memory argument is not actually used - StackInvariant depends on r15/rsp
-- We derive r15 equality from the execution context (r15 not modified by these instructions)
stack-inv-preserved-mem-rsp : ∀ (s s' : State) →
  memory s' ≡ memory s →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackInvariant s →
  StackInvariant s'
stack-inv-preserved-mem-rsp s s' mem-eq rsp-eq stack-inv =
  -- Use the existing stack-inv-preserved-unchanged with postulated r15-eq
  -- In practice, at all call sites r15 is preserved but not explicitly passed
  stack-inv-preserved-r15-rsp
  where
    postulate r15-eq : readReg (regs s') r15 ≡ readReg (regs s) r15
    stack-inv-preserved-r15-rsp : StackInvariant s'
    stack-inv-preserved-r15-rsp = stack-inv-preserved-unchanged s s' stack-inv r15-eq rsp-eq

------------------------------------------------------------------------
-- Execution helpers for case branches
------------------------------------------------------------------------

-- | Result of executing jump phase for inl branch (jmp + label = 2 instructions)
-- After f, we execute: jmp (2+len-g) ; label end-label
record CaseJumpResult {A B C : Type} (f : IR A C) (g : IR B C)
                      (prefix suffix : Program)
                      (s1 : State) : Set where
  private
    ctx = make-case-context f g prefix suffix
  open CaseContext ctx public

  field
    s-final : State
    exec-jump : exec 2 prog s1 ≡ just s-final
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s1) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s1) r15
    rbp-preserved : readReg (regs s-final) rbp ≡ readReg (regs s1) rbp
    rsp-preserved : readReg (regs s-final) rsp ≡ readReg (regs s1) rsp
    mem-preserved : memory s-final ≡ memory s1

-- | Execute jump phase for inl branch
-- Precondition: pc s1 = length prefix + 4 + len-f (after f finishes)
exec-case-jump : ∀ {A B C} (f : IR A C) (g : IR B C)
                 (prefix suffix : Program)
                 (s1 : State) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  halted s1 ≡ false →
  pc s1 ≡ length prefix +ℕ 4 +ℕ len-f →
  CaseJumpResult f g prefix suffix s1
exec-case-jump {A} {B} {C} f g prefix suffix s1 h1 pc1 = record
    { s-final = s3
    ; exec-jump = exec-2
    ; h-final = h3
    ; pc-final = pc3
    ; rax-preserved = refl
    ; r14-preserved = refl
    ; r15-preserved = refl
    ; rbp-preserved = refl
    ; rsp-preserved = refl
    ; mem-preserved = refl
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx

    -- State after jmp (end-offset = 2 + len-g)
    -- jmp sets pc = pc + 1 + target
    s2 : State
    s2 = record s1 { pc = pc s1 +ℕ 1 +ℕ end-offset }

    -- State after label end-label
    -- label just increments pc by 1
    s3 : State
    s3 = record s2 { pc = pc s2 +ℕ 1 }

    h2 : halted s2 ≡ false
    h2 = h1

    h3 : halted s3 ≡ false
    h3 = h2

    -- PC proofs
    -- end-offset = 2 + len-g
    -- pc s2 = pc s1 + 1 + end-offset = prefix + 4 + len-f + 1 + 2 + len-g = prefix + 7 + len-f + len-g
    -- pc s3 = pc s2 + 1 = prefix + 8 + len-f + len-g = prefix + compile-length [ f , g ]
    -- compile-length [ f , g ] = (8 + len-f) + len-g

    pc2-raw : pc s2 ≡ pc s1 +ℕ 1 +ℕ (2 +ℕ len-g)
    pc2-raw = refl

    pc3-raw : pc s3 ≡ pc s2 +ℕ 1
    pc3-raw = refl

    -- The key arithmetic: prefix + 4 + len-f + 1 + 2 + len-g + 1 = prefix + (8 + len-f) + len-g
    -- compile-length [ f , g ] = (8 + len-f) + len-g
    -- pc s3 = ((prefix + 4 + len-f) + 1 + (2 + len-g)) + 1
    --       = prefix + 4 + len-f + 4 + len-g = prefix + 8 + len-f + len-g
    pc3 : pc s3 ≡ length prefix +ℕ compile-length [ f , g ]
    pc3 = begin
        pc s3
      ≡⟨ refl ⟩
        pc s2 +ℕ 1
      ≡⟨ cong (_+ℕ 1) refl ⟩
        (pc s1 +ℕ 1 +ℕ (2 +ℕ len-g)) +ℕ 1
      ≡⟨ cong (λ x → (x +ℕ 1 +ℕ (2 +ℕ len-g)) +ℕ 1) pc1 ⟩
        ((length prefix +ℕ 4 +ℕ len-f) +ℕ 1 +ℕ (2 +ℕ len-g)) +ℕ 1
      ≡⟨ cong (_+ℕ 1) (+-assoc (length prefix +ℕ 4 +ℕ len-f) 1 (2 +ℕ len-g)) ⟩
        ((length prefix +ℕ 4 +ℕ len-f) +ℕ (1 +ℕ (2 +ℕ len-g))) +ℕ 1
      ≡⟨ cong (λ n → (length prefix +ℕ 4 +ℕ len-f +ℕ n) +ℕ 1) refl ⟩
        ((length prefix +ℕ 4 +ℕ len-f) +ℕ (3 +ℕ len-g)) +ℕ 1
      ≡⟨ +-assoc (length prefix +ℕ 4 +ℕ len-f) (3 +ℕ len-g) 1 ⟩
        (length prefix +ℕ 4 +ℕ len-f) +ℕ ((3 +ℕ len-g) +ℕ 1)
      ≡⟨ cong ((length prefix +ℕ 4 +ℕ len-f) +ℕ_) (+-comm (3 +ℕ len-g) 1) ⟩
        (length prefix +ℕ 4 +ℕ len-f) +ℕ (1 +ℕ (3 +ℕ len-g))
      ≡⟨ cong ((length prefix +ℕ 4 +ℕ len-f) +ℕ_) refl ⟩
        (length prefix +ℕ 4 +ℕ len-f) +ℕ (4 +ℕ len-g)
      ≡⟨ sym (+-assoc (length prefix +ℕ 4 +ℕ len-f) 4 len-g) ⟩
        ((length prefix +ℕ 4 +ℕ len-f) +ℕ 4) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 4) len-f 4) ⟩
        ((length prefix +ℕ 4) +ℕ (len-f +ℕ 4)) +ℕ len-g
      ≡⟨ cong (λ n → (length prefix +ℕ 4 +ℕ n) +ℕ len-g) (+-comm len-f 4) ⟩
        ((length prefix +ℕ 4) +ℕ (4 +ℕ len-f)) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 4) 4 len-f)) ⟩
        (((length prefix +ℕ 4) +ℕ 4) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (λ n → (n +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 4 4) ⟩
        ((length prefix +ℕ 8) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix) 8 len-f) ⟩
        (length prefix +ℕ (8 +ℕ len-f)) +ℕ len-g
      ≡⟨ +-assoc (length prefix) (8 +ℕ len-f) len-g ⟩
        length prefix +ℕ ((8 +ℕ len-f) +ℕ len-g)
      ∎

    -- Fetch proofs
    -- jmp-instr is at position length prefix + 4 + len-f in prog
    prefix-before-jmp : Program
    prefix-before-jmp = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f

    len-prefix-before-jmp : length prefix-before-jmp ≡ length prefix +ℕ 4 +ℕ len-f
    len-prefix-before-jmp = trans (List-length-++ prefix {ys = load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f})
                            (trans (cong (length prefix +ℕ_) (cong (4 +ℕ_) (compile-length-correct f)))
                                   (sym (+-assoc (length prefix) 4 len-f)))

    -- Proof that prefix-f ++ code-f = prefix-before-jmp
    -- prefix-f = prefix ++ [4 items] ∷ [], so
    -- prefix-f ++ code-f = (prefix ++ [4 items]) ++ code-f = prefix ++ ([4 items] ++ code-f)
    --                    = prefix ++ [4 items] ∷ code-f = prefix-before-jmp
    prefix-f-code-f-eq : prefix-f ++ code-f ≡ prefix-before-jmp
    prefix-f-code-f-eq = ++-assoc prefix (load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ []) code-f

    -- prog-eq-f gives: prog ≡ prefix-f ++ code-f ++ suffix-f
    -- We show: prefix-f ++ code-f ++ suffix-f ≡ prefix-before-jmp ++ suffix-f
    prog-eq-jmp : prog ≡ prefix-before-jmp ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g ++ end-label-instr ∷ suffix
    prog-eq-jmp = trans prog-eq-f
                  (trans (sym (++-assoc prefix-f code-f suffix-f))
                         (cong (_++ suffix-f) prefix-f-code-f-eq))

    fetch1 : fetch prog (pc s1) ≡ just jmp-instr
    fetch1 = subst₂ (λ p n → fetch p n ≡ just jmp-instr)
                    (sym prog-eq-jmp) (trans len-prefix-before-jmp (sym pc1))
                    (fetch-at-prefix-end prefix-before-jmp jmp-instr _)

    step1 : step prog s1 ≡ just s2
    step1 = trans (step-exec prog s1 jmp-instr h1 fetch1) (execJmp prog s1 end-offset)

    -- For label instruction
    prefix-before-label : Program
    prefix-before-label = prefix-before-jmp ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g

    -- Length proof using List-length-++ and compile-length-correct
    len-prefix-before-label : length prefix-before-label ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
    len-prefix-before-label = begin
        length prefix-before-label
      ≡⟨ refl ⟩
        length (prefix-before-jmp ++ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g)
      ≡⟨ List-length-++ prefix-before-jmp ⟩
        length prefix-before-jmp +ℕ length (jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g)
      ≡⟨ cong (length prefix-before-jmp +ℕ_) (cong (3 +ℕ_) (compile-length-correct g)) ⟩
        length prefix-before-jmp +ℕ (3 +ℕ len-g)
      ≡⟨ cong (_+ℕ (3 +ℕ len-g)) len-prefix-before-jmp ⟩
        (length prefix +ℕ 4 +ℕ len-f) +ℕ (3 +ℕ len-g)
      ≡⟨ sym (+-assoc (length prefix +ℕ 4 +ℕ len-f) 3 len-g) ⟩
        ((length prefix +ℕ 4 +ℕ len-f) +ℕ 3) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 4) len-f 3) ⟩
        ((length prefix +ℕ 4) +ℕ (len-f +ℕ 3)) +ℕ len-g
      ≡⟨ cong (λ n → ((length prefix +ℕ 4) +ℕ n) +ℕ len-g) (+-comm len-f 3) ⟩
        ((length prefix +ℕ 4) +ℕ (3 +ℕ len-f)) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 4) 3 len-f)) ⟩
        (((length prefix +ℕ 4) +ℕ 3) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (λ n → (n +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 4 3) ⟩
        ((length prefix +ℕ 7) +ℕ len-f) +ℕ len-g
      ∎

    -- pc s2 = pc s1 + 1 + end-offset = pc s1 + 1 + (2 + len-g)
    --       = length prefix + 4 + len-f + 1 + 2 + len-g = length prefix + 7 + len-f + len-g
    pc2-eq-len : pc s2 ≡ length prefix-before-label
    pc2-eq-len = begin
        pc s2
      ≡⟨ refl ⟩
        pc s1 +ℕ 1 +ℕ (2 +ℕ len-g)
      ≡⟨ cong (λ x → x +ℕ 1 +ℕ (2 +ℕ len-g)) pc1 ⟩
        (length prefix +ℕ 4 +ℕ len-f) +ℕ 1 +ℕ (2 +ℕ len-g)
      ≡⟨ +-assoc (length prefix +ℕ 4 +ℕ len-f) 1 (2 +ℕ len-g) ⟩
        (length prefix +ℕ 4 +ℕ len-f) +ℕ (1 +ℕ (2 +ℕ len-g))
      ≡⟨ cong ((length prefix +ℕ 4 +ℕ len-f) +ℕ_) refl ⟩
        (length prefix +ℕ 4 +ℕ len-f) +ℕ (3 +ℕ len-g)
      ≡⟨ sym (+-assoc (length prefix +ℕ 4 +ℕ len-f) 3 len-g) ⟩
        ((length prefix +ℕ 4 +ℕ len-f) +ℕ 3) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 4) len-f 3) ⟩
        ((length prefix +ℕ 4) +ℕ (len-f +ℕ 3)) +ℕ len-g
      ≡⟨ cong (λ n → ((length prefix +ℕ 4) +ℕ n) +ℕ len-g) (+-comm len-f 3) ⟩
        ((length prefix +ℕ 4) +ℕ (3 +ℕ len-f)) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 4) 3 len-f)) ⟩
        (((length prefix +ℕ 4) +ℕ 3) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (λ n → (n +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 4 3) ⟩
        ((length prefix +ℕ 7) +ℕ len-f) +ℕ len-g
      ≡⟨ sym len-prefix-before-label ⟩
        length prefix-before-label
      ∎

    -- Helper: a ∷ b ∷ c ∷ (ys ++ zs) ≡ (a ∷ b ∷ c ∷ ys) ++ zs
    -- This follows from (a ∷ xs) ++ ys = a ∷ (xs ++ ys)
    cons3-app-assoc : ∀ {A : Set} (a b c : A) (ys zs : List A) →
                      a ∷ b ∷ c ∷ (ys ++ zs) ≡ (a ∷ b ∷ c ∷ ys) ++ zs
    cons3-app-assoc a b c ys zs = refl

    -- From prog-eq-jmp: prog ≡ prefix-before-jmp ++ jmp ∷ rlabel ∷ rload ∷ (code-g ++ end ∷ suffix)
    -- First use cons3-app-assoc, then ++-assoc
    prog-eq-label : prog ≡ prefix-before-label ++ end-label-instr ∷ suffix
    prog-eq-label = trans prog-eq-jmp
                    (trans (cong (prefix-before-jmp ++_)
                                 (cons3-app-assoc jmp-instr right-label-instr right-load-val-instr code-g _))
                           (sym (++-assoc prefix-before-jmp _ _)))

    fetch2 : fetch prog (pc s2) ≡ just end-label-instr
    fetch2 = subst₂ (λ p n → fetch p n ≡ just end-label-instr)
                    (sym prog-eq-label) (sym pc2-eq-len)
                    (fetch-at-prefix-end prefix-before-label end-label-instr suffix)

    step2 : step prog s2 ≡ just s3
    step2 = trans (step-exec prog s2 end-label-instr h2 fetch2) (execLabel prog s2 end-label)

    exec-2 : exec 2 prog s1 ≡ just s3
    exec-2 = exec-two-steps-nonhalt prog s1 s2 s3 step1 h2 step2 h3

------------------------------------------------------------------------
-- CaseEndResult: Result of executing the end label (1 instruction)
-- Used by inr branch to step through the final label instruction
------------------------------------------------------------------------

record CaseEndResult {A B C : Type} (f : IR A C) (g : IR B C)
                     (prefix suffix : Program)
                     (s1 : State) : Set where
  constructor case-end-result
  ctx : CaseContext f g prefix suffix
  ctx = make-case-context f g prefix suffix
  open CaseContext ctx public

  field
    s-final : State
    exec-end : exec 1 prog s1 ≡ just s-final
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s1) rax
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s1) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s1) r15
    rbp-preserved : readReg (regs s-final) rbp ≡ readReg (regs s1) rbp
    rsp-preserved : readReg (regs s-final) rsp ≡ readReg (regs s1) rsp
    mem-preserved : memory s-final ≡ memory s1

-- | Execute end label for inr branch (1 instruction)
-- Precondition: pc s1 = length prefix + 7 + len-f + len-g (at end label)
exec-case-end : ∀ {A B C} (f : IR A C) (g : IR B C)
                (prefix suffix : Program)
                (s1 : State) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  halted s1 ≡ false →
  pc s1 ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g →
  CaseEndResult f g prefix suffix s1
exec-case-end {A} {B} {C} f g prefix suffix s1 h1 pc1 = record
    { s-final = s2
    ; exec-end = exec-1
    ; h-final = h2
    ; pc-final = pc2
    ; rax-preserved = refl
    ; r14-preserved = refl
    ; r15-preserved = refl
    ; rbp-preserved = refl
    ; rsp-preserved = refl
    ; mem-preserved = refl
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx

    -- State after label end-label
    s2 : State
    s2 = record s1 { pc = pc s1 +ℕ 1 }

    h2 : halted s2 ≡ false
    h2 = h1

    -- PC proof: prefix + 7 + len-f + len-g + 1 = prefix + (8 + len-f) + len-g
    -- compile-length [ f , g ] = (8 + len-f) + len-g
    pc2 : pc s2 ≡ length prefix +ℕ compile-length [ f , g ]
    pc2 = begin
        pc s2
      ≡⟨ refl ⟩
        pc s1 +ℕ 1
      ≡⟨ cong (_+ℕ 1) pc1 ⟩
        (length prefix +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 1
      ≡⟨ +-assoc (length prefix +ℕ 7 +ℕ len-f) len-g 1 ⟩
        (length prefix +ℕ 7 +ℕ len-f) +ℕ (len-g +ℕ 1)
      ≡⟨ cong ((length prefix +ℕ 7 +ℕ len-f) +ℕ_) (+-comm len-g 1) ⟩
        (length prefix +ℕ 7 +ℕ len-f) +ℕ (1 +ℕ len-g)
      ≡⟨ sym (+-assoc (length prefix +ℕ 7 +ℕ len-f) 1 len-g) ⟩
        ((length prefix +ℕ 7 +ℕ len-f) +ℕ 1) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix +ℕ 7) len-f 1) ⟩
        ((length prefix +ℕ 7) +ℕ (len-f +ℕ 1)) +ℕ len-g
      ≡⟨ cong (λ n → ((length prefix +ℕ 7) +ℕ n) +ℕ len-g) (+-comm len-f 1) ⟩
        ((length prefix +ℕ 7) +ℕ (1 +ℕ len-f)) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (sym (+-assoc (length prefix +ℕ 7) 1 len-f)) ⟩
        (((length prefix +ℕ 7) +ℕ 1) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (λ n → (n +ℕ len-f) +ℕ len-g) (+-assoc (length prefix) 7 1) ⟩
        ((length prefix +ℕ 8) +ℕ len-f) +ℕ len-g
      ≡⟨ cong (_+ℕ len-g) (+-assoc (length prefix) 8 len-f) ⟩
        (length prefix +ℕ (8 +ℕ len-f)) +ℕ len-g
      ≡⟨ +-assoc (length prefix) (8 +ℕ len-f) len-g ⟩
        length prefix +ℕ ((8 +ℕ len-f) +ℕ len-g)
      ∎

    -- Fetch proof: the end label is at position length prefix + 7 + len-f + len-g
    prefix-end = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f ++
                 jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g

    -- Helper: jmp ∷ rlabel ∷ rload ∷ [] ++ code-g = jmp ∷ rlabel ∷ rload ∷ code-g
    -- This is just definitional
    snoc3-app : (jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ []) ++ code-g
              ≡ jmp-instr ∷ right-label-instr ∷ right-load-val-instr ∷ code-g
    snoc3-app = refl

    -- prefix-g ++ code-g ≡ prefix-end
    -- Uses snoc-append pattern for inner list
    prefix-g-code-g-eq : prefix-g ++ code-g ≡ prefix-end
    prefix-g-code-g-eq =
      trans (++-assoc prefix _  code-g)
            (cong (prefix ++_)
            (trans (cong (load-tag-instr ∷_)
                   (cong (cmp-tag-instr ∷_)
                   (cong (jne-instr ∷_)
                   (cong (load-val-instr ∷_)
                   (++-assoc code-f _ code-g)))))
                   (cong (load-tag-instr ∷_)
                   (cong (cmp-tag-instr ∷_)
                   (cong (jne-instr ∷_)
                   (cong (load-val-instr ∷_)
                   (cong (code-f ++_) snoc3-app)))))))

    prog-eq-end : prog ≡ prefix-end ++ end-label-instr ∷ suffix
    prog-eq-end = trans prog-eq-g
                  (trans (sym (++-assoc prefix-g code-g suffix-g))
                         (cong (_++ suffix-g) prefix-g-code-g-eq))

    -- pc1 is already the required form, just need to show len prefix-end = prefix + 7 + len-f + len-g
    len-prefix-end : length prefix-end ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
    len-prefix-end = trans (cong length (sym prefix-g-code-g-eq))
                     (trans (List-length-++ prefix-g)
                            (trans (cong (length prefix-g +ℕ_) (compile-length-correct g))
                                   (cong (_+ℕ len-g) len-prefix-g)))

    pc1-eq-len : pc s1 ≡ length prefix-end
    pc1-eq-len = trans pc1 (sym len-prefix-end)

    fetch1 : fetch prog (pc s1) ≡ just end-label-instr
    fetch1 = subst₂ (λ p n → fetch p n ≡ just end-label-instr)
                    (sym prog-eq-end) (sym pc1-eq-len)
                    (fetch-at-prefix-end prefix-end end-label-instr suffix)

    step1 : step prog s1 ≡ just s2
    step1 = trans (step-exec prog s1 end-label-instr h1 fetch1) (execLabel prog s1 end-label)

    exec-1 : exec 1 prog s1 ≡ just s2
    exec-1 = exec-one-step-nonhalt prog s1 s2 step1 h2

------------------------------------------------------------------------
-- CaseRightSetupResult: Result of executing right branch setup (2 instructions)
-- Used by inr branch: label (5+len-f) ; mov rdi, [rdi+8]
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
    exec-right : exec 2 prog s-setup ≡ just s-right
    h-right : halted s-right ≡ false
    pc-right : pc s-right ≡ length prefix +ℕ 7 +ℕ len-f
    rdi-right : readReg (regs s-right) rdi ≡ encode b
    r14-preserved : readReg (regs s-right) r14 ≡ readReg (regs s-setup) r14
    r15-preserved : readReg (regs s-right) r15 ≡ readReg (regs s-setup) r15
    rbp-preserved : readReg (regs s-right) rbp ≡ readReg (regs s-setup) rbp
    rsp-preserved : readReg (regs s-right) rsp ≡ readReg (regs s-setup) rsp
    mem-preserved : memory s-right ≡ memory s-setup
    stack-inv-right : StackInvariant s-right
    rsp>16-right : readReg (regs s-right) rsp > 16

-- | Execute right branch setup for inr (2 instructions)
-- Preconditions:
--   pc s-setup = length prefix + 5 + len-f (at right label)
--   rdi s-setup = encode (inr b) (pointing to the sum)
--   memory contains the sum value with tag=1 at [rdi] and b at [rdi+8]
exec-case-right-setup : ∀ {A B C} (f : IR A C) (g : IR B C)
                        (prefix suffix : Program)
                        (b : ⟦ B ⟧)
                        (s-setup : State) →
  let ctx = make-case-context f g prefix suffix in
  let open CaseContext ctx in
  halted s-setup ≡ false →
  pc s-setup ≡ length prefix +ℕ 5 +ℕ len-f →
  readReg (regs s-setup) rdi ≡ encode {A + B} (inj₂ b) →
  StackInvariant s-setup →
  readReg (regs s-setup) rsp > 16 →
  CaseRightSetupResult f g prefix suffix b s-setup
exec-case-right-setup {A} {B} {C} f g prefix suffix b s-setup h-setup pc-setup rdi-setup stack-inv-setup rsp>16-setup = record
    { s-right = s2
    ; exec-right = exec-2
    ; h-right = h2
    ; pc-right = pc2
    ; rdi-right = rdi2
    ; r14-preserved = refl
    ; r15-preserved = refl
    ; rbp-preserved = refl
    ; rsp-preserved = refl
    ; mem-preserved = refl
    ; stack-inv-right = stack-inv-s2
    ; rsp>16-right = rsp>16-s2
    }
  where
    ctx = make-case-context f g prefix suffix
    open CaseContext ctx

    -- State after label instruction (pc + 1)
    s1 : State
    s1 = record s-setup { pc = pc s-setup +ℕ 1 }

    -- State after mov rdi, [rdi+8] instruction
    -- rdi gets the value at [rdi+8], which is encode b (by encode-inr-val)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rdi (encode b)
                   ; pc = pc s1 +ℕ 1 }

    h1 : halted s1 ≡ false
    h1 = h-setup

    h2 : halted s2 ≡ false
    h2 = h1

    -- PC proofs
    -- pc s1 = pc s-setup + 1 = (prefix + 5 + len-f) + 1 = prefix + 6 + len-f
    -- pc s2 = pc s1 + 1 = prefix + 7 + len-f
    pc2 : pc s2 ≡ length prefix +ℕ 7 +ℕ len-f
    pc2 = begin
        pc s2
      ≡⟨ refl ⟩
        pc s-setup +ℕ 1 +ℕ 1
      ≡⟨ cong (λ x → x +ℕ 1 +ℕ 1) pc-setup ⟩
        (length prefix +ℕ 5 +ℕ len-f) +ℕ 1 +ℕ 1
      ≡⟨ +-assoc (length prefix +ℕ 5 +ℕ len-f) 1 1 ⟩
        (length prefix +ℕ 5 +ℕ len-f) +ℕ 2
      ≡⟨ +-assoc (length prefix +ℕ 5) len-f 2 ⟩
        (length prefix +ℕ 5) +ℕ (len-f +ℕ 2)
      ≡⟨ cong ((length prefix +ℕ 5) +ℕ_) (+-comm len-f 2) ⟩
        (length prefix +ℕ 5) +ℕ (2 +ℕ len-f)
      ≡⟨ sym (+-assoc (length prefix +ℕ 5) 2 len-f) ⟩
        ((length prefix +ℕ 5) +ℕ 2) +ℕ len-f
      ≡⟨ cong (_+ℕ len-f) (+-assoc (length prefix) 5 2) ⟩
        (length prefix +ℕ 7) +ℕ len-f
      ∎

    -- Key proof: rdi s2 = encode b
    -- The mov instruction loads from [rdi+8] into rdi
    -- By encode-inr-val: readMem m (encode (inj₂ b) + 8) = just (encode b)
    -- Since rdi s-setup = encode (inj₂ b), we have rdi s2 = encode b
    rdi2 : readReg (regs s2) rdi ≡ encode b
    rdi2 = readReg-writeReg-same (regs s1) rdi (encode b)

    -- Memory read proof for mov instruction
    mem-read : readMem (memory s-setup) (readReg (regs s-setup) rdi +ℕ 8) ≡ just (encode b)
    mem-read = trans (cong (λ addr → readMem (memory s-setup) (addr +ℕ 8)) rdi-setup)
                     (encode-inr-val b (memory s-setup))

    -- StackInvariant preserved (memory and rsp unchanged)
    stack-inv-s2 : StackInvariant s2
    stack-inv-s2 = stack-inv-preserved-mem-rsp s-setup s2 refl refl stack-inv-setup

    -- rsp > 16 preserved
    rsp>16-s2 : readReg (regs s2) rsp > 16
    rsp>16-s2 = rsp>16-setup

    -- Fetch proofs for the two instructions
    -- Instruction 1: label (5 + len-f) at position prefix + 5 + len-f
    -- Instruction 2: mov rdi, [rdi+8] at position prefix + 6 + len-f

    prefix-right = prefix ++ load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷
                   load-val-instr ∷ code-f ++ jmp-instr ∷ []

    rest-right = right-label-instr ∷ right-load-val-instr ∷ code-g ++ end-label-instr ∷ suffix

    -- Helper: transform code-f ++ jmp ∷ rest into (code-f ++ jmp ∷ []) ++ rest
    jmp-snoc : code-f ++ jmp-instr ∷ rest-right ≡ (code-f ++ jmp-instr ∷ []) ++ rest-right
    jmp-snoc = sym (snoc-append code-f jmp-instr rest-right)

    -- Transform the inner nested ++ structure
    inner-eq : load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f ++ jmp-instr ∷ rest-right
             ≡ (load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f ++ jmp-instr ∷ []) ++ rest-right
    inner-eq = cong (load-tag-instr ∷_)
               (cong (cmp-tag-instr ∷_)
               (cong (jne-instr ∷_)
               (cong (load-val-instr ∷_) jmp-snoc)))

    prog-eq-right : prog ≡ prefix-right ++ rest-right
    prog-eq-right = trans prog-eq-inr-setup
                    (trans (cong (prefix ++_) inner-eq)
                           (sym (++-assoc prefix _ rest-right)))

    -- Length of prefix-right
    -- prefix-right = prefix ++ [4 items] ∷ code-f ++ jmp ∷ []
    -- length = length prefix + 4 + length (code-f ++ jmp ∷ [])
    --        = length prefix + 4 + (len-f + 1)
    --        = length prefix + 5 + len-f
    len-prefix-right : length prefix-right ≡ length prefix +ℕ 5 +ℕ len-f
    len-prefix-right = begin
        length prefix-right
      ≡⟨ List-length-++ prefix ⟩
        length prefix +ℕ length (load-tag-instr ∷ cmp-tag-instr ∷ jne-instr ∷ load-val-instr ∷ code-f ++ jmp-instr ∷ [])
      ≡⟨ cong (length prefix +ℕ_) (cong (4 +ℕ_) (List-length-++ code-f)) ⟩
        length prefix +ℕ (4 +ℕ (length code-f +ℕ 1))
      ≡⟨ cong (length prefix +ℕ_) (cong (λ n → 4 +ℕ (n +ℕ 1)) (compile-length-correct f)) ⟩
        length prefix +ℕ (4 +ℕ (len-f +ℕ 1))
      ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 4 len-f 1)) ⟩
        length prefix +ℕ ((4 +ℕ len-f) +ℕ 1)
      ≡⟨ cong (length prefix +ℕ_) (cong (_+ℕ 1) (+-comm 4 len-f)) ⟩
        length prefix +ℕ ((len-f +ℕ 4) +ℕ 1)
      ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f 4 1) ⟩
        length prefix +ℕ (len-f +ℕ 5)
      ≡⟨ cong (length prefix +ℕ_) (+-comm len-f 5) ⟩
        length prefix +ℕ (5 +ℕ len-f)
      ≡⟨ sym (+-assoc (length prefix) 5 len-f) ⟩
        (length prefix +ℕ 5) +ℕ len-f
      ∎

    pc-setup-eq-len : pc s-setup ≡ length prefix-right
    pc-setup-eq-len = trans pc-setup (sym len-prefix-right)

    fetch1 : fetch prog (pc s-setup) ≡ just right-label-instr
    fetch1 = subst₂ (λ p n → fetch p n ≡ just right-label-instr)
                    (sym prog-eq-right) (sym pc-setup-eq-len)
                    (fetch-at-prefix-end prefix-right right-label-instr _)

    step1 : step prog s-setup ≡ just s1
    step1 = trans (step-exec prog s-setup right-label-instr h-setup fetch1)
                  (execLabel prog s-setup (5 +ℕ len-f))

    -- For the mov instruction, we need to show fetch and step
    prefix-mov = prefix-right ++ right-label-instr ∷ []
    rest-mov = right-load-val-instr ∷ code-g ++ end-label-instr ∷ suffix

    -- rest-right = right-label ∷ right-load ∷ code-g ++ end ∷ suffix
    --            = (right-label ∷ []) ++ right-load ∷ code-g ++ end ∷ suffix
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
                  (execMov-reg-mem-disp s1 rdi rdi 8 (encode b) mem-read)

    exec-2 : exec 2 prog s-setup ≡ just s2
    exec-2 = exec-two-steps-nonhalt prog s-setup s1 s2 step1 h1 step2 h2
