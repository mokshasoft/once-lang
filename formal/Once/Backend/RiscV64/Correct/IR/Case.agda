------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Case
--
-- Helper records and functions for case proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
--
-- Case structure for RISC-V:
--   Dispatch (3 instr) - ld t0 0(a0); ld a0 8(a0); bne t0 zero offset
--
--   Left path (inj₁): tag=0, branch NOT taken
--     - Execute f
--     - j (skip g)
--     - label (right-branch entry point, skipped)
--     - code-g (skipped by jump)
--     - label (end)
--
--   Right path (inj₂): tag≠0, branch TAKEN
--     - code-f + j (skipped by branch)
--     - label (we jump here)
--     - Execute g
--     - label (end)
--
-- Total: (6 + len-f) + len-g instructions
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.Case where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates using (encode)
open import Once.Backend.RiscV64.Correct.CompileLength
open import Once.Backend.RiscV64.Correct.Star
  using (Star; star-trans)
open import Once.Backend.RiscV64.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-a0; ir-s1)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Helper: snoc-append pushes ++ into snoc lists
------------------------------------------------------------------------

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

    -- Dispatch instructions (3)
    dispatch-tag : Instr      -- ld t0 0(a0)
    dispatch-val : Instr      -- ld a0 8(a0)
    dispatch-branch : Instr   -- bne t0 zero offset

    -- Control flow
    left-jump : Instr         -- j (skip g)
    right-label : Instr       -- label (right entry)
    end-label : Instr         -- label (end)

    -- Derived prefixes/suffixes for left path (f)
    prefix-f : Program        -- prefix ++ dispatch
    suffix-f : Program        -- jump ++ right-label ++ code-g ++ end-label ++ suffix

    -- Derived prefixes/suffixes for right path (g)
    prefix-g : Program        -- prefix ++ dispatch ++ code-f ++ jump ++ right-label
    suffix-g : Program        -- end-label ++ suffix

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 3
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 5 +ℕ len-f

    -- Program equalities for both paths
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
  ; dispatch-tag = dispatch-tag
  ; dispatch-val = dispatch-val
  ; dispatch-branch = dispatch-branch
  ; left-jump = left-jump
  ; right-label = right-label
  ; end-label = end-label
  ; prefix-f = prefix-f
  ; suffix-f = suffix-f
  ; prefix-g = prefix-g
  ; suffix-g = suffix-g
  ; len-prefix-f = len-prefix-f
  ; len-prefix-g = len-prefix-g
  ; prog-eq-f = prog-eq-f
  ; prog-eq-g = prog-eq-g
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-riscv f
    code-g = compile-riscv g
    prog = prefix ++ compile-riscv ([_,_] f g) ++ suffix

    -- Dispatch instructions (3)
    dispatch-tag = ld t0 (+ 0) a0     -- load tag
    dispatch-val = ld a0 (+ 8) a0     -- load value
    -- Branch offset: skip 1 + len-f + 1 = 2 + len-f (to right-label)
    dispatch-branch = bne t0 zero (+ (2 +ℕ len-f))

    -- Control flow instructions
    -- From CodeGen: j end-offset where end-offset = + (2 +ℕ len-g)
    left-jump = j (+ (2 +ℕ len-g))
    -- From CodeGen: label (4 +ℕ len-f) -- position after dispatch(3) + code-f + jump(1)
    right-label = label (4 +ℕ len-f)
    -- From CodeGen: label ((5 +ℕ len-f) +ℕ len-g)
    end-label = label ((5 +ℕ len-f) +ℕ len-g)

    -- Derived programs
    prefix-f : Program
    prefix-f = prefix ++ dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ []

    suffix-f : Program
    suffix-f = left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix

    prefix-g : Program
    prefix-g = (prefix-f ++ code-f) ++ left-jump ∷ right-label ∷ []

    suffix-g : Program
    suffix-g = end-label ∷ suffix

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 3
    len-prefix-f = List-length-++ prefix

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 5 +ℕ len-f
    len-prefix-g = begin
      length prefix-g
        ≡⟨ List-length-++ (prefix-f ++ code-f) ⟩
      length (prefix-f ++ code-f) +ℕ 2
        ≡⟨ cong (_+ℕ 2) (List-length-++ prefix-f) ⟩
      (length prefix-f +ℕ length code-f) +ℕ 2
        ≡⟨ cong (λ x → (x +ℕ length code-f) +ℕ 2) len-prefix-f ⟩
      ((length prefix +ℕ 3) +ℕ length code-f) +ℕ 2
        ≡⟨ cong (λ x → ((length prefix +ℕ 3) +ℕ x) +ℕ 2) (compile-length-correct f) ⟩
      ((length prefix +ℕ 3) +ℕ len-f) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ 3) len-f 2 ⟩
      (length prefix +ℕ 3) +ℕ (len-f +ℕ 2)
        ≡⟨ +-assoc (length prefix) 3 (len-f +ℕ 2) ⟩
      length prefix +ℕ (3 +ℕ (len-f +ℕ 2))
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 3 len-f 2)) ⟩
      length prefix +ℕ ((3 +ℕ len-f) +ℕ 2)
        ≡⟨ cong (λ x → length prefix +ℕ (x +ℕ 2)) (+-comm 3 len-f) ⟩
      length prefix +ℕ ((len-f +ℕ 3) +ℕ 2)
        ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f 3 2) ⟩
      length prefix +ℕ (len-f +ℕ 5)
        ≡⟨ sym (+-assoc (length prefix) len-f 5) ⟩
      (length prefix +ℕ len-f) +ℕ 5
        ≡⟨ cong (_+ℕ 5) (+-comm (length prefix) len-f) ⟩
      (len-f +ℕ length prefix) +ℕ 5
        ≡⟨ +-assoc len-f (length prefix) 5 ⟩
      len-f +ℕ (length prefix +ℕ 5)
        ≡⟨ +-comm len-f (length prefix +ℕ 5) ⟩
      (length prefix +ℕ 5) +ℕ len-f
        ∎

    -- Program equalities

    -- Main rearrangement: move suffix inside the nested structure
    -- Transforms: (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
    --         to: code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix
    case-code-suffix : (code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ []) ++ suffix
                     ≡ code-f ++ left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix
    case-code-suffix = trans (++-assoc code-f _ suffix)
                       (cong (code-f ++_)
                       (cong (left-jump ∷_)
                       (cong (right-label ∷_)
                       (snoc-append code-g end-label suffix))))

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans (cong (prefix ++_)
                       (cong (dispatch-tag ∷_)
                       (cong (dispatch-val ∷_)
                       (cong (dispatch-branch ∷_)
                       case-code-suffix))))
                      (sym (++-assoc prefix (dispatch-tag ∷ dispatch-val ∷ dispatch-branch ∷ []) (code-f ++ suffix-f)))

    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-g = trans prog-eq-f (begin
      prefix-f ++ code-f ++ suffix-f
        ≡⟨ sym (++-assoc prefix-f code-f suffix-f) ⟩
      (prefix-f ++ code-f) ++ suffix-f
        ≡⟨ refl ⟩  -- suffix-f = left-jump ∷ right-label ∷ code-g ++ end-label ∷ suffix
      (prefix-f ++ code-f) ++ (left-jump ∷ right-label ∷ code-g ++ suffix-g)
        ≡⟨ sym (++-assoc (prefix-f ++ code-f) (left-jump ∷ right-label ∷ []) (code-g ++ suffix-g)) ⟩
      ((prefix-f ++ code-f) ++ left-jump ∷ right-label ∷ []) ++ (code-g ++ suffix-g)
        ≡⟨ refl ⟩
      prefix-g ++ code-g ++ suffix-g
        ∎)

------------------------------------------------------------------------
-- Assembler for case results (used by MutualIR)
------------------------------------------------------------------------

-- The actual dispatch execution and branch handling stays in MutualIR
-- because it involves step-by-step execution proofs that depend on
-- the encoding axioms for inj₁/inj₂.
