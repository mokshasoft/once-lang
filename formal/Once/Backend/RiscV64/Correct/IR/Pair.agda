------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Pair
--
-- Helper records and functions for pair proofs.
-- Extracts non-recursive parts to reduce mutual block compilation time.
-- The recursive calls stay in MutualIR.agda.
--
-- Pair structure for RISC-V:
--   Phase 1: Setup     (2 instr) - addi sp sp -16; mv s1 a0
--   Phase 2: Execute f (recursive)
--   Phase 3: Middle    (2 instr) - sd a0 0(sp); mv a0 s1
--   Phase 4: Execute g (recursive)
--   Phase 5: Final     (2 instr) - sd a0 8(sp); mv a0 sp
--
-- Total: 6 + len-f + len-g instructions
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.Pair where

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
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Pair Context: computed values that don't depend on execution
------------------------------------------------------------------------

record PairContext {A B C : Type} (f : IR C A) (g : IR C B)
                   (prefix suffix : Program) : Set where
  field
    -- Computed lengths
    len-f : ℕ
    len-g : ℕ

    -- Computed programs
    code-f : Program
    code-g : Program
    prog : Program

    -- Setup instructions (2)
    setup-alloc : Instr    -- addi sp sp -16
    setup-save : Instr     -- mv s1 a0

    -- Middle instructions (2)
    middle-store : Instr   -- sd a0 0(sp)
    middle-restore : Instr -- mv a0 s1

    -- Final instructions (2)
    final-store : Instr    -- sd a0 8(sp)
    final-result : Instr   -- mv a0 sp

    -- Derived prefixes/suffixes
    prefix-f : Program     -- prefix ++ setup
    suffix-f : Program     -- middle ++ code-g ++ final ++ suffix
    prefix-g : Program     -- prefix-f ++ code-f ++ middle
    suffix-g : Program     -- final ++ suffix
    prefix-mid : Program   -- prefix-f ++ code-f
    prefix-final : Program -- prefix-g ++ code-g

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 2
    len-prefix-g : length prefix-g ≡ length prefix +ℕ 4 +ℕ len-f
    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 2 +ℕ len-f
    len-prefix-final : length prefix-final ≡ length prefix +ℕ 4 +ℕ len-f +ℕ len-g

    -- Program equalities for each phase
    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g

-- | Compute the pair context
make-pair-context : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) →
  PairContext f g prefix suffix
make-pair-context {A} {B} {C} f g prefix suffix = record
  { len-f = len-f
  ; len-g = len-g
  ; code-f = code-f
  ; code-g = code-g
  ; prog = prog
  ; setup-alloc = setup-alloc
  ; setup-save = setup-save
  ; middle-store = middle-store
  ; middle-restore = middle-restore
  ; final-store = final-store
  ; final-result = final-result
  ; prefix-f = prefix-f
  ; suffix-f = suffix-f
  ; prefix-g = prefix-g
  ; suffix-g = suffix-g
  ; prefix-mid = prefix-mid
  ; prefix-final = prefix-final
  ; len-prefix-f = len-prefix-f
  ; len-prefix-g = len-prefix-g
  ; len-prefix-mid = len-prefix-mid
  ; len-prefix-final = len-prefix-final
  ; prog-eq-f = prog-eq-f
  ; prog-eq-g = prog-eq-g
  }
  where
    len-f = compile-length f
    len-g = compile-length g
    code-f = compile-riscv f
    code-g = compile-riscv g
    prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix

    -- Setup instructions (2)
    setup-alloc = addi sp sp neg16
    setup-save = mv s1 a0

    -- Middle instructions (2)
    middle-store = sd a0 (+ 0) sp
    middle-restore = mv a0 s1

    -- Final instructions (2)
    final-store = sd a0 (+ 8) sp
    final-result = mv a0 sp

    -- Final instruction sequence
    final-instrs = final-store ∷ final-result ∷ []

    -- Derived programs
    prefix-f : Program
    prefix-f = prefix ++ setup-alloc ∷ setup-save ∷ []

    suffix-f : Program
    suffix-f = middle-store ∷ middle-restore ∷ code-g ++ final-store ∷ final-result ∷ suffix

    prefix-mid : Program
    prefix-mid = prefix-f ++ code-f

    prefix-g : Program
    prefix-g = (prefix-f ++ code-f) ++ middle-store ∷ middle-restore ∷ []

    suffix-g : Program
    suffix-g = final-store ∷ final-result ∷ suffix

    prefix-final : Program
    prefix-final = prefix-g ++ code-g

    -- Length equalities
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 2
    len-prefix-f = List-length-++ prefix

    len-prefix-mid : length prefix-mid ≡ length prefix +ℕ 2 +ℕ len-f
    len-prefix-mid = begin
      length prefix-mid
        ≡⟨ List-length-++ prefix-f ⟩
      length prefix-f +ℕ length code-f
        ≡⟨ cong (_+ℕ length code-f) len-prefix-f ⟩
      (length prefix +ℕ 2) +ℕ length code-f
        ≡⟨ cong ((length prefix +ℕ 2) +ℕ_) (compile-length-correct f) ⟩
      (length prefix +ℕ 2) +ℕ len-f
        ∎

    len-prefix-g : length prefix-g ≡ length prefix +ℕ 4 +ℕ len-f
    len-prefix-g = begin
      length prefix-g
        ≡⟨ List-length-++ (prefix-f ++ code-f) ⟩
      length (prefix-f ++ code-f) +ℕ 2
        ≡⟨ cong (_+ℕ 2) len-prefix-mid ⟩
      (length prefix +ℕ 2 +ℕ len-f) +ℕ 2
        ≡⟨ +-assoc (length prefix +ℕ 2) len-f 2 ⟩
      (length prefix +ℕ 2) +ℕ (len-f +ℕ 2)
        ≡⟨ +-assoc (length prefix) 2 (len-f +ℕ 2) ⟩
      length prefix +ℕ (2 +ℕ (len-f +ℕ 2))
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 2 len-f 2)) ⟩
      length prefix +ℕ ((2 +ℕ len-f) +ℕ 2)
        ≡⟨ cong (λ x → length prefix +ℕ (x +ℕ 2)) (+-comm 2 len-f) ⟩
      length prefix +ℕ ((len-f +ℕ 2) +ℕ 2)
        ≡⟨ cong (length prefix +ℕ_) (+-assoc len-f 2 2) ⟩
      length prefix +ℕ (len-f +ℕ 4)
        ≡⟨ sym (+-assoc (length prefix) len-f 4) ⟩
      (length prefix +ℕ len-f) +ℕ 4
        ≡⟨ cong (_+ℕ 4) (+-comm (length prefix) len-f) ⟩
      (len-f +ℕ length prefix) +ℕ 4
        ≡⟨ +-assoc len-f (length prefix) 4 ⟩
      len-f +ℕ (length prefix +ℕ 4)
        ≡⟨ +-comm len-f (length prefix +ℕ 4) ⟩
      (length prefix +ℕ 4) +ℕ len-f
        ∎

    len-prefix-final : length prefix-final ≡ length prefix +ℕ 4 +ℕ len-f +ℕ len-g
    len-prefix-final = begin
      length prefix-final
        ≡⟨ List-length-++ prefix-g ⟩
      length prefix-g +ℕ length code-g
        ≡⟨ cong₂ _+ℕ_ len-prefix-g (compile-length-correct g) ⟩
      ((length prefix +ℕ 4) +ℕ len-f) +ℕ len-g
        ∎
      where
        open import Relation.Binary.PropositionalEquality using (cong₂)

    -- Program equality for f
    -- prog = prefix ++ (addi ∷ mv ∷ code-f ++ middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
    -- Need: prog = prefix-f ++ code-f ++ suffix-f
    --     = (prefix ++ addi ∷ mv ∷ []) ++ code-f ++ (middle-store ∷ middle-restore ∷ code-g ++ final-store ∷ final-result ∷ suffix)

    -- Helper: code-g ++ final-instrs ++ suffix = code-g ++ final-store ∷ final-result ∷ suffix
    final-suffix-eq : (code-g ++ final-instrs) ++ suffix ≡ code-g ++ (final-store ∷ final-result ∷ suffix)
    final-suffix-eq = ++-assoc code-g final-instrs suffix

    -- Helper: middle with code-g and final
    middle-suffix-eq : (middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
                     ≡ middle-store ∷ middle-restore ∷ (code-g ++ final-store ∷ final-result ∷ suffix)
    middle-suffix-eq = cong (middle-store ∷_) (cong (middle-restore ∷_) final-suffix-eq)

    -- Helper: code-f with middle, code-g and final
    f-suffix-eq : (code-f ++ middle-store ∷ middle-restore ∷ code-g ++ final-instrs) ++ suffix
                ≡ code-f ++ suffix-f
    f-suffix-eq = trans (++-assoc code-f (middle-store ∷ middle-restore ∷ code-g ++ final-instrs) suffix)
                        (cong (code-f ++_) middle-suffix-eq)

    -- Full program equality for f
    full-suffix-eq : compile-riscv ⟨ f , g ⟩ ++ suffix
                   ≡ setup-alloc ∷ setup-save ∷ (code-f ++ suffix-f)
    full-suffix-eq = cong (setup-alloc ∷_) (cong (setup-save ∷_) f-suffix-eq)

    prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
    prog-eq-f = trans (cong (prefix ++_) full-suffix-eq)
                      (sym (++-assoc prefix (setup-alloc ∷ setup-save ∷ []) (code-f ++ suffix-f)))

    -- Program equality for g (derived from f equality)
    prog-eq-g : prog ≡ prefix-g ++ code-g ++ suffix-g
    prog-eq-g = trans prog-eq-f (begin
      prefix-f ++ code-f ++ suffix-f
        ≡⟨ sym (++-assoc prefix-f code-f suffix-f) ⟩
      (prefix-f ++ code-f) ++ suffix-f
        ≡⟨ refl ⟩  -- suffix-f = middle-store ∷ middle-restore ∷ code-g ++ suffix-g
      prefix-mid ++ middle-store ∷ middle-restore ∷ code-g ++ suffix-g
        ≡⟨ sym (++-assoc prefix-mid (middle-store ∷ middle-restore ∷ []) (code-g ++ suffix-g)) ⟩
      (prefix-mid ++ middle-store ∷ middle-restore ∷ []) ++ (code-g ++ suffix-g)
        ≡⟨ refl ⟩
      prefix-g ++ code-g ++ suffix-g
        ∎)

------------------------------------------------------------------------
-- Helper for assembling pair result from f and g results
------------------------------------------------------------------------

-- This will be used by MutualIR to combine the recursive results
-- The actual step proofs for setup, middle, final phases are in the mutual block
-- (they don't depend on recursion, but extracting them here would duplicate work)
