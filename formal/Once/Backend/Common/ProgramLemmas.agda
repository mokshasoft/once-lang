------------------------------------------------------------------------
-- Once.Backend.Common.ProgramLemmas
--
-- Generic list manipulation lemmas for program composition proofs.
-- These lemmas handle the associativity juggling needed when executing
-- sequences of instructions with shifting prefix/suffix boundaries.
--
-- Polymorphic over instruction type for reuse across all backends.
--
-- Usage in backend:
--   open import Once.Backend.Common.ProgramLemmas
--   -- Then use compose-prog-eq, prog-shift-1, etc.
------------------------------------------------------------------------

module Once.Backend.Common.ProgramLemmas where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Basic list shift lemmas
------------------------------------------------------------------------

-- | Shift one instruction from suffix to prefix
-- prefix ++ (x ∷ rest) ≡ (prefix ++ x ∷ []) ++ rest
prog-shift-1 : ∀ {I : Set} (prefix : List I) (x : I) (rest : List I) →
  prefix ++ (x ∷ rest) ≡ (prefix ++ x ∷ []) ++ rest
prog-shift-1 prefix x rest = sym (++-assoc prefix (x ∷ []) rest)

-- | Shift two instructions from suffix to prefix
prog-shift-2 : ∀ {I : Set} (prefix : List I) (x y : I) (rest : List I) →
  prefix ++ (x ∷ y ∷ rest) ≡ (prefix ++ x ∷ y ∷ []) ++ rest
prog-shift-2 prefix x y rest = sym (++-assoc prefix (x ∷ y ∷ []) rest)

-- | Shift three instructions from suffix to prefix
prog-shift-3 : ∀ {I : Set} (prefix : List I) (x y z : I) (rest : List I) →
  prefix ++ (x ∷ y ∷ z ∷ rest) ≡ (prefix ++ x ∷ y ∷ z ∷ []) ++ rest
prog-shift-3 prefix x y z rest = sym (++-assoc prefix (x ∷ y ∷ z ∷ []) rest)

------------------------------------------------------------------------
-- Length after shift lemmas
------------------------------------------------------------------------

-- | Length after shifting 1 instruction
len-shift-1 : ∀ {I : Set} (prefix : List I) (x : I) →
  length (prefix ++ x ∷ []) ≡ length prefix +ℕ 1
len-shift-1 prefix x = length-++ prefix {x ∷ []}

-- | Length after shifting 2 instructions
len-shift-2 : ∀ {I : Set} (prefix : List I) (x y : I) →
  length (prefix ++ x ∷ y ∷ []) ≡ length prefix +ℕ 2
len-shift-2 prefix x y = length-++ prefix {x ∷ y ∷ []}

-- | Length after shifting 3 instructions
len-shift-3 : ∀ {I : Set} (prefix : List I) (x y z : I) →
  length (prefix ++ x ∷ y ∷ z ∷ []) ≡ length prefix +ℕ 3
len-shift-3 prefix x y z = length-++ prefix {x ∷ y ∷ z ∷ []}

------------------------------------------------------------------------
-- Compose program equality lemmas
------------------------------------------------------------------------
-- These are used when proving correctness of sequential composition (g ∘ f)
-- where compile-x86 (g ∘ f) = compile-x86 f ++ [transfer] ++ compile-x86 g

-- | Compose program equality: rearrange for executing f
-- Shows: prefix ++ (code-f ++ [transfer] ++ code-g) ++ suffix
--      ≡ prefix ++ code-f ++ (transfer ∷ code-g ++ suffix)
compose-prog-eq : ∀ {I : Set} (prefix code-f code-g suffix : List I) (transfer : I) →
  prefix ++ (code-f ++ transfer ∷ [] ++ code-g) ++ suffix ≡
  prefix ++ code-f ++ (transfer ∷ code-g ++ suffix)
compose-prog-eq prefix code-f code-g suffix transfer =
  cong (prefix ++_) (++-assoc code-f (transfer ∷ code-g) suffix)

-- | Compose program equality: rearrange for executing transfer
-- Shows: prefix ++ code-f ++ (transfer ∷ code-g ++ suffix)
--      ≡ (prefix ++ code-f) ++ transfer ∷ (code-g ++ suffix)
compose-transfer-eq : ∀ {I : Set} (prefix code-f code-g suffix : List I) (transfer : I) →
  prefix ++ code-f ++ (transfer ∷ code-g ++ suffix) ≡
  (prefix ++ code-f) ++ transfer ∷ (code-g ++ suffix)
compose-transfer-eq prefix code-f code-g suffix transfer =
  sym (++-assoc prefix code-f (transfer ∷ code-g ++ suffix))

-- | Compose program equality: rearrange for executing g
-- Shows: (prefix ++ code-f) ++ transfer ∷ (code-g ++ suffix)
--      ≡ (prefix ++ code-f ++ transfer ∷ []) ++ code-g ++ suffix
compose-g-eq : ∀ {I : Set} (prefix code-f code-g suffix : List I) (transfer : I) →
  (prefix ++ code-f) ++ transfer ∷ (code-g ++ suffix) ≡
  (prefix ++ code-f ++ transfer ∷ []) ++ code-g ++ suffix
compose-g-eq prefix code-f code-g suffix transfer = begin
    (prefix ++ code-f) ++ transfer ∷ (code-g ++ suffix)
  ≡⟨ ++-assoc prefix code-f (transfer ∷ (code-g ++ suffix)) ⟩
    prefix ++ (code-f ++ (transfer ∷ (code-g ++ suffix)))
  ≡⟨ cong (prefix ++_) (sym (++-assoc code-f (transfer ∷ []) (code-g ++ suffix))) ⟩
    prefix ++ ((code-f ++ transfer ∷ []) ++ (code-g ++ suffix))
  ≡⟨ sym (++-assoc prefix (code-f ++ transfer ∷ []) (code-g ++ suffix)) ⟩
    (prefix ++ (code-f ++ transfer ∷ [])) ++ (code-g ++ suffix)
  ∎

------------------------------------------------------------------------
-- Empty prefix/suffix lemmas
------------------------------------------------------------------------

-- | Program with empty prefix and suffix
prog-empty-prefix-suffix : ∀ {I : Set} (code : List I) →
  [] ++ code ++ [] ≡ code
prog-empty-prefix-suffix code = ++-identityʳ code
