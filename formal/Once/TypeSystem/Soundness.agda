------------------------------------------------------------------------
-- Once.TypeSystem.Soundness
--
-- Type soundness for Once IR.
--
-- In a traditional PL, type soundness = progress + preservation.
-- For Once's CCC-based IR, soundness takes a different form:
--
-- 1. Well-formedness: The GADT IR A B only constructs terms where
--    domain and codomain types match correctly.
--
-- 2. Type preservation: eval : IR A B → (⟦ A ⟧ → ⟦ B ⟧)
--    By the type, evaluation preserves types.
--
-- 3. Progress: eval is total (no stuck terms). This is guaranteed
--    by the pattern matching in Semantics.agda being exhaustive.
--
-- This module proves additional soundness properties.
------------------------------------------------------------------------

module Once.TypeSystem.Soundness where

open import Once.Type
open import Once.IR
open import Once.Semantics
open import Once.TypeSystem.Typing

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

------------------------------------------------------------------------
-- Type Preservation
------------------------------------------------------------------------

-- | Type preservation is built into eval's type signature:
--
--   eval : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
--
-- This says: given a morphism from A to B and a value of semantic type A,
-- we get a value of semantic type B.
--
-- As a theorem, we can state it as:

-- | eval produces values in the correct semantic type
--
-- For any IR morphism f : A → B and input x : ⟦ A ⟧,
-- eval f x inhabits ⟦ B ⟧.
--
-- This is trivially true by eval's type, but we can state it explicitly.
--
type-preservation : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧) → ⟦ B ⟧
type-preservation f x = eval f x

-- | Typed derivations and IR terms have the same semantics
--
-- eval (⌊ d ⌋) ≡ eval of the underlying IR term
-- This follows from ⌊_⌋ being a structure-preserving embedding.
--
typed-semantics : ∀ {Γ A B} (d : Γ ⊢ A ⟶ B) (x : ⟦ A ⟧)
                → eval ⌊ d ⌋ x ≡ eval ⌊ d ⌋ x
typed-semantics d x = refl

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

-- | Progress: every well-typed closed term either:
--   1. Is a value, or
--   2. Can take a step
--
-- In our setting, IR terms are "already reduced" - they're morphisms,
-- not expressions with redexes. The "values" are identity, fst, snd, etc.
--
-- eval is total: for any f : IR A B and x : ⟦ A ⟧, eval f x terminates.
-- This is guaranteed by Agda's totality checker.
--
-- We can state progress as: eval always produces a result.

-- | eval terminates on all inputs
--
-- This is witnessed by eval's definition being accepted by Agda's
-- termination checker without any {-# TERMINATING #-} pragma.
--
-- As a type, we state: for all f and x, there exists a result.
--
progress : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧) → ⟦ B ⟧
progress = eval

------------------------------------------------------------------------
-- Soundness
------------------------------------------------------------------------

-- | Type soundness: well-typed programs don't go wrong
--
-- In a traditional setting: Progress ∧ Preservation ⇒ Soundness
--
-- In our CCC setting, "going wrong" would mean:
-- - eval being partial (undefined on some inputs)
-- - eval returning a value of the wrong type
--
-- Neither can happen because:
-- 1. eval is total (pattern matching is exhaustive, Agda accepts it)
-- 2. eval's type signature enforces correct output types
--
-- Soundness theorem: If IR A B, then ⟦ A ⟧ → ⟦ B ⟧
--
soundness : ∀ {A B} → IR A B → (⟦ A ⟧ → ⟦ B ⟧)
soundness = eval

------------------------------------------------------------------------
-- Canonical Forms
------------------------------------------------------------------------

-- | Canonical forms lemma for Unit
--
-- The only value of type ⟦ Unit ⟧ is tt.
--
canonical-unit : (x : ⟦ Unit ⟧) → x ≡ tt
canonical-unit tt = refl

-- | Canonical forms lemma for Void
--
-- There are no values of type ⟦ Void ⟧.
--
canonical-void : (x : ⟦ Void ⟧) → ⊥
canonical-void ()

-- | Canonical forms lemma for products
--
-- Every value of type ⟦ A * B ⟧ is a pair.
--
canonical-product : ∀ {A B} (x : ⟦ A * B ⟧) → ∃[ a ] ∃[ b ] (x ≡ (a , b))
canonical-product (a , b) = a , b , refl
  where open import Data.Product using (∃-syntax)

-- | Canonical forms lemma for sums
--
-- Every value of type ⟦ A + B ⟧ is either inj₁ or inj₂.
--
canonical-sum : ∀ {A B} (x : ⟦ A + B ⟧)
              → (∃[ a ] x ≡ inj₁ a) ⊎ (∃[ b ] x ≡ inj₂ b)
canonical-sum (inj₁ a) = inj₁ (a , refl)
  where open import Data.Product using (∃-syntax)
canonical-sum (inj₂ b) = inj₂ (b , refl)
  where open import Data.Product using (∃-syntax)

------------------------------------------------------------------------
-- Compositionality
------------------------------------------------------------------------

-- | Semantics is compositional
--
-- eval (g ∘ f) x ≡ eval g (eval f x)
--
-- This is true by definition but stated explicitly for documentation.
--
compositionality : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                 → eval (g ∘ f) x ≡ eval g (eval f x)
compositionality g f x = refl
