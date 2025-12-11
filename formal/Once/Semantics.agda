------------------------------------------------------------------------
-- Once.Semantics
--
-- Denotational semantics for Once.
-- Interprets types as Agda Sets and IR morphisms as Agda functions.
------------------------------------------------------------------------

module Once.Semantics where

open import Once.Type
open import Once.IR

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])

-- | Semantic interpretation of types
--
-- Maps Once types to Agda types (Sets).
-- This is the object mapping of a functor from Once's CCC to Set.
--
------------------------------------------------------------------------
-- KNOWN LIMITATION: Fixed Point Semantics
------------------------------------------------------------------------
--
-- The interpretation of Fix F uses a simple newtype wrapper:
--
--   ⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧
--
-- This models Fix F ≅ F, but the correct equation should be:
--
--   Fix F ≅ F[Fix F / X]   (F with recursive occurrences substituted)
--
-- For example, Nat = Fix (Unit + X) should satisfy:
--   ⟦ Nat ⟧ ≅ ⊤ ⊎ ⟦ Nat ⟧
--
-- But this model gives:
--   ⟦ Nat ⟧ = ⟦Fix⟧ (⊤ ⊎ ⟦ X ⟧)   where X is uninterpreted
--
-- The proofs eval-fold-unfold and eval-unfold-fold are trivially refl
-- because wrap/unwrap are inverses. This proves the wrapper isomorphism,
-- NOT the recursive fixed point property.
--
-- A proper treatment requires modeling F as a functor with an explicit
-- recursive position (e.g., a universe of strictly positive functors).
-- See docs/formal/what-is-proven.md for options to address this.
--
------------------------------------------------------------------------
record ⟦Fix⟧ (A : Set) : Set where
  constructor wrap
  field unwrap : A

open ⟦Fix⟧

⟦_⟧ : Type → Set
⟦ Unit ⟧   = ⊤
⟦ Void ⟧   = ⊥
⟦ A * B ⟧  = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧  = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒ B ⟧  = ⟦ A ⟧ → ⟦ B ⟧
⟦ Fix F ⟧  = ⟦Fix⟧ ⟦ F ⟧

-- | Evaluation of IR morphisms
--
-- Maps IR morphisms to Agda functions.
-- This is the morphism mapping of a functor from Once's CCC to Set.
--
-- eval : IR A B → (⟦ A ⟧ → ⟦ B ⟧)
--
eval : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧

-- Category structure
eval id x              = x
eval (g ∘ f) x         = eval g (eval f x)

-- Products
eval fst (a , b)       = a
eval snd (a , b)       = b
eval ⟨ f , g ⟩ x       = (eval f x , eval g x)

-- Coproducts
eval inl a             = inj₁ a
eval inr b             = inj₂ b
eval [ f , g ] (inj₁ a) = eval f a
eval [ f , g ] (inj₂ b) = eval g b

-- Terminal
eval terminal _        = tt

-- Initial
eval initial ()

-- Exponential
eval (curry f) a       = λ b → eval f (a , b)
eval apply (f , a)     = f a

-- Recursive types (Fixed point isomorphism)
eval fold x            = wrap x
eval unfold x          = unwrap x
