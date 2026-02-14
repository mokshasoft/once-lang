------------------------------------------------------------------------
-- Once.Backend.X86v3.Types
--
-- Object-level types and their semantic interpretation.
-- Separated to avoid circular dependencies between Validity and IR.
------------------------------------------------------------------------

module Once.Backend.X86v3.Types where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

data Type : Set where
  _⇒_ : Type → Type → Type
  _*_ : Type → Type → Type
  Unit : Type

infixr 20 _⇒_
infixl 30 _*_

------------------------------------------------------------------------
-- Semantic Interpretation of Types
--
-- ⟦ A ⟧ gives the Agda type corresponding to our object-level type A.
------------------------------------------------------------------------

⟦_⟧ : Type → Set
⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
⟦ A * B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ Unit ⟧ = ⊤

------------------------------------------------------------------------
-- Projections (concrete definitions)
------------------------------------------------------------------------

fst : ∀ {A B} → ⟦ A * B ⟧ → ⟦ A ⟧
fst = proj₁

snd : ∀ {A B} → ⟦ A * B ⟧ → ⟦ B ⟧
snd = proj₂

pair : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A * B ⟧
pair a b = a , b

------------------------------------------------------------------------
-- Pair/Projection Laws (trivially true)
------------------------------------------------------------------------

fst-pair : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) → fst (pair a b) ≡ a
fst-pair a b = refl

snd-pair : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) → snd (pair a b) ≡ b
snd-pair a b = refl
