------------------------------------------------------------------------
-- Once.Category.Laws
--
-- Proofs of the categorical laws for Once's IR.
-- These establish that IR forms a category.
------------------------------------------------------------------------

module Once.Category.Laws where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import Function using (_∘′_)

------------------------------------------------------------------------
-- Category Laws
------------------------------------------------------------------------

-- | Left identity: id ∘ f ≡ f (semantically)
--
-- For any morphism f : A → B, composing with identity on the left
-- gives back f.
--
eval-id-left : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
             → eval (id ∘ f) x ≡ eval f x
eval-id-left f x = refl

-- | Right identity: f ∘ id ≡ f (semantically)
--
-- For any morphism f : A → B, composing with identity on the right
-- gives back f.
--
eval-id-right : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
              → eval (f ∘ id) x ≡ eval f x
eval-id-right f x = refl

-- | Associativity: (f ∘ g) ∘ h ≡ f ∘ (g ∘ h) (semantically)
--
-- Composition is associative.
--
eval-assoc : ∀ {A B C D} (f : IR C D) (g : IR B C) (h : IR A B) (x : ⟦ A ⟧)
           → eval ((f ∘ g) ∘ h) x ≡ eval (f ∘ (g ∘ h)) x
eval-assoc f g h x = refl

------------------------------------------------------------------------
-- Product Laws (Beta)
------------------------------------------------------------------------

-- | fst ∘ ⟨ f , g ⟩ ≡ f
--
-- Projecting the first component of a pair gives the first morphism.
--
eval-fst-pair : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧)
              → eval (fst ∘ ⟨ f , g ⟩) x ≡ eval f x
eval-fst-pair f g x = refl

-- | snd ∘ ⟨ f , g ⟩ ≡ g
--
-- Projecting the second component of a pair gives the second morphism.
--
eval-snd-pair : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧)
              → eval (snd ∘ ⟨ f , g ⟩) x ≡ eval g x
eval-snd-pair f g x = refl

------------------------------------------------------------------------
-- Product Laws (Eta)
------------------------------------------------------------------------

-- | ⟨ fst , snd ⟩ ≡ id (semantically)
--
-- Pairing the projections gives back the identity on products.
--
eval-pair-eta : ∀ {A B} (x : ⟦ A * B ⟧)
              → eval ⟨ fst , snd ⟩ x ≡ x
eval-pair-eta (a , b) = refl

------------------------------------------------------------------------
-- Coproduct Laws (Beta)
------------------------------------------------------------------------

-- | [ f , g ] ∘ inl ≡ f
--
-- Case analysis on a left injection gives the left branch.
--
eval-case-inl : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A ⟧)
              → eval ([ f , g ] ∘ inl) x ≡ eval f x
eval-case-inl f g x = refl

-- | [ f , g ] ∘ inr ≡ g
--
-- Case analysis on a right injection gives the right branch.
--
eval-case-inr : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ B ⟧)
              → eval ([ f , g ] ∘ inr) x ≡ eval g x
eval-case-inr f g x = refl

------------------------------------------------------------------------
-- Coproduct Laws (Eta)
------------------------------------------------------------------------

-- | [ inl , inr ] ≡ id (semantically)
--
-- Case analysis that re-injects gives back identity on coproducts.
--
eval-case-eta : ∀ {A B} (x : ⟦ A + B ⟧)
              → eval [ inl , inr ] x ≡ x
eval-case-eta (inj₁ a) = refl
eval-case-eta (inj₂ b) = refl

------------------------------------------------------------------------
-- Terminal Object Laws
------------------------------------------------------------------------

-- | Any two morphisms to Unit are equal (semantically)
--
-- Unit is terminal: there's a unique morphism from any object to Unit.
--
eval-terminal-unique : ∀ {A} (f : IR A Unit) (x : ⟦ A ⟧)
                     → eval f x ≡ eval terminal x
eval-terminal-unique f x with eval f x
... | tt = refl

------------------------------------------------------------------------
-- Exponential Laws (Curry/Apply adjunction)
------------------------------------------------------------------------

-- | apply ∘ ⟨ curry f ∘ fst , snd ⟩ ≡ f (semantically)
--
-- This is the beta law for exponentials.
--
eval-curry-apply : ∀ {A B C} (f : IR (A * B) C) (x : ⟦ A * B ⟧)
                 → eval (apply ∘ ⟨ curry f ∘ fst , snd ⟩) x ≡ eval f x
eval-curry-apply f (a , b) = refl
