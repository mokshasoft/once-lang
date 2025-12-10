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
-- Product Laws (Eta/Uniqueness)
------------------------------------------------------------------------

-- | ⟨ fst , snd ⟩ ≡ id (semantically)
--
-- Pairing the projections gives back the identity on products.
--
eval-pair-eta : ∀ {A B} (x : ⟦ A * B ⟧)
              → eval ⟨ fst , snd ⟩ x ≡ x
eval-pair-eta (a , b) = refl

-- | Product uniqueness: ⟨ fst ∘ h , snd ∘ h ⟩ ≡ h (semantically)
--
-- Any morphism into a product is uniquely determined by its projections.
-- This is the universal property of products.
--
eval-pair-unique : ∀ {A B C} (h : IR C (A * B)) (x : ⟦ C ⟧)
                 → eval ⟨ fst ∘ h , snd ∘ h ⟩ x ≡ eval h x
eval-pair-unique h x with eval h x
... | (a , b) = refl

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
-- Coproduct Laws (Eta/Uniqueness)
------------------------------------------------------------------------

-- | [ inl , inr ] ≡ id (semantically)
--
-- Case analysis that re-injects gives back identity on coproducts.
--
eval-case-eta : ∀ {A B} (x : ⟦ A + B ⟧)
              → eval [ inl , inr ] x ≡ x
eval-case-eta (inj₁ a) = refl
eval-case-eta (inj₂ b) = refl

-- | Coproduct uniqueness: [ h ∘ inl , h ∘ inr ] ≡ h (semantically)
--
-- Any morphism from a coproduct is uniquely determined by its restrictions.
-- This is the universal property of coproducts.
--
eval-case-unique : ∀ {A B C} (h : IR (A + B) C) (x : ⟦ A + B ⟧)
                 → eval [ h ∘ inl , h ∘ inr ] x ≡ eval h x
eval-case-unique h (inj₁ a) = refl
eval-case-unique h (inj₂ b) = refl

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
-- Initial Object Laws
------------------------------------------------------------------------

-- | Any two morphisms from Void are equal (semantically)
--
-- Void is initial: there's a unique morphism from Void to any object.
-- This is vacuously true since Void is empty.
--
eval-initial-unique : ∀ {A} (f : IR Void A) (x : ⟦ Void ⟧)
                    → eval f x ≡ eval initial x
eval-initial-unique f ()

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

-- | curry (apply ∘ ⟨ g ∘ fst , snd ⟩) ≡ g (semantically, for functions)
--
-- This is the eta law for exponentials.
-- Note: This requires function extensionality for full generality,
-- but we can prove it pointwise.
--
eval-curry-eta : ∀ {A B C} (g : IR A (B ⇒ C)) (a : ⟦ A ⟧) (b : ⟦ B ⟧)
               → eval (curry (apply ∘ ⟨ g ∘ fst , snd ⟩)) a b ≡ eval g a b
eval-curry-eta g a b = refl

------------------------------------------------------------------------
-- Distributivity Laws
------------------------------------------------------------------------

-- Distributivity of products over coproducts (C × (A + B) ≅ (C × A) + (C × B))
-- is proven in Once.Surface.Correct as distribute-inl and distribute-inr.

------------------------------------------------------------------------
-- Functoriality of Product and Coproduct
------------------------------------------------------------------------

-- | bimap f g = ⟨ f ∘ fst , g ∘ snd ⟩ preserves identity
--
eval-bimap-id : ∀ {A B} (x : ⟦ A * B ⟧)
              → eval ⟨ id ∘ fst , id ∘ snd ⟩ x ≡ x
eval-bimap-id (a , b) = refl

-- | bimap preserves composition
--
eval-bimap-compose : ∀ {A B C D E F}
                     (f : IR B C) (g : IR A B) (h : IR E F) (i : IR D E)
                     (x : ⟦ A * D ⟧)
                   → eval ⟨ (f ∘ g) ∘ fst , (h ∘ i) ∘ snd ⟩ x
                     ≡ eval (⟨ f ∘ fst , h ∘ snd ⟩ ∘ ⟨ g ∘ fst , i ∘ snd ⟩) x
eval-bimap-compose f g h i (a , d) = refl

-- | bicase f g = [ inl ∘ f , inr ∘ g ] preserves identity
--
eval-bicase-id : ∀ {A B} (x : ⟦ A + B ⟧)
               → eval [ inl ∘ id , inr ∘ id ] x ≡ x
eval-bicase-id (inj₁ a) = refl
eval-bicase-id (inj₂ b) = refl
