------------------------------------------------------------------------
-- Once.SPF.SizedProof
--
-- Machine-checked productivity proofs for Once.SPF using sized types.
--
-- This module provides formal justification for the TERMINATING pragmas
-- in Once.SPF. The definitions here mirror those in SPF but use sized
-- types to allow Agda to verify productivity automatically.
--
-- IMPORTANT: This module uses --sized-types. It is intentionally isolated
-- from the main codebase to avoid "infecting" other modules with the
-- sized types requirement.
--
-- The correspondence between this module and Once.SPF:
--   νˢ i F    ↔  ν F           (sized vs unsized greatest fixed point)
--   anaˢ      ↔  ana           (sized vs unsized anamorphism)
--   _∼ˢ_      ↔  _∼_           (sized vs unsized bisimulation)
--
-- The proofs here justify that:
--   1. ana is productive (each unfold produces one F-layer)
--   2. ana-unfold-bisim is productive (coinductive proof terminates)
--
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.SPF.SizedProof where

open import Size using (Size; Size<_; ↑_; ∞)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.Semantics.IR using (⟦_⟧F)

------------------------------------------------------------------------
-- Functor map (copied from SPF to avoid import issues)
------------------------------------------------------------------------

fmap : (F : Functor) {A B : Set} → (A → B) → ⟦ F ⟧F A → ⟦ F ⟧F B
fmap (K _) f x = x
fmap Id f x = f x
fmap (F ⊕ G) f (inj₁ x) = inj₁ (fmap F f x)
fmap (F ⊕ G) f (inj₂ y) = inj₂ (fmap G f y)
fmap (F ⊗ G) f (x , y) = fmap F f x , fmap G f y

------------------------------------------------------------------------
-- Sized Greatest Fixed Point
------------------------------------------------------------------------

-- | νˢ i F: coinductive values that can be observed i times
--
-- This is the sized version of ν F from Once.SPF.
-- The size parameter allows Agda to verify productivity.
--
record νˢ (i : Size) (F : Functor) : Set where
  coinductive
  field
    unfoldˢ : {j : Size< i} → ⟦ F ⟧F (νˢ j F)

open νˢ public

-- | Standard greatest fixed point (infinite observations)
--
ν∞ : Functor → Set
ν∞ F = νˢ ∞ F

------------------------------------------------------------------------
-- Sized Anamorphism (Productivity Proof)
------------------------------------------------------------------------

-- | Sized anamorphism - Agda verifies productivity
--
-- The key insight: at size i, we produce unfoldˢ at size j < i.
-- The recursive call (anaˢ {j} coalg) produces νˢ j F, which is
-- "smaller" than νˢ i F. Agda accepts this as productive.
--
-- This justifies the TERMINATING pragma on ana in Once.SPF.
--
anaˢ : ∀ {i} {F} {A : Set} → (A → ⟦ F ⟧F A) → A → νˢ i F
unfoldˢ (anaˢ {i} {F} coalg a) {j} = fmap F (anaˢ {j} coalg) (coalg a)

------------------------------------------------------------------------
-- Relational Functor Interpretation
------------------------------------------------------------------------

-- | Lift a relation through functor structure
--
⟦_⟧F-rel : (F : Functor) {A B : Set} (R : A → B → Set) → ⟦ F ⟧F A → ⟦ F ⟧F B → Set
⟦ K _ ⟧F-rel R x y = x ≡ y
⟦ Id ⟧F-rel R x y = R x y
⟦ F ⊕ G ⟧F-rel R (inj₁ x) (inj₁ y) = ⟦ F ⟧F-rel R x y
⟦ F ⊕ G ⟧F-rel R (inj₁ x) (inj₂ y) = ⊥
⟦ F ⊕ G ⟧F-rel R (inj₂ x) (inj₁ y) = ⊥
⟦ F ⊕ G ⟧F-rel R (inj₂ x) (inj₂ y) = ⟦ G ⟧F-rel R x y
⟦ F ⊗ G ⟧F-rel R (x₁ , x₂) (y₁ , y₂) = ⟦ F ⟧F-rel R x₁ y₁ × ⟦ G ⟧F-rel R x₂ y₂

-- | fmap f relates to identity when f relates to identity
--
fmap-f-rel : ∀ F {A : Set} {R : A → A → Set} {f : A → A}
           → (∀ a → R (f a) a)
           → ∀ x → ⟦ F ⟧F-rel R (fmap F f x) x
fmap-f-rel (K _) hyp x = refl
fmap-f-rel Id hyp x = hyp x
fmap-f-rel (F ⊕ G) hyp (inj₁ x) = fmap-f-rel F hyp x
fmap-f-rel (F ⊕ G) hyp (inj₂ x) = fmap-f-rel G hyp x
fmap-f-rel (F ⊗ G) hyp (x₁ , x₂) = fmap-f-rel F hyp x₁ , fmap-f-rel G hyp x₂

------------------------------------------------------------------------
-- Sized Bisimulation (Productivity Proof)
------------------------------------------------------------------------

-- | Sized bisimulation relation
--
-- Two coinductive values are bisimilar if their observations are related.
--
record _∼ˢ_ {i : Size} {F : Functor} (x y : ν∞ F) : Set where
  coinductive
  field
    unfold-∼ˢ : {j : Size< i} → ⟦ F ⟧F-rel (_∼ˢ_ {j} {F}) (unfoldˢ x) (unfoldˢ y)

open _∼ˢ_

-- | Unfold wrapper for ν∞
--
unfold∞ : ∀ {F} → ν∞ F → ⟦ F ⟧F (ν∞ F)
unfold∞ x = unfoldˢ x

-- | ana unfold is bisimilar to id (sized proof)
--
-- This justifies the TERMINATING pragma on ana-unfold-bisim in Once.SPF.
--
-- Proof: At size i, we need unfold-∼ˢ at size j < i.
-- The recursive call (ana-unfold-bisimˢ {j} F) produces a proof at size j,
-- which is "smaller". Agda accepts this as productive.
--
ana-unfold-bisimˢ : ∀ {i : Size} (F : Functor) (x : ν∞ F) → _∼ˢ_ {i} {F} (anaˢ {∞} {F} unfold∞ x) x
unfold-∼ˢ (ana-unfold-bisimˢ {i} F x) {j} = fmap-f-rel F (ana-unfold-bisimˢ {j} F) (unfold∞ x)

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- This module proves that the following definitions in Once.SPF are productive:
--
--   1. ana : (A → ⟦ F ⟧F A) → A → ν F
--      Justified by: anaˢ (Agda verifies productivity via sized types)
--
--   2. ana-unfold-bisim : ∀ F (x : ν F) → ana unfold x ∼ x
--      Justified by: ana-unfold-bisimˢ (Agda verifies productivity via sized types)
--
-- The TERMINATING pragmas in Once.SPF are therefore sound.
--
-- Note: This module intentionally uses {-# OPTIONS --sized-types #-} at the
-- module level rather than project-wide, keeping the sized types isolated.
