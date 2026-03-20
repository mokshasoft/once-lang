------------------------------------------------------------------------
-- Once.CCC.IR.Laws
--
-- Evaluation laws and semantic properties for IR.
------------------------------------------------------------------------

module Once.CCC.IR.Laws where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.IR
open import Once.CCC.Eval using (PrimSem; eval)
open import Once.Semantics.Machine using (⟦_⟧; sem-fst; sem-snd; sem-pair)

------------------------------------------------------------------------
-- Basic Evaluation Laws
------------------------------------------------------------------------

eval-id : ∀ (ps : PrimSem) {A} (x : ⟦ A ⟧) → eval ps id x ≡ x
eval-id ps x = refl

eval-fst : ∀ (ps : PrimSem) {A B} (x : ⟦ A * B ⟧) → eval ps fst x ≡ sem-fst x
eval-fst ps x = refl

eval-snd : ∀ (ps : PrimSem) {A B} (x : ⟦ A * B ⟧) → eval ps snd x ≡ sem-snd x
eval-snd ps x = refl

eval-compose : ∀ (ps : PrimSem) {A B C} (f : IR A B) (g : IR B C) (x : ⟦ A ⟧) →
  eval ps (g ∘ f) x ≡ eval ps g (eval ps f x)
eval-compose ps f g x = refl

eval-pair : ∀ (ps : PrimSem) {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) (x : ⟦ A ⟧) →
  eval ps (⟨ f , g ⟩ m) x ≡ sem-pair (eval ps f x) (eval ps g x)
eval-pair ps f g m x = refl

eval-terminal : ∀ (ps : PrimSem) {A} (x : ⟦ A ⟧) → eval ps terminal x ≡ tt
eval-terminal ps x = refl

------------------------------------------------------------------------
-- AllocMode Independence
------------------------------------------------------------------------

alloc-mode-independent-pair : ∀ (ps : PrimSem) {A B C} (f : IR A B) (g : IR A C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval ps (⟨ f , g ⟩ m₁) x ≡ eval ps (⟨ f , g ⟩ m₂) x
alloc-mode-independent-pair ps f g m₁ m₂ x = refl

alloc-mode-independent-inl : ∀ (ps : PrimSem) {A B} (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval ps (inl {A} {B} m₁) x ≡ eval ps (inl {A} {B} m₂) x
alloc-mode-independent-inl ps m₁ m₂ x = refl

alloc-mode-independent-inr : ∀ (ps : PrimSem) {A B} (m₁ m₂ : AllocMode) (x : ⟦ B ⟧) →
  eval ps (inr {A} {B} m₁) x ≡ eval ps (inr {A} {B} m₂) x
alloc-mode-independent-inr ps m₁ m₂ x = refl

alloc-mode-independent-curry : ∀ (ps : PrimSem) {A B C q} (f : IR (A * B) C) (m₁ m₂ : AllocMode) (x : ⟦ A ⟧) →
  eval ps (curry {q = q} f m₁) x ≡ eval ps (curry {q = q} f m₂) x
alloc-mode-independent-curry ps f m₁ m₂ x = refl
