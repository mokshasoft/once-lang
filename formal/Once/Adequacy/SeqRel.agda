-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SeqRel — `seqF` preserves a functor-lifted relation.
--
-- D179 made the cata fold's carrier a COMPUTATION, so every adequacy proof
-- about that fold has to show "related layers of computations sequence to
-- related computations of layers". `CataErased` and `CataBridge` each grew
-- their own induction for this (`layer-events`+`layer-z`, `layer-lemma`) —
-- which is the same duplication that made the rewrite expensive, so it lives
-- here once instead.
--
-- Deliberately NOT in `ValueDomain`: that module is spec, and this is a
-- proof-side lemma about it.
------------------------------------------------------------------------

module Once.Adequacy.SeqRel where

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.Semantics.Machine using (⟦_⟧F)
open import Once.Denotation.TraceMonad
  using (T; returnT; fmapT; _>>=T_; projTrace; valueT; RelT′; RelT′-bind)
open import Once.Denotation.ValueDomain using (seqF)

------------------------------------------------------------------------
-- A relation lifted over a functor layer. `K` holds data neither side
-- recurses into, so there it is plain equality.
------------------------------------------------------------------------

RelF : ∀ (G : Functor) {X Y : Set} (R : X → Y → Set) → ⟦ G ⟧F X → ⟦ G ⟧F Y → Set
RelF (K A)   R x        y        = x ≡ y
RelF Id      R x        y        = R x y
RelF (G ⊕ H) R (inj₁ x) (inj₁ y) = RelF G R x y
RelF (G ⊕ H) R (inj₁ _) (inj₂ _) = ⊥
RelF (G ⊕ H) R (inj₂ _) (inj₁ _) = ⊥
RelF (G ⊕ H) R (inj₂ x) (inj₂ y) = RelF H R x y
RelF (G ⊗ H) R (x₁ , y₁) (x₂ , y₂) = RelF G R x₁ x₂ × RelF H R y₁ y₂

------------------------------------------------------------------------
-- `fmapT` leaves the trace alone and maps the value, so it transports a
-- computation relation along any value-relation morphism.
------------------------------------------------------------------------

RelT′-fmap : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
             (g : X → Y) (g′ : X′ → Y′) {m : T X} {m′ : T X′}
           → (∀ x x′ → R x x′ → S (g x) (g′ x′))
           → RelT′ R m m′ → RelT′ S (fmapT g m) (fmapT g′ m′)
RelT′-fmap R S g g′ h rm k = (proj₁ (rm k) , h _ _ (proj₂ (rm k)))

------------------------------------------------------------------------
-- THE lemma. At `⊗` the two children share one budget on each side, and the
-- budgets agree because the left traces do — which is exactly what
-- `RelT′-bind` already knows.
------------------------------------------------------------------------

seqF-rel : ∀ (G : Functor) {X Y : Set} (R : X → Y → Set)
           {l : ⟦ G ⟧F (T X)} {r : ⟦ G ⟧F (T Y)}
         → RelF G (RelT′ R) l r
         → RelT′ (RelF G R) (seqF G l) (seqF G r)
seqF-rel (K A)   R {x} {y} eq k = (refl , eq)
seqF-rel Id      R         rel  = rel
seqF-rel (G ⊕ H) R {inj₁ x} {inj₁ y} rel =
  RelT′-fmap (RelF G R) (RelF (G ⊕ H) R) inj₁ inj₁ (λ _ _ z → z) (seqF-rel G R rel)
seqF-rel (G ⊕ H) R {inj₂ x} {inj₂ y} rel =
  RelT′-fmap (RelF H R) (RelF (G ⊕ H) R) inj₂ inj₂ (λ _ _ z → z) (seqF-rel H R rel)
seqF-rel (G ⊗ H) R {x₁ , y₁} {x₂ , y₂} (rG , rH) =
  RelT′-bind (RelF G R) (RelF (G ⊗ H) R)
    (seqF G x₁) (seqF G x₂)
    (λ u → seqF H y₁ >>=T λ v → returnT (u , v))
    (λ u → seqF H y₂ >>=T λ v → returnT (u , v))
    (seqF-rel G R rG)
    (λ k →
      RelT′-bind (RelF H R) (RelF (G ⊗ H) R)
        (seqF H y₁) (seqF H y₂)
        (λ v → returnT (valueT (seqF G x₁) k , v))
        (λ v → returnT (valueT (seqF G x₂) k , v))
        (seqF-rel H R rH)
        (λ j _ → (refl , (proj₂ (seqF-rel G R rG k) , proj₂ (seqF-rel H R rH j)))))
