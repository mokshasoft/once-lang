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
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.Res using (Res; stopped; returns; mapRes; rel-stopped; rel-returns)
open import Once.Semantics.Machine using (⟦_⟧F)
open import Once.Denotation.TraceMonad
  using (T; returnT; fmapT; _>>=T_; projTrace; RelRes; RelRes-value; RelT′; RelT′-bind)
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

-- plan 0.98: `mapRes` is what `fmapT` does to the result, and a related pair
-- of results maps to a related pair. The two mixed clauses are absurd rather
-- than merely unproved — `RelRes` reduces to `⊥` there.
RelRes-map : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
             (g : X → Y) (g′ : X′ → Y′) (r : Res X) (r′ : Res X′)
           → (∀ x x′ → R x x′ → S (g x) (g′ x′))
           → RelRes R r r′ → RelRes S (mapRes g r) (mapRes g′ r′)
RelRes-map R S g g′ stopped     stopped     h rr = rel-stopped
RelRes-map R S g g′ stopped     (returns _) h ()
RelRes-map R S g g′ (returns _) stopped     h ()
RelRes-map R S g g′ (returns x) (returns y) h (rel-returns rr) = rel-returns (h x y rr)

-- plan 0.98: the old statement of this proof produced a TRIPLE (trace, stop
-- flag, value) because `RelT′` was one; the flag and the value were always the
-- single fact "these two results agree", which is now `RelRes`. So the value
-- component is no longer `h` applied directly — `h` only speaks about values
-- that EXIST, and whether they do is what `RelRes-map` splits on.
RelT′-fmap : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
             (g : X → Y) (g′ : X′ → Y′) {m : T X} {m′ : T X′}
           → (∀ x x′ → R x x′ → S (g x) (g′ x′))
           → RelT′ R m m′ → RelT′ S (fmapT g m) (fmapT g′ m′)
-- plan 0.98: the two `Res` arguments are PINNED rather than left to the
-- unifier — `RelRes-map`'s conclusion mentions them under `mapRes`, which the
-- unifier cannot read back out.
RelT′-fmap R S g g′ {m} {m′} h rm k =
  (proj₁ (rm k) , RelRes-map R S g g′ (T.resT m) (T.resT m′) h (proj₂ (rm k)))

------------------------------------------------------------------------
-- THE lemma. At `⊗` the two children share one budget on each side, and the
-- budgets agree because the left traces do — which is exactly what
-- `RelT′-bind` already knows.
------------------------------------------------------------------------

seqF-rel : ∀ (G : Functor) {X Y : Set} (R : X → Y → Set)
           {l : ⟦ G ⟧F (T X)} {r : ⟦ G ⟧F (T Y)}
         → RelF G (RelT′ R) l r
         → RelT′ (RelF G R) (seqF G l) (seqF G r)
seqF-rel (K A)   R {x} {y} eq k = (refl , rel-returns eq)
seqF-rel Id      R         rel  = rel
-- plan 0.98: the two computations are PINNED. `RelT′-fmap`'s conclusion now
-- names its results only under `mapRes`, so the unifier cannot recover `m`
-- from the goal the way it could when the flag and the value were separate.
seqF-rel (G ⊕ H) R {inj₁ x} {inj₁ y} rel =
  RelT′-fmap (RelF G R) (RelF (G ⊕ H) R) inj₁ inj₁ {seqF G x} {seqF G y}
    (λ _ _ z → z) (seqF-rel G R rel)
seqF-rel (G ⊕ H) R {inj₂ x} {inj₂ y} rel =
  RelT′-fmap (RelF H R) (RelF (G ⊕ H) R) inj₂ inj₂ {seqF H x} {seqF H y}
    (λ _ _ z → z) (seqF-rel H R rel)
seqF-rel (G ⊗ H) R {x₁ , y₁} {x₂ , y₂} (rG , rH) =
  RelT′-bind (RelF G R) (RelF (G ⊗ H) R)
    (seqF G x₁) (seqF G x₂)
    (λ u → seqF H y₁ >>=T λ v → returnT (u , v))
    (λ u → seqF H y₂ >>=T λ v → returnT (u , v))
    (seqF-rel G R rG)
    -- plan 0.98: the continuation is owed only where BOTH heads returned, and
    -- the premises NAME the two values — so the old `valueT (seqF G x₁) k`,
    -- which had to guess that a value existed at budget `k`, is replaced by the
    -- bound `u`/`u′`, and the budget index disappears with it.
    (λ u u′ eu eu′ →
      RelT′-bind (RelF H R) (RelF (G ⊗ H) R)
        (seqF H y₁) (seqF H y₂)
        (λ v → returnT (u , v))
        (λ v → returnT (u′ , v))
        (seqF-rel H R rH)
        (λ v v′ ev ev′ j →
          ( refl
          , rel-returns
              ( RelRes-value (proj₂ (seqF-rel G R rG 0)) eu eu′
              , RelRes-value (proj₂ (seqF-rel H R rH 0)) ev ev′ )))) 
