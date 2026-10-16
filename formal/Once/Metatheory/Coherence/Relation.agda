{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Relation — the observational equivalence of
-- `Spec.Equivalence`, as a coinductive relation.
--
-- `Same` and `SameM` observe to every depth. For the fundamental lemma a
-- depth-free form is easier: `TreeRel R`, the bisimulation whose leaves are
-- `R`-related. Since `Obs` only weakens as the depth falls (`Obs-anti`), a
-- pair of trees related to every depth is `TreeRel Same` (`fromUpTo`), and
-- back (`toUpTo`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.Relation (Σ : Signature) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Once.Spec.Grade using (Purity; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)
open import Once.Spec.Equivalence Σ

open T∞ using (force)
open _≈_ using (force≈)
open νM using (outν)

------------------------------------------------------------------------
-- Depth
------------------------------------------------------------------------

UpTo-mono : ∀ {X} {R R′ : X → X → Set} n → (∀ {x y} → R x y → R′ x y) → ∀ {m m′} → UpTo n R m m′ → UpTo n R′ m m′
UpTo-mono zero    h p = tt
UpTo-mono (suc n) h {m} {m′} p = step (force m) (force m′) p
  where
    step : ∀ s s′ → NodeUpTo n _ s s′ → NodeUpTo n _ s s′
    step _ _ (done≈ r) = done≈ (h r)
    step _ _ (node≈ e) = node≈ λ b → UpTo-mono n h (e b)

UpTo-anti : ∀ {X} {R : X → X → Set} n {m m′} → UpTo (suc n) R m m′ → UpTo n R m m′
UpTo-anti zero    p = tt
UpTo-anti (suc n) {m} {m′} p = step (force m) (force m′) p
  where
    step : ∀ s s′ → NodeUpTo (suc n) _ s s′ → NodeUpTo n _ s s′
    step _ _ (done≈ r) = done≈ r
    step _ _ (node≈ e) = node≈ λ b → UpTo-anti n (e b)

LayerEq-mono : ∀ (G : SFunctor) {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
             → ∀ {l l′} → LayerEq G R l l′ → LayerEq G R′ l l′
LayerEq-mono (SK B)     h p = p
LayerEq-mono SId        h p = h p
LayerEq-mono (G S⊕ H) h {inj₁ x} {inj₁ y} p = LayerEq-mono G h p
LayerEq-mono (G S⊕ H) h {inj₂ x} {inj₂ y} p = LayerEq-mono H h p
LayerEq-mono (G S⊕ H) h {inj₁ x} {inj₂ y} ()
LayerEq-mono (G S⊕ H) h {inj₂ x} {inj₁ y} ()
LayerEq-mono (G S⊗ H) h (p , q) = LayerEq-mono G h p , LayerEq-mono H h q

Obs-anti   : ∀ n (A : Type) {x y} → Obs (suc n) A x y → Obs n A x y
νUpTo-anti : ∀ π (G : SFunctor) n {v w} → νUpTo π G (suc n) v w → νUpTo π G n v w
ObsM-anti  : ∀ n π (A : Type) {m m′} → ObsM (suc n) π A m m′ → ObsM n π A m m′
ObsM-anti n π A p = UpTo-mono n (Obs-anti n A) (UpTo-anti n p)
Obs-anti n (var ())
Obs-anti n Unit  p = p
Obs-anti n Void  p = p
Obs-anti n Int   p = p
Obs-anti n Float p = p
Obs-anti n (μ F) p = p
Obs-anti n (A * B) {x , x′} {y , y′} (p , q) = Obs-anti n A p , Obs-anti n B q
Obs-anti n (A + B) {inj₁ x} {inj₁ y} p = Obs-anti n A p
Obs-anti n (A + B) {inj₂ x} {inj₂ y} p = Obs-anti n B p
Obs-anti n (A + B) {inj₁ x} {inj₂ y} ()
Obs-anti n (A + B) {inj₂ x} {inj₁ y} ()
Obs-anti n (A ⇒[ mk-kind Zero π ] B) p = ObsM-anti n π B p
Obs-anti n (A ⇒[ mk-kind One  π ] B) p = λ a a′ s → ObsM-anti n π B (p a a′ s)
Obs-anti n (A ⇒[ mk-kind Many π ] B) p = λ a a′ s → ObsM-anti n π B (p a a′ s)
Obs-anti n (ν F π) p = νUpTo-anti π (code F) n p
νUpTo-anti π G zero    p = tt
νUpTo-anti π G (suc n) {v} {w} p =
  UpTo-mono (suc n) (LayerEq-mono G (νUpTo-anti π G n)) {toT∞ π (outν v)} {toT∞ π (outν w)}
    (UpTo-anti (suc n) {toT∞ π (outν v)} {toT∞ π (outν w)} p)

------------------------------------------------------------------------
-- The coinductive form
------------------------------------------------------------------------

mutual
  record TreeRel {X : Set} (R : X → X → Set) (m m′ : T∞ X) : Set where
    coinductive
    field forceR : StepRel R (force m) (force m′)

  data StepRel {X : Set} (R : X → X → Set) : Step X (T∞ X) → Step X (T∞ X) → Set where
    doneR : ∀ {x y} → R x y → StepRel R (done x) (done y)
    nodeR : ∀ {o a k k′} → (∀ b → TreeRel R (k b) (k′ b)) → StepRel R (node (call o a k)) (node (call o a k′))
open TreeRel public

toUpTo : ∀ {X} {R : X → X → Set} {m m′} → TreeRel R m m′ → ∀ n → UpTo n R m m′
toUpTo p zero    = tt
toUpTo {m = m} {m′} p (suc n) = step (forceR p)
  where
    step : ∀ {s s′} → StepRel _ s s′ → NodeUpTo n _ s s′
    step (doneR r) = done≈ r
    step (nodeR e) = node≈ λ b → toUpTo (e b) n

-- A pair of trees related to every depth, by a family of leaf relations that
-- weakens as the depth falls, is related coinductively by their meet.
module _ {X : Set} (R : ℕ → X → X → Set) (anti : ∀ n {x y} → R (suc n) x y → R n x y) where
  private
    doneAt : ∀ {n x y} → NodeUpTo n (R (suc n)) (done x) (done y) → R (suc n) x y
    doneAt (done≈ r) = r
    nodeAt : ∀ {n o a k k′} → NodeUpTo n (R (suc n)) (node (call o a k)) (node (call o a k′))
           → ∀ b → UpTo n (R (suc n)) (k b) (k′ b)
    nodeAt (node≈ e) = e

  fromUpToFam  : ∀ {m m′ : T∞ X} → (∀ n → UpTo n (R n) m m′) → TreeRel (λ x y → ∀ n → R n x y) m m′
  fromStepFam  : ∀ (s s′ : Step X (T∞ X)) → (∀ n → NodeUpTo n (R (suc n)) s s′) → StepRel (λ x y → ∀ n → R n x y) s s′
  fromStepFam′ : ∀ (s s′ : Step X (T∞ X)) → (∀ n → NodeUpTo n (R (suc n)) s s′)
               → NodeUpTo 0 (R 1) s s′ → StepRel (λ x y → ∀ n → R n x y) s s′
  forceR (fromUpToFam h) = fromStepFam _ _ λ n → h (suc n)
  fromStepFam s s′ h = fromStepFam′ s s′ h (h 0)
  fromStepFam′ (done x) (done y) h (done≈ _) = doneR λ k → anti k (doneAt (h k))
  fromStepFam′ (node (call o a k)) (node (call .o .a k′)) h (node≈ _) =
    nodeR λ b → fromUpToFam λ n → UpTo-mono n (anti n) (nodeAt (h n) b)

fromUpTo : ∀ (A : Type) {m m′ : T∞ ⟦ A ⟧ᵛ} → (∀ n → UpTo n (Obs n A) m m′) → TreeRel (Same A) m m′
fromUpTo A = fromUpToFam (λ n → Obs n A) (λ n → Obs-anti n A)

-- The computations of the Spec's `SameM`, as trees.
SameM→Tree : ∀ π (A : Type) {m m′} → SameM π A m m′ → TreeRel (Same A) (toT∞ π m) (toT∞ π m′)
SameM→Tree π A p = fromUpTo A p

Tree→SameM : ∀ π (A : Type) {m m′} → TreeRel (Same A) (toT∞ π m) (toT∞ π m′) → SameM π A m m′
Tree→SameM π A p n = UpTo-mono n (λ s → s n) (toUpTo p n)

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

-- Bisimilar trees may replace each other, on either side.
≈-TreeRelˡ : ∀ {X} {R : X → X → Set} {m m₀ m′ : T∞ X} → m ≈ m₀ → TreeRel R m₀ m′ → TreeRel R m m′
≈-StepRelˡ : ∀ {X} {R : X → X → Set} {s s₀ s′ : Step X (T∞ X)} → StepEq _≈_ s s₀ → StepRel R s₀ s′ → StepRel R s s′
forceR (≈-TreeRelˡ e p) = ≈-StepRelˡ (force≈ e) (forceR p)
≈-StepRelˡ done≈     (doneR r) = doneR r
≈-StepRelˡ (node≈ e) (nodeR p) = nodeR λ b → ≈-TreeRelˡ (e b) (p b)

≈-TreeRelʳ : ∀ {X} {R : X → X → Set} {m m′ m₀ : T∞ X} → m′ ≈ m₀ → TreeRel R m m₀ → TreeRel R m m′
≈-StepRelʳ : ∀ {X} {R : X → X → Set} {s s′ s₀ : Step X (T∞ X)} → StepEq _≈_ s′ s₀ → StepRel R s s₀ → StepRel R s s′
forceR (≈-TreeRelʳ e p) = ≈-StepRelʳ (force≈ e) (forceR p)
≈-StepRelʳ done≈     (doneR r) = doneR r
≈-StepRelʳ (node≈ e) (nodeR p) = nodeR λ b → ≈-TreeRelʳ (e b) (p b)

-- Binding related trees with related continuations.
bindRel  : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {m m′ : T∞ X} {f g : X → T∞ Y}
         → TreeRel R m m′ → (∀ {x y} → R x y → TreeRel R′ (f x) (g y)) → TreeRel R′ (m >>=∞ f) (m′ >>=∞ g)
bindRelS : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {s s′ : Step X (T∞ X)} {f g : X → T∞ Y}
         → StepRel R s s′ → (∀ {x y} → R x y → TreeRel R′ (f x) (g y)) → StepRel R′ (bindStep s f) (bindStep s′ g)
forceR (bindRel p h) = bindRelS (forceR p) h
bindRelS (doneR r) h = forceR (h r)
bindRelS (nodeR e) h = nodeR λ b → bindRel (e b) h

-- Returns are related exactly when their values are.
returnRel : ∀ {X} {R : X → X → Set} {x y} → R x y → TreeRel R (return∞ x) (return∞ y)
forceR (returnRel r) = doneR r

returnRel⁻ : ∀ {X} {R : X → X → Set} {x y} → TreeRel R (return∞ x) (return∞ y) → R x y
returnRel⁻ p = unDone (forceR p)
  where unDone : ∀ {X} {R : X → X → Set} {x y : X} → StepRel R (done x) (done y) → R x y
        unDone (doneR r) = r
