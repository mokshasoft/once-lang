-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Optimize.Shape
--
-- Shape characterization for optimizer output.
-- Proves that optimize-pair and optimize-case return specific shapes.
------------------------------------------------------------------------

module Once.Optimize.Shape where

open import Once.Type
open import Once.IR
open import Once.Optimize using (optimize-pair; optimize-case; _≟Type_; _≟IR_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; [_])
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- OptPairShape: Characterization of optimize-pair outputs
------------------------------------------------------------------------

data OptPairShape {A B : Type} : {C : Type} → IR C A → IR C B → IR C (A * B) → Set where
  ops-id   : OptPairShape (fst {A} {B}) snd id
  ops-h    : ∀ {C} (h : IR C (A * B)) → OptPairShape (fst ∘ h) (snd ∘ h) h
  ops-pair : ∀ {C} (f : IR C A) (g : IR C B) → OptPairShape f g (⟨ f , g ⟩)

------------------------------------------------------------------------
-- Direct proof: optimize-pair-shape
--
-- We prove this by mirroring the structure of optimize-pair exactly.
-- The key is to use the same `with` patterns so the goal type reduces.
------------------------------------------------------------------------

optimize-pair-shape : ∀ {A B C} (f : IR C A) (g : IR C B) →
  OptPairShape f g (optimize-pair f g)

-- Case 1: fst, snd
optimize-pair-shape (fst {A} {B}) (snd {A'} {B'}) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = ops-id
... | yes refl | no _     = ops-pair fst snd
... | no _     | yes refl = ops-pair fst snd
... | no _     | no _     = ops-pair fst snd

-- Case 2: fst ∘ h, snd ∘ h'
optimize-pair-shape (_∘_ {_} {D} (fst {A} {B}) h) (_∘_ {_} {D'} (snd {A'} {B'}) h')
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = ops-h h
...   | no _     = ops-pair (fst ∘ h) (snd ∘ h')
optimize-pair-shape (_∘_ (fst {_} {_}) h) (_∘_ (snd {_} {_}) h')
  | yes refl | yes refl | no _ = ops-pair (fst ∘ h) (snd ∘ h')
optimize-pair-shape (_∘_ (fst {_} {_}) h) (_∘_ (snd {_} {_}) h')
  | yes refl | no _ | yes refl = ops-pair (fst ∘ h) (snd ∘ h')
optimize-pair-shape (_∘_ (fst {_} {_}) h) (_∘_ (snd {_} {_}) h')
  | yes refl | no _ | no _ = ops-pair (fst ∘ h) (snd ∘ h')
optimize-pair-shape (_∘_ (fst {_} {_}) h) (_∘_ (snd {_} {_}) h')
  | no _ | yes refl | yes refl = ops-pair (fst ∘ h) (snd ∘ h')
optimize-pair-shape (_∘_ (fst {_} {_}) h) (_∘_ (snd {_} {_}) h')
  | no _ | yes refl | no _ = ops-pair (fst ∘ h) (snd ∘ h')
optimize-pair-shape (_∘_ (fst {_} {_}) h) (_∘_ (snd {_} {_}) h')
  | no _ | no _ | yes refl = ops-pair (fst ∘ h) (snd ∘ h')
optimize-pair-shape (_∘_ (fst {_} {_}) h) (_∘_ (snd {_} {_}) h')
  | no _ | no _ | no _ = ops-pair (fst ∘ h) (snd ∘ h')

-- All other cases: f is not fst (or fst ∘ _), or g is not snd (or snd ∘ _)
-- These all go to the catch-all ⟨ f , g ⟩ Heap in optimize-pair

-- f = id
optimize-pair-shape id g = ops-pair id g

-- f = snd
optimize-pair-shape snd g = ops-pair snd g

-- f = ⟨ _ , _ ⟩
optimize-pair-shape (⟨ _ , _ ⟩) g = ops-pair _ g

-- f = inl
optimize-pair-shape (inl _) g = ops-pair _ g

-- f = inr
optimize-pair-shape (inr _) g = ops-pair _ g

-- f = (case _ _)
optimize-pair-shape (case _ _) g = ops-pair _ g

-- f = terminal
optimize-pair-shape terminal g = ops-pair terminal g

-- f = initial
optimize-pair-shape initial g = ops-pair initial g

-- f = curry
optimize-pair-shape (curry _ _) g = ops-pair _ g

-- f = apply
optimize-pair-shape apply g = ops-pair apply g

-- f = fold Heap
optimize-pair-shape (fold _) g = ops-pair (fold _) g

-- f = unfold
optimize-pair-shape unfold g = ops-pair unfold g

-- f = arr
optimize-pair-shape arr g = ops-pair arr g

-- f = SigOp
optimize-pair-shape (SigOp _) g = ops-pair _ g

-- f = fst, g is not snd (snd handled above via with)
-- g must have source type (D * A) - constructors with any source type work
optimize-pair-shape fst id = ops-pair fst id
optimize-pair-shape fst fst = ops-pair fst fst
optimize-pair-shape fst (⟨ _ , _ ⟩) = ops-pair fst _
optimize-pair-shape fst (inl _) = ops-pair fst _
optimize-pair-shape fst (inr _) = ops-pair fst _
optimize-pair-shape fst terminal = ops-pair fst terminal
optimize-pair-shape fst (curry _ _) = ops-pair fst _
optimize-pair-shape fst apply = ops-pair fst apply
optimize-pair-shape fst (fold _) = ops-pair fst (fold _)
optimize-pair-shape fst (SigOp _) = ops-pair fst _
optimize-pair-shape fst (_ ∘ _) = ops-pair fst _

-- f = fst ∘ h, g is not snd ∘ _
optimize-pair-shape (fst ∘ _) id = ops-pair _ id
optimize-pair-shape (fst ∘ _) fst = ops-pair _ fst
optimize-pair-shape (fst ∘ _) snd = ops-pair _ snd
optimize-pair-shape (fst ∘ _) (⟨ _ , _ ⟩) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (inl _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (inr _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (case _ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) terminal = ops-pair _ terminal
optimize-pair-shape (fst ∘ _) initial = ops-pair _ initial
optimize-pair-shape (fst ∘ _) (curry _ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) apply = ops-pair _ apply
optimize-pair-shape (fst ∘ _) fold = ops-pair _ (fold _)
optimize-pair-shape (fst ∘ _) unfold = ops-pair _ unfold
optimize-pair-shape (fst ∘ _) arr = ops-pair _ arr
optimize-pair-shape (fst ∘ _) (SigOp _) = ops-pair _ _
-- g = _ ∘ _ where inner is not snd (snd ∘ _ handled above)
optimize-pair-shape (fst ∘ _) (id ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (fst ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) ((⟨ _ , _ ⟩) ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) ((inl _) ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) ((inr _) ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) ((case _ _) ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (terminal ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (initial ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) ((curry _ _) ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (apply ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (fold ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (unfold ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) (arr ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) ((SigOp _) ∘ _) = ops-pair _ _
optimize-pair-shape (fst ∘ _) ((_ ∘ _) ∘ _) = ops-pair _ _

-- f = h ∘ k where h is not fst
optimize-pair-shape (id ∘ _) g = ops-pair _ g
optimize-pair-shape (snd ∘ _) g = ops-pair _ g
optimize-pair-shape ((⟨ _ , _ ⟩) ∘ _) g = ops-pair _ g
optimize-pair-shape ((inl _) ∘ _) g = ops-pair _ g
optimize-pair-shape ((inr _) ∘ _) g = ops-pair _ g
optimize-pair-shape ((case _ _) ∘ _) g = ops-pair _ g
optimize-pair-shape (terminal ∘ _) g = ops-pair _ g
optimize-pair-shape (initial ∘ _) g = ops-pair _ g
optimize-pair-shape ((curry _ _) ∘ _) g = ops-pair _ g
optimize-pair-shape (apply ∘ _) g = ops-pair _ g
optimize-pair-shape (fold ∘ _) g = ops-pair _ g
optimize-pair-shape (unfold ∘ _) g = ops-pair _ g
optimize-pair-shape (arr ∘ _) g = ops-pair _ g
optimize-pair-shape ((SigOp _) ∘ _) g = ops-pair _ g
optimize-pair-shape ((_ ∘ _) ∘ _) g = ops-pair _ g

------------------------------------------------------------------------
-- OptCaseShape: Characterization of optimize-case outputs
------------------------------------------------------------------------

data OptCaseShape {A B : Type} : {C : Type} → IR A C → IR B C → IR (A + B) C → Set where
  ocs-id   : ∀ {m₁ m₂} → OptCaseShape (inl {A} {B} m₁) (inr m₂) id
  ocs-h    : ∀ {C} (h : IR (A + B) C) {m₁ m₂} → OptCaseShape (h ∘ inl m₁) (h ∘ inr m₂) h
  ocs-case : ∀ {C} (f : IR A C) (g : IR B C) → OptCaseShape f g (case f g)

------------------------------------------------------------------------
-- Direct proof: optimize-case-shape
------------------------------------------------------------------------

optimize-case-shape : ∀ {A B C} (f : IR A C) (g : IR B C) →
  OptCaseShape f g (optimize-case f g)

-- Case 1: inl, inr
optimize-case-shape (inl {A} {B} m) (inr {A'} {B'} m') with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = ocs-id
... | yes refl | no _     = ocs-case (inl m) (inr m')
... | no _     | yes refl = ocs-case (inl m) (inr m')
... | no _     | no _     = ocs-case (inl m) (inr m')

-- Case 2: h ∘ inl, h' ∘ inr
optimize-case-shape (_∘_ {_} {D} h (inl {A} {B} m)) (_∘_ {_} {D'} h' (inr {A'} {B'} m'))
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = ocs-h h
...   | no _     = ocs-case (h ∘ inl m) (h' ∘ inr m')
optimize-case-shape (_∘_ h (inl {_} {_} m)) (_∘_ h' (inr {_} {_} m'))
  | yes refl | yes refl | no _ = ocs-case (h ∘ inl m) (h' ∘ inr m')
optimize-case-shape (_∘_ h (inl {_} {_} m)) (_∘_ h' (inr {_} {_} m'))
  | yes refl | no _ | yes refl = ocs-case (h ∘ inl m) (h' ∘ inr m')
optimize-case-shape (_∘_ h (inl {_} {_} m)) (_∘_ h' (inr {_} {_} m'))
  | yes refl | no _ | no _ = ocs-case (h ∘ inl m) (h' ∘ inr m')
optimize-case-shape (_∘_ h (inl {_} {_} m)) (_∘_ h' (inr {_} {_} m'))
  | no _ | yes refl | yes refl = ocs-case (h ∘ inl m) (h' ∘ inr m')
optimize-case-shape (_∘_ h (inl {_} {_} m)) (_∘_ h' (inr {_} {_} m'))
  | no _ | yes refl | no _ = ocs-case (h ∘ inl m) (h' ∘ inr m')
optimize-case-shape (_∘_ h (inl {_} {_} m)) (_∘_ h' (inr {_} {_} m'))
  | no _ | no _ | yes refl = ocs-case (h ∘ inl m) (h' ∘ inr m')
optimize-case-shape (_∘_ h (inl {_} {_} m)) (_∘_ h' (inr {_} {_} m'))
  | no _ | no _ | no _ = ocs-case (h ∘ inl m) (h' ∘ inr m')

-- All other cases

-- f = id
optimize-case-shape id g = ocs-case id g

-- f = fst
optimize-case-shape fst g = ocs-case fst g

-- f = snd
optimize-case-shape snd g = ocs-case snd g

-- f = ⟨ _ , _ ⟩
optimize-case-shape (⟨ _ , _ ⟩) g = ocs-case _ g

-- f = inr
optimize-case-shape (inr _) g = ocs-case _ g

-- f = (case _ _)
optimize-case-shape (case _ _) g = ocs-case _ g

-- f = terminal
optimize-case-shape terminal g = ocs-case terminal g

-- f = initial
optimize-case-shape initial g = ocs-case initial g

-- f = curry
optimize-case-shape (curry _ _) g = ocs-case _ g

-- f = apply
optimize-case-shape apply g = ocs-case apply g

-- f = fold Heap
optimize-case-shape (fold _) g = ocs-case (fold _) g

-- f = unfold
optimize-case-shape unfold g = ocs-case unfold g

-- f = arr
optimize-case-shape arr g = ocs-case arr g

-- f = SigOp
optimize-case-shape (SigOp _) g = ocs-case _ g

-- f = inl, g is not inr (inr handled above)
-- g : IR B (A + X), so g's target must be a sum type
-- Remove constructors whose target type cannot be a sum:
--   ⟨ _ , _ ⟩ _ (product), terminal (Unit), curry (function), arr (Arr), fold (Fix)
optimize-case-shape (inl _) id = ocs-case _ id
optimize-case-shape (inl _) fst = ocs-case _ fst
optimize-case-shape (inl _) snd = ocs-case _ snd
optimize-case-shape (inl _) (inl _) = ocs-case _ _
optimize-case-shape (inl _) (case _ _) = ocs-case _ _
optimize-case-shape (inl _) initial = ocs-case _ initial
optimize-case-shape (inl _) apply = ocs-case _ apply
optimize-case-shape (inl _) unfold = ocs-case _ unfold
optimize-case-shape (inl _) (SigOp _) = ocs-case _ _
optimize-case-shape (inl _) (_ ∘ _) = ocs-case _ _

-- f = h ∘ inl, g is not _ ∘ inr
optimize-case-shape (_ ∘ (inl _)) id = ocs-case _ id
optimize-case-shape (_ ∘ (inl _)) fst = ocs-case _ fst
optimize-case-shape (_ ∘ (inl _)) snd = ocs-case _ snd
optimize-case-shape (_ ∘ (inl _)) (⟨ _ , _ ⟩) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (inl _) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (inr _) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (case _ _) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) terminal = ocs-case _ terminal
optimize-case-shape (_ ∘ (inl _)) initial = ocs-case _ initial
optimize-case-shape (_ ∘ (inl _)) (curry _ _) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) apply = ocs-case _ apply
optimize-case-shape (_ ∘ (inl _)) fold = ocs-case _ (fold _)
optimize-case-shape (_ ∘ (inl _)) unfold = ocs-case _ unfold
optimize-case-shape (_ ∘ (inl _)) arr = ocs-case _ arr
optimize-case-shape (_ ∘ (inl _)) (SigOp _) = ocs-case _ _
-- g = _ ∘ k where k is not inr
optimize-case-shape (_ ∘ (inl _)) (_ ∘ id) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ fst) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ snd) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ (⟨ _ , _ ⟩)) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ (inl _)) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ (case _ _)) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ terminal) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ initial) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ (curry _ _)) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ apply) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ (fold Heap)) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ unfold) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ arr) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ (SigOp _)) = ocs-case _ _
optimize-case-shape (_ ∘ (inl _)) (_ ∘ (_ ∘ _)) = ocs-case _ _

-- f = h ∘ k where k is not inl
optimize-case-shape (_ ∘ id) g = ocs-case _ g
optimize-case-shape (_ ∘ fst) g = ocs-case _ g
optimize-case-shape (_ ∘ snd) g = ocs-case _ g
optimize-case-shape (_ ∘ (⟨ _ , _ ⟩)) g = ocs-case _ g
optimize-case-shape (_ ∘ (inr _)) g = ocs-case _ g
optimize-case-shape (_ ∘ (case _ _)) g = ocs-case _ g
optimize-case-shape (_ ∘ terminal) g = ocs-case _ g
optimize-case-shape (_ ∘ initial) g = ocs-case _ g
optimize-case-shape (_ ∘ (curry _ _)) g = ocs-case _ g
optimize-case-shape (_ ∘ apply) g = ocs-case _ g
optimize-case-shape (_ ∘ (fold Heap)) g = ocs-case _ g
optimize-case-shape (_ ∘ unfold) g = ocs-case _ g
optimize-case-shape (_ ∘ arr) g = ocs-case _ g
optimize-case-shape (_ ∘ (SigOp _)) g = ocs-case _ g
optimize-case-shape (_ ∘ (_ ∘ _)) g = ocs-case _ g