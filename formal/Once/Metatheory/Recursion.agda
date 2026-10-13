-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Recursion — the fold's universal property
-- (`Spec.Metatheory.Recursion`, plan 0.112 D3) and unfold's computation law
-- (plan 0.116 E), and guarded iteration's equation (D311).
--
-- Guarded iteration is PROVED (`Metatheory.Iteration`). The fold and unfold
-- laws are POSTULATED, NOT PROVED. The statements are the Spec's; they were moved to
-- where they belong (the language's metatheory) before their proofs exist.
-- Why they hold: a `μ` value is a finite tree, and every one is `in-valueᵛ` of
-- a layer, so an `h` that commutes with the constructor agrees with the fold by
-- induction on the tree (`fold-unique`); fusion is uniqueness applied to
-- `λ v → bindM π (cata-semᵛ u wf alg v) f`, using that sequencing a layer
-- commutes with the monad's bind (a polynomial functor is traversable). At
-- `eff` both also need `T`'s bind to be a congruence in its continuation,
-- which is the `extensionality` postulate (`Once.Postulates` P1).
--
-- Equality is the grade's (`EqM`): at `prod` the trees may be infinite, so
-- bisimilarity, never `≡` (D201, D311).
--
-- Nothing proves anything FROM these postulates today: they are claims on the
-- apex (`Once.Certified`'s `language` field), each to be discharged here.
------------------------------------------------------------------------

module Once.Metatheory.Recursion where

import Once.Metatheory.Iteration as It

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Type using (μ-type; ⟦_⟧T)
open import Once.Spec.Type.WellFormed using (WellFormedF)
open import Once.Spec.Metatheory using (Recursion)
open import Once.Spec.Graded using (EqM)
open import Once.Spec.Graded using (M; ⟦_⟧ᵛ; bindM; returnM)
open import Once.Spec.Type.Grade using (pure)
open import Once.Spec.Type.Sub using (_⊑π_)
open import Once.Spec.GradedOps using (in-valueᵛ; cata-semᵛ; mapLayerᵛ; ana-semᵛ; out-semᵛ)

postulate
  fold-unique : ∀ {π} (u : pure ⊑π π) {F A} (wf : WellFormedF F) (alg : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ)
                  (h : ⟦ μ-type F ⟧ᵛ → M π ⟦ A ⟧ᵛ)
              → (∀ x → EqM π (h (in-valueᵛ wf x)) (bindM π (mapLayerᵛ u wf h x) alg))
              → ∀ v → EqM π (h v) (cata-semᵛ u wf alg v)

  fold-fusion : ∀ {π} (u : pure ⊑π π) {F A B} (wf : WellFormedF F)
                  (alg : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg′ : ⟦ ⟦ F ⟧T B ⟧ᵛ → M π ⟦ B ⟧ᵛ)
                  (f : ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ)
              → (∀ y → EqM π (bindM π (alg y) f) (bindM π (mapLayerᵛ u wf f y) alg′))
              → ∀ v → EqM π (bindM π (cata-semᵛ u wf alg v) f) (cata-semᵛ u wf alg′ v)

  unfold-out  : ∀ {π} (u : pure ⊑π π) {F A} (wf : WellFormedF F) (clo : ⟦ A ⟧ᵛ → M π ⟦ ⟦ F ⟧T A ⟧ᵛ) (a : ⟦ A ⟧ᵛ)
              → EqM π (out-semᵛ π wf (ana-semᵛ π wf clo a))
                  (bindM π (clo a) (mapLayerᵛ u wf (λ a′ → returnM u (ana-semᵛ π wf clo a′))))

recursion : Recursion
recursion = record { fold-unique = fold-unique ; fold-fusion = fold-fusion ; unfold-out = unfold-out
                   ; iter-unfold = It.iter-unfold ; iter-unique = It.iter-unique }
