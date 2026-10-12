-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Recursion — the fold's universal property
-- (`Spec.Metatheory.Recursion`, plan 0.112 D3) and unfold's computation law
-- (plan 0.116 E).
--
-- POSTULATED, NOT PROVED. The statements are the Spec's; they were moved to
-- where they belong (the language's metatheory) before their proofs exist.
-- Why they hold: a `μ` value is a finite tree, and every one is `in-valueᵛ` of
-- a layer, so an `h` that commutes with the constructor agrees with the fold by
-- induction on the tree (`fold-unique`); fusion is uniqueness applied to
-- `λ v → bindM π (cata-semᵛ π wf alg v) f`, using that sequencing a layer
-- commutes with the monad's bind (a polynomial functor is traversable). At
-- `eff` both also need `T`'s bind to be a congruence in its continuation,
-- which is the `extensionality` postulate (`Once.Postulates` P1).
--
-- Nothing proves anything FROM these postulates today: they are claims on the
-- apex (`Once.Certified`'s `language` field), each to be discharged here.
------------------------------------------------------------------------

module Once.Metatheory.Recursion where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Type using (μ-type; ⟦_⟧T)
open import Once.Spec.Type.WellFormed using (WellFormedF)
open import Once.Spec.Metatheory using (Recursion)
open import Once.Denotation.GradedDomain using (M; ⟦_⟧ᵛ; bindM; returnM)
open import Once.Spec.Type.Grade using (pure)
open import Once.Denotation.GradedOps using (in-valueᵛ; cata-semᵛ; mapLayerᵛ; ana-semᵛ; out-semᵛ)

postulate
  fold-unique : ∀ π {F A} (wf : WellFormedF F) (alg : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ)
                  (h : ⟦ μ-type F ⟧ᵛ → M π ⟦ A ⟧ᵛ)
              → (∀ x → h (in-valueᵛ wf x) ≡ bindM π (mapLayerᵛ π wf h x) alg)
              → ∀ v → h v ≡ cata-semᵛ π wf alg v

  fold-fusion : ∀ π {F A B} (wf : WellFormedF F)
                  (alg : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg′ : ⟦ ⟦ F ⟧T B ⟧ᵛ → M π ⟦ B ⟧ᵛ)
                  (f : ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ)
              → (∀ y → bindM π (alg y) f ≡ bindM π (mapLayerᵛ π wf f y) alg′)
              → ∀ v → bindM π (cata-semᵛ π wf alg v) f ≡ cata-semᵛ π wf alg′ v

  unfold-out  : ∀ π {F A} (wf : WellFormedF F) (clo : ⟦ A ⟧ᵛ → M π ⟦ ⟦ F ⟧T A ⟧ᵛ) (a : ⟦ A ⟧ᵛ)
              → out-semᵛ π wf (ana-semᵛ π pure wf clo a)
                ≡ bindM π (clo a) (mapLayerᵛ π wf (λ a′ → returnM π (ana-semᵛ π pure wf clo a′)))

recursion : Recursion
recursion = record { fold-unique = fold-unique ; fold-fusion = fold-fusion ; unfold-out = unfold-out }
