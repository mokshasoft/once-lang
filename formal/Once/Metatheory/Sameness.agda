{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Sameness — sameness is a partial equivalence, and it
-- respects `>>=` (`Spec.Metatheory.Sameness`).
--
-- Symmetry and transitivity are by recursion on the type
-- (`Once.Metatheory.Coherence.PER`). Observed computations are related runs;
-- binding related runs to related continuations relates the results, and the
-- graded bind is `>>=∞` up to bisimilarity. Sameness of streams is the
-- greatest fixed point of one layer (`Once.Metatheory.Coherence.StreamSame`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Sameness (Σ : Signature) where

open import Once.Spec.Metatheory using (Sameness)
open import Once.Spec.Effect Σ using (toT∞)
open import Once.Metatheory.Erase Σ using (toT∞-bindᵍ)
open import Once.Metatheory.Bisim Σ using (≈-sym)
open import Once.Metatheory.Coherence.Relation Σ using (≈-Relatedˡ; ≈-Relatedʳ; bindRel; fromObserved; toObserved)
import Once.Metatheory.Coherence.PER as PER
import Once.Metatheory.Coherence.StreamSame as StreamSame

sameness : Sameness Σ
sameness = record
  { Same-sym   = PER.Same-sym Σ
  ; Same-trans = PER.Same-trans Σ
  ; SameM-bind = λ π₁ π₂ A B {m} {m′} {f} {f′} s k →
      toObserved (≈-Relatedˡ (toT∞-bindᵍ π₁ π₂ m f)
                   (≈-Relatedʳ (toT∞-bindᵍ π₁ π₂ m′ f′)
                     (bindRel (fromObserved s) λ r → fromObserved (k r))))
  ; stream-out   = λ f G → StreamSame.same-out Σ f G
  ; stream-in    = λ f G → StreamSame.same-in Σ f G
  ; stream-coind = λ f G → StreamSame.same-coind Σ f G
  }
