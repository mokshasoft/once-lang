{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity — a type argument is never inspected
-- (`Spec.Metatheory.Parametricity`, D371).
--
--   abstraction  the fundamental lemma between two instances
--                (`Parametricity.Abstraction`);
--   param-tele   a program's definitions are parametric, along the
--                telescope (`Parametricity.Tele`);
--   naturality   from the definitions' parametricity at the graph of `f`
--                and the graph lemma (`Parametricity.Naturality`,
--                `Parametricity.Graph`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Parametricity (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Once.Spec.Metatheory using (Parametricity)
open import Once.Metatheory.Parametricity.Comp Σ using (obsRC)
import Once.Metatheory.Parametricity.Abstraction as Abstraction
import Once.Metatheory.Parametricity.Tele as Tele
import Once.Metatheory.Parametricity.Naturality as Naturality

parametricity : Parametricity Σ fmt S
parametricity = record
  { abstraction = λ d d′ δ pd σ σ′ r r′ ρ γ γ′ e → obsRC (Abstraction.abstraction Σ u fmt S d d′ δ pd σ σ′ r r′ ρ γ γ′ e)
  ; param-tele  = λ mo tl → Tele.param-tele Σ u fmt mo tl
  ; naturality  = Naturality.naturality Σ u fmt S
  }
