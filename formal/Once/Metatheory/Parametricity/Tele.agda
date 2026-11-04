{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Tele — a program's definitions are
-- parametric (`Spec.Metatheory.Parametricity.param-tele`).
--
-- Along the telescope: a definition's meaning at an instance is its body's,
-- read at that instance against the definitions before it; two instances of
-- the body, with a relation per type variable and no variables in scope,
-- are related by the abstraction theorem, given that the earlier
-- definitions are parametric. A body is effect-free, so its related
-- computations are related values.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)

module Once.Metatheory.Parametricity.Tele (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) where

open import Data.Fin using (zero; suc)
open import Data.Unit using (tt)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Observation Σ using (Model)
open import Once.Spec.Core.Program Σ using (Tele; []; def; teleSem)
open import Once.Spec.Metatheory using (ParamDefs)
open import Once.Metatheory.Parametricity.Comp Σ using (rcPure⁻)
import Once.Metatheory.Parametricity.Abstraction as Abstraction

param-tele : ∀ (mo : Model) {s} {S : Defs s} (tl : Tele S) → ParamDefs Σ fmt S (teleSem fmt mo tl)
param-tele mo []                  ()
param-tele mo (def {S = S} tl sc body D) zero τ τ′ r r′ ρ =
  rcPure⁻ (Abstraction.abstraction Σ u fmt S D D (teleSem fmt mo tl) (param-tele mo tl) τ τ′ r r′ ρ tt tt tt)
param-tele mo (def tl sc body D) (suc d) τ τ′ r r′ ρ = param-tele mo tl d τ τ′ r r′ ρ
