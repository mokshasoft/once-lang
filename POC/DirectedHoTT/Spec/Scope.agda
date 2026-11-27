-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — SCOPES (de Bruijn depth) and VARIABLES.
--
-- Untyped scoping — genuine dependency without the transport hell of
-- intrinsic dependent typing. Split out of `Spec/Syntax` (2026-11-27,
-- SPIKE-GENERIC-SYNTAX) because the generic syntax (`Spec/Bind`) and the
-- kernel's syntax (`Spec/Syntax`, which re-exports this module) both need
-- them.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Scope where

data Cx : Set where
  ε  : Cx
  _∙ : Cx → Cx

data Var : Cx → Set where
  vz : ∀ {Γ} → Var (Γ ∙)
  vs : ∀ {Γ} → Var Γ → Var (Γ ∙)
