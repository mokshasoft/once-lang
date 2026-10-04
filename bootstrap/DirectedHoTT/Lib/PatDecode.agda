-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ A NESTED PATTERN, DECODED (PLAN-FAITHFUL F6).
--
-- A `Lib/SynPat` case has ONE live row, at the pattern's head `h`; at any
-- other head the table holds `noRow`, whose description has no rule.  So a
-- closed normal payload at the case's row (`case-any`) FORCES the head:
--
--     pat-hit : ◇ ⊢ p ∷ El (dpay I D (R (rowAt s₀ h r s₀ k) j q c)) → IsNormal p → k ≡ h
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.PatDecode where

open import normalizer.Syntax.Types using ( _≡_; refl; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Lib.SynPat using ( rowAt; rowAt-elim; noRow )
open import DirectedHoTT.Lib.Decode using ( pay-none )

pat-hit : {I D j q c p : RTm ε} (s₀ h k : ℕ) {r : Row} →
          ◇ ⊢ p ∷ El (dpay I D (Row.R (rowAt s₀ h r s₀ k) j q c)) → IsNormal p → k ≡ h
pat-hit {I} {D} {j} {q} {c} {p} s₀ h k {r} dp np =
  rowAt-elim (λ ρ → ◇ ⊢ p ∷ El (dpay I D (Row.R ρ j q c)) → IsNormal p → k ≡ h) s₀ h s₀ k
             (λ _ e _ _ → e) (λ d n → ⊥-elim (pay-none d done n)) dp np
