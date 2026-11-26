-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · POC-0b(i) — conversion is DECIDABLE (the Dec capstone)
--
-- The Bool procedure `conv-fin` plus its soundness/completeness package into
-- the idiomatic statement of "decidable conversion": a decision that returns
-- the PROOF, not just a bit.
--
--   ≋-dec : FiniteFO A → FirstOrder C → (t u : Term A C) → Dec (t ≋ u)
--
-- This is literally "decidable dependent-type conversion" for the fragment —
-- `yes p` carries a proof `p : t ≋ u`, `no ¬p` carries a refutation. Zero
-- new postulates (whole-POC axiom inventory stays: just funext). The closed
-- case (POC-0) is the instance `≋-dec ffo-unit`.
------------------------------------------------------------------------

module OCP0009.Decidable where

open import OCP0009.Normalizer.Types
open import OCP0009.Normalizer.CCC
open import OCP0009.Normalizer.Evaluator hiding (fst; snd)
open import OCP0009.Conv using (FirstOrder)
open import OCP0009.Sound using (_≋_)
open import OCP0009.Finite
  using (FiniteFO; ffo-unit; conv-fin; conv-fin-sound; conv-fin-complete)

false≢true : false ≡ true → ⊥
false≢true ()

------------------------------------------------------------------------
-- Decidability of observational equality on the finite first-order fragment.
------------------------------------------------------------------------

≋-dec : ∀ {A C} → FiniteFO A → FirstOrder C → (t u : Term A C) → Dec (t ≋ u)
≋-dec fa fc t u with conv-fin fa fc t u | inspect (conv-fin fa fc t) u
... | true  | ⟪ eq ⟫ = yes (conv-fin-sound fa fc t u eq)
... | false | ⟪ eq ⟫ =
  no (λ e → false≢true (trans (sym eq) (conv-fin-complete fa fc t u e)))

-- Closed case (POC-0) as the `Unit`-domain instance.
≋-dec₀ : ∀ {C} → FirstOrder C → (t u : Term Unit C) → Dec (t ≋ u)
≋-dec₀ = ≋-dec ffo-unit
