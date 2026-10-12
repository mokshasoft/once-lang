-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Bool — the language's truth values.
--
-- SPEC. Once has no primitive boolean: a truth value is `Unit + Unit`, false
-- the left injection and true the right one, so a comparison's tag IS its
-- truth value (the 0/1 a machine comparison writes).
------------------------------------------------------------------------

module Once.Spec.Bool where

open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

truth : Bool → ⊤ ⊎ ⊤
truth false = inj₁ tt
truth true  = inj₂ tt
