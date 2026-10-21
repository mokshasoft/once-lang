-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Res — the laws of a computation's result (`Once.Internal.Res`).
------------------------------------------------------------------------

module Once.Res where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Internal.Res using (Res; returns)

-- | `returns` is injective — it is a constructor. Needed wherever an
--   obligation BINDS the returned value and a proof knows what it was.
returns-inj : ∀ {X} {x y : X} → returns x ≡ returns y → x ≡ y
returns-inj refl = refl

