-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Normalize.Fixpoint: Fixpoint property proofs for NoRedex terms
--
-- For NoRedex t: normalize ∘ encode t ⟶* encode t
--
-- This module is a facade that re-exports from split submodules to
-- reduce memory pressure during type-checking.
------------------------------------------------------------------------

module normalizer.TCB0.Normalizer.Proofs.Fixpoint where

-- Re-export everything from the split modules
open import normalizer.TCB0.Normalizer.SelfFixpoint public
