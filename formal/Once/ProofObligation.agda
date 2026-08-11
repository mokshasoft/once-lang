-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.ProofObligation
--
-- Marker for proof obligations that must be discharged.
--
-- Usage: Replace proof terms with !! when the proof is deferred.
-- These are NOT assumptions - they are debts that must be paid.
--
-- To find all obligations: grep for "ProofObligation.!!" or "PO.!!"
------------------------------------------------------------------------

module Once.ProofObligation where

-- Proof obligation marker
-- Type-checks but must be replaced with actual proofs
postulate
  !! : ∀ {ℓ} {A : Set ℓ} → A