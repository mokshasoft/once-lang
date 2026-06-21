-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.SigOp.Interpretation
--
-- Plan 0.38 M0 (`0.38-core`): the verified core's abstract handle on
-- "what does this external SigOp name mean?". An `Interpretation`
-- resolves each name to its declared `SigOpInfo` — machine semantics
-- (`semM`) + observable effect shape (`EffectShape`).
--
-- The core (`elaborate`, `⟦_⟧ˢ`, `⟦_⟧ᴰ`, `faithful`) is parameterized
-- over this abstract record and NEVER imports a concrete instance.
-- Concrete interpretations (Linux, seL4, a user's own) are supplied
-- off-line at the extraction root — all equal, none baked into the
-- compiler. This replaces the `generic-info` / `classify-name` /
-- `generic-semM` `String → SigOpInfo` catch-all, which gave Linux
-- special treatment INSIDE the core (the D061 / 0.38 bug: a SigOp's
-- effect came from a hardcoded name match, not its declared contract).
------------------------------------------------------------------------

module Once.SigOp.Interpretation where

open import Data.String using (String)
open import Data.Maybe using (Maybe)

open import Once.SigOp.Info using (SigOpInfo)

-- | An interpretation resolves the names of *its* (external) SigOps to
-- their declared contract — `info name = just (its SigOpInfo)`. It is
-- PARTIAL: `nothing` for any name it does not own (notably the INTERNAL
-- producers — `arith.*`, `lit.*`, `arith.block.*` — which carry their own
-- `semM` and must NOT be re-resolved through an interpretation). This is
-- what lets `resolveSigOps` swap only external placeholders and leave
-- internal SigOps (e.g. `arith.div.int`) untouched.
record Interpretation : Set where
  field
    info : ∀ {A B} → String → Maybe (SigOpInfo A B)
