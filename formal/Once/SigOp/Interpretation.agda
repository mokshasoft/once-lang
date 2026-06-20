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

open import Once.Type using (Type; ArrowKind; mk-kind; pure; eff)
open import Once.SigOp.Info using (SigOpInfo; mk-info; semM; EffectShape; Pure)

-- | An interpretation resolves each external SigOp name to its declared
-- contract. `info name` is the op's native `SigOpInfo` (its `semM` and
-- its `effect`). The value-vs-arrow `Pure` structure below is the CORE's
-- structural rule (an effect is realized only on an arrow, D018), NOT
-- the interpretation's concern.
record Interpretation : Set where
  field
    info : ∀ {A B} → String → SigOpInfo A B

module _ (I : Interpretation) where
  open Interpretation I

  -- | A SigOp referenced as a VALUE (non-arrow type, or a `closure` /
  -- `poly` reference): its effect is `Pure` — an effect is realized only
  -- on application (D018), so a bare value reference emits nothing at
  -- build. The `semM` still comes from the interpretation.
  value-info : ∀ {A B} → String → SigOpInfo A B
  value-info {A} {B} nm = mk-info nm (semM (info {A} {B} nm)) Pure

  -- | A SigOp at an ARROW type, dispatched on the arrow's purity `π` so
  -- the effect is COHERENT with the type: a `pure` arrow op is `Pure`
  -- (applying it emits nothing); an `eff` arrow op carries its declared
  -- per-application effect from `info` (no `classify-name` string guess).
  arrow-info : ∀ {A B} → ArrowKind → String → SigOpInfo A B
  arrow-info (mk-kind _ pure) nm = value-info nm
  arrow-info (mk-kind _ eff)  nm = info nm
