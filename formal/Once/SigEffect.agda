-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.SigEffect
--
-- The surface-level effect-shape ANNOTATION on a signature, declared
-- with the `! <shape>` delimiter (Plan 0.38 M0.2):
--
--   signature exit   : Eff Int Unit ! halts   -- terminates the machine
--   signature write  : Eff Int Unit ! emits   -- observable event, continues
--   signature getpid : Eff Unit Int           -- no annotation (default eff)
--   signature add    : Int -> Int             -- pure arrow (no annotation)
--
-- This is a pure, type-agnostic surface token. The compiler is
-- interpretation-BLIND: it reads NO interpretation; it learns an
-- external arrow's effect ONLY from this declared annotation, parsed
-- like any other part of the signature. The elaborator turns it (plus
-- the codomain type, for the `B ≡ Unit` coherence) into the
-- type-indexed `Once.SigOp.Info.EffectShape` at the SigOp build site.
--
-- `nothing` (no `!` annotation) means: a pure arrow elaborates to
-- `Pure`; an `Eff`-arrow defaults to `Emits` (the ordinary effectful
-- syscall). `halts`/`emits` override that.
------------------------------------------------------------------------

module Once.SigEffect where

-- | The declared effect shape of an external arrow.
data SigEffect : Set where
  emits : SigEffect   -- observable event, machine continues
  halts : SigEffect   -- observable event, machine terminates
