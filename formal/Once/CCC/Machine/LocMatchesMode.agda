-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.LocMatchesMode
--
-- The mode↔location-shape link (Plan 0.14 Camp 2): a compound value's
-- representation lives where its `AllocMode` says — Stack-mode at `AtStack`
-- locations, Heap-mode at `AtDynamic`. This is a MACHINE-VALIDITY predicate,
-- not IR syntax, so (Plan 0.47) it lives here — downstream of both the IR
-- (`AllocMode`) and the machine location types (`ValueLocation`) — rather than
-- in `Once.IR`. That keeps the IR a pure syntax tier: `Once.IR` no
-- longer imports `Once.CCC.Machine.Locations` (→ `FrameSemantics` → `Memory.*`).
--
-- Used only by the compound-type `ValidAtWF` constructors (pair / inl / inr /
-- closure / μ / ν). Primitives can live at any loc regardless of mode.
------------------------------------------------------------------------

module Once.CCC.Machine.LocMatchesMode where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open import Once.IR using (AllocMode; Stack; Heap)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)

LocMatchesMode : ∀ {FS} → AllocMode → ValueLocation FS → Set
LocMatchesMode Stack (AtStack _ _)  = ⊤
LocMatchesMode Stack (AtDynamic _)  = ⊥
LocMatchesMode Heap  (AtStack _ _)  = ⊥
LocMatchesMode Heap  (AtDynamic _)  = ⊤
