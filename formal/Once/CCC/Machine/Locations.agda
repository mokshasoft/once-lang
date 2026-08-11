-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.Locations — the fundamental location TYPES shared by
-- the categorical IR and the abstract machine (D062).
--
-- These sit strictly BELOW both `Once.IR` and the machine
-- (`Once.CCC.Machine.SMCore`). The IR's `free-heap` constructor and its
-- `LocMatchesMode` predicate need the location *types* — but the IR must NOT
-- depend on the machine's *execution* (`exec-loop`, `readLoc`, …). Extracting
-- the types here inverts the dependency correctly:
--
--     Once.IR  ─┐
--                   ├─→  Once.CCC.Machine.Locations  (types only)
--     SMCore       ─┘    (← FrameSemantics, HeapAddress)
--
-- so the denotational meaning's import closure no longer pulls in the machine.
-- `SMCore` re-exports these (`open import … public`), so its existing
-- importers are unaffected.
------------------------------------------------------------------------

module Once.CCC.Machine.Locations where

open import Data.Nat using (ℕ)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.HeapAddress using (HeapLocation)

-- | A stack slot index.
Slot : Set
Slot = ℕ

-- | A location holding a value: a slot on a stack frame, or a dynamic heap
-- cell. (No Words/addresses — the concrete backend maps these to addresses.)
data ValueLocation (FS : FrameSemantics) : Set where
  AtStack   : FrameSemantics.Frame FS → Slot → ValueLocation FS
  AtDynamic : HeapLocation → ValueLocation FS
