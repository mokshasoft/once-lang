-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.ValidAtWFHalted
--
-- Plan 0.32 choice (a), migration step 2: `ValidAtWF` is invariant under
-- the `halted` flag.
--
-- WHY: the `exec-trace-is-flat` bridge equates the flat machine's final
-- state with `exec-trace`'s only up to `forced` (halted := true) — because
-- `exec-flat` halts at end-of-program while `exec-trace` does not. To
-- transport a semantic-side `ValidAtWF` result across that bridge we need
-- it to ignore the `halted` field, which it does: every constructor reads
-- the state only through `readLoc`/`readReg` (which project
-- regs/stackMem/heapMem) and through state-independent
-- `BeforeFrontier`/`BodyCorrect`. A `halted` record-update preserves all
-- read fields definitionally, so the constructor premises pass through
-- unchanged; only nested `ValidAtWF` recurse.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.Spec.Name using (CanonicalName)

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Machine.ValidAtWFHalted (o : CanonicalName) (tbl : List IRFun) where

open import Data.Bool using (Bool)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (LocState; sucLoc; module MemOps)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.Denotation.ValueDomain using () renaming (⟦_⟧ᴰᴵ to ⟦_⟧)
open import Once.CCC.Machine.ValueRel using (module ClosureWellFormedDef)
open import Once.CCC.Machine.Validity using (module ReadLocEq)

module _ {FS : FrameSemantics} where
  open ClosureWellFormedDef {FS}
  open MemOps {FS} using (readLoc)
  open ReadLocEq {FS} using (readLoc-stack-heap-eq)

  -- `readLoc` ignores `halted`: a halted-update preserves stackMem/heapMem
  -- definitionally, so `readLoc-stack-heap-eq` collapses the two.
  -- plan 0.135 S1: an instance of the one transport — `halted` is not memory.
  validAtWF-set-halted : ∀ {prog m alloc A} {v : ⟦ A ⟧} {loc s} (b : Bool)
    → ValidAtWF {prog = prog} m alloc {A} v loc s
    → ValidAtWF {prog = prog} m alloc {A} v loc (record s { halted = b })
  validAtWF-set-halted {v = v} {loc = loc} {s = s} b =
    validityWF-mem-only v loc s (record s { halted = b }) refl refl
