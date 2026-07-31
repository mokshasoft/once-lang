-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.InstrSlot   (Plan 0.54 rung D, item 2)
--
-- THE SLOT AN INSTRUCTION ADDRESSES, if any.
--
-- This is what ties a slot-liveness fact to the instruction actually fetched:
-- a claim stated for an *arbitrary* slot at a site is not a weaker assumption,
-- it is an inconsistent one (`slot ≔ stackSlot` refutes it). It lives here, in
-- the machine layer, because BOTH sides of the slot argument need it: the
-- flat↔x86-64 correspondence (`ConcFlatSim.slot-read-in-frame`) and the emitter
-- (`Once.CCC.Codegen.SlotBudget`, which bounds it by the static budget).
--
-- ENUMERATED, with no catch-all, so it REDUCES at the use sites (a catch-all
-- does not survive the case-tree translation).
------------------------------------------------------------------------

module Once.CCC.Machine.InstrSlot where

open import Data.Maybe using (Maybe; just; nothing)

open import Once.CCC.Machine.SMCore

slot-of : AbstractInstr → Maybe Slot
slot-of (load-from-slot k)  = just k
slot-of (store-at-slot k)   = just k
slot-of (lea-slot k)        = just k
slot-of (restore-input k)   = just k
slot-of (lea-indexed k)     = just k
slot-of (worklist-init k)   = just k
slot-of (worklist-push k)   = just k
slot-of (worklist-pop k)    = just k
slot-of (worklist-check k)  = just k
slot-of mov-to-output          = nothing
slot-of mov-to-input           = nothing
slot-of mov-output-to-input2   = nothing
slot-of mov-input2-to-output   = nothing
slot-of load-indirect          = nothing
slot-of load-indirect-suc      = nothing
slot-of store-indirect         = nothing
slot-of store-indirect-suc     = nothing
slot-of (instr-alloc-stack _)  = nothing
slot-of (instr-dealloc-stack _) = nothing
slot-of (instr-reclaim-to _)   = nothing
slot-of (instr-push-frame _)   = nothing
slot-of instr-pop-frame        = nothing
slot-of instr-call-closure     = nothing
slot-of (instr-sigop _)        = nothing
slot-of (instr-load-const _ _) = nothing
slot-of (instr-load-code-addr _) = nothing
slot-of instr-save-closure-reg = nothing
slot-of (instr-load-tag-lit _) = nothing
slot-of (instr-case-on-tag _ _) = nothing
slot-of (instr-alloc-heap _)   = nothing
slot-of (instr-loop _)         = nothing
slot-of (instr-reg-op _)       = nothing
slot-of (instr-ctrl _)         = nothing
