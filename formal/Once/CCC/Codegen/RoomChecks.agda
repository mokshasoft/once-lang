-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.RoomChecks — the room checks, a late pass (D371).
--
-- Plan 0.123 A.4 step 5. `room-checks` takes the finished abstract image and
-- puts `instr-room k` (an abstract no-op; per arch, `frontier + k words ≤ stack
-- pointer`, else a call of the Host's `once_exhausted`) at every point control
-- reaches other than by falling through within a stretch:
--
--   * index 0, before the program's `c-start`;
--   * right after every `c-label` (a jump lands on the label);
--   * right after every `c-entry` (a call lands ON the entry, which reserves
--     the callee's frame before anything else runs);
--   * right after every call (the return lands one past it).
--
-- Each check's `k` is what its STRETCH spends — the instructions after it up to
-- and including the next of those boundary instructions. Spending, in words:
-- an allocation its `n` (the frontier goes up), a frame reservation its `b`
-- (the stack pointer goes down), a call one return-address word plus `E`, the
-- largest frame any entry reserves — the callee's `c-entry` reserves before the
-- callee's own check runs, and a closure call's callee is not known here.
-- Everything else spends nothing (`c-ret` only gives room back).
--
-- Placement is C.2's (plan 0.123 Part C); tightening it toward C.1 changes this
-- module and the budget proof only. IRToTrace, linking and the IR-level proofs
-- never see a check.
------------------------------------------------------------------------

module Once.CCC.Codegen.RoomChecks where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; instr-ctrl; instr-room; instr-alloc-heap; instr-call-closure
        ; c-label; c-entry; c-start; c-call-fn)

-- the frame an entry reserves (0 for anything that is not one)
entry-frame : AbstractInstr → ℕ
entry-frame (instr-ctrl (c-entry _ b)) = b
{-# CATCHALL #-}
entry-frame _                          = 0

-- the largest frame any entry of the image reserves
max-entry : AbstractTrace → ℕ
max-entry []      = 0
max-entry (i ∷ t) = entry-frame i ⊔ max-entry t

-- what one instruction spends, in words, given the largest entry frame `E`
spend : ℕ → AbstractInstr → ℕ
spend E (instr-alloc-heap n)        = n
spend E (instr-ctrl (c-start b))    = b
spend E (instr-ctrl (c-entry _ b))  = b
spend E (instr-ctrl (c-call-fn _))  = suc E
spend E instr-call-closure          = suc E
{-# CATCHALL #-}
spend E _                           = 0

-- a check goes right after these: control arrives there other than by falling
-- through (a jump lands on a label, a call on an entry, a return after a call)
boundary? : AbstractInstr → Bool
boundary? (instr-ctrl (c-label _))    = true
boundary? (instr-ctrl (c-entry _ _))  = true
boundary? (instr-ctrl (c-call-fn _))  = true
boundary? instr-call-closure          = true
{-# CATCHALL #-}
boundary? _                           = false

-- what a stretch spends: up to and including its first boundary instruction
stretch : ℕ → AbstractTrace → ℕ
stretch E []      = 0
stretch E (i ∷ t) = spend E i + (if boundary? i then 0 else stretch E t)

-- the image after a check: every boundary instruction is followed by the check
-- for the stretch after it
checks : ℕ → AbstractTrace → AbstractTrace
checks E []      = []
checks E (i ∷ t) =
  i ∷ (if boundary? i then instr-room (stretch E t) ∷ checks E t else checks E t)

-- THE PASS: a check at index 0 for the first stretch, then the rest.
room-checks : AbstractTrace → AbstractTrace
room-checks t = instr-room (stretch (max-entry t) t) ∷ checks (max-entry t) t

------------------------------------------------------------------------
-- THE BUDGET'S MEASURE: what the code spends from here up to the next check.
-- At a check it is 0 (the check itself spends nothing; its own `k` covers what
-- follows it). The pass makes each check's `k` exactly this measure just past
-- it (`RoomChecksFacts.check-k`), which is what the budget invariant runs on.
------------------------------------------------------------------------
room? : AbstractInstr → Bool
room? (instr-room _) = true
{-# CATCHALL #-}
room? _              = false

till-check : ℕ → AbstractTrace → ℕ
till-check E []      = 0
till-check E (i ∷ t) = if room? i then 0 else spend E i + till-check E t

-- …from the instruction at `pc` on
need : AbstractTrace → ℕ → ℕ
need prog pc = till-check (max-entry prog) (Data.List.drop pc prog)
  where import Data.List
