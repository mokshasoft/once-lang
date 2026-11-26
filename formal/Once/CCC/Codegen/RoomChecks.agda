-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.RoomChecks — the room checks, a late pass (D377).
--
-- Plan 0.123 A.4 step 5. `room-checks` takes the finished abstract image and
-- puts `instr-room k` (an abstract no-op; per arch, `frontier + k words ≤ stack
-- pointer`, else a call of the Host's `once_exhausted`) at every point control
-- reaches other than by falling through within a stretch:
--
--   * right after the program's `c-start` (D488: the start checks its own
--     frame and the stack it reserves, and sets the stack limit, so nothing
--     comes before it);
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
open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; instr-ctrl; instr-room; instr-alloc-heap; instr-call-closure; instr-sigop
        ; c-label; c-entry; c-start; c-call-fn; Room; room; module Room)
open import Once.CCC.Codegen.StackDepth
  using (Depths; module Depths; Owner; o-start; own; before-from; Kind; kind; k-call; k-clo; k-sig; k-entry
        ; k-label; k-jump; k-branch; k-ret; k-start; k-none; chk; consistent?; T₀)
open import Once.CCC.Codegen.StackDepthTable using (table)

-- the frame an entry reserves (0 for anything that is not one)
entry-frame : AbstractInstr → ℕ
entry-frame (instr-ctrl (c-entry _ b)) = b
{-# CATCHALL #-}
entry-frame _                          = 0

-- the largest frame any entry of the image reserves
max-entry : AbstractTrace → ℕ
max-entry []      = 0
max-entry (i ∷ t) = entry-frame i ⊔ max-entry t

-- D488: needs add part by part (cells, stack), and nothing is `r0`
_⊕ʳ_ : Room → Room → Room
r ⊕ʳ q = room (Room.room-h r + Room.room-h q) (Room.room-s r + Room.room-s q)

r0 : Room
r0 = room 0 0

-- a need's words in all (what one region holds, before D488's limit splits it)
tot : Room → ℕ
tot r = Room.room-h r + Room.room-s r

-- D490: what one instruction spends, in words, at owner `o` under the depth
-- table `T`: an allocation cells; a CHECKED call (`StackDepth.chk`) its return
-- word and the callee's whole depth; a checked closure call the same over every
-- closure body; a checked SigOp (the fallback) its block's words. An unchecked
-- call or SigOp, and an entry, spend nothing here: their stack is in their
-- function's static depth (`StackDepth.past`), which the budget carries.
cells : AbstractInstr → ℕ
cells (instr-alloc-heap n) = n
{-# CATCHALL #-}
cells _                    = 0

stack-k : Depths → Owner → Kind → ℕ
stack-k T o (k-call g)    = if chk T o g then suc (Depths.dep T g) else 0
stack-k T o k-clo         = if Depths.clo-chk T o then suc (Depths.clo-dep T) else 0
stack-k T o (k-sig w)     = if Depths.sig-chk T then w else 0
stack-k T o (k-entry _ _) = 0
stack-k T o (k-label _)   = 0
stack-k T o (k-jump _)    = 0
stack-k T o (k-branch _)  = 0
stack-k T o k-ret         = 0
stack-k T o (k-start _)   = 0
stack-k T o k-none        = 0

spend : Depths → Owner → AbstractInstr → Room
spend T o i = room (cells i) (stack-k T o (kind i))

-- a check goes right after these: control arrives there other than by falling
-- through (a jump lands on a label, a call on an entry, a return after a call)
boundary-k : Kind → Bool
boundary-k (k-start _)   = true
boundary-k (k-label _)   = true
boundary-k (k-entry _ _) = true
boundary-k (k-call _)    = true
boundary-k k-clo         = true
boundary-k (k-sig _)     = false
boundary-k (k-jump _)    = false
boundary-k (k-branch _)  = false
boundary-k k-ret         = false
boundary-k k-none        = false

-- (D490: by the instruction's kind — the start, a label, an entry, a call)
boundary? : AbstractInstr → Bool
boundary? i = boundary-k (kind i)

-- what a stretch spends: up to and including its first boundary instruction
stretch : Depths → Owner → AbstractTrace → Room
stretch T o []      = r0
stretch T o (i ∷ t) = spend T (own o i) i ⊕ʳ (if boundary? i then r0 else stretch T (own o i) t)

-- the image after a check: every boundary instruction is followed by the check
-- for the stretch after it
checks : Depths → Owner → AbstractTrace → AbstractTrace
checks T o []      = []
checks T o (i ∷ t) =
  i ∷ (if boundary? i then instr-room (stretch T (own o i) t) ∷ checks T (own o i) t else checks T (own o i) t)

-- THE PASS. (D488: no check at index 0 any more — the program's first
-- instruction is its start, which checks for itself, and is a boundary.)
-- D490: the depth table it runs on — the computed one when its certificate holds
-- of the output, else the fallback (every call checked)
-- (the computed table an argument, so it is computed once)
pick-by : AbstractTrace → Depths → Bool → Depths
pick-by t T true  = T
pick-by t T false = T₀ (max-entry t)

pick-of : AbstractTrace → Depths → Depths
pick-of t T = pick-by t T (consistent? T (checks T o-start t))

-- (opaque: no proof needs more of it than its certificate, `RoomChecksFacts.pick-cert`,
-- and unfolded it is the whole table computation)
opaque
  pick : AbstractTrace → Depths
  pick t = pick-of t (table t)

-- (opaque too: a proof that compares two spellings of the checked image then
-- compares the images, not their checked forms instruction by instruction; the
-- body is `room-checks-def`)
opaque
  room-checks : AbstractTrace → AbstractTrace
  room-checks t = checks (pick t) o-start t

opaque
  unfolding room-checks
  room-checks-def : ∀ t → room-checks t ≡ checks (pick t) o-start t
  room-checks-def t = refl

  -- (the pass keeps the image's first instruction first: the rest of it, after)
  room-rest : AbstractInstr → AbstractTrace → AbstractTrace
  room-rest i t = Data.List.drop 1 (room-checks (i ∷ t))
    where import Data.List

  room-checks-∷ : ∀ i t → room-checks (i ∷ t) ≡ i ∷ room-rest i t
  room-checks-∷ i t = refl

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

till-check : Depths → Owner → AbstractTrace → Room
till-check T o []      = r0
till-check T o (i ∷ t) = if room? i then r0 else spend T (own o i) i ⊕ʳ till-check T (own o i) t

-- the image without its checks (the pass's input, read back off its output)
strip : AbstractTrace → AbstractTrace
strip []      = []
strip (i ∷ t) = if room? i then strip t else i ∷ strip t

-- the table a program's checks were placed by
tbl : AbstractTrace → Depths
tbl prog = pick (strip prog)

-- …from the instruction at `pc` on
need : AbstractTrace → ℕ → Room
need prog pc = till-check (tbl prog) (before-from o-start prog pc) (Data.List.drop pc prog)
  where import Data.List
