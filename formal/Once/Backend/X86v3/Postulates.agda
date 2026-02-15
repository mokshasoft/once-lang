------------------------------------------------------------------------
-- Once.Backend.X86v3.Postulates
--
-- Shared postulates for X86v3 SlotMachine proof.
-- These express capacity conditions that are not yet proven.
--
-- See final-postulate-elimination.md for elimination strategies.
------------------------------------------------------------------------

module Once.Backend.X86v3.Postulates where

open import Data.Nat using (ℕ; _+_; _≤_) renaming (_*_ to _*ℕ_)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Allocation

------------------------------------------------------------------------
-- Capacity postulates
--
-- These postulates express that after running a sub-IR, there is still
-- enough capacity for program-bound-sized operations.
--
-- Root cause: After sub-IR f runs, slot advances by up to ps * ir-size f.
-- The original precondition (slot + ps * bound ≤ capacity) doesn't
-- transfer because the slot moved.
--
-- See final-postulate-elimination.md for why these can't be proven
-- from current preconditions and strategies for elimination.
------------------------------------------------------------------------

module CapacityPostulates {FS : FrameSemantics} (program-bound : ℕ) where
  open FrameSemantics FS

  -- After any sub-IR execution, program-bound capacity still holds.
  -- Used by: ComposeWF, PairWF, ApplyWF
  postulate
    program-bound-cap : ∀ (alloc : AllocState {FS}) →
      next-slot alloc + pair-slots *ℕ program-bound ≤ frame-capacity alloc
