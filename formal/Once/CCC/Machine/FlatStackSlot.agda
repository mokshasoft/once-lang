-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatStackSlot   (Plan 0.54 rung D item 2; gutted by 0.63)
--
-- THE LIVE STACK WINDOW ONLY MOVES AT A CALL OR RETURN.
--
-- This module used to be 300 lines. `Registers.stackSlot` was a RUNTIME
-- MIRROR of `%rsp` living in the abstract register file, written by
-- `exec-abstract` at three sites, and proving it constant needed an
-- induction over `exec-abstract` mutual with the nested trace/case/loop
-- walks.
--
-- Plan 0.63 deleted the mirror. The current frame's reserved slot count now
-- lives with the frame stack, as `AllocState.frame-slots`, written by
-- `enter-frame`/`leave-frame` and by nothing else — so `exec-abstract`
-- cannot touch it and every straight-line case is `refl`. What is left is
-- the enumeration itself, kept because `flat-exec-instr`'s catch-all does
-- not reduce for an abstract `i`.
--
-- Consumed by `ConcFlatSim.run-stack-slot`, which makes the window constant
-- along a run and turns `slot-read-in-frame` into arithmetic about the
-- emitter's static budget.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatStackSlot (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.Machine.SMCore
import Once.Allocator.AbstractInstance as AI
open FrameSemantics FS using (Frame)
open MemOps {FS}
open ExecFinal {FS}
open AbstractExec {FS}
open import Once.CCC.Machine.FrameFree using (FrameFreeI; FrameFreeT)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}

------------------------------------------------------------------------
-- "…reserves the same window as". An EQUATION over the ALLOCSTATE now.
------------------------------------------------------------------------
SameSlot : AllocState {FS} → AllocState {FS} → Set
SameSlot alloc' alloc = frame-slots alloc' ≡ frame-slots alloc

ss-jump : ∀ (mpc : Maybe ℕ) (fs : FlatState)
        → SameSlot (falloc (do-jump mpc fs)) (falloc fs)
ss-jump (just pc') fs = refl
ss-jump nothing    fs = refl

ss-branch : ∀ (b : Bool) (m : ℕ) (prog : AbstractTrace) (fs : FlatState)
          → SameSlot (falloc (do-branch b m prog fs)) (falloc fs)
ss-branch true  m prog fs = ss-jump (find-label prog m) fs
ss-branch false m prog fs = refl

-- the two aux-style slot reads dispatch through a `Maybe`, so they need the
-- split even though both sides are `refl` (a halt is a LocState update)
ss-mv : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
      → frame-slots (proj₂ (exec-load-from-slot-with-value mv ls alloc)) ≡ frame-slots alloc
ss-mv (just v) ls alloc = refl
ss-mv nothing  ls alloc = refl

ss-mv-ri : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
         → frame-slots (proj₂ (exec-restore-input-with-value mv ls alloc)) ≡ frame-slots alloc
ss-mv-ri (just v) ls alloc = refl
ss-mv-ri nothing  ls alloc = refl

-- NB the closure markers are the one place the window legitimately MOVES
-- (`c-thunk` reserves the callee's, `c-ret` restores the caller's). Both are
-- excluded here by `FrameFreeI`; making that statement per-frame is what
-- lands with their producer.

------------------------------------------------------------------------
-- Lifted to the FLAT machine. Control moves `fpc`/`halted` only; the
-- straight-line cases thread `exec-abstract`, which cannot reach
-- `frame-slots` — so each is `refl`. The frame-moving instructions and the
-- closure markers are `⊥`-elim (exactly what `FrameFreeI` excludes).
------------------------------------------------------------------------
flat-stack-slot : ∀ (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
                → FrameFreeI i
                → frame-slots (falloc (flat-exec-instr i prog fs))
                    ≡ frame-slots (falloc fs)
flat-stack-slot (instr-ctrl (c-label m))               prog fs ff = refl
flat-stack-slot (instr-ctrl (c-thunk m b))             prog fs ()
flat-stack-slot (instr-ctrl (c-ret b))                 prog fs ()
flat-stack-slot (instr-ctrl (c-jmp m))                 prog fs ff = ss-jump (find-label prog m) fs
flat-stack-slot (instr-ctrl (c-branch-scratch-zero m)) prog fs ff =
  ss-branch (sv-is-zero (readReg (regs (floc fs)) Scratch)) m prog fs
flat-stack-slot (instr-ctrl (c-branch-tag-zero m))     prog fs ff =
  ss-branch (tag-zf (flat-read-tag (floc fs))) m prog fs
flat-stack-slot (instr-alloc-stack n)   prog fs ()
flat-stack-slot (instr-dealloc-stack n) prog fs ()
flat-stack-slot (instr-push-frame cap)  prog fs ()
flat-stack-slot instr-pop-frame         prog fs ()
flat-stack-slot mov-to-output            prog fs ff = refl
flat-stack-slot mov-to-input             prog fs ff = refl
flat-stack-slot mov-output-to-input2     prog fs ff = refl
flat-stack-slot mov-input2-to-output     prog fs ff = refl
flat-stack-slot load-indirect            prog fs ff = refl
flat-stack-slot load-indirect-suc        prog fs ff = refl
flat-stack-slot (load-from-slot k)       prog fs ff =
  ss-mv (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs) (falloc fs)
flat-stack-slot (store-at-slot k)        prog fs ff = refl
flat-stack-slot store-indirect           prog fs ff = refl
flat-stack-slot store-indirect-suc       prog fs ff = refl
flat-stack-slot (lea-slot k)             prog fs ff = refl
flat-stack-slot (restore-input k)        prog fs ff =
  ss-mv-ri (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs) (falloc fs)
flat-stack-slot (lea-indexed k)          prog fs ff = refl
flat-stack-slot (instr-reclaim-to k)     prog fs ff = refl
flat-stack-slot instr-call-closure       prog fs ff = refl
flat-stack-slot (worklist-init k)        prog fs ff = refl
flat-stack-slot (worklist-push k)        prog fs ff = refl
flat-stack-slot (worklist-pop k)         prog fs ff =
  ss-mv (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs) (falloc fs)
flat-stack-slot (worklist-check k)       prog fs ff = refl
flat-stack-slot (instr-sigop si)         prog fs ff = refl
flat-stack-slot (instr-load-const p v)   prog fs ff = refl
flat-stack-slot (instr-load-code-addr k) prog fs ff = refl
flat-stack-slot instr-save-closure-reg   prog fs ff = refl
flat-stack-slot (instr-load-tag-lit k)   prog fs ff = refl
flat-stack-slot (instr-case-on-tag f g)  prog fs ()
flat-stack-slot (instr-alloc-heap k)     prog fs ff = refl
flat-stack-slot (instr-loop body)        prog fs ()
flat-stack-slot (instr-reg-op op)        prog fs ff = refl
