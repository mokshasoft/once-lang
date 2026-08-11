-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Once.CCC.Label using (LabelId)

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
-- "…leaves the frame stack alone". Plan 0.63: THREE equations, not one.
--
-- `frame-slots` is the current frame's reservation, `saved-frames` the
-- callers' beside their frames (D084), and `fret` the ghost return-pc stack
-- (step 1). A frame-free step touches NONE of them, and stating that as one
-- record is what lets the segmented-budget invariant carry the whole stack
-- through a run rather than just its top.
------------------------------------------------------------------------
record SameFrames (fs' fs : FlatState) : Set where
  constructor mkSameFrames
  field
    sf-slots : frame-slots  (falloc fs') ≡ frame-slots  (falloc fs)
    sf-saved : saved-frames (falloc fs') ≡ saved-frames (falloc fs)
    sf-ret   : fret fs'                  ≡ fret fs
open SameFrames public

sf-refl : ∀ (fs : FlatState) → SameFrames fs fs
sf-refl fs = mkSameFrames refl refl refl

sf-jump : ∀ (mpc : Maybe ℕ) (fs : FlatState) → SameFrames (do-jump mpc fs) fs
sf-jump (just pc') fs = mkSameFrames refl refl refl
sf-jump nothing    fs = mkSameFrames refl refl refl

sf-branch : ∀ (b : Bool) (m : LabelId) (prog : AbstractTrace) (fs : FlatState)
          → SameFrames (do-branch b m prog fs) fs
sf-branch true  m prog fs = sf-jump (find-label prog m) fs
sf-branch false m prog fs = mkSameFrames refl refl refl

-- the two aux-style slot reads dispatch through a `Maybe`, so they need the
-- split even though both sides are `refl` (a halt is a LocState update)
ss-mv : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
      → frame-slots (proj₂ (exec-load-from-slot-with-value mv ls alloc)) ≡ frame-slots alloc
ss-mv (just v) ls alloc = refl
ss-mv nothing  ls alloc = refl

ss-mv-saved : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
            → saved-frames (proj₂ (exec-load-from-slot-with-value mv ls alloc)) ≡ saved-frames alloc
ss-mv-saved (just v) ls alloc = refl
ss-mv-saved nothing  ls alloc = refl

ss-mv-ri : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
         → frame-slots (proj₂ (exec-restore-input-with-value mv ls alloc)) ≡ frame-slots alloc
ss-mv-ri (just v) ls alloc = refl
ss-mv-ri nothing  ls alloc = refl

ss-mv-ri-saved : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS) (alloc : AllocState {FS})
               → saved-frames (proj₂ (exec-restore-input-with-value mv ls alloc)) ≡ saved-frames alloc
ss-mv-ri-saved (just v) ls alloc = refl
ss-mv-ri-saved nothing  ls alloc = refl

-- NB the closure markers are the one place the frame stack legitimately MOVES
-- (`c-thunk` pushes the caller's frame and reserves the callee's, `c-ret` pops
-- both, and `instr-call-closure` will push the return pc). All three are
-- excluded here by `FrameFreeI`; giving them their real correspondence is what
-- lands with their producer.

------------------------------------------------------------------------
-- Lifted to the FLAT machine. Control moves `fpc`/`halted` only; the
-- straight-line cases thread `exec-abstract`, which cannot reach the frame
-- fields — so each is `refl`. The frame-moving instructions and the closure
-- markers are `⊥`-elim (exactly what `FrameFreeI` excludes).
------------------------------------------------------------------------
flat-same-frames : ∀ (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
                 → FrameFreeI i
                 → SameFrames (flat-exec-instr i prog fs) fs
flat-same-frames (instr-ctrl (c-label m))               prog fs ff = mkSameFrames refl refl refl
flat-same-frames (instr-ctrl (c-thunk m b))             prog fs ()
flat-same-frames (instr-ctrl (c-ret b))                 prog fs ()
flat-same-frames (instr-ctrl (c-jmp m))                 prog fs ff = sf-jump (find-label prog m) fs
flat-same-frames (instr-ctrl (c-branch-scratch-zero m)) prog fs ff =
  sf-branch (sv-is-zero (readReg (regs (floc fs)) Scratch)) m prog fs
flat-same-frames (instr-ctrl (c-branch-tag-zero m))     prog fs ff =
  sf-branch (tag-zf (flat-read-tag (floc fs))) m prog fs
flat-same-frames (instr-alloc-stack n)   prog fs ()
flat-same-frames (instr-dealloc-stack n) prog fs ()
flat-same-frames (instr-push-frame cap)  prog fs ()
flat-same-frames instr-pop-frame         prog fs ()
flat-same-frames mov-to-output            prog fs ff = mkSameFrames refl refl refl
flat-same-frames mov-to-input             prog fs ff = mkSameFrames refl refl refl
flat-same-frames mov-output-to-input2     prog fs ff = mkSameFrames refl refl refl
flat-same-frames mov-input2-to-output     prog fs ff = mkSameFrames refl refl refl
flat-same-frames load-indirect            prog fs ff = mkSameFrames refl refl refl
flat-same-frames load-indirect-suc        prog fs ff = mkSameFrames refl refl refl
flat-same-frames (load-from-slot k)       prog fs ff =
  mkSameFrames (ss-mv       (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs) (falloc fs))
               (ss-mv-saved (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs) (falloc fs))
               refl
flat-same-frames (store-at-slot k)        prog fs ff = mkSameFrames refl refl refl
flat-same-frames store-indirect           prog fs ff = mkSameFrames refl refl refl
flat-same-frames store-indirect-suc       prog fs ff = mkSameFrames refl refl refl
flat-same-frames (lea-slot k)             prog fs ff = mkSameFrames refl refl refl
flat-same-frames (restore-input k)        prog fs ff =
  mkSameFrames (ss-mv-ri       (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs) (falloc fs))
               (ss-mv-ri-saved (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs) (falloc fs))
               refl
flat-same-frames (lea-indexed k)          prog fs ff = mkSameFrames refl refl refl
flat-same-frames (instr-reclaim-to k)     prog fs ff = mkSameFrames refl refl refl
-- D092: the call MOVES the frame stack (it pushes the caller's frame and the
-- return pc), so it left `FrameFreeI` — the route is absurd like the markers'.
flat-same-frames instr-call-closure       prog fs ()
flat-same-frames (worklist-init k)        prog fs ff = mkSameFrames refl refl refl
flat-same-frames (worklist-push k)        prog fs ff = mkSameFrames refl refl refl
flat-same-frames (worklist-pop k)         prog fs ff =
  mkSameFrames (ss-mv       (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs) (falloc fs))
               (ss-mv-saved (stackMem (floc fs) (current-frame (falloc fs)) k) (floc fs) (falloc fs))
               refl
flat-same-frames (worklist-check k)       prog fs ff = mkSameFrames refl refl refl
flat-same-frames (instr-sigop si)         prog fs ff = mkSameFrames refl refl refl
flat-same-frames (instr-load-const p v)   prog fs ff = mkSameFrames refl refl refl
flat-same-frames (instr-load-code-addr k) prog fs ff = mkSameFrames refl refl refl
flat-same-frames instr-save-closure-reg   prog fs ff = mkSameFrames refl refl refl
flat-same-frames (instr-load-tag-lit k)   prog fs ff = mkSameFrames refl refl refl
flat-same-frames (instr-case-on-tag f g)  prog fs ()
flat-same-frames (instr-alloc-heap k)     prog fs ff = mkSameFrames refl refl refl
flat-same-frames (instr-loop body)        prog fs ()
flat-same-frames (instr-reg-op op)        prog fs ff = mkSameFrames refl refl refl

-- (`flat-stack-slot`, the single-field projection, is GONE: `SegWF` carries the
-- whole frame stack now, so every consumer wants `flat-same-frames` itself.)
