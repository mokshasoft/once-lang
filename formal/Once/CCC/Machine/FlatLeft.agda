-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatLeft — D320: ONLY `c-leave` LEAVES.
--
-- The machine's `left` flag says the run ended by the Host's `leave`; the run
-- observes it when it halts (`FlatEvents`). Only `c-leave` sets it; every
-- other step leaves it alone — the SigOp step included (it updates the
-- registers, the halt flag and the log). This module says so once, per
-- instruction, as `FlatLog` does for the log.
--
-- `LeftFree` excludes `c-leave` alone: the structured machine never sets the
-- flag (its control instructions are the identity there), so even the two
-- retired nested instructions, which run a nested trace, leave it alone.
------------------------------------------------------------------------

module Once.CCC.Machine.FlatLeft where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Once.Type using (fits-int; fits-float)
open import Data.Product using (proj₁; proj₂)
open import Data.Nat using (zero; suc)
import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open AllocState using (current-frame)
open LocState using (regs; heapMem; halted)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Machine.Flat

LeftFree : AbstractInstr → Set
LeftFree (instr-ctrl c-leave)    = ⊥
{-# CATCHALL #-}
LeftFree _                       = ⊤

module LeftPres {FS : FrameSemantics} where
  open MemOps {FS}
  open ExecFinal {FS}
  open AbstractExec {FS}
  open FlatMachine {FS}

  private
    lft : LocState FS → Bool
    lft = LocState.left

  -- The helpers, each by its own cases (they dispatch on a read or a
  -- resolution, which a variable does not reduce).
  writeLoc-left : ∀ (s : LocState FS) loc v → lft (writeLoc s loc v) ≡ lft s
  writeLoc-left s (AtStack f k)  v                      = refl
  writeLoc-left s (AtDynamic hl) (SV-Ptr (AtStack _ _)) = refl
  writeLoc-left s (AtDynamic hl) (SV-Ptr (AtDynamic _)) = refl
  writeLoc-left s (AtDynamic hl) (SV-Tag _)             = refl
  writeLoc-left s (AtDynamic hl) (SV-Lit _ _)           = refl
  writeLoc-left s (AtDynamic hl) (SV-Code _)            = refl

  load-with-left : ∀ dst (mv : Maybe (StoredValue FS)) s → lft (exec-load-with-value dst mv s) ≡ lft s
  load-with-left dst (just v) s = refl
  load-with-left dst nothing  s = refl

  load-via-left : ∀ dst (ml : Maybe (ValueLocation FS)) s → lft (exec-load-via-resolved dst ml s) ≡ lft s
  load-via-left dst (just loc) s = load-with-left dst (readLoc s loc) s
  load-via-left dst nothing    s = refl

  load-suc-via-left : ∀ dst (ml : Maybe (ValueLocation FS)) s → lft (exec-load-suc-via-resolved dst ml s) ≡ lft s
  load-suc-via-left dst (just loc) s = load-with-left dst (readLoc s (sucLoc loc)) s
  load-suc-via-left dst nothing    s = refl

  store-via-left : ∀ (ml : Maybe (ValueLocation FS)) v s → lft (exec-store-via-resolved ml v s) ≡ lft s
  store-via-left (just loc) v s = writeLoc-left s loc v
  store-via-left nothing    v s = refl

  store-suc-via-left : ∀ (ml : Maybe (ValueLocation FS)) v s → lft (exec-store-suc-via-resolved ml v s) ≡ lft s
  store-suc-via-left (just loc) v s = writeLoc-left s (sucLoc loc) v
  store-suc-via-left nothing    v s = refl


  load-slot-left : ∀ (mv : Maybe (StoredValue FS)) s alloc → lft (proj₁ (exec-load-from-slot-with-value mv s alloc)) ≡ lft s
  load-slot-left (just v) s alloc = refl
  load-slot-left nothing  s alloc = refl

  restore-left : ∀ (mv : Maybe (StoredValue FS)) s alloc → lft (proj₁ (exec-restore-input-with-value mv s alloc)) ≡ lft s
  restore-left (just v) s alloc = refl
  restore-left nothing  s alloc = refl

  -- THE LOOP leaves it alone if its body does (a fuel induction).

  -- ONE STEP OF THE STRUCTURED MACHINE leaves the flag alone — every step.
  abs-left   : ∀ (i : AbstractInstr) (s : LocState FS) alloc → lft (proj₁ (exec-abstract i s alloc)) ≡ lft s
  trace-left : ∀ (t : AbstractTrace) (s : LocState FS) alloc → lft (proj₁ (exec-trace t s alloc)) ≡ lft s
  trace-left []       s alloc = refl
  trace-left (i ∷ is) s alloc with halted s
  ... | true  = refl
  ... | false = trans (trace-left is (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc))) (abs-left i s alloc)
  abs-left mov-to-output s alloc = refl
  abs-left mov-to-input s alloc = refl
  abs-left load-indirect s alloc = load-via-left Output (sv-as-loc (readReg (regs s) Input1)) s
  abs-left load-indirect-suc s alloc = load-suc-via-left Output (sv-as-loc (readReg (regs s) Input1)) s
  abs-left (load-from-slot slot) s alloc = load-slot-left (readLoc s (AtStack (current-frame alloc) slot)) s alloc
  abs-left (store-at-slot slot) s alloc = writeLoc-left s (AtStack (current-frame alloc) slot) (readReg (regs s) Output)
  abs-left store-indirect s alloc = store-via-left (sv-as-loc (readReg (regs s) Input1)) (readReg (regs s) Output) s
  abs-left store-indirect-suc s alloc = store-suc-via-left (sv-as-loc (readReg (regs s) Input1)) (readReg (regs s) Output) s
  abs-left (lea-slot slot) s alloc = refl
  abs-left (restore-input slot) s alloc = restore-left (readLoc s (AtStack (current-frame alloc) slot)) s alloc
  abs-left (instr-alloc-stack n) s alloc = refl
  abs-left (instr-dealloc-stack n) s alloc = refl
  abs-left (instr-reclaim-to n) s alloc = refl
  abs-left (instr-push-frame cap) s alloc = refl
  abs-left instr-pop-frame s alloc = refl
  abs-left instr-call-closure s alloc = refl
  abs-left (worklist-init slot) s alloc = refl
  abs-left (worklist-push slot) s alloc = writeLoc-left s (AtStack (current-frame alloc) slot) (readReg (regs s) Output)
  abs-left (worklist-pop slot) s alloc = load-slot-left (readLoc s (AtStack (current-frame alloc) slot)) s alloc
  abs-left (worklist-check slot) s alloc = refl
  abs-left (instr-sigop si) s alloc = refl
  abs-left (instr-load-const p v) s alloc = refl
  abs-left (instr-load-code-addr n) s alloc = refl
  abs-left instr-save-closure-reg s alloc = refl
  abs-left (instr-load-tag-lit n) s alloc = refl
  abs-left (instr-alloc-heap n) s alloc = refl
  abs-left (instr-reg-op op) s alloc = refl
  abs-left (instr-free-heap n) s alloc = refl
  abs-left (instr-room n) s alloc = refl
  abs-left (instr-ctrl c) s alloc = refl

  exec-abstract-left : ∀ (i : AbstractInstr) → LeftFree i → ∀ s alloc → lft (proj₁ (exec-abstract i s alloc)) ≡ lft s
  exec-abstract-left i _ = abs-left i

  -- The control helpers of the flat machine, by their own cases.
  private
    flft : FlatState → Bool
    flft fs = lft (floc fs)

  do-jump-left : ∀ (mj : Maybe _) fs → flft (do-jump mj fs) ≡ flft fs
  do-jump-left (just pc') fs = refl
  do-jump-left nothing    fs = refl

  do-branch-at-left : ∀ b (mj : Maybe _) fs → flft (do-branch-at b mj fs) ≡ flft fs
  do-branch-at-left true  mj fs = do-jump-left mj fs
  do-branch-at-left false mj fs = refl

  -- D367: the guarded tag branch and `out-nz`
  do-test-left : ∀ (mb : Maybe Bool) n prog fs → flft (do-branch-test mb n prog fs) ≡ flft fs
  do-test-left (just b) n prog fs = do-branch-at-left b (find-label prog n) fs
  do-test-left nothing  n prog fs = refl

  do-nz-left : ∀ (v : StoredValue FS) fs → flft (do-nz v fs) ≡ flft fs
  do-nz-left (SV-Lit fits-int _)   fs = refl
  do-nz-left (SV-Lit fits-float _) fs = refl
  do-nz-left (SV-Tag _)            fs = refl
  do-nz-left (SV-Ptr _)            fs = refl
  do-nz-left (SV-Code _)           fs = refl

  do-ret-left : ∀ (rl : List _) fs → flft (do-ret rl fs) ≡ flft fs
  do-ret-left []         fs = refl
  do-ret-left (pc' ∷ rs) fs = refl

  do-call-at-left : ∀ (mj : Maybe _) fs → flft (do-call-at mj fs) ≡ flft fs
  do-call-at-left (just j) fs = refl
  do-call-at-left nothing  fs = refl

  do-call-code-left : ∀ prog (mv : Maybe (StoredValue FS)) fs → flft (do-call-code prog mv fs) ≡ flft fs
  do-call-code-left prog (just (SV-Code ℓ))  fs = do-call-at-left (find-thunk prog ℓ) fs
  do-call-code-left prog (just (SV-Tag _))   fs = refl
  do-call-code-left prog (just (SV-Lit _ _)) fs = refl
  do-call-code-left prog (just (SV-Ptr _))   fs = refl
  do-call-code-left prog nothing             fs = refl

  do-call-sv-left : ∀ prog (v : StoredValue FS) fs → flft (do-call-sv prog v fs) ≡ flft fs
  do-call-sv-left prog (SV-Ptr (AtDynamic hl)) fs = do-call-code-left prog (heapMem (floc fs) (sucHL hl)) fs
  do-call-sv-left prog (SV-Ptr (AtStack _ _))  fs = refl
  do-call-sv-left prog (SV-Tag _)              fs = refl
  do-call-sv-left prog (SV-Lit _ _)            fs = refl
  do-call-sv-left prog (SV-Code _)             fs = refl

  -- ONE STEP OF THE FLAT MACHINE leaves the lft alone, unless it calls.
  flat-exec-instr-left : ∀ (i : AbstractInstr) → LeftFree i → ∀ prog fs
                      → flft (flat-exec-instr i prog fs) ≡ flft fs
  flat-exec-instr-left (instr-ctrl (c-label _))               _ prog fs = refl
  flat-exec-instr-left (instr-ctrl (c-entry _ b))             _ prog fs = refl
  flat-exec-instr-left (instr-ctrl (c-start b))             _ prog fs = refl
  flat-exec-instr-left (instr-ctrl c-leave)                   () prog fs
  flat-exec-instr-left (instr-ctrl (c-call-fn f))             _ prog fs = do-call-at-left (find-fn prog f) fs
  flat-exec-instr-left (instr-ctrl (c-ret b))                 _ prog fs = do-ret-left (fret fs) fs
  flat-exec-instr-left (instr-ctrl (c-jmp n))                 _ prog fs = do-jump-left (find-label prog n) fs
  flat-exec-instr-left (instr-ctrl (c-branch-tag-zero n))     _ prog fs =
    do-test-left (tag-test (flat-read-tag (floc fs))) n prog fs
  flat-exec-instr-left instr-call-closure                     _ prog fs = do-call-sv-left prog (fclosure fs) fs
  flat-exec-instr-left instr-save-closure-reg                 _ prog fs = refl
  flat-exec-instr-left (instr-alloc-stack n)   lf prog fs = exec-abstract-left (instr-alloc-stack n) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-dealloc-stack n) lf prog fs = exec-abstract-left (instr-dealloc-stack n) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-push-frame cap)  lf prog fs = exec-abstract-left (instr-push-frame cap) lf (floc fs) (falloc fs)
  flat-exec-instr-left instr-pop-frame         lf prog fs = exec-abstract-left instr-pop-frame lf (floc fs) (falloc fs)
  flat-exec-instr-left mov-to-output            lf prog fs = exec-abstract-left mov-to-output lf (floc fs) (falloc fs)
  flat-exec-instr-left mov-to-input             lf prog fs = exec-abstract-left mov-to-input lf (floc fs) (falloc fs)
  flat-exec-instr-left load-indirect            lf prog fs = exec-abstract-left load-indirect lf (floc fs) (falloc fs)
  flat-exec-instr-left load-indirect-suc        lf prog fs = exec-abstract-left load-indirect-suc lf (floc fs) (falloc fs)
  flat-exec-instr-left (load-from-slot slot)    lf prog fs = exec-abstract-left (load-from-slot slot) lf (floc fs) (falloc fs)
  flat-exec-instr-left (store-at-slot slot)     lf prog fs = exec-abstract-left (store-at-slot slot) lf (floc fs) (falloc fs)
  flat-exec-instr-left store-indirect           lf prog fs = exec-abstract-left store-indirect lf (floc fs) (falloc fs)
  flat-exec-instr-left store-indirect-suc       lf prog fs = exec-abstract-left store-indirect-suc lf (floc fs) (falloc fs)
  flat-exec-instr-left (lea-slot slot)          lf prog fs = exec-abstract-left (lea-slot slot) lf (floc fs) (falloc fs)
  flat-exec-instr-left (restore-input slot)     lf prog fs = exec-abstract-left (restore-input slot) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-reclaim-to n)     lf prog fs = exec-abstract-left (instr-reclaim-to n) lf (floc fs) (falloc fs)
  flat-exec-instr-left (worklist-init slot)     lf prog fs = exec-abstract-left (worklist-init slot) lf (floc fs) (falloc fs)
  flat-exec-instr-left (worklist-push slot)     lf prog fs = exec-abstract-left (worklist-push slot) lf (floc fs) (falloc fs)
  flat-exec-instr-left (worklist-pop slot)      lf prog fs = exec-abstract-left (worklist-pop slot) lf (floc fs) (falloc fs)
  flat-exec-instr-left (worklist-check slot)    lf prog fs = exec-abstract-left (worklist-check slot) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-sigop si)         lf prog fs = exec-abstract-left (instr-sigop si) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-load-const p v)   lf prog fs = exec-abstract-left (instr-load-const p v) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-load-code-addr n) lf prog fs = exec-abstract-left (instr-load-code-addr n) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-load-tag-lit n)   lf prog fs = exec-abstract-left (instr-load-tag-lit n) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-alloc-heap n)     lf prog fs = exec-abstract-left (instr-alloc-heap n) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-reg-op out-nz)    lf prog fs = do-nz-left (readReg (regs (floc fs)) Output) fs
  flat-exec-instr-left (instr-free-heap n)      lf prog fs = exec-abstract-left (instr-free-heap n) lf (floc fs) (falloc fs)
  flat-exec-instr-left (instr-room n)           lf prog fs = exec-abstract-left (instr-room n) lf (floc fs) (falloc fs)

------------------------------------------------------------------------
-- D367: …AND A STEP THAT DOES NOT HALT DOES NOT FAULT. A fault sets `halted`
-- with `faulted` (`LocState.faulted`), so a step whose result is still running
-- leaves the flag as it found it — the twin of `flat-exec-instr-left`, with the
-- running result as the premise in place of `LeftFree` (every faulting arm is
-- a halting one, so its premise is `true ≡ false`).
------------------------------------------------------------------------
module FaultPres {FS : FrameSemantics} where
  open MemOps {FS}
  open ExecFinal {FS}
  open AbstractExec {FS}
  open FlatMachine {FS}

  private
    flt : LocState FS → Bool
    flt = LocState.faulted
    hlt : LocState FS → Bool
    hlt = LocState.halted

  writeLoc-fault : ∀ (s : LocState FS) loc v → flt (writeLoc s loc v) ≡ flt s
  writeLoc-fault s (AtStack f k)  v                      = refl
  writeLoc-fault s (AtDynamic hl) (SV-Ptr (AtStack _ _)) = refl
  writeLoc-fault s (AtDynamic hl) (SV-Ptr (AtDynamic _)) = refl
  writeLoc-fault s (AtDynamic hl) (SV-Tag _)             = refl
  writeLoc-fault s (AtDynamic hl) (SV-Lit _ _)           = refl
  writeLoc-fault s (AtDynamic hl) (SV-Code _)            = refl

  load-with-fault : ∀ dst (mv : Maybe (StoredValue FS)) s → hlt (exec-load-with-value dst mv s) ≡ false
                  → flt (exec-load-with-value dst mv s) ≡ flt s
  load-with-fault dst (just v) s _ = refl
  load-with-fault dst nothing  s ()

  load-via-fault : ∀ dst (ml : Maybe (ValueLocation FS)) s → hlt (exec-load-via-resolved dst ml s) ≡ false
                 → flt (exec-load-via-resolved dst ml s) ≡ flt s
  load-via-fault dst (just loc) s h = load-with-fault dst (readLoc s loc) s h
  load-via-fault dst nothing    s ()

  load-suc-via-fault : ∀ dst (ml : Maybe (ValueLocation FS)) s → hlt (exec-load-suc-via-resolved dst ml s) ≡ false
                     → flt (exec-load-suc-via-resolved dst ml s) ≡ flt s
  load-suc-via-fault dst (just loc) s h = load-with-fault dst (readLoc s (sucLoc loc)) s h
  load-suc-via-fault dst nothing    s ()

  store-via-fault : ∀ (ml : Maybe (ValueLocation FS)) v s → hlt (exec-store-via-resolved ml v s) ≡ false
                  → flt (exec-store-via-resolved ml v s) ≡ flt s
  store-via-fault (just loc) v s _ = writeLoc-fault s loc v
  store-via-fault nothing    v s ()

  store-suc-via-fault : ∀ (ml : Maybe (ValueLocation FS)) v s → hlt (exec-store-suc-via-resolved ml v s) ≡ false
                      → flt (exec-store-suc-via-resolved ml v s) ≡ flt s
  store-suc-via-fault (just loc) v s _ = writeLoc-fault s (sucLoc loc) v
  store-suc-via-fault nothing    v s ()

  load-slot-fault : ∀ (mv : Maybe (StoredValue FS)) s alloc → hlt (proj₁ (exec-load-from-slot-with-value mv s alloc)) ≡ false
                  → flt (proj₁ (exec-load-from-slot-with-value mv s alloc)) ≡ flt s
  load-slot-fault (just v) s alloc _ = refl
  load-slot-fault nothing  s alloc ()

  restore-fault : ∀ (mv : Maybe (StoredValue FS)) s alloc → hlt (proj₁ (exec-restore-input-with-value mv s alloc)) ≡ false
                → flt (proj₁ (exec-restore-input-with-value mv s alloc)) ≡ flt s
  restore-fault (just v) s alloc _ = refl
  restore-fault nothing  s alloc ()

  abs-fault : ∀ (i : AbstractInstr) (s : LocState FS) alloc → hlt (proj₁ (exec-abstract i s alloc)) ≡ false
            → flt (proj₁ (exec-abstract i s alloc)) ≡ flt s
  abs-fault mov-to-output s alloc _ = refl
  abs-fault mov-to-input s alloc _ = refl
  abs-fault load-indirect s alloc h = load-via-fault Output (sv-as-loc (readReg (regs s) Input1)) s h
  abs-fault load-indirect-suc s alloc h = load-suc-via-fault Output (sv-as-loc (readReg (regs s) Input1)) s h
  abs-fault (load-from-slot slot) s alloc h = load-slot-fault (readLoc s (AtStack (current-frame alloc) slot)) s alloc h
  abs-fault (store-at-slot slot) s alloc _ = writeLoc-fault s (AtStack (current-frame alloc) slot) (readReg (regs s) Output)
  abs-fault store-indirect s alloc h = store-via-fault (sv-as-loc (readReg (regs s) Input1)) (readReg (regs s) Output) s h
  abs-fault store-indirect-suc s alloc h = store-suc-via-fault (sv-as-loc (readReg (regs s) Input1)) (readReg (regs s) Output) s h
  abs-fault (lea-slot slot) s alloc _ = refl
  abs-fault (restore-input slot) s alloc h = restore-fault (readLoc s (AtStack (current-frame alloc) slot)) s alloc h
  abs-fault (instr-alloc-stack n) s alloc _ = refl
  abs-fault (instr-dealloc-stack n) s alloc _ = refl
  abs-fault (instr-reclaim-to n) s alloc _ = refl
  abs-fault (instr-push-frame cap) s alloc _ = refl
  abs-fault instr-pop-frame s alloc _ = refl
  abs-fault instr-call-closure s alloc _ = refl
  abs-fault (worklist-init slot) s alloc _ = refl
  abs-fault (worklist-push slot) s alloc _ = writeLoc-fault s (AtStack (current-frame alloc) slot) (readReg (regs s) Output)
  abs-fault (worklist-pop slot) s alloc h = load-slot-fault (readLoc s (AtStack (current-frame alloc) slot)) s alloc h
  abs-fault (worklist-check slot) s alloc _ = refl
  abs-fault (instr-sigop si) s alloc _ = refl
  abs-fault (instr-load-const p v) s alloc _ = refl
  abs-fault (instr-load-code-addr n) s alloc _ = refl
  abs-fault instr-save-closure-reg s alloc _ = refl
  abs-fault (instr-load-tag-lit n) s alloc _ = refl
  abs-fault (instr-alloc-heap n) s alloc _ = refl
  abs-fault (instr-free-heap n) s alloc _ = refl
  abs-fault (instr-room n) s alloc _ = refl
  abs-fault (instr-reg-op op) s alloc _ = refl
  abs-fault (instr-ctrl c) s alloc _ = refl

  private
    fflt : FlatState → Bool
    fflt fs = flt (floc fs)
    fhlt : FlatState → Bool
    fhlt fs = hlt (floc fs)

  do-jump-fault : ∀ (mj : Maybe _) fs → fflt (do-jump mj fs) ≡ fflt fs
  do-jump-fault (just pc') fs = refl
  do-jump-fault nothing    fs = refl

  do-branch-at-fault : ∀ b (mj : Maybe _) fs → fflt (do-branch-at b mj fs) ≡ fflt fs
  do-branch-at-fault true  mj fs = do-jump-fault mj fs
  do-branch-at-fault false mj fs = refl

  do-test-fault : ∀ (mb : Maybe Bool) n prog fs → fhlt (do-branch-test mb n prog fs) ≡ false
                → fflt (do-branch-test mb n prog fs) ≡ fflt fs
  do-test-fault (just b) n prog fs _ = do-branch-at-fault b (find-label prog n) fs
  do-test-fault nothing  n prog fs ()

  do-nz-fault : ∀ (v : StoredValue FS) fs → fhlt (do-nz v fs) ≡ false → fflt (do-nz v fs) ≡ fflt fs
  do-nz-fault (SV-Lit fits-int _)   fs _ = refl
  do-nz-fault (SV-Lit fits-float _) fs ()
  do-nz-fault (SV-Tag _)            fs ()
  do-nz-fault (SV-Ptr _)            fs ()
  do-nz-fault (SV-Code _)           fs ()

  do-ret-fault : ∀ (rl : List _) fs → fflt (do-ret rl fs) ≡ fflt fs
  do-ret-fault []         fs = refl
  do-ret-fault (pc' ∷ rs) fs = refl

  do-call-at-fault : ∀ (mj : Maybe _) fs → fflt (do-call-at mj fs) ≡ fflt fs
  do-call-at-fault (just j) fs = refl
  do-call-at-fault nothing  fs = refl

  do-call-code-fault : ∀ prog (mv : Maybe (StoredValue FS)) fs → fflt (do-call-code prog mv fs) ≡ fflt fs
  do-call-code-fault prog (just (SV-Code ℓ))  fs = do-call-at-fault (find-thunk prog ℓ) fs
  do-call-code-fault prog (just (SV-Tag _))   fs = refl
  do-call-code-fault prog (just (SV-Lit _ _)) fs = refl
  do-call-code-fault prog (just (SV-Ptr _))   fs = refl
  do-call-code-fault prog nothing             fs = refl

  do-call-sv-fault : ∀ prog (v : StoredValue FS) fs → fflt (do-call-sv prog v fs) ≡ fflt fs
  do-call-sv-fault prog (SV-Ptr (AtDynamic hl)) fs = do-call-code-fault prog (heapMem (floc fs) (sucHL hl)) fs
  do-call-sv-fault prog (SV-Ptr (AtStack _ _))  fs = refl
  do-call-sv-fault prog (SV-Tag _)              fs = refl
  do-call-sv-fault prog (SV-Lit _ _)            fs = refl
  do-call-sv-fault prog (SV-Code _)             fs = refl

  flat-exec-instr-fault : ∀ (i : AbstractInstr) prog fs → fhlt (flat-exec-instr i prog fs) ≡ false
                        → fflt (flat-exec-instr i prog fs) ≡ fflt fs
  flat-exec-instr-fault (instr-ctrl (c-label _))           prog fs _ = refl
  flat-exec-instr-fault (instr-ctrl (c-entry _ b))         prog fs _ = refl
  flat-exec-instr-fault (instr-ctrl (c-start b))           prog fs _ = refl
  flat-exec-instr-fault (instr-ctrl c-leave)               prog fs _ = refl
  flat-exec-instr-fault (instr-ctrl (c-call-fn f))         prog fs _ = do-call-at-fault (find-fn prog f) fs
  flat-exec-instr-fault (instr-ctrl (c-ret b))             prog fs _ = do-ret-fault (fret fs) fs
  flat-exec-instr-fault (instr-ctrl (c-jmp n))             prog fs _ = do-jump-fault (find-label prog n) fs
  flat-exec-instr-fault (instr-ctrl (c-branch-tag-zero n)) prog fs h =
    do-test-fault (tag-test (flat-read-tag (floc fs))) n prog fs h
  flat-exec-instr-fault instr-call-closure                 prog fs _ = do-call-sv-fault prog (fclosure fs) fs
  flat-exec-instr-fault instr-save-closure-reg             prog fs _ = refl
  flat-exec-instr-fault (instr-alloc-stack n)   prog fs h = abs-fault (instr-alloc-stack n) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-dealloc-stack n) prog fs h = abs-fault (instr-dealloc-stack n) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-push-frame cap)  prog fs h = abs-fault (instr-push-frame cap) (floc fs) (falloc fs) h
  flat-exec-instr-fault instr-pop-frame         prog fs h = abs-fault instr-pop-frame (floc fs) (falloc fs) h
  flat-exec-instr-fault mov-to-output            prog fs h = abs-fault mov-to-output (floc fs) (falloc fs) h
  flat-exec-instr-fault mov-to-input             prog fs h = abs-fault mov-to-input (floc fs) (falloc fs) h
  flat-exec-instr-fault load-indirect            prog fs h = abs-fault load-indirect (floc fs) (falloc fs) h
  flat-exec-instr-fault load-indirect-suc        prog fs h = abs-fault load-indirect-suc (floc fs) (falloc fs) h
  flat-exec-instr-fault (load-from-slot slot)    prog fs h = abs-fault (load-from-slot slot) (floc fs) (falloc fs) h
  flat-exec-instr-fault (store-at-slot slot)     prog fs h = abs-fault (store-at-slot slot) (floc fs) (falloc fs) h
  flat-exec-instr-fault store-indirect           prog fs h = abs-fault store-indirect (floc fs) (falloc fs) h
  flat-exec-instr-fault store-indirect-suc       prog fs h = abs-fault store-indirect-suc (floc fs) (falloc fs) h
  flat-exec-instr-fault (lea-slot slot)          prog fs h = abs-fault (lea-slot slot) (floc fs) (falloc fs) h
  flat-exec-instr-fault (restore-input slot)     prog fs h = abs-fault (restore-input slot) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-reclaim-to n)     prog fs h = abs-fault (instr-reclaim-to n) (floc fs) (falloc fs) h
  flat-exec-instr-fault (worklist-init slot)     prog fs h = abs-fault (worklist-init slot) (floc fs) (falloc fs) h
  flat-exec-instr-fault (worklist-push slot)     prog fs h = abs-fault (worklist-push slot) (floc fs) (falloc fs) h
  flat-exec-instr-fault (worklist-pop slot)      prog fs h = abs-fault (worklist-pop slot) (floc fs) (falloc fs) h
  flat-exec-instr-fault (worklist-check slot)    prog fs h = abs-fault (worklist-check slot) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-sigop si)         prog fs h = abs-fault (instr-sigop si) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-load-const p v)   prog fs h = abs-fault (instr-load-const p v) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-load-code-addr n) prog fs h = abs-fault (instr-load-code-addr n) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-load-tag-lit n)   prog fs h = abs-fault (instr-load-tag-lit n) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-alloc-heap n)     prog fs h = abs-fault (instr-alloc-heap n) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-reg-op out-nz)    prog fs h = do-nz-fault (readReg (regs (floc fs)) Output) fs h
  flat-exec-instr-fault (instr-free-heap n)      prog fs h = abs-fault (instr-free-heap n) (floc fs) (falloc fs) h
  flat-exec-instr-fault (instr-room n)           prog fs h = abs-fault (instr-room n) (floc fs) (falloc fs) h
