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
    do-branch-at-left (tag-zf (flat-read-tag (floc fs))) (find-label prog n) fs
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
  flat-exec-instr-left (instr-reg-op op)        lf prog fs = exec-abstract-left (instr-reg-op op) lf (floc fs) (falloc fs)
