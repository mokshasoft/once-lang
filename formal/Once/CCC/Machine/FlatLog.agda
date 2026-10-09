-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatLog — plan 0.105: WHAT GROWS THE EVENT LOG.
--
-- The machine's log (`LocState.ev-log`) is the history the interpretation
-- answers a call against, so a fragment's obligation states how its run grew
-- the log (`IRObsCorrect.Interface`, `ValueRealized.log`). Only a SigOp step
-- appends to it (`exec-abstract (instr-sigop si)`); every other instruction
-- leaves it alone. This module says so once, per instruction, so the
-- obligation clauses cite it instead of normalising through each
-- instruction's helpers.
--
-- `LogFree` excludes the SigOp step (it has its own equation) and the two
-- retired nested instructions (`instr-case-on-tag`, `instr-loop`): they run a
-- nested trace that may itself call, and nothing emits them.
------------------------------------------------------------------------

module Once.CCC.Machine.FlatLog where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (true; false)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Machine.Flat

LogFree : AbstractInstr → Set
LogFree (instr-sigop _)         = ⊥
LogFree (instr-case-on-tag _ _) = ⊥
LogFree (instr-loop _)          = ⊥
{-# CATCHALL #-}
LogFree _                       = ⊤

module LogPres {FS : FrameSemantics} where
  open MemOps {FS}
  open ExecFinal {FS}
  open AbstractExec {FS}
  open FlatMachine {FS}

  private
    log : LocState FS → List _
    log = LocState.ev-log

  -- The helpers, each by its own cases (they dispatch on a read or a
  -- resolution, which a variable does not reduce).
  writeLoc-log : ∀ (s : LocState FS) loc v → log (writeLoc s loc v) ≡ log s
  writeLoc-log s (AtStack f k)  v                      = refl
  writeLoc-log s (AtDynamic hl) (SV-Ptr (AtStack _ _)) = refl
  writeLoc-log s (AtDynamic hl) (SV-Ptr (AtDynamic _)) = refl
  writeLoc-log s (AtDynamic hl) (SV-Tag _)             = refl
  writeLoc-log s (AtDynamic hl) (SV-Lit _ _)           = refl
  writeLoc-log s (AtDynamic hl) (SV-Code _)            = refl

  load-with-log : ∀ dst (mv : Maybe (StoredValue FS)) s → log (exec-load-with-value dst mv s) ≡ log s
  load-with-log dst (just v) s = refl
  load-with-log dst nothing  s = refl

  load-via-log : ∀ dst (ml : Maybe (ValueLocation FS)) s → log (exec-load-via-resolved dst ml s) ≡ log s
  load-via-log dst (just loc) s = load-with-log dst (readLoc s loc) s
  load-via-log dst nothing    s = refl

  load-suc-via-log : ∀ dst (ml : Maybe (ValueLocation FS)) s → log (exec-load-suc-via-resolved dst ml s) ≡ log s
  load-suc-via-log dst (just loc) s = load-with-log dst (readLoc s (sucLoc loc)) s
  load-suc-via-log dst nothing    s = refl

  store-via-log : ∀ (ml : Maybe (ValueLocation FS)) v s → log (exec-store-via-resolved ml v s) ≡ log s
  store-via-log (just loc) v s = writeLoc-log s loc v
  store-via-log nothing    v s = refl

  store-suc-via-log : ∀ (ml : Maybe (ValueLocation FS)) v s → log (exec-store-suc-via-resolved ml v s) ≡ log s
  store-suc-via-log (just loc) v s = writeLoc-log s (sucLoc loc) v
  store-suc-via-log nothing    v s = refl

  lea-indexed-log : ∀ (ml : Maybe (ValueLocation FS)) idx s → log (exec-lea-indexed-via ml idx s) ≡ log s
  lea-indexed-log (just loc) idx s = refl
  lea-indexed-log nothing    idx s = refl

  load-slot-log : ∀ (mv : Maybe (StoredValue FS)) s alloc → log (proj₁ (exec-load-from-slot-with-value mv s alloc)) ≡ log s
  load-slot-log (just v) s alloc = refl
  load-slot-log nothing  s alloc = refl

  restore-log : ∀ (mv : Maybe (StoredValue FS)) s alloc → log (proj₁ (exec-restore-input-with-value mv s alloc)) ≡ log s
  restore-log (just v) s alloc = refl
  restore-log nothing  s alloc = refl

  -- ONE STEP OF THE STRUCTURED MACHINE leaves the log alone, unless it calls.
  exec-abstract-log : ∀ (i : AbstractInstr) → LogFree i → ∀ s alloc
                    → log (proj₁ (exec-abstract i s alloc)) ≡ log s
  exec-abstract-log mov-to-output            _ s alloc = refl
  exec-abstract-log mov-to-input             _ s alloc = refl
  exec-abstract-log load-indirect            _ s alloc = load-via-log Output (sv-as-loc (readReg (regs s) Input1)) s
  exec-abstract-log load-indirect-suc        _ s alloc = load-suc-via-log Output (sv-as-loc (readReg (regs s) Input1)) s
  exec-abstract-log (load-from-slot slot)    _ s alloc = load-slot-log (readLoc s (AtStack (current-frame alloc) slot)) s alloc
  exec-abstract-log (store-at-slot slot)     _ s alloc = writeLoc-log s (AtStack (current-frame alloc) slot) (readReg (regs s) Output)
  exec-abstract-log store-indirect           _ s alloc = store-via-log (sv-as-loc (readReg (regs s) Input1)) (readReg (regs s) Output) s
  exec-abstract-log store-indirect-suc       _ s alloc = store-suc-via-log (sv-as-loc (readReg (regs s) Input1)) (readReg (regs s) Output) s
  exec-abstract-log (lea-slot slot)          _ s alloc = refl
  exec-abstract-log (restore-input slot)     _ s alloc = restore-log (readLoc s (AtStack (current-frame alloc) slot)) s alloc
  exec-abstract-log (lea-indexed slot)       _ s alloc =
    lea-indexed-log (slot-base (readLoc s (AtStack (current-frame alloc) slot))) (sv-tag-val (readReg (regs s) Scratch)) s
  exec-abstract-log (instr-alloc-stack n)    _ s alloc = refl
  exec-abstract-log (instr-dealloc-stack n)  _ s alloc = refl
  exec-abstract-log (instr-reclaim-to n)     _ s alloc = refl
  exec-abstract-log (instr-push-frame cap)   _ s alloc = refl
  exec-abstract-log instr-pop-frame          _ s alloc = refl
  exec-abstract-log instr-call-closure       _ s alloc = refl
  exec-abstract-log (worklist-init slot)     _ s alloc = refl
  exec-abstract-log (worklist-push slot)     _ s alloc = writeLoc-log s (AtStack (current-frame alloc) slot) (readReg (regs s) Output)
  exec-abstract-log (worklist-pop slot)      _ s alloc = load-slot-log (readLoc s (AtStack (current-frame alloc) slot)) s alloc
  exec-abstract-log (worklist-check slot)    _ s alloc = refl
  exec-abstract-log (instr-sigop si)         () s alloc
  exec-abstract-log (instr-load-const p v)   _ s alloc = refl
  exec-abstract-log (instr-load-code-addr n) _ s alloc = refl
  exec-abstract-log instr-save-closure-reg   _ s alloc = refl
  exec-abstract-log (instr-load-tag-lit n)   _ s alloc = refl
  exec-abstract-log (instr-case-on-tag f g)  () s alloc
  exec-abstract-log (instr-alloc-heap n)     _ s alloc = refl
  exec-abstract-log (instr-loop body)        () s alloc
  exec-abstract-log (instr-reg-op op)        _ s alloc = refl
  exec-abstract-log (instr-ctrl c)           _ s alloc = refl

  -- The control helpers of the flat machine, by their own cases.
  private
    flog : FlatState → List _
    flog fs = log (floc fs)

  do-jump-log : ∀ (mj : Maybe _) fs → flog (do-jump mj fs) ≡ flog fs
  do-jump-log (just pc') fs = refl
  do-jump-log nothing    fs = refl

  do-branch-at-log : ∀ b (mj : Maybe _) fs → flog (do-branch-at b mj fs) ≡ flog fs
  do-branch-at-log true  mj fs = do-jump-log mj fs
  do-branch-at-log false mj fs = refl

  do-ret-log : ∀ (rl : List _) fs → flog (do-ret rl fs) ≡ flog fs
  do-ret-log []         fs = refl
  do-ret-log (pc' ∷ rs) fs = refl

  do-call-at-log : ∀ (mj : Maybe _) fs → flog (do-call-at mj fs) ≡ flog fs
  do-call-at-log (just j) fs = refl
  do-call-at-log nothing  fs = refl

  do-call-code-log : ∀ prog (mv : Maybe (StoredValue FS)) fs → flog (do-call-code prog mv fs) ≡ flog fs
  do-call-code-log prog (just (SV-Code ℓ))  fs = do-call-at-log (find-thunk prog ℓ) fs
  do-call-code-log prog (just (SV-Tag _))   fs = refl
  do-call-code-log prog (just (SV-Lit _ _)) fs = refl
  do-call-code-log prog (just (SV-Ptr _))   fs = refl
  do-call-code-log prog nothing             fs = refl

  do-call-sv-log : ∀ prog (v : StoredValue FS) fs → flog (do-call-sv prog v fs) ≡ flog fs
  do-call-sv-log prog (SV-Ptr (AtDynamic hl)) fs = do-call-code-log prog (heapMem (floc fs) (sucHL hl)) fs
  do-call-sv-log prog (SV-Ptr (AtStack _ _))  fs = refl
  do-call-sv-log prog (SV-Tag _)              fs = refl
  do-call-sv-log prog (SV-Lit _ _)            fs = refl
  do-call-sv-log prog (SV-Code _)             fs = refl

  -- ONE STEP OF THE FLAT MACHINE leaves the log alone, unless it calls.
  flat-exec-instr-log : ∀ (i : AbstractInstr) → LogFree i → ∀ prog fs
                      → flog (flat-exec-instr i prog fs) ≡ flog fs
  flat-exec-instr-log (instr-ctrl (c-label _))               _ prog fs = refl
  flat-exec-instr-log (instr-ctrl (c-entry _ b))             _ prog fs = refl
  flat-exec-instr-log (instr-ctrl (c-start b))             _ prog fs = refl
  flat-exec-instr-log (instr-ctrl (c-call-fn f))             _ prog fs = do-call-at-log (find-fn prog f) fs
  flat-exec-instr-log (instr-ctrl (c-ret b))                 _ prog fs = do-ret-log (fret fs) fs
  flat-exec-instr-log (instr-ctrl (c-jmp n))                 _ prog fs = do-jump-log (find-label prog n) fs
  flat-exec-instr-log (instr-ctrl (c-branch-scratch-zero n)) _ prog fs =
    do-branch-at-log (sv-is-zero (readReg (regs (floc fs)) Scratch)) (find-label prog n) fs
  flat-exec-instr-log (instr-ctrl (c-branch-tag-zero n))     _ prog fs =
    do-branch-at-log (tag-zf (flat-read-tag (floc fs))) (find-label prog n) fs
  flat-exec-instr-log instr-call-closure                     _ prog fs = do-call-sv-log prog (fclosure fs) fs
  flat-exec-instr-log instr-save-closure-reg                 _ prog fs = refl
  flat-exec-instr-log (instr-alloc-stack n)   lf prog fs = exec-abstract-log (instr-alloc-stack n) lf (floc fs) (falloc fs)
  flat-exec-instr-log (instr-dealloc-stack n) lf prog fs = exec-abstract-log (instr-dealloc-stack n) lf (floc fs) (falloc fs)
  flat-exec-instr-log (instr-push-frame cap)  lf prog fs = exec-abstract-log (instr-push-frame cap) lf (floc fs) (falloc fs)
  flat-exec-instr-log instr-pop-frame         lf prog fs = exec-abstract-log instr-pop-frame lf (floc fs) (falloc fs)
  flat-exec-instr-log mov-to-output            lf prog fs = exec-abstract-log mov-to-output lf (floc fs) (falloc fs)
  flat-exec-instr-log mov-to-input             lf prog fs = exec-abstract-log mov-to-input lf (floc fs) (falloc fs)
  flat-exec-instr-log load-indirect            lf prog fs = exec-abstract-log load-indirect lf (floc fs) (falloc fs)
  flat-exec-instr-log load-indirect-suc        lf prog fs = exec-abstract-log load-indirect-suc lf (floc fs) (falloc fs)
  flat-exec-instr-log (load-from-slot slot)    lf prog fs = exec-abstract-log (load-from-slot slot) lf (floc fs) (falloc fs)
  flat-exec-instr-log (store-at-slot slot)     lf prog fs = exec-abstract-log (store-at-slot slot) lf (floc fs) (falloc fs)
  flat-exec-instr-log store-indirect           lf prog fs = exec-abstract-log store-indirect lf (floc fs) (falloc fs)
  flat-exec-instr-log store-indirect-suc       lf prog fs = exec-abstract-log store-indirect-suc lf (floc fs) (falloc fs)
  flat-exec-instr-log (lea-slot slot)          lf prog fs = exec-abstract-log (lea-slot slot) lf (floc fs) (falloc fs)
  flat-exec-instr-log (restore-input slot)     lf prog fs = exec-abstract-log (restore-input slot) lf (floc fs) (falloc fs)
  flat-exec-instr-log (lea-indexed slot)       lf prog fs = exec-abstract-log (lea-indexed slot) lf (floc fs) (falloc fs)
  flat-exec-instr-log (instr-reclaim-to n)     lf prog fs = exec-abstract-log (instr-reclaim-to n) lf (floc fs) (falloc fs)
  flat-exec-instr-log (worklist-init slot)     lf prog fs = exec-abstract-log (worklist-init slot) lf (floc fs) (falloc fs)
  flat-exec-instr-log (worklist-push slot)     lf prog fs = exec-abstract-log (worklist-push slot) lf (floc fs) (falloc fs)
  flat-exec-instr-log (worklist-pop slot)      lf prog fs = exec-abstract-log (worklist-pop slot) lf (floc fs) (falloc fs)
  flat-exec-instr-log (worklist-check slot)    lf prog fs = exec-abstract-log (worklist-check slot) lf (floc fs) (falloc fs)
  flat-exec-instr-log (instr-sigop si)         () prog fs
  flat-exec-instr-log (instr-load-const p v)   lf prog fs = exec-abstract-log (instr-load-const p v) lf (floc fs) (falloc fs)
  flat-exec-instr-log (instr-load-code-addr n) lf prog fs = exec-abstract-log (instr-load-code-addr n) lf (floc fs) (falloc fs)
  flat-exec-instr-log (instr-load-tag-lit n)   lf prog fs = exec-abstract-log (instr-load-tag-lit n) lf (floc fs) (falloc fs)
  flat-exec-instr-log (instr-case-on-tag f g)  () prog fs
  flat-exec-instr-log (instr-alloc-heap n)     lf prog fs = exec-abstract-log (instr-alloc-heap n) lf (floc fs) (falloc fs)
  flat-exec-instr-log (instr-loop body)        () prog fs
  flat-exec-instr-log (instr-reg-op op)        lf prog fs = exec-abstract-log (instr-reg-op op) lf (floc fs) (falloc fs)
