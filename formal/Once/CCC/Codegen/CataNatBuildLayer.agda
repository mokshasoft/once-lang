-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatBuildLayer — the ASCEND phase's `build-layer`
-- block runs as a FlatSteps chain (Plan 0.36 task #8, allocator
-- reasoning).
--
-- `build-layer tag` (cata-trace-nat) constructs a heap layer node:
--   mov-to-output ∷ store-at-slot pstash ∷ instr-alloc-heap 2 ∷
--   store-at-slot sstash ∷ mov-to-input ∷ instr-load-tag-lit tag ∷
--   store-indirect ∷ load-from-slot pstash ∷ store-indirect-suc ∷
--   load-from-slot sstash ∷ []
-- It is SELF-CONTAINED: its own `alloc` provides the pointer the later
-- store-indirects need, and its own stashes populate the slots the loads
-- read. This module proves it runs without halting.
--
-- First piece: the PREFIX (steps 1–5 — mov / stash / alloc / stash / mov)
-- is unconditionally non-halting (reg moves, `writeLoc` stores, alloc),
-- so it is a clean 5-step chain. The suffix (the load/store-indirect
-- steps with self-generated halt conditions) follows.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatBuildLayer where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Allocation using (current-frame)
open import Once.CCC.Machine.SMCore
  using (halted; regs; readReg; Output; Input1; AtStack; AtDynamic; AbstractTrace;
         sv-as-loc; sucLoc; ValueLocation; StoredValue; Registers; LocState; HeapLocation;
         SV-Tag; SV-Ptr; writeReg-preserves;
         mov-to-output; mov-to-input; store-at-slot; instr-alloc-heap;
         instr-load-tag-lit; store-indirect; store-indirect-suc; load-from-slot;
         module MemOps)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module CataNatBuildLayer {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}
  open MemOps {FS} using (writeLoc-halted; readLoc; writeLoc-preserves-other; writeLoc-regs)

  -- A regs-only update preserves every memory read (`readLoc` reads
  -- stackMem/heapMem, never regs).
  readLoc-regs-irrelevant : ∀ (s : LocState FS) (rs : Registers FS) (loc : ValueLocation FS)
    → readLoc (record s { regs = rs }) loc ≡ readLoc s loc
  readLoc-regs-irrelevant s rs (AtStack f k)  = refl
  readLoc-regs-irrelevant s rs (AtDynamic hl) = refl

  -- store-indirect preserves halted given Input1 is a pointer.
  store-indirect-keeps-halted : ∀ (prog : AbstractTrace) (fs : FlatState) (loc : ValueLocation FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → halted (floc (flat-exec-instr store-indirect prog fs)) ≡ halted (floc fs)
  store-indirect-keeps-halted prog fs loc ptr rewrite ptr =
    writeLoc-halted (floc fs) loc (readReg (regs (floc fs)) Output)

  -- store-indirect-suc preserves halted given Input1 is a pointer.
  store-indirect-suc-keeps-halted : ∀ (prog : AbstractTrace) (fs : FlatState) (loc : ValueLocation FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → halted (floc (flat-exec-instr store-indirect-suc prog fs)) ≡ halted (floc fs)
  store-indirect-suc-keeps-halted prog fs loc ptr rewrite ptr =
    writeLoc-halted (floc fs) (sucLoc loc) (readReg (regs (floc fs)) Output)

  -- load-from-slot preserves halted given the slot is populated.
  load-from-slot-keeps-halted : ∀ (prog : AbstractTrace) (fs : FlatState) (slot : ℕ) (v : StoredValue FS)
    → readLoc (floc fs) (AtStack (current-frame (falloc fs)) slot) ≡ just v
    → halted (floc (flat-exec-instr (load-from-slot slot) prog fs)) ≡ halted (floc fs)
  load-from-slot-keeps-halted prog fs slot v slotfull rewrite slotfull = refl

  -- `store-at-slot` preserves `halted` (it `writeLoc`s a stack slot).
  store-at-slot-keeps-halted : ∀ (prog : AbstractTrace) (fs : FlatState) (slot : ℕ)
    → halted (floc (flat-exec-instr (store-at-slot slot) prog fs)) ≡ halted (floc fs)
  store-at-slot-keeps-halted prog fs slot =
    writeLoc-halted (floc fs) (AtStack (current-frame (falloc fs)) slot)
                    (readReg (regs (floc fs)) Output)

  -- The build-layer PREFIX (mov-to-output, store pstash, alloc, store
  -- sstash, mov-to-input) runs as a 5-step chain. All five are
  -- unconditionally non-halting, so `halted` threads from `fs` (reg moves
  -- + alloc preserve it definitionally; the two stores via
  -- `store-at-slot-keeps-halted`).
  build-layer-prefix : ∀ (prog : AbstractTrace) (fs : FlatState) (pstash sstash : ℕ)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs)                         ≡ just mov-to-output
    → fetch prog (suc (fpc fs))                   ≡ just (store-at-slot pstash)
    → fetch prog (suc (suc (fpc fs)))             ≡ just (instr-alloc-heap 2)
    → fetch prog (suc (suc (suc (fpc fs))))       ≡ just (store-at-slot sstash)
    → fetch prog (suc (suc (suc (suc (fpc fs))))) ≡ just mov-to-input
    → FlatSteps prog 5 fs
        (flat-exec-instr mov-to-input prog
         (flat-exec-instr (store-at-slot sstash) prog
          (flat-exec-instr (instr-alloc-heap 2) prog
           (flat-exec-instr (store-at-slot pstash) prog
            (flat-exec-instr mov-to-output prog fs)))))
  build-layer-prefix prog fs pstash sstash hf f1 f2 f3 f4 f5 =
      (hf , f1)
    ∷ (hf , f2)
    ∷ (trans (store-at-slot-keeps-halted prog A1 pstash) hf , f3)
    ∷ (trans (store-at-slot-keeps-halted prog A1 pstash) hf , f4)
    ∷ (trans (store-at-slot-keeps-halted prog A3 sstash)
             (trans (store-at-slot-keeps-halted prog A1 pstash) hf) , f5)
    ∷ []
    where
      A1 = flat-exec-instr mov-to-output prog fs
      A3 = flat-exec-instr (instr-alloc-heap 2) prog
             (flat-exec-instr (store-at-slot pstash) prog A1)

  ----------------------------------------------------------------------
  -- Threading helpers for the suffix: each suffix instruction preserves
  -- Input1 (so the store-indirects keep firing) and the stack slots (so
  -- the loads keep reading their stash). Reg writes (load-tag, load) via
  -- writeReg-preserves / readLoc-regs-irrelevant; heap writes
  -- (store-indirect to the alloc'd AtDynamic pointer) via writeLoc-regs /
  -- writeLoc-preserves-other (heap ≠ stack).
  ----------------------------------------------------------------------

  -- load-tag-lit (writes Output) preserves Input1 + all readLoc.
  load-tag-keeps-input1 : ∀ (prog : AbstractTrace) (fs : FlatState) (tag : ℕ)
    → readReg (regs (floc (flat-exec-instr (instr-load-tag-lit tag) prog fs))) Input1
      ≡ readReg (regs (floc fs)) Input1
  load-tag-keeps-input1 prog fs tag =
    writeReg-preserves (regs (floc fs)) Output Input1 (SV-Tag tag) (λ ())

  load-tag-keeps-readLoc : ∀ (prog : AbstractTrace) (fs : FlatState) (tag : ℕ) (loc : ValueLocation FS)
    → readLoc (floc (flat-exec-instr (instr-load-tag-lit tag) prog fs)) loc ≡ readLoc (floc fs) loc
  load-tag-keeps-readLoc prog fs tag loc =
    readLoc-regs-irrelevant (floc fs) _ loc

  -- store-indirect (writes *Input1 = the alloc'd heap cell) preserves
  -- Input1 (writeLoc keeps regs) + every STACK read (heap ≠ stack).
  store-indirect-keeps-input1 : ∀ (prog : AbstractTrace) (fs : FlatState) (loc : ValueLocation FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readReg (regs (floc (flat-exec-instr store-indirect prog fs))) Input1
      ≡ readReg (regs (floc fs)) Input1
  store-indirect-keeps-input1 prog fs loc ptr rewrite ptr =
    cong (λ r → readReg r Input1) (writeLoc-regs (floc fs) loc (readReg (regs (floc fs)) Output))

  store-indirect-keeps-stack-readLoc : ∀ (prog : AbstractTrace) (fs : FlatState) (hl : HeapLocation) (f : _) (k : ℕ)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just (AtDynamic hl)
    → readLoc (floc (flat-exec-instr store-indirect prog fs)) (AtStack f k)
      ≡ readLoc (floc fs) (AtStack f k)
  store-indirect-keeps-stack-readLoc prog fs hl f k ptr rewrite ptr =
    writeLoc-preserves-other (floc fs) (AtDynamic hl) (AtStack f k)
                             (readReg (regs (floc fs)) Output) (λ ())

  -- store-indirect-suc (writes *(Input1+1)) preserves Input1 + stack reads.
  store-indirect-suc-keeps-input1 : ∀ (prog : AbstractTrace) (fs : FlatState) (loc : ValueLocation FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readReg (regs (floc (flat-exec-instr store-indirect-suc prog fs))) Input1
      ≡ readReg (regs (floc fs)) Input1
  store-indirect-suc-keeps-input1 prog fs loc ptr rewrite ptr =
    cong (λ r → readReg r Input1) (writeLoc-regs (floc fs) (sucLoc loc) (readReg (regs (floc fs)) Output))

  store-indirect-suc-keeps-stack-readLoc : ∀ (prog : AbstractTrace) (fs : FlatState) (hl : HeapLocation) (f : _) (k : ℕ)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just (AtDynamic hl)
    → readLoc (floc (flat-exec-instr store-indirect-suc prog fs)) (AtStack f k)
      ≡ readLoc (floc fs) (AtStack f k)
  store-indirect-suc-keeps-stack-readLoc prog fs hl f k ptr rewrite ptr =
    writeLoc-preserves-other (floc fs) (sucLoc (AtDynamic hl)) (AtStack f k)
                             (readReg (regs (floc fs)) Output) (λ ())

  -- load-from-slot (writes Output) preserves Input1 + all readLoc, given
  -- the slot is populated (so it reduces to the writeReg form).
  load-from-slot-keeps-input1 : ∀ (prog : AbstractTrace) (fs : FlatState) (slot : ℕ) (v : StoredValue FS)
    → readLoc (floc fs) (AtStack (current-frame (falloc fs)) slot) ≡ just v
    → readReg (regs (floc (flat-exec-instr (load-from-slot slot) prog fs))) Input1
      ≡ readReg (regs (floc fs)) Input1
  load-from-slot-keeps-input1 prog fs slot v slotfull rewrite slotfull =
    writeReg-preserves (regs (floc fs)) Output Input1 v (λ ())

  load-from-slot-keeps-readLoc : ∀ (prog : AbstractTrace) (fs : FlatState) (slot : ℕ) (v : StoredValue FS) (loc : ValueLocation FS)
    → readLoc (floc fs) (AtStack (current-frame (falloc fs)) slot) ≡ just v
    → readLoc (floc (flat-exec-instr (load-from-slot slot) prog fs)) loc ≡ readLoc (floc fs) loc
  load-from-slot-keeps-readLoc prog fs slot v loc slotfull rewrite slotfull =
    readLoc-regs-irrelevant (floc fs) _ loc

  -- The build-layer SUFFIX (load-tag, store-indirect, load pstash,
  -- store-indirect-suc, load sstash) runs as a 5-step chain. Given the
  -- self-generated entry state (Input1 = the alloc'd heap pointer, pstash
  -- populated by the prefix's first stash), the store-indirects fire
  -- (Input1 a pointer) and the pstash load fires (slot populated); these
  -- facts thread through the steps via the keeps-* helpers. The final
  -- load-sstash needs no precondition (it is the last step — its result
  -- being halted-or-not is no later step's concern).
  build-layer-suffix : ∀ (prog : AbstractTrace) (fs : FlatState)
                         (hl : HeapLocation) (tag pstash sstash : ℕ) (vp : StoredValue FS)
    → halted (floc fs) ≡ false
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just (AtDynamic hl)
    → readLoc (floc fs) (AtStack (current-frame (falloc fs)) pstash) ≡ just vp
    → fetch prog (fpc fs)                         ≡ just (instr-load-tag-lit tag)
    → fetch prog (suc (fpc fs))                   ≡ just store-indirect
    → fetch prog (suc (suc (fpc fs)))             ≡ just (load-from-slot pstash)
    → fetch prog (suc (suc (suc (fpc fs))))       ≡ just store-indirect-suc
    → fetch prog (suc (suc (suc (suc (fpc fs))))) ≡ just (load-from-slot sstash)
    → FlatSteps prog 5 fs
        (flat-exec-instr (load-from-slot sstash) prog
         (flat-exec-instr store-indirect-suc prog
          (flat-exec-instr (load-from-slot pstash) prog
           (flat-exec-instr store-indirect prog
            (flat-exec-instr (instr-load-tag-lit tag) prog fs)))))
  build-layer-suffix prog fs hl tag pstash sstash vp hf p1 hp f6 f7 f8 f9 f10 =
      (hf , f6)
    ∷ (hf , f7)
    ∷ (h8 , f8)
    ∷ (h9 , f9)
    ∷ (h10 , f10)
    ∷ []
    where
      S6 = flat-exec-instr (instr-load-tag-lit tag) prog fs
      S7 = flat-exec-instr store-indirect prog S6
      S8 = flat-exec-instr (load-from-slot pstash) prog S7
      ptr-S6 : sv-as-loc (readReg (regs (floc S6)) Input1) ≡ just (AtDynamic hl)
      ptr-S6 = trans (cong sv-as-loc (load-tag-keeps-input1 prog fs tag)) p1
      slot-pstash-S7 : readLoc (floc S7) (AtStack (current-frame (falloc fs)) pstash) ≡ just vp
      slot-pstash-S7 =
        trans (store-indirect-keeps-stack-readLoc prog S6 hl (current-frame (falloc fs)) pstash ptr-S6)
              (trans (load-tag-keeps-readLoc prog fs tag (AtStack (current-frame (falloc fs)) pstash)) hp)
      ptr-S8 : sv-as-loc (readReg (regs (floc S8)) Input1) ≡ just (AtDynamic hl)
      ptr-S8 = trans (cong sv-as-loc
                 (trans (load-from-slot-keeps-input1 prog S7 pstash vp slot-pstash-S7)
                   (trans (store-indirect-keeps-input1 prog S6 (AtDynamic hl) ptr-S6)
                     (load-tag-keeps-input1 prog fs tag)))) p1
      h8  = trans (store-indirect-keeps-halted prog S6 (AtDynamic hl) ptr-S6) hf
      h9  = trans (load-from-slot-keeps-halted prog S7 pstash vp slot-pstash-S7) h8
      h10 = trans (store-indirect-suc-keeps-halted prog S8 (AtDynamic hl) ptr-S8) h9
