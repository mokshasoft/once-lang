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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Allocation using (current-frame)
open import Once.CCC.Machine.SMCore
  using (halted; regs; readReg; Output; AtStack; AbstractTrace;
         mov-to-output; mov-to-input; store-at-slot; instr-alloc-heap;
         module MemOps)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module CataNatBuildLayer {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}
  open MemOps {FS} using (writeLoc-halted)

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
