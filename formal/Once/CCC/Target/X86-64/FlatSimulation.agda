-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.FlatSimulation
--
-- Plan 0.32 Phase D, Stage 2: the abstract↔x86 plus-simulation over the
-- flat machine. `CompiledCorr prog fs s` relates a FlatState `fs` (flat
-- pc/fuel machine, typed StoredValues) to an x86 `State s` running the
-- compiled program `compile-trace prog`, where:
--   * the DATA agrees (registers under enc-sv, heap under enc-hl, flags,
--     halt) — exactly the FlatCorrespondence.FlatCorr data fields, and
--   * the CONTROL agrees up to the block offset: x86.pc = x86-off prog
--     (fpc fs)  (one flat instruction ↦ a contiguous x86 BLOCK; NOT 1-to-1
--     lockstep — see [[feedback-injectivity-not-lockstep]]).
--
-- The jump correspondence rides `FlatComposition.find-label-corr`. The
-- per-instruction DATA effects ride the FlatCorrespondence `sim-*` lemmas.
-- This module composes them under fuel.
--
-- ROADMAP (this file, in progress):
--   [x] CompiledCorr relation (data ⊕ block-offset pc)
--   [ ] block-step: one flat step ↔ `exec (x86-len i)` of its x86 block,
--       preserving CompiledCorr (uses sim-* for data, find-label-corr for
--       jumps, x86-off for the pc advance). Needs the per-x86-instr
--       "execInstr reduces to the sim-* post-state" facts (the deferred
--       (B) obligations).
--   [ ] fuel induction: exec-flat fuel prog fs ↔ exec (bound) (compile-
--       trace prog) s, lifting block-step; fuel bound = Σ x86-len.
--   [ ] wire into Correct.agda (retires compile-ir).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.CCC.Target.X86-64.FlatSimulation
  (FS : FrameSemantics)
  (enc-hl : HeapLocation → ℕ)
  (enc-hl-inj : ∀ {a b : HeapLocation} → enc-hl a ≡ enc-hl b → a ≡ b)
  where

open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X
open import Once.CCC.Target.X86-64.Syntax using (rax; rbx; rsi; rdi)

import Once.CCC.Target.X86-64.FlatCorrespondence as FC
module C = FC FS enc-hl enc-hl-inj          -- enc-sv / FlatCorr data fields
open import Once.CCC.Target.X86-64.FlatComposition FS using (x86-off)

------------------------------------------------------------------------
-- The compiled correspondence: FlatCorr's DATA fields + a block-offset pc.
-- (Reuses C.enc-sv / C.enc-maybe for the value/heap encodings.)
------------------------------------------------------------------------
record CompiledCorr (prog : AbstractTrace) (fs : FlatState) (s : X.State) : Set where
  field
    rdi-eq  : X.readReg (X.State.regs s) rdi ≡ C.enc-sv (readReg (regs (floc fs)) Input1)
    rsi-eq  : X.readReg (X.State.regs s) rsi ≡ C.enc-sv (readReg (regs (floc fs)) Input2)
    rax-eq  : X.readReg (X.State.regs s) rax ≡ C.enc-sv (readReg (regs (floc fs)) Output)
    rbx-eq  : X.readReg (X.State.regs s) rbx ≡ C.enc-sv (readReg (regs (floc fs)) Scratch)
    -- CONTROL: x86 pc sits at the block offset of the flat pc (NOT fpc fs).
    pc-off  : X.State.pc s ≡ x86-off prog (fpc fs)
    zf-eq   : X.Flags.zf (X.State.flags s) ≡ fzf fs
    halt-eq : X.State.halted s ≡ halted (floc fs)
    heap-eq : ∀ (hl : HeapLocation) →
              X.readMem (X.State.memory s) (enc-hl hl) ≡ C.enc-maybe (heapMem (floc fs) hl)
open CompiledCorr public
