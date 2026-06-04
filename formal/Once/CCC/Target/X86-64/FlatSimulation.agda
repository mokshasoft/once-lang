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
open import Data.Nat using (ℕ; _+_; _≡ᵇ_)
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
open X using (mkstate; execInstr; mkflags; _<ᵇ_)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax
  using (rax; rbx; rsi; rdi; Reg; Operand; Program; reg; imm; mem; mov; add; sub; cmp)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (refl)

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
    -- Plan 0.34: NO zf-eq — the flat machine has no flag; a conditional
    -- branch computes + consumes its condition inside one step, so the x86
    -- flags register is never a shared invariant (and add/sub clobbering zf
    -- is invisible to the correspondence).
    halt-eq : X.State.halted s ≡ halted (floc fs)
    heap-eq : ∀ (hl : HeapLocation) →
              X.readMem (X.State.memory s) (enc-hl hl) ≡ C.enc-maybe (heapMem (floc fs) hl)
open CompiledCorr public

------------------------------------------------------------------------
-- (B) execInstr-reduces facts. For each x86 instruction the codegen
-- emits, `execInstr` reduces to the exact post-state the FlatCorrespondence
-- `sim-*` lemmas assume. The PURE ones (register/imm/arith/cmp) are stated
-- standalone here; the memory ones (loads/stores) depend on the heap
-- correspondence and are discharged inside block-step.
------------------------------------------------------------------------
-- mov (reg dst) (reg src): rax↔rdi register shuffles (mov-to-output, …).
b-mov-reg-reg : ∀ (prog : Program) (s : X.State) (dst src : Reg)
  → execInstr prog s (mov (reg dst) (reg src))
    ≡ just (mkstate (xwriteReg (xregs s) dst (xreadReg (xregs s) src))
                    (memory s) (flags s) (pc s + 1) (xhalted s))
b-mov-reg-reg prog s dst src = refl

-- mov (reg dst) (imm n): tag/reg-op immediate loads (load-tag-lit, …).
b-mov-reg-imm : ∀ (prog : Program) (s : X.State) (dst : Reg) (n : ℕ)
  → execInstr prog s (mov (reg dst) (imm n))
    ≡ just (mkstate (xwriteReg (xregs s) dst n)
                    (memory s) (flags s) (pc s + 1) (xhalted s))
b-mov-reg-imm prog s dst n = refl

-- cmp (reg dst) (imm n): the control test (c-test-scratch). Like the flat
-- test, it SETS zf (= the dst≟n result) — so it preserves zf-eq, unlike
-- the arithmetic ops below.
b-cmp-reg-imm : ∀ (prog : Program) (s : X.State) (dst : Reg) (n : ℕ)
  → execInstr prog s (cmp (reg dst) (imm n))
    ≡ just (mkstate (xregs s) (memory s)
                    (mkflags (xreadReg (xregs s) dst ≡ᵇ n) (xreadReg (xregs s) dst <ᵇ n) false)
                    (pc s + 1) (xhalted s))
b-cmp-reg-imm prog s dst n = refl
