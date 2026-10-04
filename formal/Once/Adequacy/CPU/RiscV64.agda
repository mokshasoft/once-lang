-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CPU.RiscV64 — RiscV64 ArchSemantics instance
--
-- Wires the existing `Once.CCC.Target.RiscV64.Semantics` (clean
-- step / exec / run shape, RISC-V ISA Manual conformance) into the
-- portable `ArchSemantics` interface.
--
-- Concrete fields:
--   - Program      = List Instr  (from Once.CCC.Target.RiscV64.Syntax)
--   - State        = the existing record (regs, memory, pc, halted)
--   - initialState = RV.Semantics.initState
--   - run          = RV.Semantics.run  ← THE TRUST POINT.
--                    Reviewers verify each clause of `run` (which calls
--                    `step` → `execInstr`) against the RISC-V ISA Manual.
--   - observe      = read exit code from `a0` after halt.
--
-- Postulated:
--   - decode   : byte-encoding-of-Instr decoder.
------------------------------------------------------------------------

module Once.Adequacy.CPU.RiscV64 where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (if_then_else_)
open import Data.String using (_==_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Data.Maybe
import Once.CCC.Target.RiscV64.File as RF
open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)

open import Once.Denotation.Behavior      using (Behavior)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (Interp)
open import Once.Arith.Backend.CallAnswer using (CallResolver; answer-at)
open import Once.Adequacy.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.RiscV64.Semantics as RV
import Once.CCC.Target.RiscV64.Syntax    as RVS

-- Plan 0.54 Phase B / Option 2: the emit-and-continue trace over the REAL
-- riscv64 machine (arith blocks dispatched, Pure ⇒ no event), instanced from
-- the arch-generic `Arith.Backend.RunTraceCore` exactly like x86-64. This
-- DERIVES `run-trace` from `RV.run`'s step semantics, replacing the old opaque
-- observable postulate with the real machine + three small named sub-gaps.
import Once.Arith.Backend.RiscV64.RunTrace as RT
open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 using (val-riscv64)

------------------------------------------------------------------------
-- run-trace-riscv64 — DERIVED (no longer an opaque observable postulate).
-- Its remaining ingredients are the SAME named gaps x86-64 carries:
--   * `val-riscv64`        — the concrete XInstr arith interpreter (DEFINED).
--   * `arith-env-riscv64`  — the arith-block table (label ↦ block × N),
--                            recoverable from the compiled program.
--   * `ev-riscv64`         — label→SigOp resolution (the inverse of the
--                            per-arch symbol lowering; correctness = conc-flat-sim).
--   * `step-budget-riscv64`— adequate fuel (event-count ↦ machine steps).
------------------------------------------------------------------------

postulate
  -- D268: the adequate fuel of THIS run — it reads the block table, the code
  -- and the start state (a program-independent `ℕ → ℕ` cannot be adequate:
  -- event-free prefixes are unboundedly long).
  step-budget-riscv64 : List (String × RF.Payload) → RVS.Program → RV.State → ℕ → ℕ
  ev-riscv64        : String → RV.State → List SigOpEvent
  -- plan 0.105: WHICH answering call a label is, and its argument — the same
  -- label→SigOp resolution boundary as `ev-riscv64` (the loaded binary's
  -- symbol table and argument decoding). The answer itself is DEFINED
  -- (`CallAnswer.answer-at`): the world's, at the binary's log.
  call-at-riscv64   : CallResolver RV.State

-- Plan 0.107: the arith blocks are IN THE FILE, so which block a symbol names is
-- a lookup, not a postulate (it was `arith-env-riscv64`).
block-env : List (String × RF.Payload) → String → Maybe RF.Payload
block-env []              _ = nothing
block-env ((s′ , p) ∷ bs) s = if s′ == s then just p else block-env bs s

postulate
  -- D268: what an adequate budget MEANS (`RunTraceCore.Adequate`) — a deeper
  -- observation only adds events, and a short one is the whole run. Class
  -- **axiom** of the CPU model, consistent: the step count to the n-th event
  -- (or the run's end) is such a budget.
  step-budget-riscv64-adequate :
    ∀ (ι : Interp) (bs : List (String × RF.Payload)) (code : RVS.Program) (s : RV.State)
    → RT.Adequate val-riscv64 (answer-at ι call-at-riscv64)
        (RT.run-trace-fam val-riscv64 (answer-at ι call-at-riscv64) (step-budget-riscv64 bs code s) ev-riscv64 (block-env bs) code s)

run-trace-riscv64 : Interp → RF.Image → RV.State → Behavior
run-trace-riscv64 ι P s =
  RT.run-trace val-riscv64 (answer-at ι call-at-riscv64) (step-budget-riscv64 (RF.blocks P) (RF.code P) s) ev-riscv64
    (block-env (RF.blocks P)) (RF.code P) s
    (step-budget-riscv64-adequate ι (RF.blocks P) (RF.code P) s)

postulate
  -- The CPU's decoder (the ISA's encoding) — only ever used through
  -- `as-faithful`.
  decode-riscv64 : List Byte → Maybe RF.Image
  -- GNU `as` (RISC-V).
  assemble-riscv64 : String → List Byte
  -- THE TRUST POINT (plan 0.107): `as` does what it should.
  as-faithful-riscv64 : ∀ (F : RF.Image) → RF.AsmWF F
                      → decode-riscv64 (assemble-riscv64 (RF.print F)) ≡ just F

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = RF.Image
  ; State        = RV.State
  ; initialState = λ P → RV.initStateAt (Data.Maybe.fromMaybe 0 (RF.entry P))
  ; run          = λ P → RV.run (RF.code P)
  ; run-trace    = run-trace-riscv64
  ; decode       = decode-riscv64
  ; assemble     = assemble-riscv64
  ; File         = RF.Image
  ; print        = RF.print
  ; program      = λ F → F
  ; AsmWF        = RF.AsmWF
  ; as-faithful  = as-faithful-riscv64
  }
