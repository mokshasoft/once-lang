-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CPU.X86-32 — X86-32 ArchSemantics instance
--
-- Same pattern as RiscV64 / X86-64: wires the simple-shape semantics
-- into the portable `ArchSemantics` interface. Trust point is the
-- body of `X86-32.Semantics.execInstr`.
------------------------------------------------------------------------

module Once.Adequacy.CPU.X86-32 where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)

open import Once.Denotation.Behavior      using (Behavior)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (Interp)
open import Once.Arith.Backend.CallAnswer using (CallResolver; answer-at)
open import Once.Adequacy.CPU.Interface using (Byte; ArchSemantics)

import Data.Maybe
import Once.CCC.Target.X86-32.Semantics as X32
import Once.CCC.Target.X86-32.Syntax    as X32S
import Once.CCC.Target.X86-32.File as RF
open import Data.Bool using (if_then_else_)
open import Data.String using (_==_)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Plan 0.54 Phase B / Option 2: the emit-and-continue trace over the REAL
-- x86-32 machine, instanced from `Arith.Backend.RunTraceCore` like x86-64/riscv64.
-- DERIVES `run-trace` from `X32.run`'s step semantics, replacing the old opaque
-- observable postulate with the real machine + three small named sub-gaps.
import Once.Arith.Backend.X86-32.RunTrace as RT
open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Adequacy.ArchCorrectness.ArithSimX86-32 using (val-x86-32)

------------------------------------------------------------------------
-- run-trace-x86-32 — DERIVED (no longer an opaque observable postulate). Its
-- remaining ingredients are the SAME named gaps x86-64/riscv64 carry:
--   * `val-x86-32`        — the concrete XInstr arith interpreter (DEFINED).
--   * `block-env`        — the arith-block table, read off the file (plan 0.107).
--   * `ev-x86-32`         — label→SigOp resolution (inverse of symbol lowering).
--   * `step-budget-x86-32`— adequate fuel (event-count ↦ machine steps).
------------------------------------------------------------------------

postulate
  -- D268: the adequate fuel of THIS run — it reads the block table, the code
  -- and the start state (a program-independent `ℕ → ℕ` cannot be adequate:
  -- event-free prefixes are unboundedly long).
  step-budget-x86-32 : List (String × RF.Payload) → X32S.Program → X32.State → ℕ → ℕ
  ev-x86-32        : String → X32.State → List SigOpEvent
  -- plan 0.105: WHICH answering call a label is, and its argument — the same
  -- label→SigOp resolution boundary as `ev-x86-32` (the loaded binary's
  -- symbol table and argument decoding). The answer itself is DEFINED
  -- (`CallAnswer.answer-at`): the world's, at the binary's log.
  call-at-x86-32   : CallResolver X32.State

-- Plan 0.105: at the world `ι` the binary runs in — its external calls are
-- answered by `ι`, and the answer lands in the return register.
-- Plan 0.107: the arith blocks are IN THE FILE, so which block a symbol names is
-- a lookup, not a postulate (it was `arith-env-x86-32`).
block-env : List (String × RF.Payload) → String → Maybe (List XInstr)
block-env []              _ = nothing
block-env ((s′ , p) ∷ bs) s = if s′ == s then just (proj₁ p) else block-env bs s

postulate
  -- D268: what an adequate budget MEANS (`RunTraceCore.Adequate`) — a deeper
  -- observation only adds events, and a short one is the whole run. Class
  -- **axiom** of the CPU model, consistent: the step count to the n-th event
  -- (or the run's end) is such a budget.
  step-budget-x86-32-adequate :
    ∀ (ι : Interp) (bs : List (String × RF.Payload)) (code : X32S.Program) (s : X32.State)
    → RT.Adequate val-x86-32 (answer-at ι call-at-x86-32)
        (RT.run-trace-fam val-x86-32 (answer-at ι call-at-x86-32) (step-budget-x86-32 bs code s) ev-x86-32 (block-env bs) code s)

run-trace-x86-32 : Interp → RF.Image → X32.State → Behavior
run-trace-x86-32 ι P s =
  RT.run-trace val-x86-32 (answer-at ι call-at-x86-32) (step-budget-x86-32 (RF.Image.blocks P) (RF.Image.code P) s) ev-x86-32 (block-env (RF.Image.blocks P)) (RF.Image.code P) s
    (step-budget-x86-32-adequate ι (RF.Image.blocks P) (RF.Image.code P) s)

postulate
  decode-x86-32 : List Byte → Maybe RF.Image
  -- GNU `as --target=x86-32` trust point; removed by B1.
  assemble-x86-32 : String → List Byte
  -- THE TRUST POINT (plan 0.107): `as` does what it should.
  as-faithful-x86-32 : ∀ (F : RF.Image) → RF.AsmWF F
                  → decode-x86-32 (assemble-x86-32 (RF.print F)) ≡ just F

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = RF.Image
  ; State        = X32.State
  ; initialState = λ P → X32.initStateAt (Data.Maybe.fromMaybe 0 (RF.Image.entry P))
  ; run          = λ P → X32.run (RF.Image.code P)
  ; run-trace    = run-trace-x86-32
  ; decode       = decode-x86-32
  ; assemble     = assemble-x86-32
  ; File         = RF.Image
  ; print        = RF.print
  ; program      = λ F → F
  ; AsmWF        = RF.AsmWF
  ; as-faithful  = as-faithful-x86-32
  }
