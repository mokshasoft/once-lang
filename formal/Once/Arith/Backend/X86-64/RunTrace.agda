-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.RunTrace  (Plan 0.54 Phase B / Option 2)
--
-- The emit-and-continue SigOp-event trace over the concrete x86-64 machine,
-- mirroring `Adequacy.FlatEvents.flat-events` but on the real `X64` machine with
-- arith-block dispatch:
--
--   * a `call once_arith.block.*` DISPATCHES the arith subroutine and continues,
--     emitting NO event (arith is Pure — it computes in registers);
--   * a `call-sym` that LOWERS an external SigOp invocation emits its SigOp event
--     and continues past the call (emit-and-continue, replacing `execInstr`'s
--     `call-sym = halt` simplification);
--   * every other instruction executes via the CCC `execInstr` and emits nothing.
--
-- So the observable trace is exactly the sequence of external SigOp events; the
-- arith blocks contribute none (and, by `dispatch-arith-preserves`, don't perturb
-- the CCC state the surrounding events read). The SigOp-event extractor `ev` (the
-- label→SigOp resolution) is a parameter — the honest resolution boundary.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.RunTrace where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (if_then_else_)

open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.X86-64.PhysReg using (Reg)
open import Once.CCC.Target.X86-64.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.X86-64.Semantics using (State; fetch; execInstr; Word)
open State using (halted; pc)
open import Once.Arith.Backend.X86-64.Dispatch using (ArithEnv; dispatch-arith)

module _ (val : XInstr → State → Reg → Word) where

  -- The SigOp-event extractor for an external `call-sym`: `ev lbl s` reads the
  -- event (name + ℕ arg) off the label and calling-convention register.
  EvExtractor : Set
  EvExtractor = String → State → List SigOpEvent

  -- Return past a `call` (the SigOp/subroutine returns to the next instruction).
  ret-past : State → State
  ret-past s = record s { pc = suc (pc s) }

  ----------------------------------------------------------------------
  -- The emit-and-continue trace loop (fuel = step budget), mutually with its
  -- fetch / call / exec dispatch, mirroring `flat-events`.
  ----------------------------------------------------------------------
  run-events       : EvExtractor → ArithEnv val → ℕ → Program → State → List SigOpEvent
  run-events-fetch : EvExtractor → ArithEnv val → ℕ → Program → State → Maybe Instr → List SigOpEvent
  run-events-call  : EvExtractor → ArithEnv val → ℕ → Program → State → String → Maybe (List XInstr) → List SigOpEvent
  run-events-exec  : EvExtractor → ArithEnv val → ℕ → Program → State → Maybe State → List SigOpEvent

  run-events ev env zero    prog s = []
  run-events ev env (suc n) prog s =
    if halted s then [] else run-events-fetch ev env n prog s (fetch prog (pc s))

  run-events-fetch ev env n prog s nothing              = []
  run-events-fetch ev env n prog s (just (call-sym lbl)) = run-events-call ev env n prog s lbl (env lbl)
  run-events-fetch ev env n prog s (just i)              = run-events-exec ev env n prog s (execInstr prog s i)

  -- arith block: dispatch, NO event, continue.
  run-events-call ev env n prog s lbl (just blk) =
    run-events ev env n prog (dispatch-arith val blk s)
  -- external SigOp: emit its event, continue past the call.
  run-events-call ev env n prog s lbl nothing =
    ev lbl s ++ run-events ev env n prog (ret-past s)

  run-events-exec ev env n prog s nothing   = []
  run-events-exec ev env n prog s (just s') = run-events ev env n prog s'
