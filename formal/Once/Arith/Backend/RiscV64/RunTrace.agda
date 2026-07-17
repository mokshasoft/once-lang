-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.RunTrace  (Plan 0.54 Phase B / Option 2)
--
-- riscv64 emit-and-continue SigOp-event trace. Mirrors x86-64 but threads the
-- frame size `N` for arith-block dispatch (arith is Pure → no event); a
-- `call-sym` lowering an external SigOp emits its event and continues.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.RunTrace where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (if_then_else_)

open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.RiscV64.PhysReg using (Reg)
open import Once.CCC.Target.RiscV64.Syntax using (Program; Instr; call-sym)
open import Once.CCC.Target.RiscV64.Semantics using (State; halted; pc; fetch; execInstr; Word)
open State using (halted; pc)
open import Once.Arith.Backend.RiscV64.Dispatch using (ArithEnv; dispatch-arith)

module _ (val : XInstr → State → Reg → Word) where

  EvExtractor : Set
  EvExtractor = String → State → List SigOpEvent

  ret-past : State → State
  ret-past s = record s { pc = suc (pc s) }

  run-events       : EvExtractor → ArithEnv val → ℕ → Program → State → List SigOpEvent
  run-events-fetch : EvExtractor → ArithEnv val → ℕ → Program → State → Maybe Instr → List SigOpEvent
  run-events-call  : EvExtractor → ArithEnv val → ℕ → Program → State → String → Maybe (List XInstr × ℕ) → List SigOpEvent
  run-events-exec  : EvExtractor → ArithEnv val → ℕ → Program → State → Maybe State → List SigOpEvent

  run-events ev env zero    prog s = []
  run-events ev env (suc n) prog s =
    if halted s then [] else run-events-fetch ev env n prog s (fetch prog (pc s))

  run-events-fetch ev env n prog s nothing               = []
  run-events-fetch ev env n prog s (just (call-sym lbl)) = run-events-call ev env n prog s lbl (env lbl)
  run-events-fetch ev env n prog s (just i)              = run-events-exec ev env n prog s (execInstr prog s i)

  run-events-call ev env n prog s lbl (just (blk , N)) =
    run-events ev env n prog (dispatch-arith val blk N s)
  run-events-call ev env n prog s lbl nothing =
    ev lbl s ++ run-events ev env n prog (ret-past s)

  run-events-exec ev env n prog s nothing   = []
  run-events-exec ev env n prog s (just s') = run-events ev env n prog s'
