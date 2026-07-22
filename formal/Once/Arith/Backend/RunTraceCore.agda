-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.RunTraceCore  (Plan 0.54 Phase B / Option 2)
--
-- The ARCH-GENERIC emit-and-continue SigOp-event trace, factored out of the
-- per-arch `Arith.Backend.{X86-64,RiscV64}.RunTrace` modules (which now become
-- thin instances). Mirrors the existing 5 arith-generic cores (PreserveCore,
-- MemPreserveCore, …): the machine logic lives HERE, once; each arch supplies
-- only its concrete machine telescope + arith `Payload`.
--
-- The trace loop:
--   * `matchCall i ≡ just lbl` AND `env lbl ≡ just pl` (an arith block): DISPATCH
--     the arith subroutine and continue, emitting NO event (arith is Pure);
--   * `matchCall i ≡ just lbl` AND `env lbl ≡ nothing` (an external SigOp): emit
--     its event `ev lbl s` and continue past the call (emit-and-continue);
--   * any other instruction executes via `execInstr` and emits nothing.
--
-- `run-trace` adapts the fuelled `run-events` (fuel counts machine STEPS) to a
-- `Behavior` (indexed by EVENT count) via an ABSTRACT `stepBudget : ℕ → ℕ` — the
-- adequate-fuel obligation, left abstract exactly as `FlatFromObs` leaves
-- `flat-trace` abstract, so the seam stays sound pending its discharge (Layer 2).
------------------------------------------------------------------------

module Once.Arith.Backend.RunTraceCore where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.Behavior using (Behavior)

------------------------------------------------------------------------
-- The generic machine telescope. `Payload` is the arch-specific arith
-- dispatch datum (x86-64: `List XInstr`; riscv64: `List XInstr × ℕ`), with
-- `val` already baked into `dispatchArith`.
------------------------------------------------------------------------

module RunTrace
  (State   : Set)
  (Program : Set)
  (Instr   : Set)
  (Payload : Set)
  (halted        : State → Bool)
  (pc            : State → ℕ)
  (fetch         : Program → ℕ → Maybe Instr)
  (execInstr     : Program → State → Instr → Maybe State)
  (matchCall     : Instr → Maybe String)      -- `just lbl` iff `i` is `call-sym lbl`
  (ret-past      : State → State)             -- return past a `call` (pc ← suc pc)
  (dispatchArith : Payload → State → State)   -- arith-block dispatch (val baked in)
  where

  -- The arith-block table: which `once_arith.block.*` label maps to which
  -- (arch-payload) block. `nothing` ⇒ an external SigOp lowering.
  ArithEnv : Set
  ArithEnv = String → Maybe Payload

  -- The SigOp-event extractor for an external `call-sym` — the honest
  -- label→SigOp resolution boundary.
  EvExtractor : Set
  EvExtractor = String → State → List SigOpEvent

  ----------------------------------------------------------------------
  -- The emit-and-continue trace loop (fuel = step budget), mutually with its
  -- fetch / call / exec dispatch.
  ----------------------------------------------------------------------
  run-events       : EvExtractor → ArithEnv → ℕ → Program → State → List SigOpEvent
  run-events-fetch : EvExtractor → ArithEnv → ℕ → Program → State → Maybe Instr → List SigOpEvent
  run-events-instr : EvExtractor → ArithEnv → ℕ → Program → State → Instr → Maybe String → List SigOpEvent
  run-events-call  : EvExtractor → ArithEnv → ℕ → Program → State → String → Maybe Payload → List SigOpEvent
  run-events-exec  : EvExtractor → ArithEnv → ℕ → Program → State → Maybe State → List SigOpEvent

  run-events ev env zero    prog s = []
  run-events ev env (suc n) prog s =
    if halted s then [] else run-events-fetch ev env n prog s (fetch prog (pc s))

  run-events-fetch ev env n prog s nothing  = []
  run-events-fetch ev env n prog s (just i) = run-events-instr ev env n prog s i (matchCall i)

  -- arith/SigOp call: consult the arith-block table.
  run-events-instr ev env n prog s i (just lbl) = run-events-call ev env n prog s lbl (env lbl)
  -- ordinary instruction: execute, emit nothing.
  run-events-instr ev env n prog s i nothing    = run-events-exec ev env n prog s (execInstr prog s i)

  -- arith block: dispatch, NO event, continue.
  run-events-call ev env n prog s lbl (just pl) =
    run-events ev env n prog (dispatchArith pl s)
  -- external SigOp: emit its event, continue past the call.
  run-events-call ev env n prog s lbl nothing =
    ev lbl s ++ run-events ev env n prog (ret-past s)

  run-events-exec ev env n prog s nothing   = []
  run-events-exec ev env n prog s (just s') = run-events ev env n prog s'

  ----------------------------------------------------------------------
  -- The `Behavior` adapter. `Behavior n` = the first `n` effectful SigOp
  -- events; `run-events` produces the events within `stepBudget n` machine
  -- STEPS. `stepBudget` (the adequate-fuel map) is abstract — the same honest
  -- gap `FlatFromObs.flat-trace` carries.
  ----------------------------------------------------------------------
  run-trace : (stepBudget : ℕ → ℕ) → EvExtractor → ArithEnv → Program → State → Behavior
  run-trace stepBudget ev env prog s n = take n (run-events ev env (stepBudget n) prog s)

  ----------------------------------------------------------------------
  -- "No reachable external SigOp ⇒ empty trace" — the concrete analogue of the
  -- abstract `FlatEvents.flat-events-[]`. The ONLY emitting branch of
  -- `run-events` is `run-events-call … nothing` (an external SigOp, `env lbl ≡
  -- nothing`); so if every fetchable `call-sym` is instead an ARITH block
  -- (`env lbl ≡ just pl`, dispatched with no event), the whole `run-events`
  -- trace is `[]`. By fuel induction, mirroring `run-events`'s fetch/instr/
  -- call/exec dispatch. This is the D4 pure/straight-line case: it pairs with
  -- `flat-events-[]` to give `conc-flat-sim` for any IR whose lowering invokes
  -- no external SigOp (both sides `[]`).
  --
  -- Hypothesis: at every program counter, a fetched instruction that is a
  -- `call-sym lbl` resolves to an arith block (`env lbl ≡ just pl`).
  ----------------------------------------------------------------------
  run-events-[] :
      ∀ (ev : EvExtractor) (env : ArithEnv) (prog : Program)
    → (∀ pc i lbl → fetch prog pc ≡ just i → matchCall i ≡ just lbl
         → Σ Payload (λ pl → env lbl ≡ just pl))
    → ∀ (fuel : ℕ) (s : State) → run-events ev env fuel prog s ≡ []
  run-events-[] ev env prog H zero    s = refl
  run-events-[] ev env prog H (suc n) s with halted s
  ... | true  = refl
  ... | false with fetch prog (pc s) in eqf
  ...   | nothing = refl
  ...   | just i  with matchCall i in eqm
  ...     | just lbl with H (pc s) i lbl eqf eqm
  ...       | (pl , eqv) rewrite eqv = run-events-[] ev env prog H n (dispatchArith pl s)
  run-events-[] ev env prog H (suc n) s | false | just i | nothing with execInstr prog s i
  ...       | nothing  = refl
  ...       | just s'  = run-events-[] ev env prog H n s'
