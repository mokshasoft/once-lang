-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrectFlat — observable correctness over the
-- FLAT machine (Plan 0.36, corrected machine side).
--
-- `MachineRefinesObsF` is the flat-machine instance of the Plan 0.36
-- encoding: a program's only observable is its SigOp trace, so
-- trace-correctness (`traces-agree`) is the headline obligation and
-- value-correctness (`ValidAtWF`) is a FIELD (`value-realized`).
--
-- It runs over `exec-flat` (pc + jump + fuel), NOT the straight-line
-- `exec-trace`, because the recursion schemes compile to LOOPS — so,
-- unlike `compile-correct-flat`, there is NO `StraightIR` precondition.
-- It is also GENERIC in `FrameSemantics` and carries NO target `X.exec`
-- obligation: the per-target machine bridge is the IR-agnostic
-- `flat-sim`, established once per target. So `cata-correct` here is one
-- statement for all targets.
--
-- `cata-correct` is the single named postulate (top-down scaffold):
--   * `traces-agree`   — discharged by μ-induction (`μS-ind`) over the
--                        events fold + per-SigOp `respects-semM`.
--   * `value-realized` — the looping flat-semantic correctness (the
--                        `rec-scheme-semantic` value half).
------------------------------------------------------------------------

module Once.CCC.Codegen.IRObsCorrectFlat where

open import Data.Nat using (ℕ; suc; _<_)
open import Data.Bool using (false; true)
open import Data.List using (length)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Type using (Type; ⟦_⟧T; μ-type)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR using (IR; AllocMode; Cata)
open import Once.CCC.IR.Size using (ir-size)
open import Once.CCC.Eval using (eval)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; SV-Ptr; halted; regs; readReg; Input1)
open import Once.CCC.Machine.Allocation using (AllocState; next-slot; module FrontierInvariant)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.CCC.Machine.ClosureWellFormed using (module ClosureWellFormedDef)
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.TraceDenote using (obs)
open import Once.Verified.FlatEvents using (module FlatEventTrace)

module IRObsCorrectFlatness {FS : FrameSemantics} (program-bound : ℕ) where
  open FlatMachine {FS}
  open FrontierInvariant {FS} using (BeforeFrontier)
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)
  open FlatEventTrace {FS} using (flat-events)

  -- The flat run of `ir` from `s`/`alloc` at a given fuel (frontier 0).
  flat-run : ℕ → ∀ {A B} → IR A B → LocState FS → AllocState {FS} → FlatState
  flat-run fuel ir s alloc = exec-flat fuel (ir-to-trace ir) (mkFlat s alloc 0)

  -- Observable refinement over the flat machine.
  --
  -- FUEL = "just enough", not a step-index. A `Cata` is a TOTAL inductive
  -- fold over a finite μ-value, so its compiled loop TERMINATES: `enough-fuel`
  -- is a (finite, input-dependent) WITNESS that the run completes
  -- (`run-halts`), provable from totality. Every cata is verified with its
  -- OWN sufficient fuel — no fixed constant, so no program is left unverified.
  -- (A fixed `n` like `defaultFuel = 10000` is only the executable's runtime
  -- guard, never the correctness fuel.) The single step-INDEXED loop in a
  -- total+productive program is the top-level event loop = an `Ana`
  -- coinductive unfold (∀ n: first-n events match); a non-terminating loop
  -- nested inside another can't be productive. So `Cata` carries a termination
  -- witness; only `Ana` carries a step-index.
  record MachineRefinesObsF {A B} (ir : IR A B) (x : ⟦ A ⟧)
                             (s : LocState FS) (alloc : AllocState {FS}) : Set where
    field
      enough-fuel  : ℕ
      run-halts    : halted (floc (flat-run enough-fuel ir s alloc)) ≡ true
      traces-agree :
        flat-events enough-fuel (ir-to-trace ir) (mkFlat s alloc 0)
          ≡ proj₁ (obs program-bound ir x)
      value-realized :
        ∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut (falloc (flat-run enough-fuel ir s alloc))
            (eval ir x) result-loc
            (forced (floc (flat-run enough-fuel ir s alloc)))

  -- Same preconditions as `compile-correct-flat`'s semantic side (entry
  -- frontier 0), minus `StraightIR` (loops are allowed); conclusion is
  -- the flat refinement.
  IRObsCorrectF : ∀ {A B} → IR A B → Set
  IRObsCorrectF {A} {B} ir =
    ir-size ir < program-bound →
    ∀ (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
    next-slot alloc ≡ 0 →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    MachineRefinesObsF ir x s alloc

  -- `cata-correct`: the single named obligation; the record FIELDS name the
  -- parts the discharge must provide (all sharing one `enough-fuel`):
  --   * `enough-fuel`/`run-halts` — the cata terminates (totality witness).
  --   * `traces-agree`  — loop↔fold: discharge by `μS-ind` over the events
  --                       fold + per-`instr-sigop` `respects-semM`. (Pure-cata
  --                       sub-case already dischargeable: `flat-events-[]` +
  --                       `pure-cata-emits-[]`, both `[]`.)
  --   * `value-realized`— looping flat-semantic value correctness (= the
  --                       existing `rec-scheme-semantic` trust boundary).
  -- These are the boundaries the cata collapses into; Phase 4 then deletes the
  -- old `ir-to-trace-correct-non-layer0` catchall + `rec-scheme-semantic`.
  postulate
    cata-correct : ∀ {F} (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
                 → IRObsCorrectF (Cata wf alg)
