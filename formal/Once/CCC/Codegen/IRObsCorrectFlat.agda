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
open import Data.Bool using (false)
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

  -- The flat run of `ir` from `s`/`alloc` (frontier 0, fuel = trace length).
  flat-run : ∀ {A B} → IR A B → LocState FS → AllocState {FS} → FlatState
  flat-run ir s alloc =
    exec-flat (suc (length (ir-to-trace ir))) (ir-to-trace ir) (mkFlat s alloc 0)

  -- Observable refinement over the flat machine.
  record MachineRefinesObsF {A B} (ir : IR A B) (x : ⟦ A ⟧)
                             (s : LocState FS) (alloc : AllocState {FS}) : Set where
    field
      traces-agree :
        flat-events (suc (length (ir-to-trace ir))) (ir-to-trace ir) (mkFlat s alloc 0)
          ≡ proj₁ (obs program-bound ir x)
      value-realized :
        ∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut (falloc (flat-run ir s alloc))
            (eval ir x) result-loc
            (forced (floc (flat-run ir s alloc)))

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

  -- `cata-correct` decomposed top-down into its two honest halves, each a
  -- named postulate pointing at its discharge path. These are the SINGLE
  -- pair of trust boundaries the cata collapses into (Plan 0.36 Phase 4
  -- then deletes the old `ir-to-trace-correct-non-layer0` catchall and
  -- `rec-scheme-semantic`).
  postulate
    -- TRACE half: the compiled cata loop emits exactly `obs`'s events, in
    -- fold order. Discharge: μ-induction (`μS-ind`) over the events fold +
    -- per-`instr-sigop` `respects-semM`, relating `exec-flat`'s loop
    -- traversal to `obs`'s `cata-ev-alg` fold. (Pure-cata sub-case already
    -- dischargeable: `flat-events-[]` + `pure-cata-emits-[]`, both `[]`.)
    cata-traces-agree :
      ∀ {F} (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
      → ir-size (Cata wf alg) < program-bound
      → (mIn : AllocMode) (x : ⟦ μ-type F ⟧) (input-loc : ValueLocation FS)
        (s : LocState FS) (alloc : AllocState {FS})
      → next-slot alloc ≡ 0
      → ValidAtWF mIn alloc x input-loc s → BeforeFrontier alloc input-loc
      → halted s ≡ false → readReg (regs s) Input1 ≡ SV-Ptr input-loc
      → flat-events (suc (length (ir-to-trace (Cata wf alg)))) (ir-to-trace (Cata wf alg))
                    (mkFlat s alloc 0)
          ≡ proj₁ (obs program-bound (Cata wf alg) x)

    -- VALUE half: the looping flat-semantic correctness (= the existing
    -- `rec-scheme-semantic` trust boundary, restated over `exec-flat`).
    cata-value-realized :
      ∀ {F} (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
      → ir-size (Cata wf alg) < program-bound
      → (mIn : AllocMode) (x : ⟦ μ-type F ⟧) (input-loc : ValueLocation FS)
        (s : LocState FS) (alloc : AllocState {FS})
      → next-slot alloc ≡ 0
      → ValidAtWF mIn alloc x input-loc s → BeforeFrontier alloc input-loc
      → halted s ≡ false → readReg (regs s) Input1 ≡ SV-Ptr input-loc
      → ∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut (falloc (flat-run (Cata wf alg) s alloc))
            (eval (Cata wf alg) x) result-loc
            (forced (floc (flat-run (Cata wf alg) s alloc)))

  -- The single theorem, built from its two halves (no longer a bare postulate).
  cata-correct : ∀ {F} (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A)
               → IRObsCorrectF (Cata wf alg)
  cata-correct wf alg ir<b mIn x il s alloc ns valid bf nh rdi =
    record { traces-agree   = cata-traces-agree   wf alg ir<b mIn x il s alloc ns valid bf nh rdi
           ; value-realized = cata-value-realized wf alg ir<b mIn x il s alloc ns valid bf nh rdi }
