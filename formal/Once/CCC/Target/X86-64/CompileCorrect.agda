-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.CompileCorrect  (Plan 0.10 Phase A)
--
-- THE GRAND THEOREM about the EXTRACTED compiler.
--
-- Until this module landed, `Once.CCC.Target.X86-64.Correct.compile-correct`
-- was a theorem about a path through the verified Dispatcher
-- (`D.run-wf`) — a function that returns abstract states, NOT a
-- function that compiles to a Program. The actually-extracted
-- `compile-ir : IR → Program` had no theorem attached to it. The
-- header of `Correct.agda` admits the gap:
--
--     ⊕ Full theorem: CONNECTED via ir-to-x86-correctness
--
-- where `ir-to-x86-correctness` was never written.
--
-- Plan 0.10 closes this gap by making the extracted compile *be* the
-- verified compile:
--
--     compile = compile-trace ∘ ir-to-trace
--
-- Phase A (this module) writes the top-level theorem with explicit
-- postulates filling every sub-obligation. The architecture is in
-- place from day one; subsequent phases discharge each postulate.
--
-- Audit handle: `make postulates-grep` lists every unproven obligation.
-- The postulates here shrink the audit surface from "the entire
-- compile-ir is unverified" to two named obligations:
--
--   * `ir-to-trace-correct`   (Phase E discharges)
--   * `compile-trace-correct` (Phase D discharges)
--
-- See `plans/0.10-verification-gap-closure.md`.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.CompileCorrect where

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open FrameSemantics using (Frame)

open import Once.Type using (Type)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR using (IR; AllocMode)
open import Once.CCC.Eval using (eval)

open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; halted; regs; readReg; Input;
         AbstractTrace)
open import Once.CCC.Machine.Allocation using (AllocState; current-frame)

open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)
open import Once.CCC.Target.X86-64.Syntax using (Program)

------------------------------------------------------------------------
-- The theorem framework is parameterized by FrameSemantics, just like
-- the verified-path Correctness module is.
------------------------------------------------------------------------

module Correctness {FS : FrameSemantics} (program-bound : ℕ) where

  open Once.CCC.Machine.SMCore.MemOps {FS}
  open Once.CCC.Machine.SMCore.ExecFinal {FS}
  open Once.CCC.Machine.SMCore.AbstractExec {FS}

  open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace)
  open import Once.CCC.Target.X86-64.DirectSimulation using (module Simulation)
  open Simulation {FS} using (X86State; Corresponds; exec-prog)

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF)

  open Once.CCC.Machine.Allocation.FrontierInvariant {FS}
    using (BeforeFrontier)

  ----------------------------------------------------------------------
  -- The extracted compile = compile-trace ∘ ir-to-trace.
  -- Phase C will switch `Once.Target.X86-64.x86-64-irToAsm` to use this.
  ----------------------------------------------------------------------

  compile : ∀ {A B} → IR A B → Program
  compile ir = compile-trace (ir-to-trace ir)

  ----------------------------------------------------------------------
  -- Phase A postulates — the two halves of the theorem chain.
  --
  -- Each is named so it shows up in `make postulates-grep` as a
  -- specific gap with a known discharge plan.
  ----------------------------------------------------------------------

  -- Sub-theorem 1: the abstract trace produced by `ir-to-trace`,
  -- when executed on the abstract machine, reaches a state that
  -- represents `eval ir x`. This is the IR-side correctness.
  --
  -- Discharged in Phase E (plan 0.10) by:
  --   (a) factoring `Dispatcher.run-ir-wf` into a pure data helper
  --       that produces the same trace, and
  --   (b) lifting the existing `IRResultAWF.trace-correct` proofs.
  postulate
    ir-to-trace-correct :
      ∀ {A B} (ir : IR A B)
        (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
        (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF mIn alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) Input ≡ input-loc →
      let result = exec-trace (ir-to-trace ir) s alloc
          final-s = proj₁ result
          final-alloc = proj₂ result
      in ∃[ mOut ] ∃[ result-loc ]
         ValidAtWF mOut final-alloc (eval ir x) result-loc final-s

  -- Sub-theorem 2: the arch program produced by `compile-trace`, when
  -- executed on the X86 machine, reaches a state that corresponds to
  -- the abstract state reached by executing the same trace on the
  -- abstract machine. This is the per-arch correctness — the
  -- DirectSimulation work.
  --
  -- Discharged in Phase D (plan 0.10) by induction over `AbstractTrace`,
  -- delegating to the per-AbstractInstr simulations already in
  -- `DirectSimulation.exec-x86` (themselves made honest by Plan 0.9
  -- Phase B which closed the silent catch-all `exec-x86 _ xs _ = xs`).
  postulate
    compile-trace-correct :
      ∀ (trace : AbstractTrace)
        (s : LocState FS) (alloc : AllocState {FS})
        (xs : X86State) (frame : Frame FS) →
      Corresponds s xs alloc →
      halted s ≡ false →
      let abs-result = exec-trace trace s alloc
          abs-final-s = proj₁ abs-result
          abs-final-alloc = proj₂ abs-result
          arch-final-xs = exec-prog (compile-trace trace) xs frame
      in Corresponds abs-final-s arch-final-xs abs-final-alloc

  ----------------------------------------------------------------------
  -- THE GRAND THEOREM (derived).
  --
  -- For every IR term, every input value, every initial X86State that
  -- corresponds to an abstract LocState representing the input:
  --
  --   executing `compile ir` on the X86 machine produces an X86State
  --   that corresponds to an abstract LocState representing `eval ir x`.
  --
  -- I.e. the binary's runtime behavior is provably equivalent (via the
  -- abstract semantics) to the IR's denotational semantics.
  --
  -- After Phase D + E land, both postulates above become real proofs
  -- and this theorem is proved end-to-end about the actually-extracted
  -- function `compile`.
  ----------------------------------------------------------------------

  compile-correct :
    ∀ {A B} (ir : IR A B)
      (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      (xs : X86State) (frame : Frame FS) →
    Corresponds s xs alloc →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    let trace = ir-to-trace ir
        abs-result = exec-trace trace s alloc
        abs-final-s = proj₁ abs-result
        abs-final-alloc = proj₂ abs-result
        arch-final-xs = exec-prog (compile-trace trace) xs frame
    in -- The arch state corresponds to an abstract state that...
       Corresponds abs-final-s arch-final-xs abs-final-alloc
       ×
       -- ...represents (eval ir x).
       (∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut abs-final-alloc (eval ir x) result-loc abs-final-s)
  compile-correct ir mIn x input-loc s alloc xs frame
                  corr valid before not-halted rdi-eq =
    let semantic-side =
          ir-to-trace-correct ir mIn x input-loc s alloc
            valid before not-halted rdi-eq
        machine-side =
          compile-trace-correct (ir-to-trace ir) s alloc xs frame
            corr not-halted
    in machine-side , semantic-side
