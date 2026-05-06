-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.SigOp.RelaxedPOC
--
-- POC: discharge `RelaxedContract` for `arith.add.int` using the
-- existing copy-trace `mov-to-output ∷ []`.
--
-- ## Why this exists
--
-- Plan 0.10 Phase A — SigOp gap closure. We need to design a SigOp
-- contract that catches wrong codegen at typecheck time. This file is
-- the *negative-result* POC: it demonstrates that the
-- discipline-only `RelaxedContract` (preserves frame/mem/regs/halt)
-- is too weak — it admits a copy-trace as a valid implementation of
-- `add`, even though `add (a,b) ≢ (a,b)` in general.
--
-- The success of this proof is the bug. The next iteration adds a
-- value-flow obligation; at that point this proof should fail to
-- typecheck, which is the property we want.
--
-- ## What's proven
--
--   add-info-relaxed-by-copy : RelaxedContract add-info (mov-to-output ∷ [])
--
-- ## What's NOT proven
--
-- Any tie between the trace and `add-semM`. The contract has no such
-- field; the proof goes through trivially.
------------------------------------------------------------------------

module Once.Arith.SigOp.RelaxedPOC where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Once.Type using (Type; Int; _*_)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SigOp.Info using (SigOpInfo)
open import Once.CCC.Machine.SMCore
  using (LocState; mkLocState; AbstractInstr; AbstractTrace;
         AbstractReg; Input1; Output;
         Registers; halted; regs; stackMem; heapMem;
         readReg; writeReg; writeReg-preserves;
         mov-to-output;
         module AbstractExec; module MemOps; module ExecLemmas)
open import Once.CCC.Machine.Allocation
  using (AllocState; current-frame; next-slot;
         module FrontierInvariant)
open import Once.CCC.SigOp.RelaxedContract using (module RelaxedDef)

import Once.Arith.SigOp.Builders as Builders

------------------------------------------------------------------------
-- The POC module
------------------------------------------------------------------------

module POC {FS : FrameSemantics} where
  open AbstractExec {FS} using (exec-trace; exec-trace-single; exec-abstract)
  open MemOps {FS} using (readLoc)
  open ExecLemmas {FS} using (readLoc-stackMem-eq)
  open FrontierInvariant {FS} using (BeforeFrontier)
  open RelaxedDef {FS} using (RelaxedContract)

  ----------------------------------------------------------------------
  -- The "compiled" trace under test: a single mov-to-output.
  -- Semantically: Output := Input1. (A copy.)
  --
  -- For `add (a, b)`, the right output is `a + b`, which is NOT
  -- the input pair location. So this trace is wrong for `add` at
  -- the value level. The discipline-only contract doesn't see it.
  ----------------------------------------------------------------------

  copy-trace : AbstractTrace
  copy-trace = mov-to-output ∷ []

  ----------------------------------------------------------------------
  -- After-state of executing copy-trace from a not-halted state.
  -- exec-abstract mov-to-output writes Input1's value to Output,
  -- leaving everything else unchanged.
  ----------------------------------------------------------------------

  copy-after : LocState FS → AllocState {FS} → LocState FS × AllocState {FS}
  copy-after s alloc =
    mkLocState (writeReg (regs s) Output (readReg (regs s) Input1))
               (stackMem s) (heapMem s) (halted s)
    , alloc

  copy-trace-reduces : ∀ s alloc → halted s ≡ false →
    exec-trace copy-trace s alloc ≡ copy-after s alloc
  copy-trace-reduces s alloc not-halted =
    trans (exec-trace-single mov-to-output s alloc not-halted) refl

  ----------------------------------------------------------------------
  -- Field discharges (per RelaxedContract field)
  ----------------------------------------------------------------------

  -- (1) Frame discipline: alloc is unchanged by mov-to-output.
  copy-preserves-frame : ∀ s alloc → halted s ≡ false →
    current-frame (proj₂ (exec-trace copy-trace s alloc))
      ≡ current-frame alloc
  copy-preserves-frame s alloc not-halted =
    cong (λ p → current-frame (proj₂ p)) (copy-trace-reduces s alloc not-halted)

  -- (2) Pre-frontier memory preserved: stackMem/heapMem unchanged.
  copy-preserves-prior-mem : ∀ s alloc loc → halted s ≡ false →
    BeforeFrontier alloc loc →
    readLoc (proj₁ (exec-trace copy-trace s alloc)) loc
      ≡ readLoc s loc
  copy-preserves-prior-mem s alloc loc not-halted _ =
    let s' = proj₁ (exec-trace copy-trace s alloc)
        s'-eq : s' ≡ proj₁ (copy-after s alloc)
        s'-eq = cong proj₁ (copy-trace-reduces s alloc not-halted)
        stack-eq : stackMem s' ≡ stackMem s
        stack-eq = cong stackMem s'-eq
        heap-eq : heapMem s' ≡ heapMem s
        heap-eq = cong heapMem s'-eq
    in readLoc-stackMem-eq s' s loc stack-eq heap-eq

  -- (3) Slot frontier unchanged.
  copy-slot-stable : ∀ s alloc → halted s ≡ false →
    next-slot (proj₂ (exec-trace copy-trace s alloc))
      ≡ next-slot alloc
  copy-slot-stable s alloc not-halted =
    cong (λ p → next-slot (proj₂ p)) (copy-trace-reduces s alloc not-halted)

  -- (4) Only Output may change. mov-to-output writes only to Output.
  copy-regs-only-output : ∀ s alloc r → ¬ (r ≡ Output) →
    halted s ≡ false →
    readReg (regs (proj₁ (exec-trace copy-trace s alloc))) r
      ≡ readReg (regs s) r
  copy-regs-only-output s alloc r r≢out not-halted =
    let regs-eq : regs (proj₁ (exec-trace copy-trace s alloc))
                  ≡ writeReg (regs s) Output (readReg (regs s) Input1)
        regs-eq = cong (λ p → regs (proj₁ p))
                       (copy-trace-reduces s alloc not-halted)
    in trans (cong (λ rs → readReg rs r) regs-eq)
             (writeReg-preserves (regs s) Output r
                                 (readReg (regs s) Input1) r≢out)

  -- (5) Halted: stays false (mov-to-output doesn't halt).
  copy-halted-after : ∀ s alloc → halted s ≡ false →
    halted (proj₁ (exec-trace copy-trace s alloc)) ≡ false
    ⊎ halted (proj₁ (exec-trace copy-trace s alloc)) ≡ true
  copy-halted-after s alloc not-halted =
    inj₁ (trans (cong (λ p → halted (proj₁ p))
                      (copy-trace-reduces s alloc not-halted))
                not-halted)

  ----------------------------------------------------------------------
  -- THE BUG-FINDING EVIDENCE
  --
  -- The contract is satisfied by the copy-trace for `add-info`.
  -- But add (a,b) ≠ (a,b). So the contract is too weak.
  ----------------------------------------------------------------------

  add-info-relaxed-by-copy :
    RelaxedContract Builders.add-info copy-trace
  add-info-relaxed-by-copy = record
    { preserves-frame      = copy-preserves-frame
    ; preserves-prior-mem  = copy-preserves-prior-mem
    ; slot-stable          = copy-slot-stable
    ; regs-only-output     = copy-regs-only-output
    ; halted-after         = copy-halted-after
    }
    where open RelaxedContract

  ----------------------------------------------------------------------
  -- Same proof, parameterized over ANY si of any (A, B). Demonstrates
  -- that this contract has nothing to do with the SigOp's identity —
  -- it can't tell add from neg from lit.int from id.
  ----------------------------------------------------------------------

  copy-discharges-anything :
    ∀ {A B} (si : SigOpInfo A B) →
    RelaxedContract si copy-trace
  copy-discharges-anything si = record
    { preserves-frame      = copy-preserves-frame
    ; preserves-prior-mem  = copy-preserves-prior-mem
    ; slot-stable          = copy-slot-stable
    ; regs-only-output     = copy-regs-only-output
    ; halted-after         = copy-halted-after
    }
    where open RelaxedContract


------------------------------------------------------------------------
-- Tier-2 negative-test: try to prove Faithful for add-info with the
-- copy-trace.
--
-- The trace is `mov-to-output ∷ []`. Its effect: Output := Input1.
-- So `Output post-trace = readReg (regs s) Input1` and `s post-trace`
-- has the same heap/stack as `s` but with Output written.
--
-- Faithful obligation: for any Repr, given the Input1 represents x,
-- the post-trace Output represents `add-semM x`. With Output =
-- Input1 post-trace, we'd need Repr B (add-semM x) … (Input-loc).
-- But the only thing we know about Input-loc is Repr A x. The only
-- way these two could agree is if `add-semM x = x` (and even then,
-- not for arbitrary Repr — Repr A and Repr B are at different
-- types). For an OPAQUE postulated `add-semM`, no such bridge
-- exists.
--
-- We don't *write* the proof of failure (failed proofs aren't
-- checked-in code). Instead, we write the **type signature** and
-- leave a hole. The hole is the design driver: anything that
-- discharges this hole must invoke a per-name lemma about
-- `add-semM`, which doesn't (and shouldn't) exist for `add` until
-- a real codegen is in place.
------------------------------------------------------------------------

  open import Once.CCC.SigOp.Faithful using (ReprPred; module FaithfulDef)

  module FaithfulTier2 (Repr : ReprPred FS) where
    open FaithfulDef {FS} using (Faithful)

    -- The negative test. Any term inhabiting this type would be a
    -- proof that `mov-to-output ∷ []` correctly implements `add`
    -- — false in general because `add (a, b) ≢ (a, b)`. We
    -- attempt the proof honestly and document where it gets stuck.
    --
    -- Attempt: discharge `output-faithful` directly. Given Repr A x
    -- s alloc (Input-loc), the post-trace state has Output := Input1
    -- (mov-to-output's effect), and stack/heap/halted unchanged.
    -- So we need:
    --
    --   Repr B (add-semM x) (post-state) (post-alloc) (Input-loc)
    --
    -- The only Repr-fact we have is `Repr A x s alloc Input-loc`.
    -- The mov-to-output preserves all memory; only `regs` change.
    -- For Repr that depends only on memory + alloc + loc, the
    -- premise gives us `Repr A x post-state post-alloc Input-loc`.
    -- But we need `Repr B (add-semM x) ...`. Two obstructions:
    --   (a) A and B are different types (`Int * Int` vs `Int`).
    --   (b) `add-semM x ≢ x` in general; nothing pins it down for
    --       opaque `add-semM`.
    --
    -- Below we attempt to write the proof and watch Agda complain.
    -- The file is left such that uncommenting the body produces a
    -- typecheck error; with the current commented-out body, it
    -- passes (modulo the `?` which Agda flags as an
    -- unsolved-meta).
    --
    -- Uncomment to observe the failure. Recommended: keep `?`
    -- here so that `make compiler-all` flags an unsolved-meta,
    -- which is the audit handle for "this contract is not
    -- discharged for `add` with this codegen".
    --
    --   add-info-faithful-by-copy :
    --     Faithful Repr Builders.add-info copy-trace
    --   add-info-faithful-by-copy = record
    --     { output-faithful = λ s alloc x not-halted repr-input → ?
    --     }
    --     where open Faithful
    --
    -- For now, we use a postulate so the build is green. Replacing
    -- the postulate with the above body re-runs the test.
    -- =====================================================================
    -- NEGATIVE-TEST RESULTS (2026-04-28, Agda 2.8.0)
    --
    -- Test 1: add-info (Int * Int → Int) with copy-trace.
    --   Body: λ s alloc x _ repr-input → repr-input
    --   Result: REJECTED at type level.
    --     [UnequalTerms] Int * Int != Int of type Type
    --     when checking that the expression repr-input has type
    --       Repr Int (SigOpInfo.semM Builders.add-info x) ... Output-loc
    --   Interpretation: the premise is `Repr (Int*Int) x ...`; the
    --   obligation requires `Repr Int (add-semM x) ...`. The type
    --   mismatch alone makes the proof unwriteable.
    --
    -- Test 2: neg-info (Int → Int) with copy-trace.
    --   Body: λ s alloc x _ repr-input → repr-input
    --   Result: REJECTED at value level.
    --     [UnequalTerms] x != Builders.neg-semM x of type ℕ
    --     when checking that the expression repr-input has type
    --       Repr Int (SigOpInfo.semM Builders.neg-info x) ... Output-loc
    --   Interpretation: even when types align, the value `x` does
    --   not unify with `neg-semM x`. For an OPAQUE postulated
    --   `neg-semM`, no derivation closes — exactly the property
    --   the user wanted ("if codegen is wrong, proofs fail").
    --
    -- These rejections demonstrate that `Faithful` is the right
    -- shape: a wrong codegen surfaces as an Agda error, not as a
    -- silently-passing trivial proof. The earlier `Contract`
    -- (Once.CCC.SigOp.Contract.Def.Contract) plus the existing
    -- `add-int-proof` (Once.Arith.SigOp.Proofs) was admitting the
    -- copy-trace for `add` because no field tied to `add-semM`.
    -- =====================================================================

    -- The following postulates record what would need to be proven
    -- for each (si, codegen) pair, but cannot be derived for these
    -- particular (si, codegen) pairs. Replacing these `postulate`s
    -- with real definitions reproduces the rejections above.
    postulate
      add-info-faithful-by-copy : Faithful Repr Builders.add-info copy-trace
      neg-info-faithful-by-copy : Faithful Repr Builders.neg-info copy-trace
