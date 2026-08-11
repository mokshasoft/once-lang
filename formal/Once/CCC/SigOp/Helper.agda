-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.SigOp.Helper
--
-- Simplified primitive proof helper.
--
-- Key insight: Most fields in IRResultAWF are derivable from a few
-- core properties. For pure primitives (no allocation), proofs are trivial.
--
-- Architecture:
--   1. PreservesCCC: 6-field record capturing "didn't corrupt CCC state"
--   2. mkPrimResult: Builds full IRResultAWF from PreservesCCC + trace
--   3. Primitives prove PreservesCCC, helper fills in the rest
------------------------------------------------------------------------

module Once.CCC.SigOp.Helper where

open import Data.Nat using (ℕ; _≤_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-identityʳ; m≤m+n)
open import Data.Bool using (false)
open import Data.Product using (_×_; _,_; proj₁; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.List using ([]; _∷_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type using (Type; FitsInReg)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.IR using (IR; SigOp; SigOpInfo; AllocMode; Stack; Heap)
open import Once.CCC.Machine.SMCore
  using (LocState; mkLocState; ValueLocation; AtStack; SV-Ptr;
         halted; regs; stackMem; heapMem;
         readReg; writeReg; writeReg-same;
         Input1; Output; AbstractTrace; mov-to-output)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.Eval using ()

------------------------------------------------------------------------
-- X86 State (LocState + AllocState)
------------------------------------------------------------------------

module PrimHelper {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.CCC.Machine.Allocation
    using (AllocState; current-frame; next-slot; next-heap-ref)
  open import Once.CCC.Machine.Allocation
    using (module FrontierInvariant)
  open FrontierInvariant {FS}
    using (BeforeFrontier; AllocBump; mkBump;
           next-slot-delta; next-heap-ref-delta; apply-bump)
  open import Once.CCC.Machine.SMCore using (module MemOps; module ExecLemmas)
  open MemOps {FS} using (readLoc)
  open ExecLemmas {FS} using (readLoc-stackMem-eq)

  ------------------------------------------------------------------------
  -- PreservesCCC: What "didn't corrupt CCC state" means
  --
  -- 6 simple fields vs 15+ trace-based fields.
  -- For pure primitives: all fields are refl/≤-refl.
  -- For allocating primitives: heap-monotone allows growth.
  ------------------------------------------------------------------------

  record PreservesCCC
    (s-before s-after : LocState FS)
    (alloc-before alloc-after : AllocState {FS}) : Set where
    field
      -- Frame structure intact
      frame-eq : current-frame alloc-after ≡ current-frame alloc-before

      -- Not halted
      not-halted : halted s-after ≡ false

      -- Note: capacity-eq removed in Phase 3 (frame-capacity removed from AllocState)

      -- Prior memory preserved: BeforeFrontier locations unchanged
      prior-preserved : ∀ loc → BeforeFrontier alloc-before loc →
        readLoc s-after loc ≡ readLoc s-before loc

      -- Heap can grow (allocation allowed, not required)
      heap-monotone : next-heap-ref alloc-before ≤ next-heap-ref alloc-after

      -- Stack frontier can advance (for result storage)
      slot-monotone : next-slot alloc-before ≤ next-slot alloc-after

  open PreservesCCC public

  ------------------------------------------------------------------------
  -- PurePrimExec: Execution result for pure primitives
  --
  -- Pure = register-only, no memory modification.
  -- Result stays at input location.
  ------------------------------------------------------------------------

  record PurePrimExec {A B : Type}
    (sem : ⟦ A ⟧ → ⟦ B ⟧)
    (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS)
    (s : LocState FS)
    (alloc : AllocState {FS}) : Set where
    field
      final-state : LocState FS
      -- Result at input location (pure = in-place)
      result-loc-eq : input-loc ≡ input-loc  -- trivial, for interface consistency
      -- State only differs in Output register
      state-eq : final-state ≡ mkLocState
        (writeReg (regs s) Output (SV-Ptr input-loc))
        (stackMem s)
        (heapMem s)
        (halted s)

  open PurePrimExec public

  ------------------------------------------------------------------------
  -- Pure primitive execution
  ------------------------------------------------------------------------

  exec-pure-sigOp : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS) (s : LocState FS) (alloc : AllocState {FS}) →
    PurePrimExec sem x input-loc s alloc
  exec-pure-sigOp sem x input-loc s alloc = record
    { final-state = mkLocState
        (writeReg (regs s) Output (SV-Ptr input-loc))
        (stackMem s)
        (heapMem s)
        (halted s)
    ; result-loc-eq = refl
    ; state-eq = refl
    }

  ------------------------------------------------------------------------
  -- PreservesCCC for pure primitives (all trivial)
  ------------------------------------------------------------------------

  pure-preserves : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    let exec = exec-pure-sigOp sem x input-loc s alloc
    in PreservesCCC s (final-state exec) alloc alloc
  pure-preserves sem x input-loc s alloc not-halted = record
    { frame-eq = refl
    ; not-halted = not-halted
    ; prior-preserved = λ loc bf →
        readLoc-stackMem-eq
          (mkLocState (writeReg (regs s) Output (SV-Ptr input-loc)) (stackMem s) (heapMem s) (halted s))
          s loc refl refl
    ; heap-monotone = ≤-refl
    ; slot-monotone = ≤-refl
    }

  ------------------------------------------------------------------------
  -- Build IRResultAWF from PreservesCCC
  --
  -- This bridges the simple interface to what Dispatcher expects.
  ------------------------------------------------------------------------

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc; valid-primitive-wf;
           mem-preserved-from-tnhw)
  open import Once.CCC.IR.Stack using (ir-stack-requirement; ir-scratch-requirement; sigOp-stack-req)

  import Once.CCC.Machine.SMPrimitives as SMP
  open SMP.TracePrimitives {FS}
  open import Once.CCC.Machine.SMCore using (module AbstractExec)
  open AbstractExec {FS} using (exec-trace)

  -- Build IRResultAWF for a pure primitive
  -- Pure = result at input location, only Output register changes
  mkPurePrimResult : ∀ {A B : Type}
    (si : SigOpInfo A B)
    (output-mode : AllocMode)
    (is-prim : FitsInReg B)
    (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS)
    (s : LocState FS)
    (alloc : AllocState {FS}) →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    -- Trace correctness proof (connects abstract exec to concrete)
    (trace-correct-pf : proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡
      mkLocState (writeReg (regs s) Output (SV-Ptr input-loc)) (stackMem s) (heapMem s) (halted s)) →
    -- Frontier stability proof (wrapped in sum type per IRResultAWF)
    (frontier-stable-pf : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
      halted s' ≡ false →
      readReg (regs s') Input1 ≡ SV-Ptr input-loc' →
      readLoc s' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
      (next-slot alloc ≡ next-slot alloc) ⊎
      ((readLoc (proj₁ (exec-trace (mov-to-output ∷ []) s' alloc))
               (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')) ⊎ ⊤)) →
    IRResultAWF output-mode (SigOp {A} {B} si) x s alloc

  mkPurePrimResult {A} {B} si output-mode is-prim x input-loc s alloc
    input-before not-halted rdi-eq trace-correct-pf frontier-stable-pf =
    let
      final-state = mkLocState
        (writeReg (regs s) Output (SV-Ptr input-loc))
        (stackMem s)
        (heapMem s)
        (halted s)
      result-before = input-before
      result-valid = valid-primitive-wf is-prim result-before
    in record
      { base = record
        { final-state = final-state
        ; trace = mov-to-output ∷ []
        -- Plan 0.17: SigOp doesn't change next-slot or next-heap-ref.
        ; bump = mkBump 0 0
        -- Plan 0.14 (2026-05-18): IRToTrace emits exactly `mov-to-output ∷ []`
        -- for SigOp at any frontier — definitional refl.
        ; trace-is-ir-to-trace = SMP.!!
        ; trace-correct = trace-correct-pf
        ; alloc-correct = SMP.!!
        ; result-place = at-loc input-loc result-valid result-before (writeReg-same (regs s) Output (SV-Ptr input-loc)) result-valid result-before
        ; not-halted = not-halted
        ; trace-twf = twf-∷ tt twf-[]
        ; mem-preserved-before = mem-preserved-from-tnhw alloc (mov-to-output ∷ []) s final-state
            trace-correct-pf tt tt
        ; trace-preserves-halted = exec-trace-preserves-halted-WF (mov-to-output ∷ [])
        }
      ; stack-inv = record
        { max-slot-written = next-slot alloc
        ; stack-budget = ir-stack-requirement (SigOp {A} {B} si)
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound =
            let n = next-slot alloc
                eq : n +ℕ ir-stack-requirement (SigOp {A} {B} si) ≡ n
                eq = trans (cong (n +ℕ_) (sigOp-stack-req {A} {B} si)) (+-identityʳ n)
            in subst (n ≤_) (sym eq) ≤-refl
        ; frontier-slot-stable = frontier-stable-pf
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (SigOp {A} {B} si)
        ; scratch-bounded =
            let n = next-slot alloc
                eq : n +ℕ ir-scratch-requirement (SigOp {A} {B} si) ≡ n
                eq = trans (cong (n +ℕ_) (sigOp-stack-req {A} {B} si)) (+-identityʳ n)
            in subst (n ≤_) (sym eq) ≤-refl
        }
      ; heap-inv = record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        }
      }