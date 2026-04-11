-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Prim.Helper
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

module Once.CCC.Prim.Helper where

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

open import Once.Type using (Type; IsPrimitive)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.IR using (IR; Prim; AllocMode; Stack; Heap)
open import Once.CCC.Machine.SMCore
  using (LocState; mkLocState; ValueLocation; OnStack;
         halted; regs; stackMem; heapMem;
         readReg; writeReg; writeReg-same;
         Input; Output; AbstractTrace; mov-to-output)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.Eval using (PrimSem; evalPrim)

------------------------------------------------------------------------
-- X86 State (LocState + AllocState)
------------------------------------------------------------------------

module PrimHelper {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open import Once.CCC.Machine.Allocation
    using (AllocState; current-frame; next-slot; next-heap-ref)
  open import Once.CCC.Machine.Allocation
    using (module FrontierInvariant)
  open FrontierInvariant {FS}
    using (BeforeFrontier)
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
        (writeReg (regs s) Output input-loc)
        (stackMem s)
        (heapMem s)
        (halted s)

  open PurePrimExec public

  ------------------------------------------------------------------------
  -- Pure primitive execution
  ------------------------------------------------------------------------

  exec-pure-prim : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS) (s : LocState FS) (alloc : AllocState {FS}) →
    PurePrimExec sem x input-loc s alloc
  exec-pure-prim sem x input-loc s alloc = record
    { final-state = mkLocState
        (writeReg (regs s) Output input-loc)
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
    let exec = exec-pure-prim sem x input-loc s alloc
    in PreservesCCC s (final-state exec) alloc alloc
  pure-preserves sem x input-loc s alloc not-halted = record
    { frame-eq = refl
    ; not-halted = not-halted
    -- Note: capacity-eq removed in Phase 3
    ; prior-preserved = λ loc bf →
        readLoc-stackMem-eq
          (mkLocState (writeReg (regs s) Output input-loc) (stackMem s) (heapMem s) (halted s))
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
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; valid-primitive-wf)
  open import Once.CCC.IR.Stack using (ir-stack-requirement; ir-scratch-requirement; prim-stack-req)

  import Once.CCC.Machine.SMPrimitives as SMP
  open SMP.TracePrimitives {FS}
  open import Once.CCC.Machine.SMCore using (module AbstractExec)
  open AbstractExec {FS} using (exec-trace)

  -- Build IRResultAWF for a pure primitive
  -- Pure = result at input location, only Output register changes
  mkPurePrimResult : ∀ {A B : Type}
    (name : String)
    (output-mode : AllocMode)
    (is-prim : IsPrimitive B)
    (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS)
    (s : LocState FS)
    (alloc : AllocState {FS}) →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    -- Trace correctness proof (connects abstract exec to concrete)
    (trace-correct-pf : proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡
      mkLocState (writeReg (regs s) Output input-loc) (stackMem s) (heapMem s) (halted s)) →
    -- Frontier stability proof (wrapped in sum type per IRResultAWF)
    (frontier-stable-pf : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
      halted s' ≡ false →
      readReg (regs s') Input ≡ input-loc' →
      readLoc s' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc' →
      (next-slot alloc ≡ next-slot alloc) ⊎
      ((readLoc (proj₁ (exec-trace (mov-to-output ∷ []) s' alloc))
               (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc') ⊎ ⊤)) →
    IRResultAWF output-mode (Prim {A} {B} name) x s alloc

  mkPurePrimResult {A} {B} name output-mode is-prim x input-loc s alloc
    input-before not-halted rdi-eq trace-correct-pf frontier-stable-pf =
    let
      final-state = mkLocState
        (writeReg (regs s) Output input-loc)
        (stackMem s)
        (heapMem s)
        (halted s)
      result-before = input-before
      result-valid = valid-primitive-wf is-prim result-before
    in record
      { result-loc = input-loc
      ; final-state = final-state
      ; final-alloc = alloc
      ; trace = mov-to-output ∷ []
      ; trace-correct = trace-correct-pf
      ; result-valid-wf = result-valid
      ; result-before = result-before
      ; rax-is-result = writeReg-same (regs s) Output input-loc
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      -- Note: capacity-preserved removed in Phase 3
      -- Note: mem-preserved-before removed in Phase 4 - use irresult-mem-preserved
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = result-before
      ; reclaim-preserves-validity = result-valid
      ; reclaim-size-bound =
          let n = next-slot alloc
              eq : n +ℕ ir-stack-requirement (Prim {A} {B} name) ≡ n
              eq = trans (cong (n +ℕ_) (prim-stack-req {A} {B} name)) (+-identityʳ n)
          in subst (n ≤_) (sym eq) ≤-refl
      -- Pure primitives don't write to stack, so max-slot-written = next-slot alloc
      ; max-slot-written = next-slot alloc
      ; max-slot-geq-reclaim = ≤-refl
      -- max-slot-usage-bound: next-slot alloc ≤ next-slot alloc +ℕ ir-stack-requirement (Prim name)
      -- Since prim-stack-req proves ir-stack-requirement (Prim name) ≡ 0, this is trivially ≤-refl
      ; max-slot-usage-bound =
          let n = next-slot alloc
              eq : n +ℕ ir-stack-requirement (Prim {A} {B} name) ≡ n
              eq = trans (cong (n +ℕ_) (prim-stack-req {A} {B} name)) (+-identityʳ n)
          in subst (n ≤_) (sym eq) ≤-refl
      -- slot-stays-in-budget: final = input for pure primitives
      ; slot-stays-in-budget =
          let n = next-slot alloc
              eq : n +ℕ ir-stack-requirement (Prim {A} {B} name) ≡ n
              eq = trans (cong (n +ℕ_) (prim-stack-req {A} {B} name)) (+-identityʳ n)
          in subst (n ≤_) (sym eq) ≤-refl
      ; frontier-slot-stable = frontier-stable-pf
      ; trace-writes-above = tt
      ; trace-slot-reads-above = tt
      ; trace-writes-below = tt
      ; trace-slot-reads-below = tt
      -- scratch-bounded: max-slot-written = next-slot alloc = next-slot final-alloc
      -- ir-scratch-requirement (Prim name) = 0, so bound is n +ℕ 0 = n
      ; scratch-bounded =
          let n = next-slot alloc
              eq : n +ℕ ir-scratch-requirement (Prim {A} {B} name) ≡ n
              eq = trans (cong (n +ℕ_) (prim-stack-req {A} {B} name)) (+-identityʳ n)
          in subst (n ≤_) (sym eq) ≤-refl
      -- Note: trace-preserves-capacity removed in Phase 3
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output tph-[]
      }