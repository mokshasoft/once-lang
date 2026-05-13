-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.SigOp.Proofs
--
-- Arithmetic primitive proofs (arch-portable).
--
-- Parameterized by FrameSemantics, not tied to any specific target.
-- Uses the simplified Once.CCC.SigOp.Helper interface.
------------------------------------------------------------------------

module Once.Arith.SigOp.Proofs where

open import Data.Nat using (ℕ; _≤_; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Bool using (false)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type using (Type; Int; FitsInReg; fits-int; _*_)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.IR using (IR; SigOp; AllocMode; Stack)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; AtStack; SV-Ptr; halted; regs;
         readReg; Input1; Output; AbstractTrace; mov-to-output;
         mkLocState; stackMem; heapMem; writeReg; module MemOps;
         module AbstractExec; module ExecLemmas)
open import Once.CCC.Eval using ()
open import Once.Semantics.Machine using (⟦_⟧)
import Once.Arith.SigOp.Builders as Builders

------------------------------------------------------------------------
-- Arithmetic Semantics
------------------------------------------------------------------------

add-sem : ⟦ Int * Int ⟧ → ⟦ Int ⟧
add-sem (a , b) = a +ℕ b

------------------------------------------------------------------------
-- Arithmetic Proof Module
------------------------------------------------------------------------

module ArithProofs {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.CCC.SigOp.Helper
  open PrimHelper {FS} program-bound

  open import Once.CCC.Machine.Allocation
    using (AllocState; current-frame; next-slot; frame-capacity)
  open import Once.CCC.Machine.Allocation
    using (module FrontierInvariant)
  open FrontierInvariant {FS} using (BeforeFrontier)

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF)

  open import Once.CCC.SigOp.Contract using (module Def)
  open Def {FS} program-bound
    using (Contract)

  open AbstractExec {FS} using (exec-trace; exec-trace-single; exec-abstract)
  open MemOps {FS} using (readLoc)
  open ExecLemmas {FS} using (readLoc-stackMem-eq)
  open import Data.List using ([]; _∷_)

  ------------------------------------------------------------------------
  -- Lemmas
  ------------------------------------------------------------------------

  -- Trace execution: mov-to-output writes Input1 to Output
  -- Precondition: readReg (regs s) Input1 ≡ input-loc
  arith-trace-correct : ∀ (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡
    mkLocState (writeReg (regs s) Output (SV-Ptr input-loc))
               (stackMem s) (heapMem s) (halted s)
  arith-trace-correct input-loc s alloc not-halted rdi-eq =
    let
      step1 : proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡
              proj₁ (exec-abstract mov-to-output s alloc)
      step1 = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      step2 : proj₁ (exec-abstract mov-to-output s alloc) ≡
              mkLocState (writeReg (regs s) Output (readReg (regs s) Input1))
                         (stackMem s) (heapMem s) (halted s)
      step2 = refl

      step3 : mkLocState (writeReg (regs s) Output (readReg (regs s) Input1))
                         (stackMem s) (heapMem s) (halted s) ≡
              mkLocState (writeReg (regs s) Output (SV-Ptr input-loc))
                         (stackMem s) (heapMem s) (halted s)
      step3 = cong (λ loc → mkLocState (writeReg (regs s) Output loc)
                                       (stackMem s) (heapMem s) (halted s)) rdi-eq
    in trans step1 (trans step2 step3)

  -- Frontier slot stability: mov-to-output only affects registers
  arith-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS)
    (alloc : AllocState {FS}) →
    halted s' ≡ false →
    readReg (regs s') Input1 ≡ SV-Ptr input-loc' →
    readLoc s' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ []) s' alloc))
            (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')
  arith-frontier-stable s' input-loc' alloc not-halted rdi-eq slot-eq =
    let
      s'' = proj₁ (exec-trace (mov-to-output ∷ []) s' alloc)

      -- After mov-to-output, stackMem is unchanged
      stack-preserved : stackMem s'' ≡ stackMem s'
      stack-preserved = cong stackMem
        (trans (cong proj₁ (exec-trace-single mov-to-output s' alloc not-halted)) refl)

      -- heapMem is also unchanged
      heap-preserved : heapMem s'' ≡ heapMem s'
      heap-preserved = cong heapMem
        (trans (cong proj₁ (exec-trace-single mov-to-output s' alloc not-halted)) refl)

      -- readLoc only depends on stackMem/heapMem for AtStack locations
      loc-preserved : readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡
                      readLoc s' (AtStack (current-frame alloc) (next-slot alloc))
      loc-preserved = readLoc-stackMem-eq s'' s'
                        (AtStack (current-frame alloc) (next-slot alloc))
                        stack-preserved heap-preserved
    in trans loc-preserved slot-eq

  ------------------------------------------------------------------------
  -- THE PROOF: Clean and simple
  ------------------------------------------------------------------------

  add-int-proof : Contract {Int * Int} {Int} Stack (SigOp Builders.add-info)
  add-int-proof mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mkPurePrimResult
      Builders.add-info
      Stack
      fits-int
      x
      input-loc
      s
      alloc
      input-before
      not-halted
      rdi-eq
      (arith-trace-correct input-loc s alloc not-halted rdi-eq)
      (λ s' loc' nh' rdi' slot-eq' → inj₂ (inj₁ (arith-frontier-stable s' loc' alloc nh' rdi' slot-eq')))

  ------------------------------------------------------------------------
  -- Provider: Maps add-info to its proof
  ------------------------------------------------------------------------

  add-int-contract-proof : ∃[ m ] Contract {Int * Int} {Int} m (SigOp Builders.add-info)
  add-int-contract-proof = Stack , add-int-proof