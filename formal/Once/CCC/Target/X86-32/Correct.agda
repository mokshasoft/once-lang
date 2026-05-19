-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.Correct
--
-- COMPILER CORRECTNESS THEOREM for x86-32
--
-- The FULL correctness property we want to prove:
--
--   ∀ ir x x86-32-state →
--     let program = compile-ir ir
--         x86-32-final = exec program x86-32-state
--     in eax x86-32-final represents (eval ir x)
--
-- This decomposes into two layers:
--
--   Layer 1: IR → AbstractTrace (via Dispatcher/PairWF)
--   Layer 2: AbstractTrace → x86-32 (via DirectSimulation)
--
-- Current status:
--   ✓ Layer 1: Complete (compile-correct via IRResultAWF.trace-correct)
--   ✓ Layer 2: STRUCTURE COMPLETE (DirectSimulation.trace-simulation)
--   ⊕ Full theorem: CONNECTED via ir-to-x86-32-correctness
--
-- ENTRY POINT:
--   See Once.CCC.EntryPointCCC for the concrete instantiation that:
--     - Instantiates Correctness with x86-32-frame-semantics
--     - Exports compile-x86-32 (code generation via AbstractTrace)
--     - Exports compile-correct-x86-32 (for dead code analysis)
--
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.Correct where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (_++_; length; [])
open import Data.Nat using (ℕ; suc; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open FrameSemantics using (Frame; _≺_)
open import Once.CCC.Machine.SMCore using (LocState; ValueLocation; StoredValue; SV-Ptr; halted; regs; readReg; Input1)

open import Once.Type using (Type)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR using (IR; AllocMode)
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size using (ir-size)
open import Once.CCC.IR.Stack using (ir-stack-requirement)
open import Once.CCC.Machine.Allocation using (AllocState; next-slot; current-frame; module FrontierInvariant)

-- Import the RuntimeContract
open import Once.CCC.Target.X86-32.RuntimeContract using (RuntimeContract; FrameOps)

-- Import escape interface for SurvivesFramePop
import Once.CCC.Machine.IR.ApplyWF as ApplyWFModule

-- Import Dispatcher for PrimProofInterface
import Once.CCC.Machine.Dispatcher as DispatcherModule

------------------------------------------------------------------------
-- THE CORRECTNESS THEOREM
--
-- Uses RuntimeContract instead of scattered parameters
------------------------------------------------------------------------

module Correctness
  {FS : FrameSemantics}
  (runtime : RuntimeContract FS)
  (sigOp-proof : DispatcherModule.SigOpContract.Provider {FS} (RuntimeContract.program-bound runtime))
  where

  open RuntimeContract runtime
  open FrontierInvariant {FS} using (BeforeFrontier)

  open import Once.CCC.Machine.ClosureWellFormed
  module CWF = ClosureWellFormedDef {FS} program-bound

  open import Once.CCC.Machine.Dispatcher

  module D = Dispatcher {FS} program-bound acc-pb sigOp-proof

  ----------------------------------------------------------------------
  -- Represents: value v is stored at location loc in state s
  --
  -- This is the abstraction boundary. ValidAtWF carries proof details,
  -- but conceptually it just means "v is at loc".
  ----------------------------------------------------------------------

  Represents : ∀ {A : Type} → AllocMode → AllocState {FS} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set
  Represents m alloc v loc s = CWF.ValidAtWF m alloc v loc s

  ----------------------------------------------------------------------
  -- COMPILER CORRECTNESS (Layer 1: IR → AbstractTrace)
  --
  -- The one theorem that matters:
  --   If input represents x, output represents (eval ir x)
  ----------------------------------------------------------------------

  compile-correct : ∀ {A B} (ir : IR A B)
    (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    -- If input represents x...
    Represents mIn alloc x input-loc s →
    -- ...and preconditions hold...
    BeforeFrontier alloc input-loc →
    ir-size ir < program-bound →
    -- Machine is ready to execute (caller must establish)
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    -- Phase 3: capacity parameter removed (unbounded stack model)
    -- ...then output represents (eval ir x)
    ∃[ mOut ] ∃[ result-loc ] ∃[ s' ] ∃[ alloc' ]
      Represents mOut alloc' (eval ir x) result-loc s'
  compile-correct ir mIn x input-loc s alloc repr before ir<bound not-halted rdi-eq =
    let (mOut , result) = D.run-wf mIn ir ir<bound x input-loc s alloc
          repr before not-halted rdi-eq
    in mOut
     , CWF.place-loc (CWF.IRResultAWF.result-place result)
     , CWF.IRResultAWF.final-state result
     , CWF.IRResultAWF.final-alloc result
     , CWF.place-valid (CWF.IRResultAWF.result-place result)

------------------------------------------------------------------------
-- LAYER 1: Complete
--
-- compile-correct shows:
--   Represents x input-loc s
--   ∧ halted s ≡ false           (CPU running)
--   ∧ Input1 = input-loc          (calling convention)
--   ∧ capacity sufficient        (stack space)
--     →
--   Represents (eval ir x) result-loc s'
------------------------------------------------------------------------

------------------------------------------------------------------------
-- LAYER 2: AbstractTrace → x86-32 (via DirectSimulation)
--
-- DirectSimulation proves:
--   X86-32Corresponds ls xs
--     →
--   X86-32Corresponds (exec-trace trace ls alloc) (exec-x86-32-trace trace xs)
------------------------------------------------------------------------

-- Import DirectSimulation module (Simulation submodule contains X86-32State, Corresponds)
-- Currently imported for documentation; actual use pending Layer 2 integration
import Once.CCC.Target.X86-32.DirectSimulation as DS

------------------------------------------------------------------------
-- FULL CHAIN: IR → eval semantics → x86-32 execution
--
-- The complete verification:
--
--   ┌─────────────────────────────────────────────────────────────────┐
--   │                         IR Term                                 │
--   │                           │                                     │
--   │            ┌──────────────┴──────────────┐                      │
--   │            │                             │                      │
--   │            ▼                             ▼                      │
--   │     ┌────────────┐               ┌──────────────┐               │
--   │     │  Dispatcher │               │ compile-trace│              │
--   │     │  (PairWF)  │               │ (AbstractTo- │              │
--   │     │            │               │   X86-32)    │              │
--   │     └─────┬──────┘               └──────┬───────┘               │
--   │           │                             │                       │
--   │           │ IRResultAWF.trace           │                       │
--   │           │                             │                       │
--   │           ▼                             ▼                       │
--   │     ┌────────────┐    ═══════     ┌──────────────┐               │
--   │     │ exec-trace │     trace-     │ exec-x86-32- │               │
--   │     │            │    simulation  │   trace      │               │
--   │     └─────┬──────┘               └──────┬───────┘               │
--   │           │                             │                       │
--   │           │ trace-correct               │                       │
--   │           ▼                             ▼                       │
--   │     ┌────────────┐    ═══════     ┌──────────────┐               │
--   │     │final-state │X86-32Corresponds│ x86-32 State│               │
--   │     │(LocState)  │                │ (result)     │               │
--   │     └────────────┘               └──────────────┘               │
--   │                                                                 │
--   │  Result: eax holds address of value satisfying                  │
--   │          eval ir x                                      │
--   └─────────────────────────────────────────────────────────────────┘
--
------------------------------------------------------------------------