-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.SigOp.Contract
--
-- Contract and Provider for signature operations.
--
-- The contract specifies what implementors must prove for a SigOp:
-- given valid input state, running the codegen trace leaves the CCC
-- in a valid state with the result at the expected location.
--
-- The Provider is a **partial** function: given a `SigOpInfo`, it
-- returns `just` a contract if it recognizes the SigOp, or `nothing`
-- otherwise. Providers compose via `_<|>_` (see SigOp.Compose).
--
-- Plan 0.2.4.1 Phase A: partial provider + SigOpInfo keying.
-- Plan 0.2.4.1 Phase B: composition + coverage.
------------------------------------------------------------------------

module Once.CCC.SigOp.Contract where

open import Data.Nat using (ℕ)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe)
open import Data.Product using (∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Type)
open import Once.CCC.IR using (IR; SigOp; AllocMode; SigOpInfo)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Semantics.Machine using (⟦_⟧)

------------------------------------------------------------------------
-- Contract and Provider (arch-portable, parameterized by FrameSemantics)
------------------------------------------------------------------------

module Def {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.CCC.Machine.SMCore using (LocState; ValueLocation; SV-Ptr; halted; regs; readReg; Input1)
  open import Once.CCC.Machine.Allocation using (AllocState; module FrontierInvariant)
  open FrontierInvariant {FS} using (BeforeFrontier)
  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound using (ValidAtWF; IRResultAWF)

  -- | The contract: what implementors must prove for a SigOp.
  -- Given a valid input state and the standard CCC preconditions,
  -- the contract promises a valid `IRResultAWF` at `output-mode`.
  Contract : ∀ {A B : Type}
    (output-mode : AllocMode)
    (ir : IR A B) →
    Set
  Contract {A} {B} output-mode ir =
    ∀ (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF mIn alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) Input1 ≡ SV-Ptr input-loc →
      IRResultAWF output-mode ir x s alloc

  -- | Provider interface (partial).
  --
  -- Given a `SigOpInfo A B`, return `just (m , proof)` if this
  -- provider recognizes the SigOp (with output mode `m` and a
  -- contract proof), or `nothing` otherwise. Concrete providers
  -- are written as pattern-matches on the `name` field; each domain
  -- owns its string prefix (e.g. `"lit.int."`, `"linux."`,
  -- `"arith.<op>.int"`).
  --
  -- Composition (`_<|>_`) makes the whole-program provider a
  -- first-win chain of domain providers.
  Provider : Set
  Provider =
    ∀ {A B : Type} (si : SigOpInfo A B) →
    Maybe (∃[ m ] Contract {A} {B} m (SigOp si))
