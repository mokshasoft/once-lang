-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.SigOp.Contract
--
-- Contract for primitive operations.
--
-- The contract specifies what implementors must prove.
-- Provider is the interface for domain compilers to register primitives.
------------------------------------------------------------------------

module Once.CCC.SigOp.Contract where

open import Data.Nat using (ℕ)
open import Data.Bool using (false)
open import Data.Product using (∃-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Type)
open import Once.CCC.IR using (IR; SigOp; AllocMode)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Eval using (SigOpSem)
open import Once.Semantics.Machine using (⟦_⟧)

------------------------------------------------------------------------
-- Contract and Provider (arch-portable)
--
-- Parameterized by FrameSemantics for portability.
------------------------------------------------------------------------

module Def {FS : FrameSemantics} (program-bound : ℕ) (sigOpSem : SigOpSem) where
  open import Once.CCC.Machine.SMCore using (LocState; ValueLocation; halted; regs; readReg; Input)
  open import Once.CCC.Machine.Allocation using (AllocState; module FrontierInvariant)
  open FrontierInvariant {FS} using (BeforeFrontier)
  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound sigOpSem using (ValidAtWF; IRResultAWF)

  -- The contract: what implementors must prove for a primitive
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
      readReg (regs s) Input ≡ input-loc →
      IRResultAWF output-mode ir x s alloc

  -- Interface for domain compilers to register primitives
  Provider : Set
  Provider =
    ∀ {A B : Type} (name : String) →
    ∃[ m ] Contract {A} {B} m (SigOp name)