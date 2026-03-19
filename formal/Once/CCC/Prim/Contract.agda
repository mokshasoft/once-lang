------------------------------------------------------------------------
-- Once.CCC.Prim.Contract
--
-- Contract for primitive operations.
--
-- Contains:
--   1. PrimContract record: metadata (output-mode)
--   2. PrimProof: what implementors must prove
--   3. PrimProofProvider: interface for domain compilers
------------------------------------------------------------------------

module Once.CCC.Prim.Contract where

open import Data.Nat using (ℕ)
open import Data.Bool using (false)
open import Data.Product using (∃-syntax)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Type)
open import Once.CCC.IR using (IR; Prim; AllocMode)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Eval using (PrimSem)
open import Once.Sem using (⟦_⟧)

------------------------------------------------------------------------
-- PrimContract: Metadata about a primitive
------------------------------------------------------------------------

record PrimContract (A B : Type) : Set where
  field
    output-mode : AllocMode

open PrimContract public

------------------------------------------------------------------------
-- PrimProof: What implementors must prove (arch-portable)
--
-- Parameterized by FrameSemantics for portability.
------------------------------------------------------------------------

module PrimProofDef {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open import Once.CCC.SMCore using (LocState; ValueLocation; halted; regs; readReg; Input)
  open import Once.CCC.Target.X86v3.Dispatcher.Allocation using (AllocState; module FrontierInvariant)
  open FrontierInvariant {FS} using (BeforeFrontier)
  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem using (ValidAtWF; IRResultAWF)

  -- What a proof for a primitive must provide
  PrimProof : ∀ {A B : Type}
    (c : PrimContract A B)
    (ir : IR A B) →
    Set
  PrimProof {A} {B} c ir =
    ∀ (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF mIn alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) Input ≡ input-loc →
      IRResultAWF (output-mode c) ir x s alloc

  -- Interface for domain compilers
  PrimProofProvider : Set
  PrimProofProvider =
    ∀ {A B : Type} (name : String) →
    ∃[ c ] PrimProof {A} {B} c (Prim name)
