------------------------------------------------------------------------
-- Once.Backend.X86v3.IRResult
--
-- IR execution result type for X86v3 dispatcher.
-- Separate module to avoid circular dependencies.
------------------------------------------------------------------------

module Once.Backend.X86v3.IRResult where

open import Data.Nat using (ℕ; _≤_; _+_; _<_)
open import Data.Bool using (Bool; false)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Induction.WellFounded using (Acc)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation
open import Once.Backend.X86v3.Validity

------------------------------------------------------------------------
-- Dispatcher Result with Allocation
------------------------------------------------------------------------

module DispatcherResult {FS : FrameSemantics} (program-bound : ℕ) where
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open FrameSemantics FS

  record IRResultA {A B : Type}
                   (ir : IR A B)
                   (x : ⟦ A ⟧)
                   (s : LocState FS)
                   (alloc : AllocState {FS}) : Set where
    field
      result-loc : ValueLocation FS
      final-state : LocState FS
      final-alloc : AllocState {FS}
      result-valid : ValidAt final-alloc (eval ir x) result-loc final-state
      result-before : BeforeFrontier final-alloc result-loc
      rax-is-result : readReg (regs final-state) RAX ≡ result-loc
      not-halted : halted final-state ≡ false
      -- Frontier monotonicity: allocation only advances
      frame-preserved : current-frame final-alloc ≡ current-frame alloc
      slot-monotone : next-slot alloc ≤ next-slot final-alloc
      heap-monotone : next-heap-ref alloc ≤ next-heap-ref final-alloc
      -- Stack requirement bound: IR uses at most ir-stack-requirement slots
      slot-bounded : next-slot final-alloc ≤ next-slot alloc + ir-stack-requirement ir
      -- Capacity is preserved (frame size doesn't change within a frame)
      capacity-preserved : frame-capacity final-alloc ≡ frame-capacity alloc

------------------------------------------------------------------------
-- RecDispatcher: Recursive Dispatch Interface
------------------------------------------------------------------------

module RecDispatcherDef {FS : FrameSemantics} (program-bound : ℕ) where
  open ValidityDef {FS} program-bound
  open DispatcherResult {FS} program-bound
  open FrontierInvariant {FS}

  -- RecDispatcher allows dispatching to any IR smaller than bound
  -- NO Acc parameter - the main dispatcher handles Acc internally
  -- The pattern is: dispatcher constructs rec using (rs lt) from its Acc
  RecDispatcher : ℕ → Set
  RecDispatcher bound = ∀ {A B} (ir : IR A B) →
    ir-size ir < bound →
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS) (s : LocState FS)
    (alloc : AllocState {FS}) →
    ValidAt alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultA ir x s alloc

