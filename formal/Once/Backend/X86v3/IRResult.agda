------------------------------------------------------------------------
-- Once.Backend.X86v3.IRResult
--
-- IR execution result type for X86v3 dispatcher.
-- Separate module to avoid circular dependencies.
------------------------------------------------------------------------

module Once.Backend.X86v3.IRResult where

open import Data.Nat using (ℕ; _≤_; _<_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
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
      -- slot-bounded REMOVED: Using dynamic capacity threading instead (X86 pattern)
      -- Capacity is threaded via BodyCorrect.body-capacity for apply
      -- Capacity is preserved (frame size doesn't change within a frame)
      capacity-preserved : frame-capacity final-alloc ≡ frame-capacity alloc

      -- Stack reclamation: After IR completes, only the result needs to persist.
      -- Intermediate allocations can be reclaimed to free stack space.
      -- reclaimable-slot is the minimum next-slot that preserves the result.
      --
      -- For IRs that don't allocate (id, fst, snd, terminal):
      --   reclaimable-slot = next-slot alloc
      -- For IRs that allocate fresh (pair, curry):
      --   reclaimable-slot = next-slot alloc + result-slots
      -- For compose/apply: depends on structure
      reclaimable-slot : ℕ
      -- reclaimable-slot is between start and end
      reclaim-monotone : next-slot alloc ≤ reclaimable-slot
      reclaim-bounded : reclaimable-slot ≤ next-slot final-alloc
      -- Result location survives reclamation (it's before reclaimable-slot)
      reclaim-preserves-result : ∀ (fits : reclaimable-slot ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = reclaimable-slot ; slots-available = fits }) result-loc
      -- NOTE: reclaim-size-bound REMOVED (X86 pattern)
      -- X86 has no such constraint - capacity is threaded dynamically via caller.
      -- For apply, the body's capacity is carried in BodyCorrect.body-capacity.

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

