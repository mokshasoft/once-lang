------------------------------------------------------------------------
-- Once.Backend.X86v3.Allocation
--
-- Allocation model for SlotMachine POC.
--
-- Supports both stack and heap allocation:
--   - Stack: slots within current frame (for non-escaping values)
--   - Heap: fresh HeapRefs (for escaping values)
--
-- This models the output of escape analysis - the IR specifies
-- which allocation mode to use for each value.
------------------------------------------------------------------------

module Once.Backend.X86v3.Allocation where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <⇒≤; +-monoʳ-≤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine

------------------------------------------------------------------------
-- Allocation Mode (output of escape analysis)
------------------------------------------------------------------------

data AllocMode : Set where
  StackAlloc : AllocMode  -- Value doesn't escape, allocate on stack
  HeapAlloc  : AllocMode  -- Value escapes, allocate on heap

------------------------------------------------------------------------
-- Allocation State
--
-- Tracks available resources for allocation:
--   - Stack: current frame + next available slot + capacity
--   - Heap: next available HeapRef
------------------------------------------------------------------------

record AllocState {FS : FrameSemantics} : Set where
  constructor mkAllocState
  open FrameSemantics FS
  field
    -- Stack allocation state
    current-frame : Frame
    next-slot : ℕ
    frame-capacity : ℕ
    slots-available : next-slot ≤ frame-capacity

    -- Heap allocation state
    next-heap-ref : ℕ

open AllocState public

------------------------------------------------------------------------
-- Stack Allocation
--
-- Allocate n consecutive slots in the current frame.
-- Returns the base slot and updated state.
------------------------------------------------------------------------

module StackAllocation {FS : FrameSemantics} where
  open FrameSemantics FS

  -- Allocate n slots, returning base location
  stack-alloc : (as : AllocState {FS}) (n : ℕ) →
    next-slot as + n ≤ frame-capacity as →
    ValueLocation FS × AllocState {FS}
  stack-alloc as n fits =
    OnStack (current-frame as) (next-slot as) ,
    record as
      { next-slot = next-slot as + n
      ; slots-available = fits
      }

  -- The allocated location
  stack-alloc-loc : (as : AllocState {FS}) (n : ℕ) →
    (fits : next-slot as + n ≤ frame-capacity as) →
    ValueLocation FS
  stack-alloc-loc as n fits = proj₁ (stack-alloc as n fits)

  -- The updated state
  stack-alloc-state : (as : AllocState {FS}) (n : ℕ) →
    (fits : next-slot as + n ≤ frame-capacity as) →
    AllocState {FS}
  stack-alloc-state as n fits = proj₂ (stack-alloc as n fits)

  -- Key property: allocated slots are in the current frame
  stack-alloc-in-frame : (as : AllocState {FS}) (n : ℕ) →
    (fits : next-slot as + n ≤ frame-capacity as) →
    ∃[ slot ] stack-alloc-loc as n fits ≡ OnStack (current-frame as) slot
  stack-alloc-in-frame as n fits = next-slot as , refl

  -- Successive slots are at offset from base
  stack-alloc-offset : (as : AllocState {FS}) (n : ℕ) →
    (fits : next-slot as + n ≤ frame-capacity as) →
    (k : ℕ) → k < n →
    ValueLocation FS
  stack-alloc-offset as n fits k k<n =
    OnStack (current-frame as) (next-slot as + k)

------------------------------------------------------------------------
-- Heap Allocation
--
-- Allocate a fresh heap block of n slots.
-- Returns a fresh HeapRef and updated state.
------------------------------------------------------------------------

module HeapAllocation {FS : FrameSemantics} where

  -- Allocate heap block, returning base location
  heap-alloc : (as : AllocState {FS}) (n : ℕ) →
    ValueLocation FS × AllocState {FS}
  heap-alloc as n =
    OnHeap (mkHeapRef (next-heap-ref as)) 0 ,
    record as { next-heap-ref = suc (next-heap-ref as) }

  -- The allocated location
  heap-alloc-loc : (as : AllocState {FS}) (n : ℕ) → ValueLocation FS
  heap-alloc-loc as n = proj₁ (heap-alloc as n)

  -- The updated state
  heap-alloc-state : (as : AllocState {FS}) (n : ℕ) → AllocState {FS}
  heap-alloc-state as n = proj₂ (heap-alloc as n)

  -- Key property: new HeapRef is fresh (different from all previous)
  heap-alloc-fresh : (as : AllocState {FS}) (n : ℕ) →
    (old-ref : HeapRef) →
    ref-id old-ref < next-heap-ref as →
    mkHeapRef (next-heap-ref as) ≢ old-ref
  heap-alloc-fresh as n old-ref old<next eq =
    <⇒≢ old<next (cong ref-id (sym eq))
    where
      open import Data.Nat.Properties using (<⇒≢)

------------------------------------------------------------------------
-- Unified Allocation Interface
------------------------------------------------------------------------

module Allocator {FS : FrameSemantics} where
  open StackAllocation {FS}
  open HeapAllocation {FS}

  -- Allocate based on mode
  -- For stack: requires proof that slots fit
  -- For heap: always succeeds

  record AllocResult (as : AllocState {FS}) (n : ℕ) : Set where
    field
      location : ValueLocation FS
      new-state : AllocState {FS}
      -- The location points to n consecutive slots
      -- sucLoc^k location is valid for k < n

  -- Stack allocation (requires capacity proof)
  alloc-stack : (as : AllocState {FS}) (n : ℕ) →
    next-slot as + n ≤ frame-capacity as →
    AllocResult as n
  alloc-stack as n fits = record
    { location = stack-alloc-loc as n fits
    ; new-state = stack-alloc-state as n fits
    }

  -- Heap allocation (always succeeds)
  alloc-heap : (as : AllocState {FS}) (n : ℕ) → AllocResult as n
  alloc-heap as n = record
    { location = heap-alloc-loc as n
    ; new-state = heap-alloc-state as n
    }

------------------------------------------------------------------------
-- Extended Machine State (with allocation)
------------------------------------------------------------------------

record LocStateWithAlloc {FS : FrameSemantics} : Set where
  constructor mkLocStateWithAlloc
  field
    machine-state : LocState FS
    alloc-state : AllocState {FS}

open LocStateWithAlloc public

------------------------------------------------------------------------
-- Memory Write Operations
--
-- Write a ValueLocation pointer to memory at a given location.
------------------------------------------------------------------------

module WriteOps {FS : FrameSemantics} where
  open MemOps {FS}
  open FrameSemantics FS

  -- Write to a stack slot
  write-stack-slot : LocState FS → Frame → ℕ → ValueLocation FS → LocState FS
  write-stack-slot s frame slot val =
    record s { stackMem = writeStackMem (stackMem s) frame slot val }

  -- Write to a heap slot
  write-heap-slot : LocState FS → HeapRef → ℕ → ValueLocation FS → LocState FS
  write-heap-slot s ref offset val =
    record s { heapMem = writeHeapMem (heapMem s) ref offset val }

  -- Write to a ValueLocation
  write-loc : LocState FS → ValueLocation FS → ValueLocation FS → LocState FS
  write-loc s (OnStack f k) val = write-stack-slot s f k val
  write-loc s (OnHeap r o) val = write-heap-slot s r o val

  -- Write preserves reads at different locations (stack)
  write-stack-preserves-diff : ∀ s f₁ k₁ f₂ k₂ val →
    (f₁ ≢ f₂) ⊎ (k₁ ≢ k₂) →
    stackMem (write-stack-slot s f₁ k₁ val) f₂ k₂ ≡ stackMem s f₂ k₂
  write-stack-preserves-diff s f₁ k₁ f₂ k₂ val (inj₁ f≢f)
    with _≟F_ f₁ f₂
  ... | yes refl = ⊥-elim (f≢f refl)
  ... | no _ = refl
  write-stack-preserves-diff s f₁ k₁ f₂ k₂ val (inj₂ k≢k)
    with _≟F_ f₁ f₂ | Data.Nat._≟_ k₁ k₂
  ... | yes _ | yes refl = ⊥-elim (k≢k refl)
  ... | yes _ | no _ = refl
  ... | no _ | _ = refl

  -- Write then read same location
  write-stack-read-same : ∀ s f k val →
    stackMem (write-stack-slot s f k val) f k ≡ just val
  write-stack-read-same s f k val with _≟F_ f f | Data.Nat._≟_ k k
  ... | yes _ | yes _ = refl
  ... | yes _ | no k≢k = ⊥-elim (k≢k refl)
  ... | no f≢f | _ = ⊥-elim (f≢f refl)

  -- Similar for heap
  write-heap-read-same : ∀ s r o val →
    heapMem (write-heap-slot s r o val) r o ≡ just val
  write-heap-read-same s r o val with r ≟H r | Data.Nat._≟_ o o
  ... | yes _ | yes _ = refl
  ... | yes _ | no o≢o = ⊥-elim (o≢o refl)
  ... | no r≢r | _ = ⊥-elim (r≢r refl)

------------------------------------------------------------------------
-- Allocation Frontier Invariant
--
-- A location is "before" the allocation frontier if:
--   - Stack: slot index < next-slot (for current frame)
--   - Heap: ref-id < next-heap-ref
--
-- All valid locations are before the frontier.
------------------------------------------------------------------------

module FrontierInvariant {FS : FrameSemantics} where
  open FrameSemantics FS
  open MemOps {FS}
  open import Data.Nat.Properties using (≤-trans; m≤m+n; n≤1+n; <⇒≢)

  -- Location is before allocation frontier
  data BeforeFrontier (alloc : AllocState {FS}) : ValueLocation FS → Set where
    stack-before : ∀ {f k} →
      f ≡ current-frame alloc →
      k < next-slot alloc →
      BeforeFrontier alloc (OnStack f k)

    stack-other-frame : ∀ {f k} →
      f ≢ current-frame alloc →
      BeforeFrontier alloc (OnStack f k)

    heap-before : ∀ {r o} →
      ref-id r < next-heap-ref alloc →
      BeforeFrontier alloc (OnHeap r o)

  -- Fresh allocation is after all existing locations
  fresh-stack-after : ∀ (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    loc ≢ OnStack (current-frame alloc) (next-slot alloc)
  fresh-stack-after alloc (OnStack f k) (stack-before refl k<next) eq
    with eq
  ... | refl = (<⇒≢ k<next) refl
  fresh-stack-after alloc (OnStack f k) (stack-other-frame f≢cf) eq
    with eq
  ... | refl = f≢cf refl
  fresh-stack-after alloc (OnHeap r o) (heap-before _) ()

  fresh-heap-after : ∀ (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    loc ≢ OnHeap (mkHeapRef (next-heap-ref alloc)) 0
  fresh-heap-after alloc (OnStack f k) _ ()
  fresh-heap-after alloc (OnHeap r o) (heap-before r<next) eq
    with eq
  ... | refl = (<⇒≢ r<next) refl

  -- Allocation advances frontier
  stack-alloc-advances : ∀ (alloc : AllocState {FS}) n
    (fits : next-slot alloc + n ≤ frame-capacity alloc) →
    ∀ loc → BeforeFrontier alloc loc →
    BeforeFrontier (record alloc { next-slot = next-slot alloc + n ; slots-available = fits }) loc
  stack-alloc-advances alloc n fits (OnStack f k) (stack-before refl k<next) =
    stack-before refl (≤-trans k<next (m≤m+n (next-slot alloc) n))
  stack-alloc-advances alloc n fits (OnStack f k) (stack-other-frame f≢cf) =
    stack-other-frame f≢cf
  stack-alloc-advances alloc n fits (OnHeap r o) (heap-before r<next) =
    heap-before r<next

  heap-alloc-advances : ∀ (alloc : AllocState {FS}) →
    ∀ loc → BeforeFrontier alloc loc →
    BeforeFrontier (record alloc { next-heap-ref = suc (next-heap-ref alloc) }) loc
  heap-alloc-advances alloc (OnStack f k) (stack-before eq k<next) =
    stack-before eq k<next
  heap-alloc-advances alloc (OnStack f k) (stack-other-frame f≢cf) =
    stack-other-frame f≢cf
  heap-alloc-advances alloc (OnHeap r o) (heap-before r<next) =
    heap-before (≤-trans r<next (n≤1+n (next-heap-ref alloc)))

  -- General frontier monotonicity: if frontier advances, old locations are still before
  -- This is useful when alloc' is derived from alloc through arbitrary operations
  frontier-monotone : ∀ (alloc alloc' : AllocState {FS}) →
    current-frame alloc ≡ current-frame alloc' →
    next-slot alloc ≤ next-slot alloc' →
    next-heap-ref alloc ≤ next-heap-ref alloc' →
    ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc' loc
  frontier-monotone alloc alloc' cf-eq slot-≤ heap-≤ (OnStack f k) (stack-before f-eq k<slot) =
    stack-before (trans f-eq cf-eq) (<-≤-trans k<slot slot-≤)
    where open import Data.Nat.Properties using (<-≤-trans)
  frontier-monotone alloc alloc' cf-eq slot-≤ heap-≤ (OnStack f k) (stack-other-frame f≢cf) =
    stack-other-frame (λ eq → f≢cf (trans eq (sym cf-eq)))
  frontier-monotone alloc alloc' cf-eq slot-≤ heap-≤ (OnHeap r o) (heap-before r<heap) =
    heap-before (<-≤-trans r<heap heap-≤)
    where open import Data.Nat.Properties using (<-≤-trans)

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--
--   AllocMode     : StackAlloc | HeapAlloc
--   AllocState    : tracking available slots/refs
--
--   StackAllocation:
--     stack-alloc      : allocate n stack slots
--     stack-alloc-in-frame : result is in current frame
--
--   HeapAllocation:
--     heap-alloc       : allocate n heap slots
--     heap-alloc-fresh : new ref differs from old refs
--
--   WriteOps:
--     write-loc              : write pointer to location
--     write-stack-read-same  : read back what we wrote
--     write-heap-read-same   : read back what we wrote
--
--   FrontierInvariant:
--     BeforeFrontier      : location is before allocation frontier
--     fresh-stack-after   : new stack slot ≠ old locations
--     fresh-heap-after    : new HeapRef ≠ old locations
--     stack-alloc-advances: old locations stay before new frontier
--     heap-alloc-advances : same for heap
--
-- NO POSTULATES - all operations are concrete.
------------------------------------------------------------------------
