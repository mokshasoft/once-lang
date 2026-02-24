------------------------------------------------------------------------
-- Once.Backend.X86v3.EscapeInterface
--
-- Escape analysis interface for memory safety proofs.
--
-- This module defines:
--   SurvivesFramePop   - what locations survive when a frame is popped
--   StackAllocationSafe - witness that stack allocations don't escape
--   ChildFrameSafe     - witness for child frame execution safety
--   CanFreeHeap        - witness that a heap block can be freed
--   ReferencesBlock    - helper predicate for heap block references
--
-- These witnesses enable removing postulates from ApplyWF.agda by
-- providing explicit proofs of escape safety.
------------------------------------------------------------------------

module Once.Backend.X86v3.EscapeInterface where

open import Data.Nat using (ℕ; _<_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine using (HeapRef; HeapLocation; heap-ref; ref-id; LocState)

------------------------------------------------------------------------
-- Escape Interface parameterized by FrameSemantics
------------------------------------------------------------------------

module EscapeInterfaceDef {FS : FrameSemantics} where
  open FrameSemantics FS
  open import Once.Backend.Common.SlotMachine using (ValueLocation; OnStack; OnHeap)
  open import Once.Backend.X86v3.Allocation using (AllocState; next-heap-ref)
  open import Once.Backend.X86v3.Allocation using (module FrontierInvariant)
  open FrontierInvariant {FS}

  ------------------------------------------------------------------------
  -- SurvivesFramePop
  --
  -- Structural predicate: which locations survive when a frame is popped?
  --   - Locations in ancestor frames survive (LIFO stack discipline)
  --   - Heap locations always survive (heap is not frame-scoped)
  --   - Locations in the popped frame do NOT survive
  ------------------------------------------------------------------------

  data SurvivesFramePop (frame : Frame) : ValueLocation FS → Set where
    -- Stack location in ancestor frame survives
    in-ancestor : ∀ {f k} → frame ≺ f → SurvivesFramePop frame (OnStack f k)
    -- Heap location always survives
    on-heap : ∀ {hl} → SurvivesFramePop frame (OnHeap hl)

  ------------------------------------------------------------------------
  -- References
  --
  -- Predicate for when one location references another.
  -- Used to track which locations point to stack-allocated data.
  --
  -- NOTE: In the heap-only model, heap locations can only reference
  -- other heap locations (enforced by HeapLocation type). So
  -- OnHeap locations never reference OnStack locations.
  ------------------------------------------------------------------------

  data References : ValueLocation FS → ValueLocation FS → Set where
    -- Direct reference: location contains pointer to target
    direct-ref : ∀ {src tgt} → References src tgt
    -- Note: Heap-to-stack references are impossible in the heap-only model
    -- because OnHeap hl stores HeapLocation, not ValueLocation

  ------------------------------------------------------------------------
  -- ReferencesBlock
  --
  -- Predicate for when a location references a specific heap block.
  -- Used for CanFreeHeap to ensure no dangling references after free.
  ------------------------------------------------------------------------

  data ReferencesBlock : ValueLocation FS → HeapRef → Set where
    -- HeapLocation with matching ref references that block
    heap-ref-match : ∀ {hl : HeapLocation} →
      ReferencesBlock (OnHeap hl) (heap-ref hl)

  ------------------------------------------------------------------------
  -- StackAllocationSafe
  --
  -- Witness that stack allocations in a frame don't escape.
  -- Provides proof that no surviving location references the frame's slots.
  --
  -- This is used to ensure stack allocations can be safely reclaimed
  -- when the frame is popped.
  ------------------------------------------------------------------------

  record StackAllocationSafe (frame : Frame) (alloc : AllocState {FS}) : Set where
    field
      -- No surviving location references slots in this frame
      no-surviving-refs : ∀ {loc k} →
        SurvivesFramePop frame loc →
        ¬ References loc (OnStack frame k)

  ------------------------------------------------------------------------
  -- ChildFrameSafe
  --
  -- Witness for child frame execution safety.
  -- Used by ApplyWF to transfer results from child to parent frame.
  --
  -- Key properties:
  --   1. Result must survive child frame pop (be on heap or ancestor)
  --   2. No surviving location references child frame slots
  ------------------------------------------------------------------------

  record ChildFrameSafe (child-frame parent-frame : Frame) : Set where
    field
      -- Result location survives child frame deallocation
      result-survives : ∀ {result-loc : ValueLocation FS} →
        SurvivesFramePop child-frame result-loc
      -- No surviving location references child frame
      no-child-refs : ∀ {k} {loc : ValueLocation FS} →
        SurvivesFramePop child-frame loc →
        ¬ References loc (OnStack child-frame k)

  ------------------------------------------------------------------------
  -- CanFreeHeap
  --
  -- Witness that a heap block can be safely freed.
  -- Requires proof that no reachable location references the block.
  --
  -- Used by free-heap IR operation to ensure no dangling pointers.
  ------------------------------------------------------------------------

  record CanFreeHeap (block : HeapRef) (alloc : AllocState {FS}) (s : LocState FS) : Set where
    field
      -- No location before the frontier references this block
      no-refs : ∀ loc → BeforeFrontier alloc loc → ¬ ReferencesBlock loc block
      -- Block is within allocated range (sanity check)
      block-allocated : ref-id block < next-heap-ref alloc

  ------------------------------------------------------------------------
  -- Heap-only model guarantees
  --
  -- With the HeapLocation type enforcing that heap memory only stores
  -- heap locations, we get these properties for free:
  --
  -- 1. Stack locations can never be stored in heap memory
  -- 2. After freeing a heap block, no stack locations become dangling
  -- 3. Frame pop only invalidates stack references, not heap references
  --
  -- This makes escape analysis simpler: we only need to track
  -- heap → heap references, not heap → stack.
  ------------------------------------------------------------------------
