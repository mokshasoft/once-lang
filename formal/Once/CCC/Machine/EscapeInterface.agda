-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.EscapeInterface
--
-- Escape analysis interface for memory safety proofs.
--
-- MINIMAL INTERFACE:
--   SurvivesFramePop  - structural predicate (what survives frame pop)
--   derive-survives   - derives SurvivesFramePop from escape obligation
--
-- The escape obligation is simply:
--   "Fresh child-frame stack allocations don't escape"
--
-- This is expressed as a function that the compiler/escape analysis provides.
-- It does NOT expose BeforeFrontier to the outside world.
------------------------------------------------------------------------

module Once.CCC.Machine.EscapeInterface where

open import Data.Nat using (ℕ; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; subst)
open import Relation.Nullary using (¬_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (HeapRef; HeapLocation; heap-ref; ref-id; LocState)

------------------------------------------------------------------------
-- Escape Interface parameterized by FrameSemantics
------------------------------------------------------------------------

module EscapeInterfaceDef {FS : FrameSemantics} where
  open FrameSemantics FS
  open import Once.CCC.Machine.SMCore using (ValueLocation; AtStack; AtDynamic)
  open import Once.CCC.Machine.Allocation using (AllocState; next-heap-ref; current-frame; next-slot)
  open import Once.CCC.Machine.Allocation using (module FrontierInvariant)
  open FrontierInvariant {FS}

  ------------------------------------------------------------------------
  -- SurvivesFramePop
  --
  -- STRUCTURAL predicate: which locations survive when a frame is popped?
  --   - Locations in ancestor frames survive (LIFO stack discipline)
  --   - Heap locations always survive (heap is not frame-scoped)
  --   - Locations in the popped frame do NOT survive
  --
  -- This is the CLEAN interface - no internal allocation details exposed.
  ------------------------------------------------------------------------

  data SurvivesFramePop (frame : Frame) : ValueLocation FS → Set where
    -- Stack location in ancestor frame survives
    in-ancestor : ∀ {f k} → frame ≺ f → SurvivesFramePop frame (AtStack f k)
    -- Heap location always survives
    on-heap : ∀ {hl} → SurvivesFramePop frame (AtDynamic hl)

  ------------------------------------------------------------------------
  -- Derive SurvivesFramePop from BeforeFrontier
  --
  -- Given:
  --   1. An escape obligation (stack-before case is impossible)
  --   2. BeforeFrontier proof for result location
  --
  -- Produces: SurvivesFramePop proof
  --
  -- The escape obligation is the ONLY thing the compiler needs to provide.
  -- It says: "Fresh child-frame stack allocations don't appear as results."
  --
  -- Internally, BeforeFrontier has three cases:
  --   - AtDynamic: trivially survives (on-heap)
  --   - AtStack via stack-ancestor: survives (in-ancestor)
  --   - AtStack via stack-before: eliminated by escape obligation
  ------------------------------------------------------------------------

  -- Derive SurvivesFramePop for any valid result location
  derive-survives : ∀ (child-frame : Frame) (body-final : AllocState {FS})
    (result-loc : ValueLocation FS) →
    -- Escape obligation: fresh child-frame allocations don't escape
    -- (eliminates stack-before case)
    (∀ {k} → k < next-slot body-final → ⊥) →
    -- Frame equality (body preserves frame)
    current-frame body-final ≡ child-frame →
    -- Result is valid in body's final allocation
    BeforeFrontier body-final result-loc →
    -- Result survives child frame pop
    SurvivesFramePop child-frame result-loc
  derive-survives child-frame body-final (AtDynamic hl) _ _ _ = on-heap
  derive-survives child-frame body-final (AtStack f k) escape-obl cf-eq (stack-before f≡cf k<ns) =
    -- stack-before gives: f ≡ current-frame body-final AND k < next-slot body-final
    -- Escape obligation eliminates this case
    ⊥-elim (escape-obl k<ns)
  derive-survives child-frame body-final (AtStack f k) escape-obl cf-eq (stack-ancestor cf≺f _) =
    -- stack-ancestor gives: current-frame body-final ≺ f
    -- Since current-frame body-final ≡ child-frame, we have child-frame ≺ f
    in-ancestor (subst (_≺ f) cf-eq cf≺f)

  ------------------------------------------------------------------------
  -- ReferencesBlock
  --
  -- Predicate for when a location references a specific heap block.
  -- Used for CanFreeHeap to ensure no dangling references after free.
  ------------------------------------------------------------------------

  data ReferencesBlock : ValueLocation FS → HeapRef → Set where
    -- HeapLocation with matching ref references that block
    heap-ref-match : ∀ {hl : HeapLocation} →
      ReferencesBlock (AtDynamic hl) (heap-ref hl)

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
  -- Summary: Minimal Interface to Compiler
  --
  -- The compiler/escape analysis provides ONE thing:
  --
  --   escape-obligation : ∀ {k} → k < slot-bound → ⊥
  --
  -- This says: "For the result location, if it's AtStack child-frame k
  -- with k < slot-bound (freshly allocated in child frame), that's
  -- impossible."
  --
  -- The derive-survives function uses this to produce SurvivesFramePop,
  -- which is the clean structural predicate used elsewhere.
  --
  -- BeforeFrontier is INTERNAL to this module - not exposed to compiler.
  ------------------------------------------------------------------------