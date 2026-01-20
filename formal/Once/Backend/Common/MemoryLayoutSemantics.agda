------------------------------------------------------------------------
-- Once.Backend.Common.MemoryLayoutSemantics
--
-- Memory layout interface and types.
--
-- This module provides:
--   1. Core types (Addr, RegionBounds)
--   2. MemoryLayout record (bundles bounds + disjointness)
--   3. Parameterized definitions (InStack, InHeap, InCode)
--   4. Default postulate-based layout for backward compatibility
--
-- For zero-postulates architecture, see X86.Layout which provides
-- concrete bounds where all properties are proven.
------------------------------------------------------------------------

module Once.Backend.Common.MemoryLayoutSemantics where

open import Data.Nat using (ℕ; zero; _≤_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Product using (_×_)

-- Import Memory type from Common.Memory
open import Once.Backend.Common.Memory using (Word) public

------------------------------------------------------------------------
-- Address Type
------------------------------------------------------------------------

Addr : Set
Addr = ℕ

------------------------------------------------------------------------
-- Region Bounds (CORE ABSTRACTION)
------------------------------------------------------------------------

-- | A region is defined by its address interval [lower, upper]
record RegionBounds : Set where
  field
    lower : Addr
    upper : Addr
    bounds-valid : lower ≤ upper

open RegionBounds public

------------------------------------------------------------------------
-- Memory Layout Record
--
-- Bundles region bounds with disjointness proof.
-- Architecture-specific modules provide concrete instances.
------------------------------------------------------------------------

-- | Region membership predicates (parameterized by bounds)
InRegion : RegionBounds → Addr → Set
InRegion rb a = lower rb ≤ a × a ≤ upper rb

-- | Complete memory layout: bounds + disjointness
record MemoryLayout : Set where
  field
    stack-bounds : RegionBounds
    heap-bounds  : RegionBounds
    code-bounds  : RegionBounds
    intervals-disjoint : ∀ a →
      ¬ (InRegion stack-bounds a × InRegion heap-bounds a) ×
      ¬ (InRegion stack-bounds a × InRegion code-bounds a) ×
      ¬ (InRegion heap-bounds a × InRegion code-bounds a)

-- Note: Not opening MemoryLayout to avoid name clashes with backward-compat defs

------------------------------------------------------------------------
-- Default Layout (postulate-based, for backward compatibility)
--
-- JUSTIFICATION: Runtime initializes memory with non-overlapping regions.
-- This default uses postulates; concrete layouts (X86.Layout) use proofs.
------------------------------------------------------------------------

postulate
  default-stack-bounds : RegionBounds
  default-heap-bounds  : RegionBounds
  default-code-bounds  : RegionBounds
  default-intervals-disjoint : ∀ a →
    ¬ (InRegion default-stack-bounds a × InRegion default-heap-bounds a) ×
    ¬ (InRegion default-stack-bounds a × InRegion default-code-bounds a) ×
    ¬ (InRegion default-heap-bounds a × InRegion default-code-bounds a)

defaultLayout : MemoryLayout
defaultLayout = record
  { stack-bounds = default-stack-bounds
  ; heap-bounds = default-heap-bounds
  ; code-bounds = default-code-bounds
  ; intervals-disjoint = default-intervals-disjoint
  }

------------------------------------------------------------------------
-- Backward Compatibility: Use default layout
--
-- These definitions use the default (postulate-based) layout.
-- New code should use parameterized modules with concrete layouts.
------------------------------------------------------------------------

-- Re-export bounds from default layout
stack-bounds : RegionBounds
stack-bounds = MemoryLayout.stack-bounds defaultLayout

heap-bounds : RegionBounds
heap-bounds = MemoryLayout.heap-bounds defaultLayout

code-bounds : RegionBounds
code-bounds = MemoryLayout.code-bounds defaultLayout

-- | Address is in stack if within [lower, upper]
InStack : Addr → Set
InStack a = lower stack-bounds ≤ a × a ≤ upper stack-bounds

-- | Address is in heap if within [lower, upper]
InHeap : Addr → Set
InHeap a = lower heap-bounds ≤ a × a ≤ upper heap-bounds

-- | Address is in code if within [lower, upper]
InCode : Addr → Set
InCode a = lower code-bounds ≤ a × a ≤ upper code-bounds

intervals-disjoint : ∀ a →
  ¬ (InStack a × InHeap a) ×
  ¬ (InStack a × InCode a) ×
  ¬ (InHeap a × InCode a)
intervals-disjoint = MemoryLayout.intervals-disjoint defaultLayout

------------------------------------------------------------------------
-- Abstract Address Types (in-region by construction)
--
-- These types bundle an address with proof of region membership.
-- Using these types guarantees addresses are in the correct region
-- without carrying proofs separately.
------------------------------------------------------------------------

-- | Stack address: in stack region by construction
-- Note: Field names match existing StackPointer for compatibility
record StackAddr : Set where
  constructor stack-addr
  field
    addr : Addr
    in-stack : InStack addr

open StackAddr public

-- | Heap address: in heap region by construction
-- Note: Field name 'haddr' matches existing HeapPointer
record HeapAddr : Set where
  constructor heap-addr
  field
    haddr : Addr
    in-heap : InHeap haddr

open HeapAddr public

-- | Code address: in code region by construction
record CodeAddr : Set where
  constructor code-addr
  field
    addr : Addr
    in-code : InCode addr

open CodeAddr public

------------------------------------------------------------------------
-- Boundary Conversions
--
-- Use these at the edges where abstract addresses meet concrete ℕ.
------------------------------------------------------------------------

-- | Enter abstract world (requires proof)
from-raw-stack : (a : Addr) → InStack a → StackAddr
from-raw-stack a proof = stack-addr a proof

from-raw-heap : (a : Addr) → InHeap a → HeapAddr
from-raw-heap a proof = heap-addr a proof

from-raw-code : (a : Addr) → InCode a → CodeAddr
from-raw-code a proof = code-addr a proof

-- | Exit abstract world (extract raw address)
to-raw-stack : StackAddr → Addr
to-raw-stack sa = StackAddr.addr sa

to-raw-heap : HeapAddr → Addr
to-raw-heap ha = HeapAddr.haddr ha

to-raw-code : CodeAddr → Addr
to-raw-code ca = CodeAddr.addr ca

------------------------------------------------------------------------
-- Stack Growth Interface
--
-- Architecture provides an implementation of this interface.
-- This abstracts over word size and growth direction.
--
-- Key abstractions:
--   - grow: slot address computation (direction-independent)
--   - FramePreserved: "frame won't be clobbered by writes at stack-ptr"
--   - StackGrew: "stack expanded from old to new"
--
-- See: docs/formal/guides/architecture-independent-stack-abstraction.md
------------------------------------------------------------------------

-- | Abstract interface for stack slot addressing and frame preservation
-- The architecture provides:
--   - grow: how to compute address at offset k from base
--   - FramePreserved: when a frame is safe from stack writes
--   - StackGrew: when the stack has grown
--   - proofs that these satisfy required properties
record StackGrowth : Set₁ where
  field
    --------------------------------------------------------------------
    -- Slot Address Computation (pure arithmetic properties)
    --------------------------------------------------------------------

    -- | Compute address at slot offset k from base address
    grow : Addr → ℕ → Addr

    -- | Growing by zero is identity (origin slot is at base)
    grow-identity : ∀ a → grow a zero ≡ a

    -- | Different offsets yield different addresses
    grow-injective : ∀ a k₁ k₂ → k₁ ≢ k₂ → grow a k₁ ≢ grow a k₂

    -- | Different base addresses yield different slot addresses (same offset)
    grow-addr-injective : ∀ a₁ a₂ k → a₁ ≢ a₂ → grow a₁ k ≢ grow a₂ k

    --------------------------------------------------------------------
    -- Region Preservation
    --
    -- NOTE: This is a CAPACITY property, not pure arithmetic.
    -- It says "growing stays in stack region", which requires sufficient
    -- stack capacity. In the zero-postulates architecture, this is
    -- derived from StackCapacity at each use site.
    --
    -- For backward compatibility, we keep it here but it should be
    -- proven from capacity evidence, not postulated.
    --------------------------------------------------------------------

    -- | Growth preserves stack region membership
    -- DEPRECATION: This will be removed; use StackCapacity-based proofs
    grow-preserves-region : ∀ a k → InStack a → InStack (grow a k)

    --------------------------------------------------------------------
    -- Frame Preservation (Abstract Ordering)
    --
    -- FramePreserved frame stack-ptr means:
    --   "Memory at frame (and its slots) won't be clobbered by
    --    stack operations at stack-ptr"
    --
    -- X86 instantiation: FramePreserved = _≥_ (frame >= stack-ptr)
    -- Upward-growth arch: FramePreserved = _≤_ (frame <= stack-ptr)
    --------------------------------------------------------------------

    -- | Frame is preserved when writing at/below stack-ptr
    FramePreserved : Addr → Addr → Set

    -- | Stack grew from old position to new position
    -- X86: StackGrew old new = new ≤ old (stack ptr decreased)
    -- Upward: StackGrew old new = new ≥ old (stack ptr increased)
    StackGrew : Addr → Addr → Set

    -- | Preserved frames stay preserved when stack grows
    frame-preserved-under-growth : ∀ frame old-sp new-sp →
      FramePreserved frame old-sp →
      StackGrew old-sp new-sp →
      FramePreserved frame new-sp

    -- | Slots in a preserved frame are also preserved
    slot-in-preserved-frame : ∀ frame k sp →
      FramePreserved frame sp →
      FramePreserved (grow frame k) sp
