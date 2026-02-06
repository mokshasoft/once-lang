------------------------------------------------------------------------
-- Once.Backend.Common.FrameSemantics
--
-- Architecture-independent calling convention semantics.
--
-- This module defines the contract for stack frame ownership without
-- architecture-specific assumptions (no stack direction, no register names).
--
-- Key insight: At function entry, the stack is divided into two regions:
--   - Caller's frame: where the caller allocated the input
--   - Callee's frame: where the callee will allocate (sub sp, push, etc.)
--
-- These regions are disjoint, so callee operations preserve caller's data.
--
-- Architecture instantiation:
--   - X86-64 (stack grows down): InCallerFrame = addr ≥ boundary
--                                InCalleeFrame = addr < boundary
--   - Stack-grows-up arch:       InCallerFrame = addr ≤ boundary
--                                InCalleeFrame = addr > boundary
--
-- See: docs/formal/guides/frame-semantics.md (TODO)
------------------------------------------------------------------------

module Once.Backend.Common.FrameSemantics where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-- Import Addr from MemoryLayoutSemantics
open import Once.Backend.Common.MemoryLayoutSemantics using (Addr)

------------------------------------------------------------------------
-- FrameSemantics Interface
--
-- Architectures provide concrete instances with:
--   - Boundary type (typically Word, representing stack pointer at entry)
--   - InCallerFrame / InCalleeFrame predicates
--   - Proof that these regions are disjoint
------------------------------------------------------------------------

record FrameSemantics : Set₁ where
  field
    --------------------------------------------------------------------
    -- Boundary Type
    --
    -- The boundary between caller's frame and callee's frame.
    -- Typically the stack pointer value at function entry.
    --------------------------------------------------------------------

    Boundary : Set

    --------------------------------------------------------------------
    -- Frame Regions
    --
    -- Two disjoint regions of stack memory:
    --   - InCallerFrame: addresses owned by the caller
    --   - InCalleeFrame: addresses owned by the callee
    --
    -- No direction implied - each architecture defines what "caller's"
    -- and "callee's" means based on its stack growth direction.
    --------------------------------------------------------------------

    -- | Address is in caller's frame (allocated before call)
    InCallerFrame : Addr → Boundary → Set

    -- | Address is in callee's frame (allocated by callee via sub sp, push)
    InCalleeFrame : Addr → Boundary → Set

    --------------------------------------------------------------------
    -- Disjointness
    --
    -- The key property: caller's frame and callee's frame don't overlap.
    -- This ensures callee operations (writes to InCalleeFrame) preserve
    -- caller's data (in InCallerFrame).
    --------------------------------------------------------------------

    frames-disjoint : ∀ (addr : Addr) (b : Boundary) →
      InCallerFrame addr b →
      InCalleeFrame addr b →
      ⊥

    --------------------------------------------------------------------
    -- Decidability (optional but useful for proofs)
    --
    -- For any stack address, we can determine which frame it belongs to.
    -- This is useful for case analysis in proofs.
    --------------------------------------------------------------------

    -- Note: We might add decidability later if needed:
    -- frame-decidable : ∀ addr b → InStack addr →
    --                   InCallerFrame addr b ⊎ InCalleeFrame addr b

open FrameSemantics public

------------------------------------------------------------------------
-- Derived Properties
--
-- These follow from disjointness and are useful in proofs.
------------------------------------------------------------------------

-- | If an address is in caller's frame, it's not in callee's frame
caller-not-callee : ∀ (fs : FrameSemantics) (addr : Addr) (b : Boundary fs) →
  InCallerFrame fs addr b →
  InCalleeFrame fs addr b →
  ⊥
caller-not-callee fs = frames-disjoint fs

-- | If an address is in callee's frame, it's not in caller's frame
callee-not-caller : ∀ (fs : FrameSemantics) (addr : Addr) (b : Boundary fs) →
  InCalleeFrame fs addr b →
  InCallerFrame fs addr b →
  ⊥
callee-not-caller fs addr b in-callee in-caller =
  frames-disjoint fs addr b in-caller in-callee
