------------------------------------------------------------------------
-- Once.Backend.Common.OwnershipSemantics
--
-- Architecture-independent ownership semantics interface.
--
-- This module defines the contract for memory ownership tracking.
-- The key insight: ownership is about WHO is responsible for data,
-- not WHERE data is stored. This enables preservation proofs.
--
-- Architecture instantiation must provide:
--   - Frame type (from FrameSemantics)
--   - ValidAt predicate (value validity at address)
--   - Owner type with Caller constructor
--   - OwnedBy predicate (ownership indexed by ValidAt)
--   - init-input-owned: trust boundary postulate for program entry
--
-- TRUST BOUNDARY:
--   The init-input-owned field is the ONLY ownership assumption.
--   Internal function calls PROVE ownership from compilation structure.
--   This isolates the trust to: "runtime places input correctly"
--
-- See: docs/formal/guides/slot-based-ownership-architecture.md
------------------------------------------------------------------------

module Once.Backend.Common.OwnershipSemantics where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Import common types
open import Once.Type using (Type)
open import Once.Backend.Common.MemoryLayoutSemantics using (Addr)
open import Once.Backend.Common.Memory using (Memory; Word)

------------------------------------------------------------------------
-- OwnershipSemantics Interface
--
-- Defines the contract for ownership tracking. Each architecture
-- instantiates this with its specific types and provides the
-- init-input-owned postulate.
------------------------------------------------------------------------

record OwnershipSemantics (⦦_⦧ : Type → Set) : Set₁ where
  field
    --------------------------------------------------------------------
    -- Frame Type (from FrameSemantics)
    --
    -- A Frame identifies a stack frame. Ownership is relative to
    -- the caller's frame at function entry.
    --------------------------------------------------------------------

    Frame : Set

    --------------------------------------------------------------------
    -- Validity Predicate
    --
    -- ValidAt v addr m means semantic value v is valid at address
    -- addr in memory m. This is architecture-specific because it
    -- depends on encoding and memory layout.
    --------------------------------------------------------------------

    ValidAt : ∀ {A : Type} → ⦦ A ⦧ → Addr → Memory → Set

    --------------------------------------------------------------------
    -- Owner Type
    --
    -- Caller  = Data belongs to caller, must be preserved
    -- Current = Data belongs to us, may be modified
    --------------------------------------------------------------------

    Owner : Set
    Caller : Owner

    --------------------------------------------------------------------
    -- Ownership Predicate
    --
    -- OwnedBy owner va frame means the data proven valid by va
    -- is owned by owner, relative to caller-frame.
    --
    -- For Caller ownership:
    --   - Stack data: at exact slot in caller's frame
    --   - Heap data: preserved by region separation
    --------------------------------------------------------------------

    OwnedBy : (owner : Owner) →
              {A : Type} → {v : ⦦ A ⦧} → {addr : Addr} → {m : Memory} →
              ValidAt {A} v addr m →
              Frame →
              Set

    --------------------------------------------------------------------
    -- Initial Ownership (TRUST BOUNDARY)
    --
    -- At program entry, the input is owned by the "caller"
    -- (the OS/runtime that invoked the program).
    --
    -- This is the ONLY ownership postulate in the entire system.
    -- Internal function calls PROVE ownership from compilation.
    --
    -- Why this is safe:
    --   - The runtime places arguments per calling convention
    --   - We trust this initial setup is correct
    --   - All subsequent ownership is derived from code structure
    --------------------------------------------------------------------

    init-input-owned : ∀ {A : Type} {v : ⦦ A ⦧} {addr : Addr} {m : Memory}
      (init-frame : Frame) →
      (va : ValidAt {A} v addr m) →
      OwnedBy Caller va init-frame

open OwnershipSemantics public
