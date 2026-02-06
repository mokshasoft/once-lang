------------------------------------------------------------------------
-- Once.Backend.X86.OwnershipInstantiation
--
-- X86-64 instantiation of OwnershipSemantics.
--
-- This module provides the concrete instantiation of the
-- architecture-independent OwnershipSemantics interface for X86-64.
--
-- Separated from Ownership.agda to avoid circular imports:
--   - Ownership.agda defines Frame, Owner, OwnedBy, ValidAt
--   - InitState.agda imports Ownership and defines init-input-owned
--   - This module imports both and creates the instantiation
------------------------------------------------------------------------

module Once.Backend.X86.OwnershipInstantiation where

open import Once.Platform.X86-64 using (⟦_⟧)

-- Import architecture-independent interface
open import Once.Backend.Common.OwnershipSemantics as OS
  using (OwnershipSemantics)

-- Import X86 ownership types
open import Once.Backend.X86.Correct.Ownership
  using (Frame; Owner; Caller; OwnedBy)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)

-- Import the trust boundary postulate
open import Once.Backend.X86.Correct.InitState using (init-input-owned)

------------------------------------------------------------------------
-- X86-64 OwnershipSemantics Instance
------------------------------------------------------------------------

x86-ownership-semantics : OwnershipSemantics ⟦_⟧
x86-ownership-semantics = record
  { Frame = Frame
  ; ValidAt = ValidAt
  ; Owner = Owner
  ; Caller = Caller
  ; OwnedBy = OwnedBy
  ; init-input-owned = init-input-owned
  }

-- Re-export for convenience
open OwnershipSemantics x86-ownership-semantics public
  renaming ( Frame to X86-Frame
           ; ValidAt to X86-ValidAt
           ; Owner to X86-Owner
           ; Caller to X86-Caller
           ; OwnedBy to X86-OwnedBy
           ; init-input-owned to X86-init-input-owned
           )
