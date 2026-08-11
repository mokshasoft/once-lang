-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Memory.HeapAddress
--
-- Language-agnostic heap address types: HeapRef, HeapOffset,
-- HeapLocation. These are pure data types — no CCC, no allocator,
-- no allocator-state. They define what a heap address *is*, so both
-- the abstract trace layer (SMCore) and the allocator can consume them
-- without depending on each other.
--
-- Previously defined inside Once.CCC.Machine.SMCore. Lifted here so
-- Once.Allocator.AbstractInstance can depend on heap addresses
-- without importing SMCore.
------------------------------------------------------------------------

module Once.Memory.HeapAddress where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (_≟_)

------------------------------------------------------------------------
-- HeapOffset: position within a heap block
------------------------------------------------------------------------

HeapOffset : Set
HeapOffset = ℕ

------------------------------------------------------------------------
-- HeapRef: opaque reference to a heap block
------------------------------------------------------------------------

record HeapRef : Set where
  constructor mkHeapRef
  field
    ref-id : ℕ

open HeapRef public

_≟H_ : (h₁ h₂ : HeapRef) → Dec (h₁ ≡ h₂)
mkHeapRef n₁ ≟H mkHeapRef n₂ with n₁ ≟ n₂
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }

------------------------------------------------------------------------
-- HeapLocation: a HeapRef + HeapOffset
--
-- Encapsulates HeapRef + HeapOffset so heap-allocated values can only
-- reference other heap locations, never stack locations. By using
-- HeapLocation as the unique address type for heap reads/writes, we
-- structurally prevent storing stack references in heap memory.
------------------------------------------------------------------------

record HeapLocation : Set where
  constructor heap-loc
  field
    heap-ref : HeapRef
    heap-offset : HeapOffset

open HeapLocation public

-- Decidable equality for HeapLocation. Inner Dec results are
-- explicitly enumerated via a top-level helper to avoid the with-
-- block case-tree artifact under --exact-split.
≟HL-aux : ∀ {r₁ r₂ o₁ o₂}
        → Dec (r₁ ≡ r₂) → Dec (o₁ ≡ o₂)
        → Dec (heap-loc r₁ o₁ ≡ heap-loc r₂ o₂)
≟HL-aux (yes refl) (yes refl) = yes refl
≟HL-aux (yes refl) (no o≢o)   = no λ { refl → o≢o refl }
≟HL-aux (no r≢r)   (yes _)    = no λ { refl → r≢r refl }
≟HL-aux (no r≢r)   (no _)     = no λ { refl → r≢r refl }

_≟HL_ : (hl₁ hl₂ : HeapLocation) → Dec (hl₁ ≡ hl₂)
heap-loc r₁ o₁ ≟HL heap-loc r₂ o₂ = ≟HL-aux (r₁ ≟H r₂) (o₁ ≟ o₂)

-- Project a HeapLocation to its HeapRef.
hl-ref : HeapLocation → HeapRef
hl-ref = heap-ref

------------------------------------------------------------------------
-- Offset arithmetic on HeapLocation
------------------------------------------------------------------------

sucHL : HeapLocation → HeapLocation
sucHL (heap-loc r o) = heap-loc r (suc o)

offsetHL : HeapLocation → ℕ → HeapLocation
offsetHL (heap-loc r o) n = heap-loc r (n + o)
