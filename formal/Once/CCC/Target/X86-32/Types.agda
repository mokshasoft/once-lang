-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.Types
--
-- x86-32 (IA-32) type layout calculations.
--
-- This module provides:
--   - stack-type-slots: Stack slot counts for types
--   - heap-type-slots: Heap slot counts for types
--
-- Key difference from x86-64:
--   - 4-byte slots instead of 8-byte slots
--   - Same logical slot counts (pointers still fit in one slot)
--
-- Generic semantic interpretation (⟦_⟧, sem-*) is in Once.Sem.
-- This module re-exports Once.Sem for backwards compatibility.
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.Types where

open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Re-export Type and Quantity from Once.Type
------------------------------------------------------------------------

open import Once.Type public
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Eff; Fix; Int; Float; Str; Buffer; TVar;
         Quantity; Zero; One; Many;
         _⊸_; _⇒_; _⇒₀_; IO)

------------------------------------------------------------------------
-- Re-export generic semantics from Once.Sem
------------------------------------------------------------------------

open import Once.Semantics.Machine public
  using (⟦_⟧; ⟦Fix⟧; wrap; unwrap;
         sem-fst; sem-snd; sem-pair;
         sem-inl; sem-inr; sem-case;
         sem-fold; sem-unfold;
         sem-fst-pair; sem-snd-pair;
         sem-case-inl; sem-case-inr;
         sem-unfold-fold; sem-fold-unfold)

-- Legacy alias
pair : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A * B ⟧
pair = sem-pair

------------------------------------------------------------------------
-- Type Slots: Memory representation sizes (X86-32-SPECIFIC)
--
-- Reference-based model: All values accessed by pointer.
-- x86-32 uses 4-byte pointers (vs 8 bytes for x86-64).
--
-- Note: Slot counts are the SAME as x86-64 because we're counting
-- logical slots (pointers), not bytes. Each slot is just 4 bytes
-- instead of 8 bytes on x86-32.
------------------------------------------------------------------------

-- Stack slot counts (reference-based, 4 bytes per slot)
stack-type-slots : Type → ℕ
stack-type-slots Unit = 0
stack-type-slots Void = 0
stack-type-slots Int = 1
stack-type-slots Float = 1
stack-type-slots Str = 1          -- pointer to string data
stack-type-slots Buffer = 1       -- pointer to buffer data
stack-type-slots (A * B) = 2      -- ptr to fst + ptr to snd
stack-type-slots (A + B) = 2      -- tag + ptr to payload
stack-type-slots (_ ⇒[ _ ] _) = 2 -- closure: env-ptr + code-ptr
stack-type-slots (Eff _ B) = stack-type-slots B
stack-type-slots (Fix _) = 1      -- pointer to recursive structure
stack-type-slots (TVar _) = 1     -- polymorphic = pointer

-- Heap representation: identical to stack (reference-based model)
heap-type-slots : Type → ℕ
heap-type-slots Unit = 0
heap-type-slots Void = 0
heap-type-slots Int = 1
heap-type-slots Float = 1
heap-type-slots Str = 1
heap-type-slots Buffer = 1
heap-type-slots (A * B) = 2
heap-type-slots (A + B) = 2
heap-type-slots (_ ⇒[ _ ] _) = 2
heap-type-slots (Eff _ B) = heap-type-slots B
heap-type-slots (Fix _) = 1
heap-type-slots (TVar _) = 1

-- Legacy alias
type-slots : Type → ℕ
type-slots = stack-type-slots