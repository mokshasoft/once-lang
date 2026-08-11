-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Memory.TypeSlots
--
-- Type-to-slot-count mapping for memory layout.
--
-- This module defines how many "slots" each type requires in memory.
-- A slot is a machine-word-sized unit (e.g., 8 bytes on x86-64).
--
-- The representation is reference-based: compound types are accessed
-- via pointers, so all compound types have fixed slot counts regardless
-- of their recursive structure.
--
-- This is TARGET-INDEPENDENT because:
--   - Slot counts are logical units, not byte sizes
--   - All targets use the same reference-based representation
--   - Target-specific byte sizes are defined elsewhere (e.g., slot-bytes)
------------------------------------------------------------------------

module Once.Memory.TypeSlots where

open import Data.Nat using (ℕ)
open import Once.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_;
                             Int; Float; Str; Buffer;
                             Functor; μ-type; ν-type)
-- TVar removed: Code generation works with concrete types only.
-- Type variables exist only in PolyType during type inference.

------------------------------------------------------------------------
-- Type Slot Counts
--
-- Reference-based model: All values accessed by pointer (reference).
-- Stack vs Heap determines only WHERE allocation occurs, not HOW
-- values are represented.
--
-- Slot counts:
--   - Unit, Void: 0 (no runtime representation)
--   - Primitives (Int, Float): 1 (fits in register)
--   - Str, Buffer: 1 (pointer to data)
--   - Products: 2 (ptr to fst + ptr to snd)
--   - Sums: 2 (tag + ptr to payload)
--   - Functions: 2 (closure: env-ptr + code-ptr)
--   - Eff: delegates to result type
--   - Recursive types: 1 (pointer to structure)
-- Note: Type variables (TVar) only exist in PolyType during inference.
-- By code generation time, all types are concrete.
------------------------------------------------------------------------

-- | Compute slot count for stack allocation
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
stack-type-slots (μ-type _) = 1   -- pointer to inductive structure
stack-type-slots (ν-type _) = 1   -- pointer to coinductive structure

-- | Compute slot count for heap allocation
-- Identical to stack (reference-based model)
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
heap-type-slots (μ-type _) = 1
heap-type-slots (ν-type _) = 1

-- | Legacy alias (defaults to stack representation)
type-slots : Type → ℕ
type-slots = stack-type-slots
