-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.Types
--
-- X86-specific type layout calculations for the SlotMachine.
--
-- This module provides:
--   - stack-type-slots: Stack slot counts for types
--   - heap-type-slots: Heap slot counts for types
--   - type-slots: Legacy alias
--
-- Generic semantic interpretation (⟦_⟧, sem-*) is in Once.Sem.
-- This module re-exports Once.Sem for backwards compatibility.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.Types where

open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Re-export Type and Quantity from Once.Type
------------------------------------------------------------------------

open import Once.Type public
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Eff; Int; Float; Str; Buffer; TVar;
         Quantity; Zero; One; Many;
         _⊸_; _⇒_; _⇒₀_; IO;
         Functor; μ-type; ν-type; GuardedT)
  -- OCP-0003: Fix removed. Use μ-type/ν-type instead.

------------------------------------------------------------------------
-- Re-export generic semantics from Once.Sem
--
-- For backwards compatibility with existing code that imports from
-- this module. New code should import directly from Once.Sem.
------------------------------------------------------------------------

open import Once.Semantics.Machine public
  using (⟦_⟧;
         sem-fst; sem-snd; sem-pair;
         sem-inl; sem-inr; sem-case;
         sem-fst-pair; sem-snd-pair;
         sem-case-inl; sem-case-inr)
  -- OCP-0003: ⟦Fix⟧, wrap, unwrap, sem-fold, sem-unfold, etc. removed.
  -- Use μ-type/ν-type and recursion scheme semantics instead.

-- Legacy alias: pair is safe (IR uses ⟨_,_⟩ not pair)
-- NOTE: Do NOT add aliases for fold, unfold, inl, inr, case, fst, snd
-- as these conflict with IR constructor names.
pair : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A * B ⟧
pair = sem-pair

------------------------------------------------------------------------
-- Type Slots: Memory representation sizes (X86-SPECIFIC)
--
-- Reference-based model: All values accessed by pointer (reference).
-- Stack vs Heap determines only WHERE allocation occurs, not HOW
-- values are represented. Both modes use identical pointer-based
-- representation.
--
-- This enables:
--   - Linear values passed by reference (zero-copy)
--   - Semantic copy only when linearity requires duplication
--   - Simplified proofs (one constructor works for both modes)
--   - Direct mapping to x86 calling conventions
--
-- See unboxed-stack-design.md for full design rationale.
------------------------------------------------------------------------

-- Reference-based representation: all compound types use fixed pointer sizes
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
-- OCP-0003: Fix removed. Use μ-type/ν-type instead.
stack-type-slots (μ-type _) = 1   -- OCP-0003: pointer to inductive structure
stack-type-slots (ν-type _) = 1   -- OCP-0003: pointer to coinductive structure
stack-type-slots (GuardedT _ _) = 1  -- OCP-0003: pointer to guarded functor value
stack-type-slots (TVar _) = 1     -- polymorphic = pointer

-- Heap representation: identical to stack (reference-based model)
-- Kept separate for API compatibility; both are definitionally equal.
heap-type-slots : Type → ℕ
heap-type-slots Unit = 0
heap-type-slots Void = 0
heap-type-slots Int = 1
heap-type-slots Float = 1
heap-type-slots Str = 1
heap-type-slots Buffer = 1
heap-type-slots (A * B) = 2        -- ptr to fst + ptr to snd
heap-type-slots (A + B) = 2        -- tag + ptr to payload
heap-type-slots (_ ⇒[ _ ] _) = 2   -- closure: env-ptr + code-ptr
heap-type-slots (Eff _ B) = heap-type-slots B
-- OCP-0003: Fix removed. Use μ-type/ν-type instead.
heap-type-slots (μ-type _) = 1     -- OCP-0003: pointer to inductive structure
heap-type-slots (ν-type _) = 1     -- OCP-0003: pointer to coinductive structure
heap-type-slots (GuardedT _ _) = 1  -- OCP-0003: pointer to guarded functor value
heap-type-slots (TVar _) = 1       -- polymorphic = pointer

-- Legacy alias (all representations now use reference-based model)
type-slots : Type → ℕ
type-slots = stack-type-slots