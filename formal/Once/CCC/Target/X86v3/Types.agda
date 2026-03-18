------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.Types
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

module Once.CCC.Target.X86v3.Types where

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
--
-- For backwards compatibility with existing code that imports from
-- this module. New code should import directly from Once.Sem.
------------------------------------------------------------------------

open import Once.Sem public
  using (⟦_⟧; ⟦Fix⟧; wrap; unwrap;
         sem-fst; sem-snd; sem-pair;
         sem-inl; sem-inr; sem-case;
         sem-fold; sem-unfold;
         sem-fst-pair; sem-snd-pair;
         sem-case-inl; sem-case-inr;
         sem-unfold-fold; sem-fold-unfold)

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
stack-type-slots (Fix _) = 1      -- pointer to recursive structure
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
heap-type-slots (Fix _) = 1        -- pointer to recursive structure
heap-type-slots (TVar _) = 1       -- polymorphic = pointer

-- Legacy alias (all representations now use reference-based model)
type-slots : Type → ℕ
type-slots = stack-type-slots
