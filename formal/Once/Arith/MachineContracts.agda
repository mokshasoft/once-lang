------------------------------------------------------------------------
-- Once.Arith.MachineContracts
--
-- Arithmetic contracts using MachineInterface.
-- NO ENCODE POSTULATES - machine operations ARE the semantics.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- ARCHITECTURE:
--   This module provides semantic functions and contract requirements
--   for arithmetic operations. Key insight:
--
--     ⟦ Int ⟧ = Word  (from SemanticBaseMachine)
--     add-int-sem : Word × Word → Word = word-add
--
--   The semantic function IS the machine operation. No encode gap.
--
--   The ONLY trust is in MachineInterface instantiation (Word64Interface),
--   which is documented in a single location.
------------------------------------------------------------------------

module Once.Arith.MachineContracts where

open import Once.Type using (Type; Int; Unit; _*_)
open import Once.Type using () renaming (Float to FloatTy)
open import Once.Backend.MachineInterface using (MachineInterface)

open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Type Mapping: NumType → Once.Type
------------------------------------------------------------------------

open import Once.Arith.Type using (NumType; I8; I16; I32; I64; F32; F64)

NumToType : NumType → Type
NumToType I8  = Int
NumToType I16 = Int
NumToType I32 = Int
NumToType I64 = Int
NumToType F32 = FloatTy
NumToType F64 = FloatTy

------------------------------------------------------------------------
-- Parameterized Semantic Functions
------------------------------------------------------------------------

-- | Semantic functions parameterized by MachineInterface
-- These ARE the machine operations - no encode gap!

module Semantics (MI : MachineInterface) where
  open MachineInterface MI

  -- Integer binary operations
  add-int-sem : Word × Word → Word
  add-int-sem = word-add

  sub-int-sem : Word × Word → Word
  sub-int-sem = word-sub

  mul-int-sem : Word × Word → Word
  mul-int-sem = word-mul

  div-int-sem : Word × Word → Word
  div-int-sem = word-div

  mod-int-sem : Word × Word → Word
  mod-int-sem = word-mod

  -- Integer unary operations
  neg-int-sem : Word → Word
  neg-int-sem = word-neg

  -- Integer comparisons (return word-one or word-zero)
  lt-int-sem : Word × Word → Word
  lt-int-sem = word-lt

  le-int-sem : Word × Word → Word
  le-int-sem = word-le

  gt-int-sem : Word × Word → Word
  gt-int-sem = word-gt

  ge-int-sem : Word × Word → Word
  ge-int-sem = word-ge

  eq-int-sem : Word × Word → Word
  eq-int-sem = word-eq

  ne-int-sem : Word × Word → Word
  ne-int-sem = word-ne

  -- Constant loading
  const-int-sem : Word → ⊤ → Word
  const-int-sem n _ = n

------------------------------------------------------------------------
-- ArithMachineContracts: Contract requirements for arithmetic
------------------------------------------------------------------------

-- | Record of contracts for arithmetic operations.
-- Parameterized by MachineInterface only.
--
-- NOTE: The record uses Word directly in its contract types, avoiding
-- the need to unify ⟦_⟧ across module boundaries. The caller
-- (BoundaryMachine) specializes their Contract type to Word.

module ArithContracts (MI : MachineInterface) where
  open MachineInterface MI
  open Semantics MI

  -- Contract types specialized to Word (not generic ⟦_⟧)
  -- This avoids module instantiation issues with ⟦_⟧ unification.
  record ArithMachineContracts
      (BinOpContract : (Word × Word → Word) → Set)
      (UnaryOpContract : (Word → Word) → Set)
      (ConstContract : ∀ (n : Word) → (⊤ → Word) → Set)
      : Set₁ where
    field
      -- Integer binary operations
      add-int-contract : BinOpContract add-int-sem
      sub-int-contract : BinOpContract sub-int-sem
      mul-int-contract : BinOpContract mul-int-sem
      div-int-contract : BinOpContract div-int-sem
      mod-int-contract : BinOpContract mod-int-sem

      -- Integer comparisons
      lt-int-contract : BinOpContract lt-int-sem
      eq-int-contract : BinOpContract eq-int-sem

      -- Integer unary operations
      neg-int-contract : UnaryOpContract neg-int-sem

      -- Constant loading (parameterized by value)
      const-int-contract : ∀ (n : Word) → ConstContract n (const-int-sem n)

  open ArithMachineContracts public

------------------------------------------------------------------------
-- Key Insight: Why No Encode Postulates?
------------------------------------------------------------------------

-- OLD APPROACH (Once.Arith.Contracts):
--   ⟦ Int ⟧ = ℤ
--   add-int-sem : ℤ × ℤ → ℤ
--   add-int-sem (a, b) = a + b
--
--   x86 ADD operates on Word64, not ℤ.
--   Need: postulate encode-add : encode a + encode b ≡ encode (a + b)
--
-- NEW APPROACH (this module):
--   ⟦ Int ⟧ = Word  (from MachineInterface)
--   add-int-sem : Word × Word → Word
--   add-int-sem = word-add  (from MachineInterface)
--
--   x86 ADD operates on Word64.
--   Word64Interface.word-add = word64-add (modular addition).
--   NO GAP! The semantic operation IS the machine operation.
--
-- The trust boundary is:
--   Word64Interface.word-add matches x86 ADD instruction.
-- This is stated ONCE in Word64.agda, not repeated for each operation.
