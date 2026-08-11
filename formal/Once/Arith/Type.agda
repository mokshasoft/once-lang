-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Type
--
-- Numeric types for the arithmetic compiler.
-- These define the domain of efficient register-based computation.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Type where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ)
open import Data.Float using (Float)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Numeric types
------------------------------------------------------------------------

-- | NumType: Types supported by the arithmetic compiler
--
-- These are the base types for efficient register-based computation.
-- Integer types are signed; unsigned variants could be added later.
--
data NumType : Set where
  I8   : NumType    -- 8-bit signed integer
  I16  : NumType    -- 16-bit signed integer
  I32  : NumType    -- 32-bit signed integer
  I64  : NumType    -- 64-bit signed integer
  F32  : NumType    -- 32-bit IEEE 754 float
  F64  : NumType    -- 64-bit IEEE 754 float (double)

------------------------------------------------------------------------
-- Type properties
------------------------------------------------------------------------

-- | Bit width of each numeric type
bitwidth : NumType → ℕ
bitwidth I8  = 8
bitwidth I16 = 16
bitwidth I32 = 32
bitwidth I64 = 64
bitwidth F32 = 32
bitwidth F64 = 64

-- | Whether the type is a floating-point type
isFloat : NumType → Bool
isFloat I8  = false
isFloat I16 = false
isFloat I32 = false
isFloat I64 = false
isFloat F32 = true
isFloat F64 = true

-- | Whether the type is an integer type
isInteger : NumType → Bool
isInteger I8  = true
isInteger I16 = true
isInteger I32 = true
isInteger I64 = true
isInteger F32 = false
isInteger F64 = false

------------------------------------------------------------------------
-- Register class (for code generation)
------------------------------------------------------------------------

-- | Register class: GPR for integers, XMM for floats
data RegClass : Set where
  GPR : RegClass    -- General-purpose registers (rax, rbx, ...)
  XMM : RegClass    -- SSE/AVX registers (xmm0, xmm1, ...)

-- | Determine register class from numeric type
regClass : NumType → RegClass
regClass I8  = GPR
regClass I16 = GPR
regClass I32 = GPR
regClass I64 = GPR
regClass F32 = XMM
regClass F64 = XMM

------------------------------------------------------------------------
-- Semantic interpretation
------------------------------------------------------------------------

-- | Interpretation of numeric types as Agda types
--
-- For now, we use ℤ for all integer types and Float for all float types.
-- A more precise model would use bounded integers (e.g., Int8, Int16, etc.)
-- but Agda's standard library doesn't provide these directly.
--
⟦_⟧N : NumType → Set
⟦ I8  ⟧N = ℤ
⟦ I16 ⟧N = ℤ
⟦ I32 ⟧N = ℤ
⟦ I64 ⟧N = ℤ
⟦ F32 ⟧N = Float
⟦ F64 ⟧N = Float

------------------------------------------------------------------------
-- Type equality (decidable)
------------------------------------------------------------------------

-- | Decidable equality for NumType
--
-- Needed for type checking and register allocation.
--
data _≟N_ : NumType → NumType → Set where
  refl-I8  : I8  ≟N I8
  refl-I16 : I16 ≟N I16
  refl-I32 : I32 ≟N I32
  refl-I64 : I64 ≟N I64
  refl-F32 : F32 ≟N F32
  refl-F64 : F64 ≟N F64

-- | Type equality to propositional equality
≟N-to-≡ : ∀ {τ₁ τ₂} → τ₁ ≟N τ₂ → τ₁ ≡ τ₂
≟N-to-≡ refl-I8  = refl
≟N-to-≡ refl-I16 = refl
≟N-to-≡ refl-I32 = refl
≟N-to-≡ refl-I64 = refl
≟N-to-≡ refl-F32 = refl
≟N-to-≡ refl-F64 = refl