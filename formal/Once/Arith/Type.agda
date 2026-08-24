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
open import Once.Word using (Carrier)
open import Once.Float.Decimal using (Decimal)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Numeric types
------------------------------------------------------------------------

-- | NumType: the KINDS of number the arithmetic compiler handles — NOT their
-- widths.
--
-- This used to read `I8 | I16 | I32 | I64 | F32 | F64`, i.e. the width lived in
-- the type. That is the design D054 (for `Int`) and D112 (for `Float`) both
-- REJECTED, and D112 names it explicitly: putting the width in the type
-- "changes the surface language and makes users pick". The width is a property
-- of the TARGET — `norm` applies it for integers, the target's `FloatFormat`
-- for floats.
--
-- The six width-carrying constructors were also, measured 2026-08-19, NEVER
-- USED: not one occurrence anywhere in the tree outside this module. They were
-- a fossil of the rejected design, and they misled a reader into thinking the
-- arith IR already had a float story. Deleting them is the honest state: the
-- arith path is width-free, and always was.
data NumType : Set where
  NInt   : NumType    -- the target's integer word
  NFloat : NumType    -- the target's float

------------------------------------------------------------------------
-- Type properties
------------------------------------------------------------------------

-- `bitwidth` is DELETED with the width-carrying constructors: a `NumType` no
-- longer knows a width, because the target owns it.

-- | Whether the type is a floating-point type
isFloat : NumType → Bool
isFloat NInt   = false
isFloat NFloat = true

-- | Whether the type is an integer type
isInteger : NumType → Bool
isInteger NInt   = true
isInteger NFloat = false

------------------------------------------------------------------------
-- Register class (for code generation)
------------------------------------------------------------------------

-- | Register class: GPR for integers, XMM for floats
data RegClass : Set where
  GPR : RegClass    -- General-purpose registers (rax, rbx, ...)
  XMM : RegClass    -- SSE/AVX registers (xmm0, xmm1, ...)

-- | Determine register class from numeric type
regClass : NumType → RegClass
regClass NInt   = GPR
regClass NFloat = XMM

------------------------------------------------------------------------
-- Semantic interpretation
------------------------------------------------------------------------

-- | Interpretation of numeric kinds as Agda types.
--
-- `Carrier` and `Decimal` (K0), NOT `ℤ` and Agda's builtin `Float`. The old reading
-- was the third fossil in this module: an Agda `Float` denotation is exactly
-- what D112 removed everywhere else, because it bakes the widest target's
-- format into the meaning of a value. Both carriers here are WIDTH-FREE, and
-- the target applies its own width.
⟦_⟧N : NumType → Set
⟦ NInt   ⟧N = Carrier
⟦ NFloat ⟧N = Decimal

------------------------------------------------------------------------
-- Type equality (decidable)
------------------------------------------------------------------------

-- | Decidable equality for NumType
--
-- Needed for type checking and register allocation.
--
data _≟N_ : NumType → NumType → Set where
  refl-NInt   : NInt   ≟N NInt
  refl-NFloat : NFloat ≟N NFloat

-- | Type equality to propositional equality
≟N-to-≡ : ∀ {τ₁ τ₂} → τ₁ ≟N τ₂ → τ₁ ≡ τ₂
≟N-to-≡ refl-NInt   = refl
≟N-to-≡ refl-NFloat = refl