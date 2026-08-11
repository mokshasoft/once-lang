-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Semantics.FloatBits
--
-- THE IEEE-754 BIT PATTERN OF A FLOAT CONSTANT. `⟦ Float ⟧` is Agda's
-- builtin double, and a double IS a 64-bit word — so a float CONSTANT
-- needs no floating-point unit to load: the compiler emits the pattern as
-- an ordinary immediate (`movq $<bits>, %rax`, which gas promotes to
-- `movabs`), exactly as it does for an `Int` literal.
--
-- This is what retires the `load-const-float` divergence (D079): before,
-- codegen emitted `ud2` (halt) while the abstract machine loaded the
-- value and continued — a route on which the two machines genuinely
-- disagreed. Now BOTH load the same 64-bit pattern.
--
-- NaN: `toWord` is `nothing` for NaN (it has many representations, and
-- Agda declines to pick one), so a NaN constant encodes as 0. That is a
-- deterministic choice used by BOTH sides — the abstract encoding
-- (`enc-sv`) and the emitted immediate are literally this function — so
-- the correspondence holds by `refl` regardless. It is NOT injective on
-- NaN, and nothing downstream needs it to be: the encoding is only ever
-- read forwards (abstract value ↦ concrete word).
--
-- Float ARITHMETIC remains unsupported (no FPU instructions are emitted);
-- this module is only about constants.
------------------------------------------------------------------------

module Once.Semantics.FloatBits where

open import Data.Nat using (ℕ)
open import Data.Maybe using (maybe′)
open import Data.Float using () renaming (Float to AgdaFloat)
import Data.Float as F
open import Data.Word using () renaming (toℕ to word→ℕ)

float-bits : AgdaFloat → ℕ
float-bits x = maybe′ word→ℕ 0 (F.toWord x)
