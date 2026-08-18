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
open import Once.Float.Dyadic using (Dyadic)
open import Data.Float using () renaming (Float to AgdaFloat)
import Data.Float as F
open import Data.Word using () renaming (toℕ to word→ℕ)

float-bits : Dyadic → ℕ
float-bits x = maybe′ word→ℕ 0 (F.toWord x)

------------------------------------------------------------------------
-- THE SAME VALUE AT SINGLE PRECISION (plan 0.66, D109).
--
-- A double is 64 bits and an i386 register is 32, so `float-bits` has no
-- encoding on a 32-bit target — which is why x86-32's emitter lowered a float
-- literal to `ud2` and why no correspondence could exist for it. The fix is the
-- one every 32-bit ABI makes: a `Float` IS single precision there. The width of
-- the encoding is a property of the TARGET, exactly as `slot-size` is.
--
-- Written in Agda rather than bound to a C primitive deliberately. The stdlib
-- has no double→single conversion and this repo has no FFI bindings at all;
-- introducing one here would put the encoding of every float constant outside
-- the language the rest of the compiler is checked in. It is only arithmetic
-- on the 64-bit pattern, so there is nothing to import.
--
-- ROUNDING IS TRUNCATION (round-toward-zero), and that is a CHOICE, not an
-- accident: the encoding is only ever read FORWARDS (abstract value ↦ concrete
-- word — see the note above), so the correspondence needs it to be
-- DETERMINISTIC, not to be IEEE's default rounding. Anything finer is a
-- fidelity question for the float story, not a soundness one for this proof.
--
--   sign     bit 63           ↦ bit 31
--   exponent bits 62–52, bias 1023 ↦ bits 30–23, bias 127
--   mantissa bits 51–0        ↦ bits 22–0 (top 23 kept, low 29 dropped)
--
-- The four edge classes are pinned rather than left to arithmetic:
--   * a zero or subnormal double  → signed zero (a double subnormal is far
--     below the smallest single, so this loses nothing a single could hold);
--   * ±∞ / NaN (exponent all ones) → ±∞, or a NaN with a set mantissa bit;
--   * exponent above single's range → ±∞ (overflow);
--   * exponent below it            → signed zero (underflow).
------------------------------------------------------------------------

open import Data.Nat using (_+_; _∸_; _*_; _^_; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)

private
  2^23 2^29 2^31 2^52 2^63 2^11 : ℕ
  2^11 = 2048
  2^23 = 8388608
  2^29 = 536870912
  2^31 = 2147483648
  2^52 = 4503599627370496
  2^63 = 9223372036854775808

-- the raw single-precision pattern (< 2^32 by construction of its parts)
float-bits-single : Dyadic → ℕ
float-bits-single x =
  let b = float-bits x
      s = (b / 2^63) * 2^31          -- sign bit, already in place
      e = (b / 2^52) % 2^11          -- biased exponent of the double
      m = b % 2^52                   -- mantissa of the double
  in if e ≡ᵇ 0        then s                                        -- ±0 / subnormal
     else if e ≡ᵇ 2047 then s + 255 * 2^23 + (if m ≡ᵇ 0 then 0 else 1)  -- ±∞ / NaN
     else if (e + 127) <ᵇ 1024 then s                               -- underflow → ±0
     else if 1150 <ᵇ e then s + 255 * 2^23                          -- overflow → ±∞
     else s + ((e + 127) ∸ 1023) * 2^23 + (m / 2^29)
