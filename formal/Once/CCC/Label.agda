-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Label
--
-- Plan 0.33: provenance-typed jump labels. A label number alone cannot be
-- collision-free across the two compile-time boundary: the verified
-- compiler allocates its own labels at compiler-compile-time (`once`,
-- counter-distinct), while SigOps are resolved at once-program-compile-time
-- (`sigop`, constrained only via PreservesCCC). Carrying provenance in the
-- TYPE makes cross-provenance disjointness DEFINITIONAL — a compiler jump
-- (`once X`) can never match a SigOp label (`sigop name k`), so find-label
-- resolution is collision-free by construction, no shared counter, no
-- postulate. (Renders to `.Lonce_n` / `.Lsigops_<name>_n` at Emit.)
--
-- Plan 0.63 (D082): a THIRD provenance, `thunk` — the entry label of a
-- closure body. A call target and a jump target are different kinds of
-- code address, so the same principle applies one level down: a `c-jmp`
-- can never land on a body entry, and a call can never land on a jump
-- label, DEFINITIONALLY (via the catch-all below) rather than by the
-- accident that the two share one monotone counter. Renders to
-- `.L_thunk_<n>` — the name `emit-thunk-body` and the `rip+label`
-- operand already use, so the emitted text is byte-identical.
------------------------------------------------------------------------

module Once.CCC.Label where

open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.String using (String) renaming (_==_ to _==ˢ_)
open import Data.Bool using (Bool; true; false; _∧_)

data Label : Set where
  once  : ℕ → Label            -- compiler-allocated (monotonic counter ⟹ distinct)
  sigop : String → ℕ → Label   -- SigOp-allocated; String = the SigOp's name
  thunk : ℕ → Label            -- closure-body entry (Plan 0.63, D082)

-- Boolean equality used by find-label's scan. Cross-provenance is `false`
-- by the catch-all (the definitional disjointness that makes collisions
-- impossible between compiler and SigOp labels).
infix 4 _≡ᵇᴸ_
_≡ᵇᴸ_ : Label → Label → Bool
once  n   ≡ᵇᴸ once  m   = n ≡ᵇ m
sigop a n ≡ᵇᴸ sigop b m = (a ==ˢ b) ∧ (n ≡ᵇ m)
thunk n   ≡ᵇᴸ thunk m   = n ≡ᵇ m
_         ≡ᵇᴸ _         = false
