{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Numerics — the target's numeric structure, a parameter of the
-- meaning.
--
-- SPEC. `Int` denotes a word of the target's width and `Float` a value of
-- the target's format, so the meaning of a program is relative to these two
-- facts — and to nothing else about the target. A target has at least one bit:
-- at zero bits the literal range would admit `-1` and store it as `0`.
------------------------------------------------------------------------

module Once.Spec.Numerics where

open import Data.Nat using (ℕ; _<_)
open import Once.Spec.Float.Dyadic using (FloatFormat)

record TargetNum : Set where
  constructor mkTargetNum
  field
    int-bits     : ℕ            -- the word's width; `Int` is two's complement at it
    float-format : FloatFormat  -- the format `Float` is rounded to
    int-bits-pos : 0 < int-bits
