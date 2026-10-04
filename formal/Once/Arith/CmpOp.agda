-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.CmpOp — plan 0.108: THE SIX COMPARISONS, as one operation code.
--
-- Signed word comparisons (D054) at a width: what the comparison SigOps mean
-- (`Prim.cmp-semM`, into `Bool = Unit + Unit` with true = inr, D263), what the
-- arith block's `acmp` node computes as a 0/1 word, and what every arith
-- machine level below it (`AbsInstr.cmp-rrr`, `XInstr.Xcmp-rrr`) executes.
------------------------------------------------------------------------

module Once.Arith.CmpOp where

open import Data.Bool using (Bool; not; if_then_else_)
open import Data.Nat using (ℕ)
open import Once.Word using (module Width)

data CmpOp : Set where
  c-lt c-le c-gt c-ge c-eq c-ne : CmpOp

cmp-word : (bits : ℕ) → CmpOp → ℕ → ℕ → Bool
cmp-word bits c-lt a b = Width._<ˢ_ bits a b
cmp-word bits c-le a b = not (Width._<ˢ_ bits b a)
cmp-word bits c-gt a b = Width._<ˢ_ bits b a
cmp-word bits c-ge a b = not (Width._<ˢ_ bits a b)
cmp-word bits c-eq a b = Width._≡ʷ_ bits a b
cmp-word bits c-ne a b = not (Width._≡ʷ_ bits a b)

-- | The comparison as a 0/1 WORD — the form every arith machine level writes
-- into its destination register.
cmp-bit : (bits : ℕ) → CmpOp → ℕ → ℕ → ℕ
cmp-bit bits o a b = if cmp-word bits o a b then 1 else 0
