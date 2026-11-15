-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.CmpOp — plan 0.108: THE SIX COMPARISONS, as one operation code
-- (and plan 0.150: the comparisons at `Float`, `FCmpOp`).
--
-- Signed word comparisons (D054) at a width: what the comparison SigOps mean
-- (`Prim.cmp-semM`, into `Bool = Unit + Unit` with true = inr, D263), what the
-- arith block's `acmp` node computes as a 0/1 word, and what every arith
-- machine level below it (`AbsInstr.cmp-rrr`, `XInstr.Xcmp-rrr`) executes.
------------------------------------------------------------------------

module Once.Arith.CmpOp where

open import Data.Bool using (Bool; not; if_then_else_)
open import Data.Nat using (ℕ)
open import Once.Spec.Word using (module Width)

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

------------------------------------------------------------------------
-- The comparisons at `Float` (plan 0.150): one code per row and symbol of
-- the Spec's table (`Spec.Theory`: the IEEE comparisons of `Rounded`, the
-- total order of `Order`, the identity of `Equality`), meaning the Spec's
-- symbol on the values the words encode.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum; mkTargetNum)
open import Once.Spec.Float.Dyadic using (FloatFormat)
open import Data.Nat using (s≤s; z≤n)
open import Once.Spec.Theory using (Has; float-neg; float-rounded; float-order; float-equality; Sym; compare; module Models; ⟦_⟧ₛ) renaming (float to nfloat)
open import Once.Spec.Float.Encoding using (decode)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data FCmpOp : Set where
  fcmp : ∀ {U} → Has nfloat U → Sym U compare → FCmpOp

-- (The Float rows of the table read only the target's float format, so a
-- comparison's meaning is stated at a format: `floatTarget` fills the width,
-- which nothing here reads.)
floatTarget : FloatFormat → TargetNum
floatTarget F = mkTargetNum 1 F (s≤s z≤n)

fcmp-word : FloatFormat → FCmpOp → ℕ → ℕ → Bool
fcmp-word F (fcmp h o) a b = ⟦ o ⟧ₛ (Models.structure (floatTarget F) h) (decode F a , decode F b)

fcmp-bit : FloatFormat → FCmpOp → ℕ → ℕ → ℕ
fcmp-bit F o a b = if fcmp-word F o a b then 1 else 0

-- | …and that IS the comparison read at any target with that format: a Float
-- row's structure reads only the format (row by row, since `structure` is
-- defined by them).
fcmp-word-at : ∀ {U} (h : Has nfloat U) (o : Sym U compare) (tn : TargetNum) (a b : ℕ)
             → fcmp-word (TargetNum.float-format tn) (fcmp h o) a b
               ≡ ⟦ o ⟧ₛ (Models.structure tn h)
                        (decode (TargetNum.float-format tn) a , decode (TargetNum.float-format tn) b)
fcmp-word-at float-rounded  o tn a b = refl
fcmp-word-at float-order    o tn a b = refl
fcmp-word-at float-equality o tn a b = refl
fcmp-word-at float-neg      () tn a b
