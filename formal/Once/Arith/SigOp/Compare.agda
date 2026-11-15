-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.SigOp.Compare — plan 0.108: WHICH SigOps are comparisons, and
-- the arith block each one computes its tag with.
--
-- A comparison stays ATOMIC in the IR (`SigOp lt-info`, plan §6). Codegen
-- lowers it as its block (`Output := 0/1`), the tag normalisation `out-nz`,
-- then the sum build; the rewrite registers the same block so the file
-- defines it. Both read the block from here, so they cannot disagree.
------------------------------------------------------------------------

module Once.Arith.SigOp.Compare where

open import Data.Maybe using (Maybe; just; nothing)
open import Once.Spec.Type using (Type; Int; Float; _*_)
open import Once.SigOp.Info using (SigOpInfo; SigOpSem; primV)
open import Once.Arith.Prim using (p-cmp; p-fcmp)
open import Once.Arith.CmpOp using (CmpOp; FCmpOp; fcmp)
open import Once.Arith.Type using (NInt)
open import Once.Arith.Machine.Shape using (InputShape; shape-int; shape-float; shape-pair)
open import Once.Arith.Machine.Shape using (here-int; here-flt; go-fst; go-snd)
open import Once.Arith.Machine.IR using (MArithIR; ainput; acmp; afcmp; ArithBlock; mk-block)
open import Once.Arith.SigOp.Block using (block-info)

-- | The comparison a contract IS, if it is one. Only the six comparison
-- primitives answer `just`.
-- | A comparison, by its operands' type: an `Int` one (`CmpOp`) or a `Float`
-- one (`FCmpOp`, plan 0.150). Both are a block computing a 0/1 word, read as
-- the `Bool` the comparison SigOp means.
data CmpAt : Type → Set where
  int-c : CmpOp → CmpAt (Int * Int)
  flt-c : FCmpOp → CmpAt (Float * Float)

cmp-of : ∀ {A B} → SigOpSem A B → Maybe (CmpAt A)
cmp-of (primV (p-cmp o))    = just (int-c o)
cmp-of (primV (p-fcmp h o)) = just (flt-c (fcmp h o))
{-# CATCHALL #-}
cmp-of _                    = nothing

cmp-shape : ∀ {A} → CmpAt A → InputShape
cmp-shape (int-c _) = shape-pair shape-int shape-int
cmp-shape (flt-c _) = shape-pair shape-float shape-float

cmp-body : ∀ {A} (c : CmpAt A) → MArithIR (cmp-shape c) NInt
cmp-body (int-c o) = acmp o (ainput (go-fst here-int)) (ainput (go-snd here-int))
cmp-body (flt-c o) = afcmp o (ainput (go-fst here-flt)) (ainput (go-snd here-flt))

cmp-block : ∀ {A} → CmpAt A → ArithBlock
cmp-block c = mk-block (cmp-shape c) NInt (cmp-body c)

cmp-block-info : ∀ {A} → CmpAt A → SigOpInfo A Int
cmp-block-info (int-c o) = block-info (cmp-body (int-c o))
cmp-block-info (flt-c o) = block-info (cmp-body (flt-c o))
