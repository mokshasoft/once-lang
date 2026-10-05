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
open import Once.Type using (Int; _*_)
open import Once.SigOp.Info using (SigOpInfo; SigOpSem; primV)
open import Once.Arith.Prim using (p-cmp)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.Type using (NInt)
open import Once.Arith.Machine.Shape using (shape-int; shape-pair)
open import Once.Arith.Machine.Shape using (here-int; go-fst; go-snd)
open import Once.Arith.Machine.IR using (MArithIR; ainput; acmp; ArithBlock; mk-block)
open import Once.Arith.SigOp.Block using (block-info)

-- | The comparison a contract IS, if it is one. Only the six comparison
-- primitives answer `just`.
cmp-of : ∀ {A B} → SigOpSem A B → Maybe CmpOp
cmp-of (primV (p-cmp o)) = just o
cmp-of _                 = nothing

-- | The block: compare the pair's two `Int`s.
cmp-body : CmpOp → MArithIR (shape-pair shape-int shape-int) NInt
cmp-body o = acmp o (ainput (go-fst here-int)) (ainput (go-snd here-int))

cmp-block : CmpOp → ArithBlock
cmp-block o = mk-block (shape-pair shape-int shape-int) NInt (cmp-body o)

cmp-block-info : CmpOp → SigOpInfo (Int * Int) Int
cmp-block-info o = block-info (cmp-body o)
