-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageBlocks — plan 0.146 B1.7 step 3 (D462): THE NEW IMAGE'S
-- ARITH BLOCKS. An op's blocks are its own (a block op's body) and a
-- comparison's (`sigop-blocks`); the image's are its ops', in order. The
-- emitter writes them into the file (`Emit.blocksOf`); every call of the
-- image names one of them (`ImageOwned`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Data.Nat using (ℕ)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.ImageBlocks (fmt : TargetNum) (bw : Base → ℕ) where

open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.SigOp.Info using (SigOpSem; blockV; primV; ffiV; callsV; emitsV; haltsV; module SigOpInfo)
open import Once.Arith.Machine.IR using (ArithBlock; mk-block)
open import Once.Arith.Machine.Rewrite using (sigop-blocks)
open import Once.LinCore.Core fmt using (Sig; module Sig)
open Sig using (info)
open import Once.LinCore.Lower fmt bw using (cmpOf)
open import Once.LinCore.Keys fmt bw using (Univ; module Univ)
open Univ using (ops)

-- an op's own block: a block op's body
own : ∀ {A B} → SigOpSem A B → List ArithBlock
own (blockV {sh} {n} e _ _) = mk-block sh n e ∷ []
own (primV _)               = []
own ffiV                    = []
own callsV                  = []
own (emitsV _)              = []
own (haltsV _)              = []

-- ★ an op's blocks, and the image's
opBlks : Sig → List ArithBlock
opBlks s = own (SigOpInfo.sem (info s)) ++ sigop-blocks (cmpOf s)

imageBlocks : Univ → List ArithBlock
imageBlocks U = concatMap opBlks (ops U)

-- an op's blocks are the image's
op-blocks : ∀ {ss : List Sig} {s} → s ∈ ss → ∀ {b} → b ∈ opBlks s → b ∈ concatMap opBlks ss
op-blocks {s ∷ ss} (here refl) m = ∈-++⁺ˡ m
op-blocks {s′ ∷ ss} (there p) m = ∈-++⁺ʳ (opBlks s′) (op-blocks p m)
