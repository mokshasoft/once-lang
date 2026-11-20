-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreOwed — plan 0.146 B1.7 step 3 (D464):
-- ★ WHAT THE NEW IMAGE STILL OWES, NAMED.
--
-- The linear core's image owes the arch layer one fact
-- (`LinCore.Apex.NewImage.Owed`), and `Certified` takes it here. (Its RUN
-- facts — a slot the run addresses is in its frame, a closure call's cell
-- names a body, a return is owed and releases its frame — were owed here
-- until B1.7b (D456) made them machine gates, read off a sound run.)
--
--   * that an external op's symbol is no arith block's (`ExtMiss`): what
--     master's `external-sigop-contract` assumes of its own file, on each
--     arch. Its discharge is a name discipline (an external's name is a source
--     name, the blocks' `arith.block.<digest>` is none), owed.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module Once.Adequacy.CoreOwed where

open import Data.List using (List)
open import Once.Spec.Name using (CanonicalName)
open import Once.Target.Backend using (Backend)
open import Once.Adequacy.ArchCorrectness.Interface using (ArchSim; module ArchSim; ExtMiss)
open import Once.Denotation.Program using (IRFun)
open import Once.IR.Semantics.Trace using (Interp; module Interp)
open import Once.CCC.FrameSemantics using (fs-numerics; module FrameSemantics)
import Once.IR
import Once.IRTy
import Once.LinCore.ExprBuild
import Once.LinCore.Apex
import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB64
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBrv
import Once.Adequacy.ArchCorrectness.X86-64.Sim as S64
import Once.Adequacy.ArchCorrectness.X86-32.Sim as S32
import Once.Adequacy.ArchCorrectness.RiscV64.Sim as Srv

-- the bridge's facts of a program, at an arch's numerics and its world's signatures
BridgedAt : ∀ {o : CanonicalName} {B : Backend} → ArchSim o B → List IRFun → Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit → Set
BridgedAt A tbl ir =
  Once.LinCore.ExprBuild.Bridged (fs-numerics (ArchSim.FS A)) (Interp.sig (FrameSemantics.fs-interp (ArchSim.FS A))) tbl ir

-- ★ its externals miss its blocks' table, per arch
module X86-64 (o : CanonicalName) (tbl₀ : List IRFun) (ι : Interp)
              (r : RB64.RegRange o ι) (a : RB64.AddrNoWrap o ι) (l : RB64.LitFits o ι) where
  A = S64.x86-64-sim o tbl₀ ι r a l
  postulate
    ext-miss : ∀ (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit) (bf : BridgedAt A tbl ir)
             → ExtMiss (ArchSim.FS A) (Once.LinCore.Apex.NewImage.env o A tbl ir bf) (Once.LinCore.Apex.NewImage.P′ o A tbl ir bf)

module X86-32 (o : CanonicalName) (tbl₀ : List IRFun) (ι : Interp)
              (r : RB32.RegRange o ι) (a : RB32.AddrNoWrap o ι) (l : RB32.LitFits o ι) where
  A = S32.x86-32-sim o tbl₀ ι r a l
  postulate
    ext-miss : ∀ (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit) (bf : BridgedAt A tbl ir)
             → ExtMiss (ArchSim.FS A) (Once.LinCore.Apex.NewImage.env o A tbl ir bf) (Once.LinCore.Apex.NewImage.P′ o A tbl ir bf)

module RiscV64 (o : CanonicalName) (tbl₀ : List IRFun) (ι : Interp)
               (r : RBrv.RegRange o ι) (s : RBrv.SlotAddrNoWrap o ι) (a : RBrv.AddrNoWrap o ι) (l : RBrv.LitFits o ι) where
  A = Srv.riscv64-sim o tbl₀ ι r s a l
  postulate
    ext-miss : ∀ (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit) (bf : BridgedAt A tbl ir)
             → ExtMiss (ArchSim.FS A) (Once.LinCore.Apex.NewImage.env o A tbl ir bf) (Once.LinCore.Apex.NewImage.P′ o A tbl ir bf)
