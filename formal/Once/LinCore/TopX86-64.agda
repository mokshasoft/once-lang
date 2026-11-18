-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
------------------------------------------------------------------------
-- Once.LinCore.TopX86-64 — plan 0.146 B1.7 step 3 (D455–D458): ★ THE
-- COMPILED PROGRAM'S NEW IMAGE ON x86-64, FROM MASTER'S APEX PREMISES.
--
-- The front end gives the bridge's facts (`ExprLinked.bridged`: the module
-- compiles to `ir`, its table's names are distinct, its table is `tbl`, it is
-- linked against the interpretation's signatures); the arch apex
-- (`ArchX86-64.NewImage.conc-trᴺ`) turns them, with what the image still owes
-- the arch layer (`Owed`, B1.7b), into master's trace refinement. Checked as
-- `Certified` is (`AGDA_RTS_EXTRA=-c`: both stacks loaded at once).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Name using (CanonicalName)
import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB
open import Data.List using (List)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Once.Denotation.Program using (IRFun; IRProgram; NamesDistinct)
open import Once.IR.Semantics.Trace using (Interp; module Interp)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Compile using (moduleToIR; moduleTable)
open import Once.Module using (moduleSig)
import Once.IR
import Once.IRTy
import Once.LinCore.ArchX86-64
import Once.LinCore.ExprBuild
import Once.LinCore.ExprLinked
import Once.Adequacy.ArchCorrectness.X86-64
open import Once.CCC.FrameSemantics using (fs-numerics)

module Once.LinCore.TopX86-64
  (o : CanonicalName) (tbl : List IRFun) (ι : Interp)
  (x86-64-reg-range : RB.RegRange o ι)
  (x86-64-addr-no-wrap : RB.AddrNoWrap o ι)
  (x86-64-lit-fits : RB.LitFits o ι)
  where

module A = Once.LinCore.ArchX86-64 o tbl ι x86-64-reg-range x86-64-addr-no-wrap x86-64-lit-fits

-- the machine's numerics
fmt = fs-numerics (Once.Adequacy.ArchCorrectness.X86-64.x86-64-frame-semantics o tbl ι x86-64-reg-range x86-64-addr-no-wrap x86-64-lit-fits)

module Program (p : IRProgram) (m : Resolved) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
  (mi : moduleToIR m ≡ just ir) (nd : NamesDistinct (moduleTable m)) (te : moduleTable m ≡ tbl)
  (ls : moduleSig m ≡ Interp.sig ι) where

  -- the bridge's facts, from the compile pipeline, in the interpretation's signatures
  bf = subst (λ σ → Once.LinCore.ExprBuild.Bridged fmt σ tbl ir) ls (Once.LinCore.ExprLinked.bridged fmt m ir mi nd te)

  module N = A.NewImage p ir bf

  -- ★★ the compiled program's new image on x86-64 has the trace of the program
  conc-tr★ = N.conc-trᴺ
