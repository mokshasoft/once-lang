-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
------------------------------------------------------------------------
-- Once.LinCore.Top — plan 0.146 B1.7 step 3, B1.7c (D455–D460): ★ THE
-- COMPILED PROGRAM'S NEW IMAGE, ON ANY ARCH, FROM MASTER'S APEX PREMISES.
--
-- The front end gives the bridge's facts (`ExprLinked.bridged`: the module
-- compiles to `ir`, its table's names are distinct, its table is `tbl`, it is
-- linked against the interpretation's signatures); the apex (`Apex.NewImage`)
-- turns them, with what the image still owes (`Owed`, B1.7b), into the
-- program's trace on the arch (`ArchSim`: x86-64, x86-32 and riscv64 are
-- `ArchCorrectness.<Arch>.Sim`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Name using (CanonicalName)
open import Once.Adequacy.ArchCorrectness.Interface using (ArchSim; module ArchSim)
open import Once.Target.Backend using (Backend)

module Once.LinCore.Top (o : CanonicalName) {B : Backend} (A : ArchSim o B) where

open import Data.List using (List)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Data.Bool using (false)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Maybe.Properties using (just-injective)
open import Data.String using (String)
open import Once.Spec.Type using (Type)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.Adequacy.SourceTrace using (⟦_⟧IRᵗ)
open import Once.Denotation.Program using (irProgram)
open import Once.IR using (Heap)
open import Once.Compile using (EffUU)
open import Once.CompileSrc using (CompiledSrc; srcModule; mainOf)
open import Once.LinCore.Emit using (fileOf)
open import Once.Denotation.Program using (IRFun; NamesDistinct)
open import Once.IR.Semantics.Trace using (module Interp)
open import Once.CCC.FrameSemantics using (fs-numerics; module FrameSemantics)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Compile using (moduleToIR; moduleTable)
open import Once.Module using (moduleSig)
open import Once.LinCore.Loader using (bw)
import Once.IR
import Once.IRTy
import Once.LinCore.ExprBuild
import Once.LinCore.ExprLinked
import Once.LinCore.Apex

module Program (m : Resolved) (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
  (mi : moduleToIR m ≡ just ir) (nd : NamesDistinct (moduleTable m)) (te : moduleTable m ≡ tbl)
  (ls : moduleSig m ≡ Interp.sig (FrameSemantics.fs-interp (ArchSim.FS A))) where

  -- the bridge's facts, from the compile pipeline, in the interpretation's signatures
  -- (only the declarations' fact depends on the signatures: moved alone, so the others stay the
  -- front end's, `ExprLinked.bridged`'s)
  module B₀ = Once.LinCore.ExprBuild.Bridged (Once.LinCore.ExprLinked.bridged (fs-numerics (ArchSim.FS A)) m ir mi nd te)
  bf : Once.LinCore.ExprBuild.Bridged (fs-numerics (ArchSim.FS A)) (Interp.sig (FrameSemantics.fs-interp (ArchSim.FS A))) tbl ir
  bf = record { tl = B₀.tl ; gb = B₀.gb ; mty = B₀.mty ; mpm = B₀.mpm ; mg = B₀.mg ; tbl-eq = B₀.tbl-eq ; mir = B₀.mir
              ; sd = subst (λ σ → Once.LinCore.ExprBuild.SrcsDecl (fs-numerics (ArchSim.FS A)) σ B₀.tl) ls B₀.sd }

  module N = Once.LinCore.Apex.NewImage o A bw tbl ir bf

  -- ★★ the compiled program's new image on the arch has the trace of the program, and so
  -- does the file the backend writes for it
  conc-tr★ = N.conc-trᴺ
  file-tr★ = N.file-trᴺ

