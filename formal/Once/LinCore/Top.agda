-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
------------------------------------------------------------------------
-- Once.LinCore.Top — plan 0.146 B1.7 step 3, B1.7c (D458–D463): ★ THE
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
open import Once.Target.Backend using (Backend; module Backend)

module Once.LinCore.Top (o : CanonicalName) {B : Backend} (A : ArchSim o B) where

open import Data.List using (List; [])
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans)
open import Data.Bool using (Bool; false)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Maybe.Properties using (just-injective)
open import Data.String using (String)
open import Once.Spec.Type using (Type)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.Denotation.ProgramTrace using (⟦_⟧IRᵗ)
open import Once.Denotation.Program using (irProgram)
open import Once.IR using (Heap)
open import Once.Compile using (EffUU)
open import Once.CompileSrc using (CompiledSrc; srcModule; mainOf)
open import Once.LinCore.Emit using (fileOf)
open import Once.CCC.Codegen.ImageExterns using (image-externs)
open import Once.Denotation.Program using (IRFun; NamesDistinct)
open import Once.IR.Semantics.Trace using (module Interp)
open import Once.CCC.FrameSemantics using (fs-numerics; module FrameSemantics)
open import Once.Parser.Module.Core using (Resolved)
open import Once.Compile using (moduleToIR; moduleTable)
open import Once.Module using (moduleSig)
import Once.IR
import Once.IRTy
import Once.LinCore.ExprBuild
import Once.LinCore.ExprLinked
import Once.LinCore.Apex
import Once.LinCore.ExprImage
import Once.CCC.Codegen.AllocExpandClasses

module Program (m : Resolved) (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
  (mi : moduleToIR m ≡ just ir) (nd : NamesDistinct (moduleTable m)) (te : moduleTable m ≡ tbl)
  (ls : moduleSig m ≡ Interp.sig (FrameSemantics.fs-interp (ArchSim.FS A)))
  (a : Once.CCC.Codegen.AllocExpandClasses.Alloc) (inl : Bool) where

  -- the bridge's facts, from the compile pipeline, in the interpretation's signatures
  -- (only the declarations' fact depends on the signatures: moved alone, so the others stay the
  -- front end's, `ExprLinked.bridged`'s)
  module B₀ = Once.LinCore.ExprBuild.Bridged (Once.LinCore.ExprLinked.bridged (fs-numerics (ArchSim.FS A)) m ir mi nd te)
  bf : Once.LinCore.ExprBuild.Bridged (fs-numerics (ArchSim.FS A)) (Interp.sig (FrameSemantics.fs-interp (ArchSim.FS A))) tbl ir
  bf = record { tl = B₀.tl ; gb = B₀.gb ; mty = B₀.mty ; mpm = B₀.mpm ; mg = B₀.mg ; tbl-eq = B₀.tbl-eq ; mir = B₀.mir
              ; sd = subst (λ σ → Once.LinCore.ExprBuild.SrcsDecl (fs-numerics (ArchSim.FS A)) σ B₀.tl) ls B₀.sd }

  module N = Once.LinCore.Apex.NewImage o A tbl ir bf

  -- ★★ the compiled program's new image on the arch has the trace of the program, and so
  -- does the file the backend writes for it
  conc-tr★ = N.conc-trᴺ
  file-tr★ = N.file-trᴺ


  -- ★★ THE FILE THE COMPILER WRITES (`Emit.fileOf`, of the module's sources and their main,
  -- D461) runs with the program's trace: the bridge's sources are the module's
  -- (`ExprProgram.src-eq`), its main theirs (`main-eq`), so the file is `Apex.file-at`'s
  module EPm = Once.LinCore.ExprLinked.ExprProgram (Once.LinCore.ExprLinked.expr-program (fs-numerics (ArchSim.FS A)) m ir mi nd)

  FileAt : List CompiledSrc → Σ Type (λ T → T <: EffUU) → Set
  FileAt tl (T , pm) =
    ArchSim.run-file A (Once.LinCore.ExprImage.fileAt (fs-numerics (ArchSim.FS A)) B a inl tl pm
                         (image-externs (Once.LinCore.ExprImage.imageAt (fs-numerics (ArchSim.FS A)) tl pm)))
    ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics (ArchSim.FS A)) (FrameSemantics.fs-interp (ArchSim.FS A))

  FileTr : List CompiledSrc → Σ Type (λ T → T <: EffUU) → Set
  FileTr s (T , pm) = ArchSim.run-file A (fileOf B a inl (fs-numerics (ArchSim.FS A)) s pm)
                      ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics (ArchSim.FS A)) (FrameSemantics.fs-interp (ArchSim.FS A))

  private
    -- the bridge's sources and main are the front end's
    tl-eq : N.IT.BF.tl ≡ Once.LinCore.ExprBuild.srcOrder (fs-numerics (ArchSim.FS A)) EPm.srcs []
    tl-eq = refl
    main-eq : _≡_ {A = Σ Type (λ T → T <: EffUU)} (N.IT.BF.mty , N.IT.BF.mpm) (EPm.mty , EPm.mpm)
    main-eq = refl

    -- …so the file at them is the compiler's of them (its externs, the image's)
    at-front : N.Owed → FileTr EPm.srcs (EPm.mty , EPm.mpm)
    at-front O = subst₂ FileAt tl-eq main-eq
                   (N.file-at a inl (image-externs (Once.LinCore.ExprImage.imageAt (fs-numerics (ArchSim.FS A)) N.IT.BF.tl N.IT.BF.mpm)) O)

    move : ∀ {s s′} → s ≡ s′ → ∀ {x y} → mainOf s ≡ just x → mainOf s′ ≡ just y → FileTr s x → FileTr s′ y
    move {s} refl e e′ t = subst (λ z → FileTr s z) (just-injective (trans (sym e) e′)) t

  file★ : N.Owed → ∀ srcs → srcModule Heap false m ≡ inj₂ srcs → ∀ {T} (pm : T <: EffUU) → mainOf srcs ≡ just (T , pm)
        → FileTr srcs (T , pm)
  file★ O srcs se {T} pm mo =
    move {EPm.srcs} {srcs} (inj₂-injective (trans (sym EPm.src-eq) se)) {EPm.mty , EPm.mpm} {T , pm} EPm.main-eq mo (at-front O)

  -- ★★ THE FILE THE COMPILER WRITES IS WHAT THE ASSEMBLER DEMANDS (D464)
  FileWfAt : List CompiledSrc → Σ Type (λ T → T <: EffUU) → Set
  FileWfAt tl (T , pm) =
    Backend.AsmWF B (Once.LinCore.ExprImage.fileAt (fs-numerics (ArchSim.FS A)) B a inl tl pm
                      (image-externs (Once.LinCore.ExprImage.imageAt (fs-numerics (ArchSim.FS A)) tl pm)))

  FileWf : List CompiledSrc → Σ Type (λ T → T <: EffUU) → Set
  FileWf s (T , pm) = Backend.AsmWF B (fileOf B a inl (fs-numerics (ArchSim.FS A)) s pm)

  private
    wf-front : FileWf EPm.srcs (EPm.mty , EPm.mpm)
    wf-front = subst₂ FileWfAt tl-eq main-eq (N.file-wf-at a inl)

    move-wf : ∀ {s s′} → s ≡ s′ → ∀ {x y} → mainOf s ≡ just x → mainOf s′ ≡ just y → FileWf s x → FileWf s′ y
    move-wf {s} refl e e′ w = subst (λ z → FileWf s z) (just-injective (trans (sym e) e′)) w

  file-wf★ : ∀ srcs → srcModule Heap false m ≡ inj₂ srcs → ∀ {T} (pm : T <: EffUU) → mainOf srcs ≡ just (T , pm)
           → FileWf srcs (T , pm)
  file-wf★ srcs se {T} pm mo =
    move-wf {EPm.srcs} {srcs} (inj₂-injective (trans (sym EPm.src-eq) se)) {EPm.mty , EPm.mpm} {T , pm} EPm.main-eq mo wf-front
