-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ApexFile — (split from `Apex` for its build time) plan 0.146 B1.7c (D465): ★ THE NEW IMAGE ON ANY ARCH.
--
-- An arch is an `ArchSim` (`Adequacy.ArchCorrectness.Interface`). Over it,
-- the compiled program's new image (the bridge's facts `bf`, D460–D462) has
-- the program's trace: the flat theorem (`FlatTop.ExprApex`) at the arch's
-- start, the image's shape facts (`ImageAll`, `ImageGuard`, and what it
-- still owes, `Owed`: B1.7b), its arith table (D464: `ImageOwned`), into
-- the arch's theorem (`ArchSim.sim`). Nothing here names an arch.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Name using (CanonicalName)
open import Once.Adequacy.ArchCorrectness.Interface using (ArchSim; module ArchSim; ExtMiss)
open import Once.Target.Backend using (Backend; module Backend; file-table)
open import Data.Nat using (ℕ)
open import Once.LinCore.Flat using (Base; int; float)

module Once.LinCore.ApexFile (o : CanonicalName) {B : Backend} (A : ArchSim o B) where

open import Data.List using (List; []; _∷_)
open import Once.LinCore.Loader using (bw)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym)
import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.Adequacy.MachineTrace using (module Machine)
open import Once.Denotation.ProgramTrace using (⟦_⟧IRᵗ)
open import Once.Denotation.Program using (IRFun; irProgram)
open import Once.IR.Semantics.Trace using (module Interp)
open import Once.CCC.FrameSemantics using (fs-numerics; fs-ffi; module FrameSemantics)
open import Once.CCC.Codegen.RoomChecks using (room-checks; room-rest; room-checks-∷; rsv-of)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-ret; c-start; start-stack-words; instr-call-closure; instr-sigop; instr-alloc-heap; instr-free-heap; SV-Ptr; SV-Code; module LocState; module AllocState)
open import Data.Sum using (_⊎_)
open import Data.Bool using (Bool; true; false)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (LabelId)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.Arith.Machine.IR using (ArithBlock)
import Once.Adequacy.BlockTable as BT
import Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import Once.IR
import Once.IRTy
import Once.LinCore.MachineLit
import Once.LinCore.FlatTop
import Once.LinCore.ExprBuild
import Once.LinCore.ImageAll
import Once.LinCore.ImageGuard
import Once.LinCore.ImageOwned
import Once.LinCore.ImageBlocks
import Once.LinCore.Keys
import Once.LinCore.ExprImage
import Once.LinCore.ImageSyms
import Once.Adequacy.ArchCorrectness.ExpandSim
import Once.Adequacy.ArchCorrectness.ExpandSimCall
import Once.Adequacy.ArchCorrectness.OutlineEmitted
import Once.CCC.Codegen.AllocOutline
import Once.CCC.Codegen.AllocOutlineSizes
import Once.CCC.Codegen.AllocExpandClasses
import Once.CCC.Codegen.AllocExpandEmitted
import Once.CCC.Codegen.AllocExpand
import Once.SigOp.Info
import Data.Nat
import Data.List.Relation.Unary.Any
open import Once.CCC.Codegen.ImageExterns using (image-externs; ImageWF)

open ArchSim A
open FlatMachine {FS} using (fetch; find-thunk; module FlatState)
open FlatState using (fpc; floc; fclosure; fret; falloc)
open Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq using (Emitted)



-- (`file-wf` at a room-checked image: the pass keeps its start first)

open import Once.LinCore.Apex o A
open import Once.LinCore.ApexX o A
open import Once.LinCore.ApexC o A

module NewImageF (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
  (bf : Once.LinCore.ExprBuild.Bridged (fs-numerics FS) (Interp.sig (FrameSemantics.fs-interp FS)) tbl ir) where
  open NewImage tbl ir bf
  open NewImageX tbl ir bf
  open NewImageC tbl ir bf

  module _ (a : Once.CCC.Codegen.AllocExpandClasses.Alloc) where
    -- ★★ THE FILE THE COMPILER WRITES, in either mode (`--inline-alloc`: `true`)
    file-at : (inl : Bool) (ex : List String) → Owed
            → run-file (Once.LinCore.ExprImage.fileAt (fs-numerics FS) B a inl IT.BF.tl IT.BF.mpm ex) ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
    file-at true  = file-atˣ a
    file-at false = file-atᶜ a

    file-wf-at : (inl : Bool) → Backend.AsmWF B (Once.LinCore.ExprImage.fileAt (fs-numerics FS) B a inl IT.BF.tl IT.BF.mpm
                                     (image-externs (Once.LinCore.ExprImage.imageAt (fs-numerics FS) IT.BF.tl IT.BF.mpm)))
    file-wf-at true  = file-wf-atˣ a
    file-wf-at false = file-wf-atᶜ a
