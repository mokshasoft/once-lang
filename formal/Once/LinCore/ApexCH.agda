-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ApexCH — (split from `Apex`, `ApexC`, for build time: the call mode's helpers) plan 0.146 B1.7c (D465): ★ THE NEW IMAGE ON ANY ARCH.
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

module Once.LinCore.ApexCH (o : CanonicalName) {B : Backend} (A : ArchSim o B) where

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

module NewImageCH (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
  (bf : Once.LinCore.ExprBuild.Bridged (fs-numerics FS) (Interp.sig (FrameSemantics.fs-interp FS)) tbl ir) where
  open NewImage tbl ir bf

  module ByAlloc (a : Once.CCC.Codegen.AllocExpandClasses.Alloc) where
    module XS = Once.Adequacy.ArchCorrectness.ExpandSim o A
    module PL = Once.CCC.Codegen.AllocExpandClasses.Choice a image
    module CL = Once.CCC.Codegen.AllocExpandClasses
    module CLF = Once.CCC.Codegen.AllocExpandClasses.Fetch {FS}
    module CD = Once.CCC.Codegen.AllocExpandEmitted.Code {FS} PL.C PL.small PL.in-range PL.fits
    module EM = Once.CCC.Codegen.AllocExpandEmitted {FS}

    ------------------------------------------------------------------------
    -- ★★ D482: THE ALLOCATOR AS A CALL (the default mode; `--inline-alloc` is the
    -- expansion above): the expansion of the OUTLINED image, its sites calls of one
    -- routine per size of the image's, the same trace
    ------------------------------------------------------------------------

    module XC = Once.Adequacy.ArchCorrectness.ExpandSimCall o A
    module OE = Once.Adequacy.ArchCorrectness.OutlineEmitted o FS slot-size word-eq
    module OS = Once.CCC.Codegen.AllocOutlineSizes {FS}

    -- the routines' sizes: the image's, each once
    -- (spelled as `ExprImage.imageAtᶜ`: the file's statement and this compare by names, not by
    -- evaluating the sizes over two spellings of the image; docs/performance-patterns.md A3)
    ksᶜ : List ℕ
    ksᶜ = CL.dsizes (Once.LinCore.ExprImage.imageAt (fs-numerics FS) IT.BF.tl IT.BF.mpm)

    imageᵒ : AbstractTrace
    imageᵒ = Once.CCC.Codegen.AllocExpand.outline ksᶜ (Once.LinCore.ExprImage.imageAt (fs-numerics FS) IT.BF.tl IT.BF.mpm)

    module PLC = Once.CCC.Codegen.AllocExpandClasses.Choice a imageᵒ
    module CDC = Once.CCC.Codegen.AllocExpandEmitted.Code {FS} PLC.C PLC.small PLC.in-range PLC.fits

    imageᶜ : AbstractTrace
    imageᶜ = Once.CCC.Codegen.AllocExpand.expand PLC.C imageᵒ

    P‴ : AbstractTrace
    P‴ = room-checks imageᶜ

    module _ where
      ks-pos : ∀ k → k ∈ ksᶜ → 1 Data.Nat.≤ k
      ks-pos = OS.dsizes-pos image IA.em-alloc

      ks-in : ∀ q k → (fetch IA.tail q ≡ just (instr-alloc-heap k)) ⊎ (fetch IA.tail q ≡ just (instr-free-heap k)) → k ∈ ksᶜ
      ks-in q k e = OS.in-dsizes image (Data.Nat.suc q) k e

      emᵒ : Emitted imageᵒ
      emᵒ = OE.emitted ksᶜ IA.em-budget start-stack-words IA.tail emitted ks-pos ks-in IS.calls-apart

      -- an op the room-checked call image calls is one the room-checked image calls
      sig-backᶜ : ∀ {A B} (si : Once.SigOp.Info.SigOpInfo A B) → instr-sigop si ∈ P‴ → instr-sigop si ∈ P′
      sig-backᶜ si m = EM.∈-room image (Once.CCC.Codegen.AllocOutline.sig-out {FS} si ksᶜ IA.em-budget start-stack-words IA.tail
                         (CDC.exp-sig 0 imageᵒ (Emitted.em-alloc emᵒ) si (EM.room-sig imageᶜ si m))) (λ _ _ ())

    namedᶜ : Data.List.Relation.Unary.All.All (BT.SigNamed bs) P‴
    namedᶜ = Data.List.Relation.Unary.All.tabulate λ {i} m {A} {B} si e →
      Once.LinCore.ImageOwned.named-call (fs-numerics FS) bw U IT.canon si (IA.sigops si (sig-backᶜ si (subst (λ j → j ∈ P‴) e m)))

    ext-missᶜ : Owed → ExtMiss FS env P‴
    ext-missᶜ O si k ex f =
      let (k′ , f′) = ∈-fetch P′ (sig-backᶜ si (fetch-∈ P‴ k f)) in Owed.o-ext-miss O si k′ ex f′

    -- ★★ THE CALL MODE ON THE ARCH: its run has the trace of the program
