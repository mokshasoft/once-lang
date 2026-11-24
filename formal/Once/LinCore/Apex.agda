-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Apex — plan 0.146 B1.7c (D463): ★ THE NEW IMAGE ON ANY ARCH.
--
-- An arch is an `ArchSim` (`Adequacy.ArchCorrectness.Interface`). Over it,
-- the compiled program's new image (the bridge's facts `bf`, D458–D460) has
-- the program's trace: the flat theorem (`FlatTop.ExprApex`) at the arch's
-- start, the image's shape facts (`ImageAll`, `ImageGuard`, and what it
-- still owes, `Owed`: B1.7b), its arith table (D462: `ImageOwned`), into
-- the arch's theorem (`ArchSim.sim`). Nothing here names an arch.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Name using (CanonicalName)
open import Once.Adequacy.ArchCorrectness.Interface using (ArchSim; module ArchSim; ExtMiss)
open import Once.Target.Backend using (Backend; module Backend; file-table)
open import Data.Nat using (ℕ)
open import Once.LinCore.Flat using (Base; int; float)

module Once.LinCore.Apex (o : CanonicalName) {B : Backend} (A : ArchSim o B) where

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
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-ret; instr-call-closure; instr-sigop; instr-alloc-heap; instr-free-heap; SV-Ptr; SV-Code; module LocState; module AllocState)
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
open import Once.CCC.Codegen.ImageExterns using (image-externs)

open ArchSim A
open FlatMachine {FS} using (fetch; find-thunk; module FlatState)
open FlatState using (fpc; floc; fclosure; fret; falloc)
open Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq using (Emitted)


module ML = Once.LinCore.MachineLit FS bw

-- a constant's loader is an `instr-load-const`
ld-is : Once.LinCore.ImageAll.LoadConst (fs-numerics FS) (fs-ffi FS) bw ML.ldConst
ld-is {int}   v = _ , _ , v , refl
ld-is {float} v = _ , _ , v , refl

-- ★ the compiled program (D458–D460): the bridge's facts of `ir` over `tbl`
-- (`ExprBuild.Bridged`; the compile pipeline's: `ExprLinked.bridged`)
module NewImage (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
  (bf : Once.LinCore.ExprBuild.Bridged (fs-numerics FS) (Interp.sig (FrameSemantics.fs-interp FS)) tbl ir) where
  module IT = Once.LinCore.FlatTop.ExprApex FS bw tbl ir bf
                ML.ldConst ML.ld-nl ML.wordOf ML.w-int ML.w-float entry-frame entry-regs

  image : AbstractTrace
  image = IT.XT.TP.image

  P′ : AbstractTrace
  P′ = room-checks image

  -- ★ the file's table: the image's own blocks (D462: `ImageBlocks.imageBlocks`, as `Emit.blocksOf`)
  U = Once.LinCore.Keys.Program.U (fs-numerics FS) bw IT.ds IT.f₀
  bs = Once.LinCore.ImageBlocks.imageBlocks (fs-numerics FS) bw U
  env = block-env (file-table (Backend.payload B) bs)

  -- the image's pointwise facts and its start (`ImageAll`)
  module IA = Once.LinCore.ImageAll.Img (fs-numerics FS) (fs-ffi FS) bw o IT.ds IT.f₀ ML.ldConst ld-is
  module IAF = IA.Fetch {FS}
  -- nothing falls into an entry (`ImageGuard`, D454)
  module IG = Once.LinCore.ImageGuard.G.Img (fs-numerics FS) (fs-ffi FS) bw {FS} IT.ds IT.f₀ ML.ldConst ML.ld-nl

  -- ★ WHAT THE NEW IMAGE OWES THE ARCH LAYER: that its externals miss its table (what
  -- master's `external-sigop-contract` assumes of its file: compiler symbols apart from the
  -- source's names). (Its run facts — a slot in the frame, a closure call's cell, a return
  -- owed and its budget — are the machine's gates now, B1.7b D456: nothing of the run is owed.)
  record Owed : Set where
    field
      o-ext-miss : ExtMiss FS env P′

  -- ★ THE ARITH TABLE (D462): every op call of the image names one of its blocks — an op of the
  -- universe's, lowered (`ImageAll.sigops`), canonical by the bridge (`FlatTop.canon`), so
  -- `Named` (`ImageOwned.named-call`)
  named : Data.List.Relation.Unary.All.All (BT.SigNamed bs) P′
  named = Data.List.Relation.Unary.All.tabulate λ {i} m {A} {B} si e →
    Once.LinCore.ImageOwned.named-call (fs-numerics FS) bw U IT.canon si (IA.sigops si (subst (λ j → j ∈ P′) e m))

  o-table : Owed → ArithTable P′ env
  o-table O = table P′ bs named (Owed.o-ext-miss O)

  -- ★ the image facts the arch layer reads: all proved
  emitted : Emitted image
  emitted = record
    { em-budget = IA.em-budget ; em-zero = IAF.em-zero ; em-start = IAF.em-start
    ; em-image = IA.em-image ; em-alloc = IA.em-alloc
    ; em-calls = IAF.em-calls ; em-code = IAF.em-code
    ; em-guard = IG.em-guard }

  -- ★★ THE NEW IMAGE ON THE ARCH: its run has the trace of the program (master's `conc-tr`)
  conc-trᴺ : Owed
           → Machine.trace (δ env (compile P′)) init ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
  conc-trᴺ O = sim (irProgram tbl ir) _ _ env emitted (o-table O)
                   (IT.flat-sound (λ {b} v → ML.ld {b} v image)) (IT.flat-ir (λ {b} v → ML.ld {b} v image))

  -- ★★ THE FILE: what the backend writes for the image (its code, its blocks' table, the
  -- externs `ex`; `Emit.emitCore`) runs with the program's trace
  file-trᴺ : (ex : List String) → Owed
           → run-file (Backend.file B P′ (file-table (Backend.payload B) bs) ex) ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
  file-trᴺ ex O = subst (λ T → T ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)) (sym (file-runs P′ bs ex)) (conc-trᴺ O)

  -- ★ the image and its blocks are the compiler's (`ExprImage`: what `Emit` writes), over the
  -- bridge's sources and main
  image-eq : image ≡ Once.LinCore.ExprImage.imageAt (fs-numerics FS) IT.BF.tl IT.BF.mpm
  image-eq = refl

  blocks-eq : bs ≡ Once.LinCore.ExprImage.blocksAt (fs-numerics FS) IT.BF.tl IT.BF.mpm
  blocks-eq = refl

  -- ★★ THE FILE THE COMPILER WRITES (`ExprImage.fileAt`) runs with the program's trace

  -- ★★ THE FILE IS WHAT THE ASSEMBLER DEMANDS (D464): the image's symbols are well-formed
  -- (`ImageSyms.image-wf`), so the backend's file of it is (`ArchSim.file-wf`)
  module IS = Once.LinCore.ImageSyms.Img (fs-numerics FS) (fs-ffi FS) bw o IT.ds IT.f₀ ML.ldConst ld-is IT.canon {FS}

  file-wfᴺ : Backend.AsmWF B (Backend.file B P′ (file-table (Backend.payload B) bs) (image-externs image))
  file-wfᴺ = file-wf _ _ _ bs (image-externs image) IS.image-wf

  -- …the file the compiler writes (`ExprImage.fileAt`, its externs the image's)

  ------------------------------------------------------------------------
  -- ★★ THE ALLOCATOR'S EXPANSION OF THE IMAGE ON THE ARCH (D468, the slab:
  -- `AllocExpandClasses.slab`): cells reused through free lists, the same trace
  ------------------------------------------------------------------------

  -- (the compiler's choice of allocator, `--alloc`)
  module _ (a : Once.CCC.Codegen.AllocExpandClasses.Alloc) where
    module XS = Once.Adequacy.ArchCorrectness.ExpandSim o A
    module PL = Once.CCC.Codegen.AllocExpandClasses.Choice a image
    module CL = Once.CCC.Codegen.AllocExpandClasses
    module CLF = Once.CCC.Codegen.AllocExpandClasses.Fetch {FS}
    module CD = Once.CCC.Codegen.AllocExpandEmitted.Code {FS} PL.C PL.small PL.in-range PL.fits
    module EM = Once.CCC.Codegen.AllocExpandEmitted {FS}

    imageˣ : AbstractTrace
    imageˣ = Once.CCC.Codegen.AllocExpand.expand PL.C image

    P″ : AbstractTrace
    P″ = room-checks imageˣ

    private
      -- an op the room-checked expansion calls is one the room-checked image calls
      sig-back : ∀ {A B} (si : Once.SigOp.Info.SigOpInfo A B) → instr-sigop si ∈ P″ → instr-sigop si ∈ P′
      sig-back si m = EM.∈-room image (CD.exp-sig 0 image IA.em-alloc si (EM.room-sig imageˣ si m))

      fetch-∈ : ∀ (xs : AbstractTrace) k {i} → fetch xs k ≡ just i → i ∈ xs
      fetch-∈ (x ∷ xs) Data.Nat.zero    refl = Data.List.Relation.Unary.Any.here refl
      fetch-∈ (x ∷ xs) (Data.Nat.suc k) e    = Data.List.Relation.Unary.Any.there (fetch-∈ xs k e)

      ∈-fetch : ∀ (xs : AbstractTrace) {i} → i ∈ xs → Σ ℕ λ k → fetch xs k ≡ just i
      ∈-fetch (x ∷ xs) (Data.List.Relation.Unary.Any.here refl) = 0 , refl
      ∈-fetch (x ∷ xs) (Data.List.Relation.Unary.Any.there m) = let (k , f) = ∈-fetch xs m in Data.Nat.suc k , f

    namedˣ : Data.List.Relation.Unary.All.All (BT.SigNamed bs) P″
    namedˣ = Data.List.Relation.Unary.All.tabulate λ {i} m {A} {B} si e →
      Once.LinCore.ImageOwned.named-call (fs-numerics FS) bw U IT.canon si (IA.sigops si (sig-back si (subst (λ j → j ∈ P″) e m)))

    -- the image's owed fact, at the expansion (its ops are the image's)
    ext-missˣ : Owed → ExtMiss FS env P″
    ext-missˣ O si k ex f =
      let (k′ , f′) = ∈-fetch P′ (sig-back si (fetch-∈ P″ k f)) in Owed.o-ext-miss O si k′ ex f′

    conc-trˣ : Owed
             → Machine.trace (δ env (compile P″)) init ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
    conc-trˣ O = XS.sim-exp PL.C PL.small PL.in-range PL.fits (irProgram tbl ir) IA.em-budget IA.tail env
                   (CL.Sz image) PL.uniform (CLF.sz-alloc image) (CLF.sz-free image)
                   IS.img-path IS.jmp-path IS.br-path IAF.no-lrec IAF.no-srec emitted
                   (IT.flat-sound (λ {b} v → ML.ld {b} v image))
                   (table P″ bs namedˣ (ext-missˣ O)) (IT.flat-ir (λ {b} v → ML.ld {b} v image))

    -- ★★ THE FILE OF THE EXPANSION (what the compiler writes: `ExprImage.fileAt`) runs with the
    -- program's trace, and is what the assembler demands
    file-trˣ : (ex : List String) → Owed
             → run-file (Backend.file B P″ (file-table (Backend.payload B) bs) ex) ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
    file-trˣ ex O = subst (λ T → T ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)) (sym (file-runs P″ bs ex)) (conc-trˣ O)

    file-atˣ : (ex : List String) → Owed
             → run-file (Once.LinCore.ExprImage.fileAt (fs-numerics FS) B a true IT.BF.tl IT.BF.mpm ex) ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
    file-atˣ ex O = file-trˣ ex O

    module ISX = IS.Xp PL.C

    -- (in the image's own names: the file's shape is the room-checked expansion's)
    file-wfˣ : Backend.AsmWF B (Backend.file B P″ (file-table (Backend.payload B) bs) (image-externs image))
    file-wfˣ = file-wf _ _ _ bs (image-externs image) ISX.image-wfˣ
    file-wf-atˣ : Backend.AsmWF B (Once.LinCore.ExprImage.fileAt (fs-numerics FS) B a true IT.BF.tl IT.BF.mpm
                                     (image-externs (Once.LinCore.ExprImage.imageAt (fs-numerics FS) IT.BF.tl IT.BF.mpm)))
    file-wf-atˣ = file-wfˣ


    ------------------------------------------------------------------------
    -- ★★ D480: THE ALLOCATOR AS A CALL (the default mode; `--inline-alloc` is the
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

    private
      ks-pos : ∀ k → k ∈ ksᶜ → 1 Data.Nat.≤ k
      ks-pos = OS.dsizes-pos image IA.em-alloc

      ks-in : ∀ q k → (fetch IA.tail q ≡ just (instr-alloc-heap k)) ⊎ (fetch IA.tail q ≡ just (instr-free-heap k)) → k ∈ ksᶜ
      ks-in q k e = OS.in-dsizes image (Data.Nat.suc q) k e

      emᵒ : Emitted imageᵒ
      emᵒ = OE.emitted ksᶜ IA.em-budget IA.tail emitted ks-pos ks-in IS.calls-apart

      -- an op the room-checked call image calls is one the room-checked image calls
      sig-backᶜ : ∀ {A B} (si : Once.SigOp.Info.SigOpInfo A B) → instr-sigop si ∈ P‴ → instr-sigop si ∈ P′
      sig-backᶜ si m = EM.∈-room image (Once.CCC.Codegen.AllocOutline.sig-out {FS} si ksᶜ IA.em-budget IA.tail
                         (CDC.exp-sig 0 imageᵒ (Emitted.em-alloc emᵒ) si (EM.room-sig imageᶜ si m)))

    namedᶜ : Data.List.Relation.Unary.All.All (BT.SigNamed bs) P‴
    namedᶜ = Data.List.Relation.Unary.All.tabulate λ {i} m {A} {B} si e →
      Once.LinCore.ImageOwned.named-call (fs-numerics FS) bw U IT.canon si (IA.sigops si (sig-backᶜ si (subst (λ j → j ∈ P‴) e m)))

    ext-missᶜ : Owed → ExtMiss FS env P‴
    ext-missᶜ O si k ex f =
      let (k′ , f′) = ∈-fetch P′ (sig-backᶜ si (fetch-∈ P‴ k f)) in Owed.o-ext-miss O si k′ ex f′

    -- ★★ THE CALL MODE ON THE ARCH: its run has the trace of the program
    conc-trᶜ : Owed
             → Machine.trace (δ env (compile P‴)) init ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
    conc-trᶜ O = XC.sim-call PLC.C PLC.small PLC.in-range PLC.fits (irProgram tbl ir) IA.em-budget IA.tail env
                   ksᶜ (CL.Sz imageᵒ) PLC.uniform
                   emitted (IT.flat-sound (λ {b} v → ML.ld {b} v image))
                   ks-pos (λ k m → OS.outline-sz ksᶜ IA.em-budget IA.tail k m) ks-in IS.skip-apart IS.calls-apart
                   IS.img-path IS.jmp-path IS.br-path IAF.no-lrec IAF.no-srec
                   (table P‴ bs namedᶜ (ext-missᶜ O)) (IT.flat-ir (λ {b} v → ML.ld {b} v image))

    -- ★★ THE CALL MODE'S FILE (what the compiler writes by default) runs with the program's trace,
    -- and is what the assembler demands
    file-atᶜ : (ex : List String) → Owed
             → run-file (Once.LinCore.ExprImage.fileAt (fs-numerics FS) B a false IT.BF.tl IT.BF.mpm ex) ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
    file-atᶜ ex O = subst (λ T → T ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)) (sym (file-runs P‴ bs ex)) (conc-trᶜ O)

    module ISC = IS.Xc PLC.C

    file-wfᶜ : Backend.AsmWF B (Backend.file B P‴ (file-table (Backend.payload B) bs) (image-externs image))
    file-wfᶜ = file-wf _ _ _ bs (image-externs image) ISC.image-wfᶜ
    file-wf-atᶜ : Backend.AsmWF B (Once.LinCore.ExprImage.fileAt (fs-numerics FS) B a false IT.BF.tl IT.BF.mpm
                                     (image-externs (Once.LinCore.ExprImage.imageAt (fs-numerics FS) IT.BF.tl IT.BF.mpm)))
    file-wf-atᶜ = file-wfᶜ

    -- ★★ THE FILE THE COMPILER WRITES, in either mode (`--inline-alloc`: `true`)
    file-at : (inl : Bool) (ex : List String) → Owed
            → run-file (Once.LinCore.ExprImage.fileAt (fs-numerics FS) B a inl IT.BF.tl IT.BF.mpm ex) ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
    file-at true  = file-atˣ
    file-at false = file-atᶜ

    file-wf-at : (inl : Bool) → Backend.AsmWF B (Once.LinCore.ExprImage.fileAt (fs-numerics FS) B a inl IT.BF.tl IT.BF.mpm
                                     (image-externs (Once.LinCore.ExprImage.imageAt (fs-numerics FS) IT.BF.tl IT.BF.mpm)))
    file-wf-at true  = file-wf-atˣ
    file-wf-at false = file-wf-atᶜ
