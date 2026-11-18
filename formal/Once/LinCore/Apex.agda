-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Apex — plan 0.146 B1.7c (D460): ★ THE NEW IMAGE ON ANY ARCH.
--
-- An arch is an `ArchSim` (`Adequacy.ArchCorrectness.Interface`). Over it,
-- the compiled program's new image (the bridge's facts `bf`, D455–D457) has
-- the program's trace: the flat theorem (`FlatTop.ExprApex`) at the arch's
-- start, the image's shape facts (`ImageAll`, `ImageGuard`, and what it
-- still owes, `Owed`: B1.7b), its arith table (D459: `ImageOwned`), into
-- the arch's theorem (`ArchSim.sim`). Nothing here names an arch.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Name using (CanonicalName)
open import Once.Adequacy.ArchCorrectness.Interface using (ArchSim; module ArchSim; ExtMiss)
open import Once.Target.Backend using (Backend; module Backend; file-table)
open import Data.Nat using (ℕ)
open import Once.LinCore.Flat using (Base; int; float)

module Once.LinCore.Apex (o : CanonicalName) {B : Backend} (A : ArchSim o B) (bw : Base → ℕ) where

open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.Adequacy.MachineTrace using (module Machine)
open import Once.Adequacy.SourceTrace using (⟦_⟧IRᵗ)
open import Once.Denotation.Program using (IRFun; irProgram)
open import Once.IR.Semantics.Trace using (module Interp)
open import Once.CCC.FrameSemantics using (fs-numerics; fs-ffi; module FrameSemantics)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-ret; instr-call-closure; SV-Ptr; SV-Code; module LocState; module AllocState)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.Locations using (Slot; AtDynamic)
open import Once.CCC.Machine.InstrSlot using (slot-of)
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

open ArchSim A
open FlatMachine {FS} using (fetch; find-thunk; fpc; floc; fclosure; fret; falloc)
open Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq using (Emitted; Reachable)

private
  fmt = fs-numerics FS
  ι   = FrameSemantics.fs-interp FS

module ML = Once.LinCore.MachineLit FS bw

-- a constant's loader is an `instr-load-const`
ld-is : Once.LinCore.ImageAll.LoadConst fmt (fs-ffi FS) bw ML.ldConst
ld-is {int}   v = _ , _ , v , refl
ld-is {float} v = _ , _ , v , refl

-- ★ the compiled program (D455–D457): the bridge's facts of `ir` over `tbl`
-- (`ExprBuild.Bridged`; the compile pipeline's: `ExprLinked.bridged`)
module NewImage (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
  (bf : Once.LinCore.ExprBuild.Bridged fmt (Interp.sig ι) tbl ir) where
  module IT = Once.LinCore.FlatTop.ExprApex FS bw tbl ir bf
                ML.ldConst ML.ld-nl ML.wordOf ML.w-int ML.w-float entry-frame entry-regs

  image : AbstractTrace
  image = IT.XT.TP.image

  P′ : AbstractTrace
  P′ = room-checks image

  -- ★ the file's table: the image's own blocks (D459: `ImageBlocks.imageBlocks`, as `Emit.blocksOf`)
  U = Once.LinCore.Keys.Program.U fmt bw IT.ds IT.f₀
  bs = Once.LinCore.ImageBlocks.imageBlocks fmt bw U
  env = block-env (file-table (Backend.payload B) bs)

  -- the image's pointwise facts and its start (`ImageAll`)
  module IA = Once.LinCore.ImageAll.Img fmt (fs-ffi FS) bw o IT.ds IT.f₀ ML.ldConst ld-is
  module IAF = IA.Fetch {FS}
  -- nothing falls into an entry (`ImageGuard`, D451)
  module IG = Once.LinCore.ImageGuard.G.Img fmt (fs-ffi FS) bw {FS} IT.ds IT.f₀ ML.ldConst ML.ld-nl

  -- ★ WHAT THE NEW IMAGE OWES THE ARCH LAYER: `RunContext.Emitted`'s fields not yet proved
  -- (the run's facts: the machine gates, B1.7b), and that its externals miss its table
  record Owed : Set where
    field
      -- D452: a slot the run addresses is inside the current frame
      o-slots  : ∀ fs (i : AbstractInstr) (slot : Slot) → Reachable image 0 fs
               → fetch image (fpc fs) ≡ just i → slot-of i ≡ just slot
               → slot < AllocState.frame-slots (falloc fs)
      o-call-site : ∀ fs → Reachable image 0 fs → fetch image (fpc fs) ≡ just instr-call-closure
                  → Σ HeapLocation (λ hl → Σ LabelId (λ ℓ → Σ ℕ (λ j →
                      (fclosure fs ≡ SV-Ptr (AtDynamic hl))
                      × (LocState.heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ))
                      × (find-thunk image ℓ ≡ just j))))
      o-ret-owes  : ∀ fs (b : ℕ) → Reachable image 0 fs → fetch image (fpc fs) ≡ just (instr-ctrl (c-ret b))
                  → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest))
      o-ret-budget : ∀ fs (b : ℕ) → Reachable image 0 fs → fetch image (fpc fs) ≡ just (instr-ctrl (c-ret b))
                   → b ≡ AllocState.frame-slots (falloc fs)
      -- an external op's symbol is not a block's (what master's `external-sigop-contract`
      -- assumes of its file: compiler symbols apart from the source's names)
      o-ext-miss : ExtMiss FS env P′

  -- ★ THE ARITH TABLE (D459): every op call of the image names one of its blocks — an op of the
  -- universe's, lowered (`ImageAll.sigops`), canonical by the bridge (`FlatTop.canon`), so
  -- `Named` (`ImageOwned.named-call`)
  named : Data.List.Relation.Unary.All.All (BT.SigNamed bs) P′
  named = Data.List.Relation.Unary.All.tabulate λ {i} m {A} {B} si e →
    Once.LinCore.ImageOwned.named-call fmt bw U IT.canon si (IA.sigops si (subst (λ j → j ∈ P′) e m))

  o-table : Owed → ArithTable P′ env
  o-table O = table P′ bs named (Owed.o-ext-miss O)

  -- ★ the image facts the arch layer reads: the proved ones and the owed ones
  emitted : Owed → Emitted image
  emitted O = record
    { em-budget = IA.em-budget ; em-zero = IAF.em-zero ; em-start = IAF.em-start
    ; em-image = IA.em-image ; em-alloc = IA.em-alloc
    ; em-calls = IAF.em-calls ; em-code = IAF.em-code
    ; em-slots = Owed.o-slots O
    ; em-guard = IG.em-guard
    ; em-call-site = Owed.o-call-site O ; em-ret-owes = Owed.o-ret-owes O ; em-ret-budget = Owed.o-ret-budget O }

  -- ★★ THE NEW IMAGE ON THE ARCH: its run has the trace of the program (master's `conc-tr`)
  conc-trᴺ : Owed
           → Machine.trace (δ env (compile P′)) init ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ fmt ι
  conc-trᴺ O = sim (irProgram tbl ir) _ _ env (emitted O) (o-table O)
                   (IT.flat-sound (λ {b} v → ML.ld {b} v image)) (IT.flat-ir (λ {b} v → ML.ld {b} v image))

  -- ★★ THE FILE: what the backend writes for the image (its code, its blocks' table, the
  -- externs `ex`; `Emit.emitCore`) runs with the program's trace
  file-trᴺ : (ex : List String) → Owed
           → run-file (Backend.file B P′ (file-table (Backend.payload B) bs) ex) ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ fmt ι
  file-trᴺ ex O = subst (λ T → T ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ fmt ι) (sym (file-runs P′ bs ex)) (conc-trᴺ O)
