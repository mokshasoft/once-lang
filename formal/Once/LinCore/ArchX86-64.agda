-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ArchX86-64 — plan 0.146 B1.6: ★ THE NEW IMAGE ON x86-64, IN
-- MASTER'S APEX SHAPE (`ArchCorrectness.X86-64.conc-tr`). Top-down: composed
-- as master's from what is proved — the flat theorem (`FlatTop.IRTop`), the
-- arch simulation (`events-agree-boot`, generic in the program), the boot's
-- room check (`RoomEvents.ev-boot`) — with what the new image still owes the
-- arch layer as named fields of `Owed`, the work list of B1.6/B1.7.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Name using (CanonicalName)
import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB
open import Data.List using (List; [])
open import Once.Denotation.Program using (IRFun; IRProgram; irProgram; LinkedProgram; runIR)
open import Once.IR.Semantics.Trace using (Interp; module Interp; pureHalf)
import Once.IR
import Once.IRTy
import Once.LinCore.FromIR

module Once.LinCore.ArchX86-64
  (o : CanonicalName) (tbl : List IRFun) (ι : Interp)
  (x86-64-reg-range : RB.RegRange o ι)
  (x86-64-addr-no-wrap : RB.AddrNoWrap o ι)
  (x86-64-lit-fits : RB.LitFits o ι)
  where

open import Data.Nat using (ℕ; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function using (case_of_)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.Adequacy.MachineTrace using (module Machine)
open import Once.Adequacy.SourceTrace using (⟦_⟧IRᵗ)
open import Once.Target.Arch using (x86-64; arch-numerics)
open import Once.Adequacy.BudgetApex (arch-numerics x86-64) using (budget-apex-⊑; BudgetFact⊑; budget-fact-of)
open import Once.Arith.Backend.CallAnswer using (answer-at)
open import Once.Adequacy.CPU.X86-64 using (call-at-x86-64; ev-x86-64; block-env; val-x86-64)
import Once.Arith.Backend.X86-64.RunTrace as RTx
import Once.CCC.Target.X86-64.Semantics as X
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.Adequacy.RoomChecksEvents using (module RoomEvents)
open import Once.CCC.Machine.SMCore using (AbstractTrace)
import Once.Compile as C
open import Once.LinCore.Flat using (Base; int; float)

-- master's x86-64 apex: its machine, its entry, its arch simulation
open import Once.Adequacy.ArchCorrectness.X86-64 o tbl ι x86-64-reg-range x86-64-addr-no-wrap x86-64-lit-fits
  using (x86-64-frame-semantics; entry-frame-x86-64; module FFOx; entry-corr; entry-wf; entry-like)
open import Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim o
  x86-64-frame-semantics refl refl
  x86-64-reg-range
  (RB.AddrNoWrap.ret-no-wrap x86-64-addr-no-wrap)
  (RB.LitFits.tag-fits x86-64-lit-fits) (RB.LitFits.lit-fits x86-64-lit-fits) (RB.float-fits o ι)
  using (events-agree-boot; AgreeAt; reach-start; mkRunAt; x86-64-arith-table)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunLow o x86-64-frame-semantics slot-size refl using (RunLow; low-start)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o x86-64-frame-semantics slot-size refl using (Emitted; Reachable)
open import Once.CCC.FrameSemantics using (fs-numerics; fs-ffi)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; instr-ctrl; c-call-fn; c-entry; c-jmp; c-ret; instr-load-code-addr; instr-call-closure
        ; SV-Ptr; SV-Code; module LocState; module AllocState)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {x86-64-frame-semantics} using (fetch; find-fn; find-thunk; find-label; fpc; floc; fclosure; fret; falloc)
open import Once.CCC.Machine.Locations using (Slot; AtDynamic)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.CCC.Codegen.SlotSeg using (seg-at; mkSeg; SegState; module SegState)
open import Once.CCC.Codegen.LabelSeg using (mention-at)
open import Once.CCC.Label using (LabelId; EntryId)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Data.Nat using (_<_)
open import Data.Sum using (_⊎_)
open import Data.List using (_∷_)

-- a base value is one word (`Spec.ABI`)
bw : Base → ℕ
bw int   = 1
bw float = 1

import Once.LinCore.MachineLit
module ML = Once.LinCore.MachineLit x86-64-frame-semantics bw
import Once.LinCore.FlatTop
import Once.LinCore.ImageAll
import Once.LinCore.ImageGuard

-- a constant's loader is an `instr-load-const`
ld-is : Once.LinCore.ImageAll.LoadConst (fs-numerics x86-64-frame-semantics) (fs-ffi x86-64-frame-semantics) bw ML.ldConst
ld-is {int}   v = _ , _ , v , refl
ld-is {float} v = _ , _ , v , refl

module NewImage (p : IRProgram) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
  (tp : _) (etp : _) (f : _) (ef : _)
  (lk : LinkedProgram (Interp.sig ι) (irProgram tbl ir)) where
  module IT = Once.LinCore.FlatTop.IRTop x86-64-frame-semantics bw tbl ir tp etp f ef
                ML.ldConst ML.ld-nl ML.wordOf ML.w-int ML.w-float entry-frame-x86-64 FFOx.entry-regs lk

  image : AbstractTrace
  image = IT.TP.image

  P′ : AbstractTrace
  P′ = room-checks image

  env = block-env (C.blocks-x86-64 p)

  -- the image's pointwise facts and its start (`ImageAll`)
  module IA = Once.LinCore.ImageAll.Img (fs-numerics x86-64-frame-semantics) (fs-ffi x86-64-frame-semantics) bw o
                IT.TP.ds IT.TP.f₀ ML.ldConst ld-is
  module IAF = IA.Fetch {x86-64-frame-semantics}
  -- nothing falls into an entry (`ImageGuard`, D451)
  module IG = Once.LinCore.ImageGuard.G.Img (fs-numerics x86-64-frame-semantics) (fs-ffi x86-64-frame-semantics) bw
                {x86-64-frame-semantics} IT.TP.ds IT.TP.f₀ ML.ldConst ML.ld-nl

  -- ★ WHAT THE NEW IMAGE OWES THE ARCH LAYER: `RunContext.Emitted`'s fields not yet proved
  -- (the image's shape, then the run's facts), and the arith blocks
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
      -- the arith blocks the image's sigops run (B1.7: the compiled image is the new one)
      o-table : x86-64-arith-table P′ env

  -- ★ the image facts the arch layer reads: the proved ones and the owed ones
  emitted : Owed → Emitted image
  emitted O = record
    { em-budget = IA.em-budget ; em-zero = IAF.em-zero ; em-start = IAF.em-start
    ; em-image = IA.em-image ; em-alloc = IA.em-alloc
    ; em-calls = IAF.em-calls ; em-code = IAF.em-code
    ; em-slots = Owed.o-slots O
    ; em-guard = IG.em-guard
    ; em-call-site = Owed.o-call-site O ; em-ret-owes = Owed.o-ret-owes O ; em-ret-budget = Owed.o-ret-budget O }

  δc = RTx.Run.δ val-x86-64 (answer-at (arch-numerics x86-64) ι call-at-x86-64) ev-x86-64 env (compile-trace P′)

  private
    retarget : ∀ {A : ℕ → _} {o o′ c c′} → o ≡ o′ → c ≡ c′
             → Σ ℕ (λ M → AgreeAt (A M) o c M) → Σ ℕ (λ M → AgreeAt (A M) o′ c′ M)
    retarget refl refl x = x

  -- ★★ THE NEW IMAGE ON x86-64: its run has the trace of the program (master's `conc-tr`)
  conc-trᴺ : Owed
           → Machine.trace δc ([] , X.initState) ⊑ᵗ⟨ _≡_ ⟩ ⟦ just (irProgram tbl ir) ⟧IRᵗ (arch-numerics x86-64) ι
  conc-trᴺ O = budget-apex-⊑ δc ([] , X.initState) ι (runIR (arch-numerics x86-64) (pureHalf ι) (irProgram tbl ir)) fact
    where
      run₀ : RunLow P′ FFOx.start-flat
      run₀ = low-start image FFOx.start-flat
               (mkRunAt (emitted O) (reach-start FFOx.start-flat (entry-like 0) refl (IT.flat-sound (λ {b} v → ML.ld {b} v IT.TP.image))))
               refl
      fact : BudgetFact⊑ δc ([] , X.initState) ι (runIR (arch-numerics x86-64) (pureHalf ι) (irProgram tbl ir))
      fact k = case IT.flat-ir (λ {b} v → ML.ld {b} v IT.TP.image) k of λ where
        (N , e , c) →
          let open RoomEvents {x86-64-frame-semantics} image using (ev-boot)
              boot = ev-boot N FFOx.start-flat 0 refl _ refl
              agree₀ = events-agree-boot (proj₁ boot) ev-x86-64 env P′ FFOx.start-flat X.initState _ _ (entry-corr P′)
                         (entry-wf 0) tt refl (Owed.o-table O) run₀ refl refl refl refl refl refl
              agree = retarget (proj₁ (proj₂ boot)) (proj₂ (proj₂ boot)) agree₀
          in budget-fact-of δc ([] , X.initState) ι (runIR (arch-numerics x86-64) (pureHalf ι) (irProgram tbl ir)) k (proj₁ agree) _ _ _
               (RTx.Run.runN-events val-x86-64 (answer-at (arch-numerics x86-64) ι call-at-x86-64) ev-x86-64 env (compile-trace P′) (proj₁ agree) [] X.initState)
               (cong (RTx.Run.outObs val-x86-64 (answer-at (arch-numerics x86-64) ι call-at-x86-64) ev-x86-64 env (compile-trace P′)) e)
               c (proj₂ agree)
