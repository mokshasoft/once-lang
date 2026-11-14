-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalOp — plan 0.146 B1.4b (D426): AN OP'S STEP with the whole relation, relative to the
-- machine's world: an answered op to the next path, a halting op to a halted machine.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}


open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool using (false; true)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.IR.Semantics.Event using (SigOpEvent)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
import Once.Memory.HeapAddress
import Once.LinCore.Moves
import Data.Nat.Properties


module Once.LinCore.GlobalOp
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw using (Frame; frame; frameOf; budget; wsz; ws; EP; OP)
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.ImagePt fmt ans bw using (Sub; Pt; at; disp; next; body; whole)
open import Once.LinCore.LowAt fmt ans bw using (module At)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.PointAt fmt ans bw using (module Ctl)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
open import Once.LinCore.LoopStep fmt ans bw using (module Loops)
open import Once.LinCore.CallStep fmt ans bw using (module Calls; module Frames)
open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
open import Once.LinCore.TrampAt fmt ans bw using (under; module TrImg; module Tr)

open import Once.LinCore.Global fmt ans bw using (module Relate)
open import Once.LinCore.GlobalTramp fmt ans bw using (module TrampR)
open import Once.LinCore.GlobalTrampO fmt ans bw using (module TrampO)
open import Once.LinCore.OpStep fmt ans bw using (module OpR; module OpSim; op-n)
open import Once.LinCore.StepOp fmt ans bw using (module Agree)
open import Once.LinCore.GlobalTrView fmt ans bw using (module TrV)

module OpG {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrV {FS} ds f ldConst ld-nl wordOf using (Is-tf0; it-tf0; fopen-v)
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin; trFin)
  open Program ds f using (U)
  open ProgramRun ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst
  open Calls {FS} ds f ldConst ld-nl wordOf using (blockR; module K; module From; call-core)
  open Rel {FS} U wordOf using (EnvW; StkW)
  open FlatMachine {FS} using (FlatState; floc; falloc; fret)
  open FrameSemantics FS using (_≺_)
  open TrImg {FS} ds f ldConst ld-nl using (image-tr)
  open Tr U ncty ldConst using (trAt)
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; vnu; SlotsAt; cellPtr)
  open FlatMachine {FS} using (fpc)
  open import Once.LinCore.Moves {FS} using (slot; InBlk; r-inb; inb-pt)
  open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
  open Sim {FS} U wordOf using (envW-heap; stkW-heap; envW-frame; slots-frame; cntE; cntS)
  open Rel {FS} U wordOf using (cellLoc)
  open import Once.LinCore.FreshI fmt ans bw using (module Cells)
  open Cells {FS} U wordOf using (FreshR)
  open import Once.LinCore.Moves {FS} using (Old)
  open FrameSemantics FS using (≺-trans; ≺-irrefl)
  open import Once.LinCore.ImageRun fmt ans bw using (StepI)
  open import Once.LinCore.LocalStep fmt ans bw using (module Steps)
  open import Once.LinCore.StepKinds fmt ans bw using (Local; LocalC; StraightC; straight-local; CoveredC; covered-elim)
  open import Once.LinCore.HeldI fmt ans bw using (InvI)
  open import Once.LinCore.LabelsI fmt ans bw using (module Img)
  open import Once.LinCore.LowAt fmt ans bw using (Inside)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Once.LinCore.Moves {FS} using (Keep; k-frame; k-ret; k-saved; k-other)
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret)
  open Img {FS} ds f ldConst ld-nl using (image-label)
  open Frames {FS} using (Called)
  open Called
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; co-frame; co-ret; co-saved; co-rest; co-next)
  open import Once.LinCore.LowerSimH fmt ans bw using (module SimH)
  open SimH {FS} U wordOf using (open1-sim)
  open import Once.LinCore.LowAt fmt ans bw using (in-trans; in-r)
  open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)
  open ImgE {FS} ds f ldConst ld-nl using (image-at)
  open Program ds f using (blocks-in)
  open import Data.List.Properties using (length-++; ++-assoc)
  open Sim {FS} U wordOf using (len-mvPS)
  open import Once.LinCore.PointAt fmt ans bw using (module Fetch)
  open Fetch {FS} using (in-seg)
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ; Ran; r-pc; r-keep; k-halt)
  open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
  open SimF {FS} U wordOf using (leave; area-gen)
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in; FreeIn)
  open FreeIn
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)

  open import Once.LinCore.Moves {FS} using (r-next; r-old; r-top)
  open import Once.LinCore.NoCell fmt ans bw using (sub-nc; comp-nc; block-nc; allK-nt)
  open Related

  Arrives : ∀ {T sh U′} → List SigOpEvent → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
  Arrives E c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′ × LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs) ++ E

  private
    nat-r0 : ∀ {a b : ℕ} → a + b ≡ 0 → b ≡ 0
    nat-r0 {zero} e = e
    nat-r0 {suc a} ()

  open Agree {FS} U wordOf using (OpVal; OpHalt)
  open import Once.LinCore.Moves {FS} using (k-inb)
  open OpSim {FS} U ncty ldConst wordOf using (or-frame; or-ret; or-saved; or-other; or-top; or-old; or-next; or-inb; or-log)
  module OS = OpR {FS} U ncty ldConst wordOf image main j₀ L₀ˢ start-root
  module OK {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = OpR {FS} U ncty ldConst wordOf image (blockᴵ κ) (idx p) (L₀ᵇ κ p) (blockR p)

  -- ★ AN ANSWERED OP (i-prim at `lop`): to the next path, its answer on the stack
  gop : ∀ {T Γ} {ds′ : Defs Γ} {Es} {s : Sig} {S V} {k : Codeᴵ (Es ∣ ⌜ scod s ⌝ ∷ S) V} {r : Ret V T} {es : Slots Es}
          {x : MV ⌜ sdom s ⌝} {y : MV ⌜ scod s ⌝} {os : Stk S} {n n′ h t E fs}
          (P : Pnt (prim ds′ (lop s) ⨾ k)) → Run ds′ (lop s) mone x n (gives y n′) t
      → InvI (es ∥ x ∷ˢ os) r n h → HereP P (es ∥ x ∷ˢ os) fs
      → AllocState.next-heap-ref (falloc fs) ≡ n
      → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
      → InBlk fs → OpVal s x y E fs
      → Arrives E k r (es ∥ y ∷ˢ os) n′ fs
  gop {r = r} {fs = fs} (p-start (at sb)) run inv H nx ok I ag = case OS.st-op sb H ag of λ where
    (N , fs′ , st , H′ , OR) →
      N , fs′ , st , record { g-pt = p-start (at (next sb)) ; g-here = H′ ; g-next = trans (or-next OR) (trans nx (sym (op-n run)))
                            ; g-ret = ctx-to (sym (or-frame OR)) (sym (or-ret OR)) (sym (or-saved OR))
                                        (ret-top (or-other OR)
                                           (λ y le → trans (cong (λ g → LocState.stackMem (floc fs′) g y) (sym (or-frame OR))) (or-top OR y le))
                                           (or-old OR) (subst (FreshR r) (sym nx) (fresh-ret inv)) ok)
                            ; g-blk = or-inb OR I } , or-log OR
  gop {r = r} {fs = fs} (p-block p (at sb)) run inv H nx ok I ag = case OK.st-op p sb H ag of λ where
    (N , fs′ , st , H′ , OR) →
      N , fs′ , st , record { g-pt = p-block p (at (next sb)) ; g-here = H′ ; g-next = trans (or-next OR) (trans nx (sym (op-n run)))
                            ; g-ret = ctx-to (sym (or-frame OR)) (sym (or-ret OR)) (sym (or-saved OR))
                                        (ret-top (or-other OR)
                                           (λ y le → trans (cong (λ g → LocState.stackMem (floc fs′) g y) (sym (or-frame OR))) (or-top OR y le))
                                           (or-old OR) (subst (FreshR r) (sym nx) (fresh-ret inv)) ok)
                            ; g-blk = or-inb OR I } , or-log OR
  gop (p-tramp p pt) run inv (() , H) nx ok I ag

  -- ★ A HALTING OP (i-opend): to a halted machine
  gopend : ∀ {Γ} {ds′ : Defs Γ} {Es} {s : Sig} {S V} {k : Codeᴵ (Es ∣ ⌜ scod s ⌝ ∷ S) V} {es : Slots Es}
             {x : MV ⌜ sdom s ⌝} {os : Stk S} {E fs}
             (P : Pnt (prim ds′ (lop s) ⨾ k)) → HereP P (es ∥ x ∷ˢ os) fs → OpHalt s x E fs
         → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × LocState.halted (floc fs′) ≡ true × LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs) ++ E
             × LocState.left (floc fs′) ≡ LocState.left (floc fs) × LocState.halted (floc fs) ≡ false
  gopend (p-start (at sb)) H ag = OS.st-opend sb H ag
  gopend (p-block p (at sb)) H ag = OK.st-opend p sb H ag
  gopend (p-tramp p pt) (() , H) ag
