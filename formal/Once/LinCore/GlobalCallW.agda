-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalCallW — plan 0.146 B1.4b (D434, D442): A MANY-USE BODY'S TRAMPOLINE'S INNER CALL
-- (beside `GlobalDispatchW`, for its build time).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}


open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool using (false)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
import Once.Memory.HeapAddress
import Once.LinCore.Moves
import Data.Nat.Properties


module Once.LinCore.GlobalCallW
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt bw
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt bw
open import Once.LinCore.Layout fmt bw using (Frame; frame; frameOf; budget; ws; module Frame)
open Frame using (EP; OP)
open import Once.LinCore.Lower fmt bw
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
open import Once.LinCore.LiveRun fmt ans bw using (LiveG; FreshAl)
open import Once.LinCore.GlobalTramp fmt ans bw using (module TrampR)
open import Once.LinCore.GlobalTrampO fmt ans bw using (module TrampO)
open import Once.LinCore.GlobalTrampW fmt ans bw using (module TrampW)

module CallW {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampW {FS} ds f ldConst ld-nl wordOf using (tw-call; tW-pos₂)
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin; trFin)
  open Program ds f using (U)
  open Program ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst
  open Calls {FS} ds f ldConst ld-nl wordOf using (blockR; module K; module From; call-core)
  open Rel {FS} U wordOf using (EnvW; StkW)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc; falloc; fret; fpc)
  open FrameSemantics FS using (_≺_)
  open TrImg {FS} ds f ldConst ld-nl using (image-tr)
  open Tr U ncty ldConst using (trAt)
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; vnu; SlotsAt; cellPtr)
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
  open import Once.LinCore.Moves {FS} using (Keep; module Keep)
  open Keep using (k-frame; k-saved; k-ret; k-other)
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret; away-[])
  open Img {FS} ds f ldConst ld-nl using (image-label)
  open Frames {FS} using (Called)
  open Called
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; module CallOutA)
  open CallOutA using (co-frame; co-saved; co-ret; co-rest; co-next)
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
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ; Ran; module Ran)
  open Ran using (r-keep; r-pc)
  open Keep using (k-halt)
  open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
  open SimF {FS} U wordOf using (leave; area-gen)
  open CallOutA using (co-pc; co-halt)
  open import Once.LinCore.LowerSimG {FS} using (ClosInω)
  open ClosInω
  open import Once.LinCore.CallStepH fmt ans bw using (module FramesH)
  open FramesH {FS} using (CalledH)
  open CalledH
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)
  open Ran using (r-next; r-old; r-top)
  open import Once.LinCore.NoCell fmt ans bw using (sub-nc; comp-nc; block-nc; allK-nt)
  open Related

  Arrives : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
  Arrives c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′ × LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

  private
    nat-r0 : ∀ {a b : ℕ} → a + b ≡ 0 → b ≡ 0
    nat-r0 {zero} e = e
    nat-r0 {suc a} ()


  -- ★ ITS INNER CALL (i-call at its depth 1): the body, the trampoline saved above it; the body's
  -- area pointer the trampoline's (the dispatcher's area, D442)
  gcallω : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} {r : Ret (Fn many g A B ∷ [] ∣ B ∷ []) T}
             {es : Slots (X ∷ Fn many g A B ∷ [])} {a : MV A} {os : Stk []} {n h fs} (p : under (ktrω ds′ b γ) ∈ allK U)
         → InvI (es ∥ a ∷ˢ os) r n h → HereTr (tw1 p) (es ∥ a ∷ˢ os) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rtramp {κ = ktrω ds′ b γ} p) (trFin (idx p) (ktrω ds′ b γ)) r
                 (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs → LiveG r (es ∥ a ∷ˢ os) fs → FreshAl (falloc fs)
         → Arrives (blockᴵ (kbodyω ds′ b γ)) (frm {t = just X} {Es = Fn many g A B ∷ []} (epop ⨾ end) es os r) (topv (just X) es ∥ a ∷ˢ []ˢ) n fs
  gcallω {ds′ = ds′} {b} {γ} {r = r} {es = es@(vw x (vw (mfn i lam _) []ᵉ))} {a = a} {os = []ˢ} {n = n} {fs = fs} p inv T1 nx ok I lv F =
    case tw-call p T1 of λ where
      (N , fs′ , run , H′ , CD) →
        N , fs′ , run ,
        record { g-pt = p-block p (at whole) ; g-here = H′ ; g-next = trans (dh-next CD) nx
               ; g-ret = ok-callω p cur (AllocState.frame-slots (falloc fs)) (AllocState.saved-frames (falloc fs)) (fret fs)
                           refl refl
                           (trans (dh-ret CD) (cong (_∷ fret fs) (trans (cong (λ z → suc (suc z)) (TrW1.w1-pc T1)) (sym (tW-pos₂ p)))))
                           (dh-saved CD) (TrW1.w1-slots T1) (under-cur CD)
                           (trans (dh-area CD) (sym (trans (dh-others CD cur 0 (callee-≢ cur bb)) (TrW1.w1-s0 T1))))
                           (ret-deep (AllocState.current-frame (falloc fs′)) (under-cur CD)
                              (λ f′ y ne → dh-others CD f′ y (λ e → ne (trans (sym e) (sym (dh-frame CD))))) (dh-old CD)
                              (subst (FreshR r) (sym nx) (fresh-ret inv)) (away-[] r) ok)
               ; g-blk = dh-inb CD I
               ; g-live = proj₁ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv F (dh-freed CD) (dh-bsize CD) (dh-next CD))
               ; g-fal = proj₂ (live-moved {fs = fs} {fs′ = fs′} st₁ (λ _ → no-alloc-tmp) inv nx lv F (dh-freed CD) (dh-bsize CD) (dh-next CD)) } , dh-log CD
    where
      st₁ = StepI.i-call {κ = kbodyω ds′ b γ} {k = epop ⨾ end} {r = r} {es = es} {a = a} {os = []ˢ} {n = n}
      cur = AllocState.current-frame (falloc fs)
      bb = fbudget (frameOf (blockᴵ (kbodyω ds′ b γ)))
      under-cur : ∀ {fs′ r′ sv ap} → CalledH fs fs′ r′ bb sv ap → AllocState.current-frame (falloc fs′) ≺ cur
      under-cur CD = subst (_≺ cur) (sym (dh-frame CD)) (callee-below cur bb)
