-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalRetTC — plan 0.146 B1.4b (D438, D434): A TRAMPOLINE'S RETURNS, by the trampoline
-- (`GretC` at each kind: a one-shot's, an observation's, a free's) (beside `GlobalRetT`, for its build time).
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


module Once.LinCore.GlobalRetTC
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt using (_⊗t_; Defs; FS; Gd; LF∙; LTm; Nu; One; Tm; module Defs; module Tm)
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.Events fmt ans bw using (ds; p-halt; Γ)
open import Once.LinCore.Values fmt bw using (MV; Trace; module MV)
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt bw using (Codeᴵ; Insᴵ; Key; blockᴵ; case; end; ktr1; ktrf; ktro; module Codeᴵ; module Insᴵ; module Key)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt bw using (allK; os; module Program)
open import Once.LinCore.Layout fmt bw using (Frame; frame; frameOf; budget; wsz; ws; envW; opW; module Frame)
open Frame using (EP; OP)
open import Once.LinCore.Lower fmt bw using (idx; module Lowering; module Program′)
open import Once.LinCore.Words fmt ans bw using (module Rel)
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
open import Once.LinCore.GlobalTrampF fmt ans bw using (module TrampF)
open import Once.LinCore.GlobalCall fmt ans bw using (module CallR)
open import Once.LinCore.GlobalRetB fmt ans bw using (module RetB)

module RetTC {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf using (DSite; HereF; HereP; Related; RetOK; TrM; d-block; d-start; dsiteFin; dsitePos; dsiteRoot; dsiteφ; rootOf; rtramp; s-tramp; s-trampf; s-trampo; sitePos; siteφ; tf2; to2; tp2; trM; trMc; trPos; ≺-≢; module DSite; module HereF; module Related; module RetOK; module S; module TrM)
  open TrampR {FS} ds f ldConst ld-nl wordOf using (tr-back′; tr-end)
  open TrampO {FS} ds f ldConst ld-nl wordOf using (tOM; to-end)
  open TrampF {FS} ds f ldConst ld-nl wordOf using (tf-end)
  open CallR {FS} ds f ldConst ld-nl wordOf using (module GCall)
  open RetB {FS} ds f ldConst ld-nl wordOf using (module GRetB)
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin; trFin)
  open Program ds f using (U)
  open Program ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst using (Tp; fbudget)
  open Calls {FS} ds f ldConst ld-nl wordOf using (blockR; module K; module From; call-core)
  open Rel {FS} U wordOf using (EnvW; StkW)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc; falloc; fret; fpc)
  open FrameSemantics FS using (_≺_)
  open TrImg {FS} ds f ldConst ld-nl using (image-tr)
  open Tr U ncty ldConst using (trAt)
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; vone; SlotsAt; cellPtr)
  open import Once.LinCore.Moves {FS} using (slot; InBlk; inb-pt)
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
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret)
  open Img {FS} ds f ldConst ld-nl using (image-label)
  open Frames {FS} using (Called)
  open Called
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; module CallOutA)
  open CallOutA using (co-frame; co-saved; co-ret; co-rest; co-next; co-log)
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
  open CallOutA using (co-slots; co-pc; co-size; co-halt)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)


  module GRetTC where
    open Related
    open GCall using (ArrivesAt)
    open GRetB

    module _ where
      rc-tramp : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b}
                (p₂ : under (ktr1 ds′ b γ) ∈ allK U) → GretC (s-tramp p₂)
      rc-tramp p₂ {es = []ᵉ} {os = []ˢ} {fs = fs} (p-block p (at e)) _ cfc sl sv′ rets′ refl eF eC H eRets eSv eSl abv area ev sk fr rest nx I =
        case tr-back′ p e cfc (sitePos (s-tramp p₂)) rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) (area0 fs area (Data.Nat.Properties.n∸n≡0 (Tp (siteφ (s-tramp p₂)) [])))
               (subst (λ z → _ ≤ z) (sym eSl) (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n≤1+n _))) of λ where
          (N , fs′ , run , H′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-tramp p₂ (at (next (next whole))) ; g-here = (tp2 p₂ , subst (λ z → HereF (frame 0 _) z _ _ fs′) eSl H′)
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest ; g-blk = co-inb CO I } , co-log CO
      rc-tramp p₂ (p-start (at e)) _ cfc sl sv′ rets′ () eF eC H eRets eSv eSl abv area ev sk fr rest nx I
      rc-tramp p₂ (p-tramp _ _) _ cfc sl sv′ rets′ () eF eC H eRets eSv eSl abv area ev sk fr rest nx I

      rc-trampo : ∀ {Γ′} {ds′ : Defs Γ′} {F S′} (p₂ : under (ktro ds′ F S′) ∈ allK U) → GretC (s-trampo p₂)
      rc-trampo p₂ {es = []ᵉ} {os = []ˢ} {fs = fs} (p-block p (at e)) _ cfc sl sv′ rets′ refl eF eC H eRets eSv eSl abv area ev sk fr rest nx I =
        case tr-back′ p e cfc (sitePos (s-trampo p₂)) rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) (area0 fs area (Data.Nat.Properties.n∸n≡0 (Tp (siteφ (s-trampo p₂)) [])))
               (subst (λ z → _ ≤ z) (sym eSl) (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n≤1+n _))) of λ where
          (N , fs′ , run , H′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-tramp p₂ (at (next (next whole))) ; g-here = (to2 p₂ , subst (λ z → HereF (frame 0 _) z _ _ fs′) eSl H′)
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest ; g-blk = co-inb CO I } , co-log CO
      rc-trampo p₂ (p-start (at e)) _ cfc sl sv′ rets′ () eF eC H eRets eSv eSl abv area ev sk fr rest nx I
      rc-trampo p₂ (p-tramp _ _) _ cfc sl sv′ rets′ () eF eC H eRets eSv eSl abv area ev sk fr rest nx I

      rc-trampf : ∀ {X C} (p₂ : under (ktrf X C) ∈ allK U) → GretC (s-trampf {X = X} {C} p₂)
      rc-trampf {X} {C} p₂ {es = []ᵉ} {os = []ˢ} {b = b} {fs = fs} (p-block p (at e)) _ cfc sl sv′ rets′ refl eF eC H eRets eSv eSl abv area ev sk fr rest nx I =
        case tr-back′ p e cfc (sitePos (s-trampf {X = X} {C} p₂)) rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″))
               (area0 fs area (trans (cong (wsz X ∸_) (Data.Nat.Properties.⊔-identityʳ (wsz X))) (Data.Nat.Properties.n∸n≡0 (wsz X))))
               (subst (λ z → _ ≤ z) (sym eSl) (Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.⊔-identityʳ (wsz X))) (Data.Nat.Properties.n≤1+n (wsz X)))) of λ where
          (N , fs′ , run , H′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-tramp p₂ (at (next (next whole)))
                                   ; g-here = (tf2 {X = X} {C} p₂
                                              , subst (λ M → HereF (frame 0 M) (suc (wsz X)) (sitePos (s-trampf {X = X} {C} p₂)) ([]ᵉ ∥ b ∷ˢ []ˢ) fs′)
                                                      (Data.Nat.Properties.⊔-identityʳ (wsz X))
                                                      (subst (λ z → HereF (frame 0 (wsz X ⊔ 0)) z (sitePos (s-trampf {X = X} {C} p₂)) ([]ᵉ ∥ b ∷ˢ []ˢ) fs′) eSl H′))
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO (λ x le → tk x (subst (_≤ x) (sym (Data.Nat.Properties.⊔-identityʳ (wsz X))) le)) fr rest ; g-blk = co-inb CO I } , co-log CO
      rc-trampf p₂ (p-start (at e)) _ cfc sl sv′ rets′ () eF eC H eRets eSv eSl abv area ev sk fr rest nx I
      rc-trampf p₂ (p-tramp _ _) _ cfc sl sv′ rets′ () eF eC H eRets eSv eSl abv area ev sk fr rest nx I
