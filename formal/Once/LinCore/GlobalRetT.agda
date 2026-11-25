-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalRetT — plan 0.146 B1.4b (D440, D436): A TRAMPOLINE'S RETURNS (the inner block's into it, its way out)
-- (split from `GlobalRet` for its build time).
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
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
import Once.Memory.HeapAddress
import Once.LinCore.Moves
import Data.Nat.Properties


module Once.LinCore.GlobalRetT
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt using (_⊗t_; Defs; FS; Gd; LF∙; LTm; Nu; One; Tm; module Defs; module Tm)
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.Events fmt ans bw using (ds; p-halt; Γ)
open import Once.LinCore.Values fmt bw using (MV; Trace; module MV; wsz)
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt bw using (Codeᴵ; Insᴵ; Key; blockᴵ; case; end; ktr1; ktrf; ktro; module Codeᴵ; module Insᴵ; module Key)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt bw using (allK; os; module Program)
open import Once.LinCore.Layout fmt bw using (Frame; frame; frameOf; budget; ws; envW; opW; module Frame)
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

module RetT {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
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
  open Lowering U ncty ldConst using (Tp; fbudget; liveT)
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
  open CallOutA using (co-slots; co-pc; co-size; co-halt; co-freed)
  open import Once.LinCore.LiveRun fmt ans bw using (LiveG; FreshAl; live-eq; fresh-eq)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)


  module GRetT where
    open Related
    open GCall using (ArrivesAt)
    open GRetB

    -- ★ a one-shot trampoline's way out (and an observation's): the result into the dispatch's
    -- caller, at the path after its dispatch (D440)
    module _ where
      gret-out : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} {Es D S V}
                   {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ B ∷ S)} {k : Codeᴵ (Es ∣ B ∷ S) V}
                   {es : Slots Es} {os : Stk S} {r : Ret V T} {w : MV B} {n fs}
                   (p : under (ktr1 ds′ b γ) ∈ allK U) (d : DSite i k) (cfc : FrameSemantics.Frame FS) (sl : ℕ)
                   (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
               → HereF (frame 0 ((wsz X + wsz A) ⊔ wsz B)) (suc (suc ((wsz X + wsz A) ⊔ wsz B))) (trPos (ktr1 ds′ b γ) p 2) ([]ᵉ ∥ w ∷ˢ []ˢ) fs
               → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
               → sl ≡ fbudget (dsiteφ d)
               → AllocState.current-frame (falloc fs) ≺ cfc
               → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (suc ((wsz X + wsz A) ⊔ wsz B))
                 ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ (suc (wsz A) ⊔ wsz B))))
               → (suc (wsz A) ⊔ wsz B) + ws S ≤ OP (dsiteφ d)
               → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
               → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
               → FreshR r (AllocState.next-heap-ref (falloc fs))
               → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
               → AllocState.next-heap-ref (falloc fs) ≡ n
               → InBlk fs → LiveG r (es ∥ w ∷ˢ os) fs → FreshAl (falloc fs)
               → ArrivesAt k r (es ∥ w ∷ˢ os) n fs
      gret-out {es = es} {os = os} {r = r} {w = w} {fs = fs} p (d-start s) cfc sl sv′ rets′ H eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa =
        case tr-end p (frameOf main) cfc (S.pos (next s)) rets′ sv′ sl H eRets eSv (subst (λ z → _ ≤ z) (sym eSl) (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n≤1+n _))) (λ e → ≺-≢ abv (sym e)) area ev sk
               fit (proj₁ (S.shape-fits (next s))) (proj₂ (S.shape-fits (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-start (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ ; h-slots = trans (co-slots CO) eSl }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest ; g-blk = co-inb CO I
                                   ; g-live = live-eq {r = r} {r′ = r} {m = es ∥ w ∷ˢ os} {m′ = es ∥ w ∷ˢ os} {fs = fs} {fs′ = fs′} (λ _ q → q) (λ q → cong (λ fr → fr q) (co-freed CO)) (λ q → cong (λ bs → bs q) (co-size CO)) lv
                                   ; g-fal = fresh-eq {fs = fs} {fs′ = fs′} (λ q → cong (λ fr → fr q) (co-freed CO)) (co-next CO) Fa } , co-log CO
      gret-out {es = es} {os = os} {r = r} {w = w} {fs = fs} p (d-block {κ′ = κ′} p′ s) cfc sl sv′ rets′ H eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa =
        case tr-end p (frameOf (blockᴵ κ′)) cfc (K.pos p′ (next s)) rets′ sv′ sl H eRets eSv (subst (λ z → _ ≤ z) (sym eSl) (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n≤1+n _))) (λ e → ≺-≢ abv (sym e)) area ev sk
               fit (proj₁ (K.shape-fits p′ (next s))) (proj₂ (K.shape-fits p′ (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-block p′ (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ ; h-slots = trans (co-slots CO) eSl }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest ; g-blk = co-inb CO I
                                   ; g-live = live-eq {r = r} {r′ = r} {m = es ∥ w ∷ˢ os} {m′ = es ∥ w ∷ˢ os} {fs = fs} {fs′ = fs′} (λ _ q → q) (λ q → cong (λ fr → fr q) (co-freed CO)) (λ q → cong (λ bs → bs q) (co-size CO)) lv
                                   ; g-fal = fresh-eq {fs = fs} {fs′ = fs′} (λ q → cong (λ fr → fr q) (co-freed CO)) (co-next CO) Fa } , co-log CO

      gret-outo : ∀ {T Γ′} {ds′ : Defs Γ′} {F S′} {Es D S V} {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ LF∙ F (Nu F) ∷ S)}
                    {k : Codeᴵ (Es ∣ LF∙ F (Nu F) ∷ S) V} {es : Slots Es} {os : Stk S} {r : Ret V T} {w : MV (LF∙ F (Nu F))} {n fs}
                    (p : under (ktro ds′ F S′) ∈ allK U) (d : DSite i k) (cfc : FrameSemantics.Frame FS) (sl : ℕ)
                    (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
                → HereF (frame 0 (tOM F S′)) (suc (suc (tOM F S′))) (trPos (ktro ds′ F S′) p 2) ([]ᵉ ∥ w ∷ˢ []ˢ) fs
                → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
                → sl ≡ fbudget (dsiteφ d)
                → AllocState.current-frame (falloc fs) ≺ cfc
                → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (suc (tOM F S′))
                  ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ (1 ⊔ wsz (LF∙ F (Nu F))))))
                → (1 ⊔ wsz (LF∙ F (Nu F))) + ws S ≤ OP (dsiteφ d)
                → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
                → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
                → FreshR r (AllocState.next-heap-ref (falloc fs))
                → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
                → AllocState.next-heap-ref (falloc fs) ≡ n
                → InBlk fs → LiveG r (es ∥ w ∷ˢ os) fs → FreshAl (falloc fs)
                → ArrivesAt k r (es ∥ w ∷ˢ os) n fs
      gret-outo {es = es} {os = os} {r = r} {w = w} {fs = fs} p (d-start s) cfc sl sv′ rets′ H eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa =
        case to-end p (frameOf main) cfc (S.pos (next s)) rets′ sv′ sl H eRets eSv (subst (λ z → _ ≤ z) (sym eSl) (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n≤1+n _))) (λ e → ≺-≢ abv (sym e)) area ev sk
               fit (proj₁ (S.shape-fits (next s))) (proj₂ (S.shape-fits (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-start (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ ; h-slots = trans (co-slots CO) eSl }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest ; g-blk = co-inb CO I
                                   ; g-live = live-eq {r = r} {r′ = r} {m = es ∥ w ∷ˢ os} {m′ = es ∥ w ∷ˢ os} {fs = fs} {fs′ = fs′} (λ _ q → q) (λ q → cong (λ fr → fr q) (co-freed CO)) (λ q → cong (λ bs → bs q) (co-size CO)) lv
                                   ; g-fal = fresh-eq {fs = fs} {fs′ = fs′} (λ q → cong (λ fr → fr q) (co-freed CO)) (co-next CO) Fa } , co-log CO
      gret-outo {es = es} {os = os} {r = r} {w = w} {fs = fs} p (d-block {κ′ = κ′} p′ s) cfc sl sv′ rets′ H eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa =
        case to-end p (frameOf (blockᴵ κ′)) cfc (K.pos p′ (next s)) rets′ sv′ sl H eRets eSv (subst (λ z → _ ≤ z) (sym eSl) (Data.Nat.Properties.m≤n⇒m≤1+n (Data.Nat.Properties.n≤1+n _))) (λ e → ≺-≢ abv (sym e)) area ev sk
               fit (proj₁ (K.shape-fits p′ (next s))) (proj₂ (K.shape-fits p′ (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-block p′ (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ ; h-slots = trans (co-slots CO) eSl }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest ; g-blk = co-inb CO I
                                   ; g-live = live-eq {r = r} {r′ = r} {m = es ∥ w ∷ˢ os} {m′ = es ∥ w ∷ˢ os} {fs = fs} {fs′ = fs′} (λ _ q → q) (λ q → cong (λ fr → fr q) (co-freed CO)) (λ q → cong (λ bs → bs q) (co-size CO)) lv
                                   ; g-fal = fresh-eq {fs = fs} {fs′ = fs′} (λ q → cong (λ fr → fr q) (co-freed CO)) (co-next CO) Fa } , co-log CO

    module _ where
      gret-outf : ∀ {T X C} {Es D S V} {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ One ∷ S)} {k : Codeᴵ (Es ∣ One ∷ S) V}
                    {es : Slots Es} {os : Stk S} {r : Ret V T} {w : MV One} {n fs}
                    (p : under (ktrf X C) ∈ allK U) (l : liveT (idx p) ≡ true) (d : DSite i k) (cfc : FrameSemantics.Frame FS) (sl : ℕ)
                    (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
                → HereF (frame 0 (wsz X)) (suc (wsz X)) (trPos (ktrf X C) p 2) ([]ᵉ ∥ w ∷ˢ []ˢ) fs
                → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
                → sl ≡ fbudget (dsiteφ d)
                → AllocState.current-frame (falloc fs) ≺ cfc
                → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
                → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
                → FreshR r (AllocState.next-heap-ref (falloc fs))
                → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
                → AllocState.next-heap-ref (falloc fs) ≡ n
                → InBlk fs → LiveG r (es ∥ w ∷ˢ os) fs → FreshAl (falloc fs)
                → ArrivesAt k r (es ∥ w ∷ˢ os) n fs
      gret-outf {X = X} {C} {es = es} {os = os} {r = r} {w = w} {fs = fs} p l (d-start s) cfc sl sv′ rets′ H eRets eSv eSl abv ev sk fr rest nx I lv Fa =
        case tf-end {X} {C} p l cfc (S.pos (next s)) rets′ sv′ sl (HereF.f-pc H) (HereF.f-run H) eRets (HereF.f-slots H) eSv of λ where
          (fs′ , run , CO) →
            1 , fs′ , run , record { g-pt = p-start (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H)
                                                     ; h-cfg = one-cfg w CO ev sk (proj₁ (S.shape-fits (next s))) (proj₂ (S.shape-fits (next s))) ; h-slots = trans (co-slots CO) eSl }
                                   ; g-next = trans (co-next CO) nx
                                   ; g-ret = back CO (λ x _ → co-rest CO (AtStack cfc x) (λ k ())) fr rest ; g-blk = co-inb CO I
                                   ; g-live = live-eq {r = r} {r′ = r} {m = es ∥ w ∷ˢ os} {m′ = es ∥ w ∷ˢ os} {fs = fs} {fs′ = fs′} (λ _ q → q) (λ q → cong (λ fr → fr q) (co-freed CO)) (λ q → cong (λ bs → bs q) (co-size CO)) lv
                                   ; g-fal = fresh-eq {fs = fs} {fs′ = fs′} (λ q → cong (λ fr → fr q) (co-freed CO)) (co-next CO) Fa } , co-log CO
      gret-outf {X = X} {C} {es = es} {os = os} {r = r} {w = w} {fs = fs} p l (d-block {κ′ = κ′} p′ s) cfc sl sv′ rets′ H eRets eSv eSl abv ev sk fr rest nx I lv Fa =
        case tf-end {X} {C} p l cfc (K.pos p′ (next s)) rets′ sv′ sl (HereF.f-pc H) (HereF.f-run H) eRets (HereF.f-slots H) eSv of λ where
          (fs′ , run , CO) →
            1 , fs′ , run , record { g-pt = p-block p′ (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H)
                                                     ; h-cfg = one-cfg w CO ev sk (proj₁ (K.shape-fits p′ (next s))) (proj₂ (K.shape-fits p′ (next s))) ; h-slots = trans (co-slots CO) eSl }
                                   ; g-next = trans (co-next CO) nx
                                   ; g-ret = back CO (λ x _ → co-rest CO (AtStack cfc x) (λ k ())) fr rest ; g-blk = co-inb CO I
                                   ; g-live = live-eq {r = r} {r′ = r} {m = es ∥ w ∷ˢ os} {m′ = es ∥ w ∷ˢ os} {fs = fs} {fs′ = fs′} (λ _ q → q) (λ q → cong (λ fr → fr q) (co-freed CO)) (λ q → cong (λ bs → bs q) (co-size CO)) lv
                                   ; g-fal = fresh-eq {fs = fs} {fs′ = fs′} (λ q → cong (λ fr → fr q) (co-freed CO)) (co-next CO) Fa } , co-log CO

    module _ where
      -- a trampoline's way out, by its point
      gret-t : ∀ {T σ} {κ : Key σ} {Es D B S V} {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ B ∷ S)} {k : Codeᴵ (Es ∣ B ∷ S) V} {r : Ret V T}
                 {es : Slots Es} {os : Stk S} {e′ : Slots []} {b : MV B} {n fs}
                 (P : Pnt (end {sh = [] ∣ B ∷ []})) (d : DSite i k) (p : under κ ∈ allK U)
                 (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
             → rootOf P ≡ rtramp {κ = κ} p → ptFin P ≡ trFin (idx p) κ
             → HereP P (e′ ∥ b ∷ˢ []ˢ) fs → TrM κ
             → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
             → sl ≡ fbudget (dsiteφ d)
             → AllocState.current-frame (falloc fs) ≺ cfc
             → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (suc (trM κ))
               ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ trMc κ)))
             → trMc κ + ws S ≤ OP (dsiteφ d)
             → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
             → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
             → FreshR r (AllocState.next-heap-ref (falloc fs))
             → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
             → AllocState.next-heap-ref (falloc fs) ≡ n
             → InBlk fs → LiveG r (es ∥ b ∷ˢ os) fs → FreshAl (falloc fs)
             → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
      gret-t {e′ = []ᵉ} (p-tramp p₂ _) d p cfc sl sv′ rets′ refl eF (tp2 _ , H) _ eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa =
        gret-out p d cfc sl sv′ rets′ H eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa
      gret-t {e′ = []ᵉ} (p-tramp p₂ _) d p cfc sl sv′ rets′ refl eF (to2 _ , H) _ eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa =
        gret-outo p d cfc sl sv′ rets′ H eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa
      gret-t {e′ = []ᵉ} (p-tramp p₂ _) d p cfc sl sv′ rets′ refl eF (tf2 _ _ , H) () eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa
      gret-t (p-start (at e)) d p cfc sl sv′ rets′ () eF H _ eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa
      gret-t (p-block _ (at e)) d p cfc sl sv′ rets′ () eF H _ eRets eSv eSl abv area fit ev sk fr rest nx I lv Fa

      -- a free's trampoline's way out, by its point
      gret-tf : ∀ {T X C} {Es D S V} {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ One ∷ S)} {k : Codeᴵ (Es ∣ One ∷ S) V} {r : Ret V T}
                  {es : Slots Es} {os : Stk S} {e′ : Slots []} {b : MV One} {n fs}
                  (P : Pnt (end {sh = [] ∣ One ∷ []})) (d : DSite i k) (p : under (ktrf X C) ∈ allK U)
                  (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
              → rootOf P ≡ rtramp {κ = ktrf X C} p → ptFin P ≡ trFin (idx p) (ktrf X C)
              → HereP P (e′ ∥ b ∷ˢ []ˢ) fs
              → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
              → sl ≡ fbudget (dsiteφ d)
              → AllocState.current-frame (falloc fs) ≺ cfc
              → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
              → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
              → FreshR r (AllocState.next-heap-ref (falloc fs))
              → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
              → AllocState.next-heap-ref (falloc fs) ≡ n
              → InBlk fs → LiveG r (es ∥ b ∷ˢ os) fs → FreshAl (falloc fs)
              → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
      gret-tf {X = X} {C} {e′ = []ᵉ} (p-tramp p₂ _) d p cfc sl sv′ rets′ refl eF (tf2 _ l , H) eRets eSv eSl abv ev sk fr rest nx I lv Fa =
        gret-outf {X = X} {C} p l d cfc sl sv′ rets′ H eRets eSv eSl abv ev sk fr rest nx I lv Fa
      gret-tf (p-start (at e)) d p cfc sl sv′ rets′ () eF H eRets eSv eSl abv ev sk fr rest nx I lv Fa
      gret-tf (p-block _ (at e)) d p cfc sl sv′ rets′ () eF H eRets eSv eSl abv ev sk fr rest nx I lv Fa

