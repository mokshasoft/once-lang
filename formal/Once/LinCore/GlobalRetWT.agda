-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalRetWT — plan 0.146 B1.4b (D434, D442): A MANY-USE BODY'S TRAMPOLINE'S RETURN
-- into the dispatcher's area, two frames up (beside `GlobalRetW`, for its build time).
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
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


module Once.LinCore.GlobalRetWT
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt using (Defs; FS; Fn; Gd; LTm; One; Tm; many; module Defs; module Tm)
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.Events fmt ans bw using (ds; p-halt; Γ)
open import Once.LinCore.Values fmt bw using (MV; Trace; module MV)
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt bw using (_⨾_; Codeᴵ; Insᴵ; Key; blockᴵ; case; end; epop; kbodyω; ktrω; module Codeᴵ; module Insᴵ; module Key)
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
open import Once.LinCore.GlobalTrampW fmt ans bw using (module TrampW)
open import Once.LinCore.GlobalCall fmt ans bw using (module CallR)
open import Once.LinCore.GlobalRetB fmt ans bw using (module RetB)

module RetWT {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf using (DSite; HereP; LoopTo; Related; RetOK; TrM; TrW2; ctx-to; d-block; d-start; dsiteFin; dsitePos; dsiteRoot; dsiteφ; ok-call; ok-callω; ok-loop; ok-top; ok-tramp; ok-trampf; ok-trampω; rblock; ret-top; rootOf; rootφ; rtramp; stk-all; trB; trPos; tw2; tw3; ≺-≢; module DSite; module Related; module RetOK; module S; module TrM; module TrW2)
  open TrampW {FS} ds f ldConst ld-nl wordOf using (tw-back; tw-end)
  open CallR {FS} ds f ldConst ld-nl wordOf using (module GCall)
  open RetB {FS} ds f ldConst ld-nl wordOf using (module GRetB)
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin; trFin)
  open Program ds f using (U)
  open Program ds f using (ncty)
  open Program′ ds f ldConst using (image; j₀)
  open Lowering U ncty ldConst using (Tp; fbudget; sv₁; sv₂)
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
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; CallOutA)
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
  open SimF {FS} U wordOf using (leave; area-gen; area-bnd)
  open import Once.LinCore.LowerSimE {FS} using (anc-win)
  open CallOutA using (co-slots; co-pc; co-size; co-halt)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)


  module GRetWT where
    open Related
    open GCall using (ArrivesAt)
    open GRetB
    open import Data.Sum using (_⊎_; inj₁; inj₂)
    open Sim {FS} U wordOf using (env-below; stkW-frame)
    open Rel {FS} U wordOf using (W; vw-frame)
    private
      res-at : ∀ {sm : FrameSemantics.Frame FS → ℕ → Maybe W} {o cfc ar af ar′} {wb : List W}
             → just (SV-Ptr (AtStack {FS} cfc ar)) ≡ just (SV-Ptr (AtStack af ar′))
             → SlotsAt (sm af) (o + ar′) wb → SlotsAt (sm cfc) (o + ar) wb
      res-at refl s = s

      res-cfg : ∀ {fs fs′ cfc pc rets′ sv′ sl} {φ : Frame} {Es B S} {es : Slots Es} {os : Stk S} {w : MV B} (M : ℕ) (wb : List W)
              → CallOut fs fs′ cfc 0 0 0 0 pc rets′ sv′ sl
              → VW (LocState.heapMem (floc fs)) w wb → SlotsAt (LocState.stackMem (floc fs) cfc) ((M ∸ wsz B) + ((budget φ ∸ ws S) ∸ M)) wb
              → wsz B ≤ M → M + ws S ≤ OP φ
              → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
              → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) φ os
              → envW (Es ∣ B ∷ S) ≤ EP φ → opW (Es ∣ B ∷ S) ≤ OP φ
              → CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ (es ∥ w ∷ˢ os)
      res-cfg {fs} {fs′} {cfc} {φ = φ} {B = B} {S} {es} {os} {w} M wb CO pw sw le fit ev sk fe fb =
        subst (λ g → CfgW (LocState.heapMem (floc fs′)) (LocState.stackMem (floc fs′) g) φ (es ∥ w ∷ˢ os)) (sym (co-frame CO))
          (record { c-env = envW-heap es (λ i k _ → hp (cellLoc i k)) (envW-frame es (λ x _ → sp x) ev)
                  ; c-stk = ( wb , vw-frame pw (λ i k _ → hp (cellLoc i k))
                            , slots-frame wb (λ k _ → sp _)
                                (subst (λ z → SlotsAt (LocState.stackMem (floc fs) cfc) z wb)
                                  (area-gen (budget φ) (wsz B) M (ws S) le
                                    (Data.Nat.Properties.≤-trans fit (Data.Nat.Properties.m≤n+m (OP φ) (EP φ)))) sw) )
                          , stkW-heap os (λ i k _ → hp (cellLoc i k)) (stk-all os (λ x → sp x) sk)
                  ; c-efit = fe ; c-sfit = fb })
        where
          hp : ∀ hl → LocState.heapMem (floc fs′) hl ≡ LocState.heapMem (floc fs) hl
          hp hl = co-rest CO (AtDynamic hl) (λ k ())
          sp : ∀ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x
          sp x = co-rest CO (AtStack cfc x) (λ k ())

    -- ★ the trampoline's way out (D442): a bare return; the result's words already in the
    -- dispatcher's area, so its configuration back in its frame with the result on top
    gret-tω : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ X A B} {γ : Gd g b} {Es S V}
                {i : Insᴵ (Fn many g A B ∷ Es ∣ A ∷ S) (Fn many g A B ∷ Es ∣ B ∷ S)} {k : Codeᴵ (Fn many g A B ∷ Es ∣ B ∷ S) V}
                {es : Slots (Fn many g A B ∷ Es)} {os : Stk S} {r : Ret V T} {e′ : Slots (Fn many g A B ∷ [])} {w : MV B} {n fs}
                (P : Pnt (end {sh = Fn many g A B ∷ [] ∣ B ∷ []})) (p : under (ktrω ds′ b γ) ∈ allK U) (d : DSite i k)
                (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
            → rootOf P ≡ rtramp {κ = ktrω ds′ b γ} p → HereP P (e′ ∥ w ∷ˢ []ˢ) fs
            → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
            → sl ≡ fbudget (dsiteφ d)
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) 0 ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ (wsz A ⊔ wsz B))))
            → (wsz A ⊔ wsz B) + ws S ≤ OP (dsiteφ d)
            → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
            → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
            → FreshR r (AllocState.next-heap-ref (falloc fs))
            → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → InBlk fs
            → ArrivesAt k r (es ∥ w ∷ˢ os) n fs
    gret-tω (p-start (at _)) _ d cfc sl sv′ rets′ () H eRets eSv eSl area fit ev sk fr rest nx I
    gret-tω (p-block _ (at _)) _ d cfc sl sv′ rets′ () H eRets eSv eSl area fit ev sk fr rest nx I
    gret-tω {A = A} {B} {S = S} {fs = fs} (p-tramp _ _) _ (d-start s) cfc sl sv′ rets′ refl (tw3 p , T) eRets eSv eSl area fit ev sk fr rest nx I =
      case tw-end p cfc (S.pos (next s)) rets′ sv′ sl (TrW2.w2-pc T) (TrW2.w2-run T) eRets (TrW2.w2-slots T) eSv of λ where
        (fs′ , run , CO) →
          1 , fs′ , run , record { g-pt = p-start (at (next s))
                                 ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (TrW2.w2-run T)
                                                   ; h-cfg = res-cfg (wsz A ⊔ wsz B) (TrW2.w2-wb T) CO (TrW2.w2-b T)
                                                               (res-at {sm = LocState.stackMem (floc fs)} (trans (sym area) (TrW2.w2-s0 T)) (TrW2.w2-res T))
                                                               (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B)) fit ev sk
                                                               (proj₁ (S.shape-fits (next s))) (proj₂ (S.shape-fits (next s))) ; h-slots = trans (co-slots CO) eSl }
                                 ; g-next = trans (co-next CO) nx
                                 ; g-ret = back CO (λ x _ → co-rest CO (AtStack cfc x) (λ k ())) fr rest ; g-blk = co-inb CO I } , co-log CO
    gret-tω {A = A} {B} {S = S} {fs = fs} (p-tramp _ _) _ (d-block p′ s) cfc sl sv′ rets′ refl (tw3 p , T) eRets eSv eSl area fit ev sk fr rest nx I =
      case tw-end p cfc (K.pos p′ (next s)) rets′ sv′ sl (TrW2.w2-pc T) (TrW2.w2-run T) eRets (TrW2.w2-slots T) eSv of λ where
        (fs′ , run , CO) →
          1 , fs′ , run , record { g-pt = p-block p′ (at (next s))
                                 ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (TrW2.w2-run T)
                                                   ; h-cfg = res-cfg (wsz A ⊔ wsz B) (TrW2.w2-wb T) CO (TrW2.w2-b T)
                                                               (res-at {sm = LocState.stackMem (floc fs)} (trans (sym area) (TrW2.w2-s0 T)) (TrW2.w2-res T))
                                                               (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B)) fit ev sk
                                                               (proj₁ (K.shape-fits p′ (next s))) (proj₂ (K.shape-fits p′ (next s))) ; h-slots = trans (co-slots CO) eSl }
                                 ; g-next = trans (co-next CO) nx
                                 ; g-ret = back CO (λ x _ → co-rest CO (AtStack cfc x) (λ k ())) fr rest ; g-blk = co-inb CO I } , co-log CO
