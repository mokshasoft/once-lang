-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalRet — plan 0.146 B1.4b (D417 step 3, D420, D421): A RETURN: the caller's frame back, the result on its stack
-- (split from `GlobalCall` for its build time; over `Global.Relate`).
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


module Once.LinCore.GlobalRet
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
open import Once.LinCore.GlobalCall fmt ans bw using (module CallR)

module RetR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open CallR {FS} ds f ldConst ld-nl wordOf using (module GCall)
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
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; SlotsAt; cellPtr)
  open FlatMachine {FS} using (fpc)
  open import Once.LinCore.Moves {FS} using (slot)
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
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)


  module GRet where
    open Related
    open GCall using (ArrivesAt)

    -- ★ a return: the caller's frame back, the result on its stack
    private
      frame-eq : ∀ {f g x y} → AtStack {FS} f x ≡ AtStack g y → f ≡ g
      frame-eq refl = refl

      back : ∀ {T U′ R fin} {r : Ret U′ T} {fs fs′ cfc a src o nb pc rets′ sv′ sl}
           → CallOut fs fs′ cfc a src o nb pc rets′ sv′ sl
           → (∀ x → budget (rootφ R) ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x)
           → FreshR r (AllocState.next-heap-ref (falloc fs))
           → RetOK R fin r cfc rets′ sv′ fs
           → RetOK R fin r (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
      back {cfc = cfc} CO tk fr ok =
        ctx-to (sym (co-frame CO)) (sym (co-ret CO)) (sym (co-saved CO))
          (ret-top (λ f x ne → co-rest CO (AtStack f x) (λ k k< e → ne (frame-eq e))) tk
                   (λ hl _ → co-rest CO (AtDynamic hl) (λ k k< ())) fr ok)

    -- ★ a one-shot trampoline's way out (and an observation's): the result into the dispatch's
    -- caller, at the path after its dispatch (D421)
    private
      gret-out : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} {Es D S V}
                   {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ B ∷ S)} {k : Codeᴵ (Es ∣ B ∷ S) V}
                   {es : Slots Es} {os : Stk S} {r : Ret V T} {w : MV B} {n fs}
                   (p : under (ktr1 ds′ b γ) ∈ allK U) (d : DSite i k) (cfc : FrameSemantics.Frame FS) (sl : ℕ)
                   (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
               → HereF (frame 0 ((wsz X + wsz A) ⊔ wsz B)) (trPos (ktr1 ds′ b γ) p 2) ([]ᵉ ∥ w ∷ˢ []ˢ) fs
               → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
               → AllocState.current-frame (falloc fs) ≺ cfc
               → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (suc ((wsz X + wsz A) ⊔ wsz B))
                 ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ (suc (wsz A) ⊔ wsz B))))
               → (suc (wsz A) ⊔ wsz B) + ws S ≤ OP (dsiteφ d)
               → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
               → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
               → FreshR r (AllocState.next-heap-ref (falloc fs))
               → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
               → AllocState.next-heap-ref (falloc fs) ≡ n
               → ArrivesAt k r (es ∥ w ∷ˢ os) n fs
      gret-out p (d-start s) cfc sl sv′ rets′ H eRets eSv abv area fit ev sk fr rest nx =
        case tr-end p (frameOf main) cfc (S.pos (next s)) rets′ sv′ sl H eRets eSv (λ e → ≺-≢ abv (sym e)) area ev sk
               fit (proj₁ (S.shape-fits (next s))) (proj₂ (S.shape-fits (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-start (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }
      gret-out p (d-block {κ′ = κ′} p′ s) cfc sl sv′ rets′ H eRets eSv abv area fit ev sk fr rest nx =
        case tr-end p (frameOf (blockᴵ κ′)) cfc (K.pos p′ (next s)) rets′ sv′ sl H eRets eSv (λ e → ≺-≢ abv (sym e)) area ev sk
               fit (proj₁ (K.shape-fits p′ (next s))) (proj₂ (K.shape-fits p′ (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-block p′ (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }

      gret-outo : ∀ {T Γ′} {ds′ : Defs Γ′} {F S′} {Es D S V} {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ LF∙ F (Nu F) ∷ S)}
                    {k : Codeᴵ (Es ∣ LF∙ F (Nu F) ∷ S) V} {es : Slots Es} {os : Stk S} {r : Ret V T} {w : MV (LF∙ F (Nu F))} {n fs}
                    (p : under (ktro ds′ F S′) ∈ allK U) (d : DSite i k) (cfc : FrameSemantics.Frame FS) (sl : ℕ)
                    (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
                → HereF (frame 0 (tOM F S′)) (trPos (ktro ds′ F S′) p 2) ([]ᵉ ∥ w ∷ˢ []ˢ) fs
                → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
                → AllocState.current-frame (falloc fs) ≺ cfc
                → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (suc (tOM F S′))
                  ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ (1 ⊔ wsz (LF∙ F (Nu F))))))
                → (1 ⊔ wsz (LF∙ F (Nu F))) + ws S ≤ OP (dsiteφ d)
                → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
                → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
                → FreshR r (AllocState.next-heap-ref (falloc fs))
                → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
                → AllocState.next-heap-ref (falloc fs) ≡ n
                → ArrivesAt k r (es ∥ w ∷ˢ os) n fs
      gret-outo p (d-start s) cfc sl sv′ rets′ H eRets eSv abv area fit ev sk fr rest nx =
        case to-end p (frameOf main) cfc (S.pos (next s)) rets′ sv′ sl H eRets eSv (λ e → ≺-≢ abv (sym e)) area ev sk
               fit (proj₁ (S.shape-fits (next s))) (proj₂ (S.shape-fits (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-start (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }
      gret-outo p (d-block {κ′ = κ′} p′ s) cfc sl sv′ rets′ H eRets eSv abv area fit ev sk fr rest nx =
        case to-end p (frameOf (blockᴵ κ′)) cfc (K.pos p′ (next s)) rets′ sv′ sl H eRets eSv (λ e → ≺-≢ abv (sym e)) area ev sk
               fit (proj₁ (K.shape-fits p′ (next s))) (proj₂ (K.shape-fits p′ (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-block p′ (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }

    -- a block's return to the start's code, to a block's (by `From.return`)
    private
      gret-ss : ∀ {T t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {r : Ret V T}
                  {es : Slots (t ⊳ Es)} {os : Stk S} {e′ : Slots (t ⊳ [])} {b : MV B} {n fs}
                  (s : Sub main (call κ ⨾ k)) (e : Sub (blockᴵ κ) (end {sh = t ⊳ [] ∣ B ∷ []}))
                  (p : (bsig t A B , κ) ∈ allK U) → FrS.callee s ≡ p
              → ∀ (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
              → ptFin (p-block p (at e)) ≡ blockFin κ
              → K.Here p e (e′ ∥ b ∷ˢ []ˢ) fs
              → fret fs ≡ FrS.C.pos (next s) ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
              → AllocState.current-frame (falloc fs) ≺ cfc
              → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ κ)))
                ≡ just (SV-Ptr (AtStack cfc (Tp (frameOf main) S ∸ (wsz A ⊔ wsz B))))
              → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
              → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (frameOf main) os
              → FreshR r (AllocState.next-heap-ref (falloc fs))
              → RetOK rstart (SA.lfin (S.lowAt s)) r cfc rets′ sv′ fs
              → AllocState.next-heap-ref (falloc fs) ≡ n
              → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
      gret-ss s e p eC cfc sl sv′ rets′ eF H eRets eSv abv area ev sk fr rest nx =
        case FrS.return s e cfc rets′ sv′ sl p eC eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) area ev sk of λ where
          (N , fs′ , run , H′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-start (at (next s)) ; g-here = H′ ; g-next = trans (co-next CO) nx
                                   ; g-ret = back CO tk fr rest }

      gret-sb : ∀ {T t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {r : Ret V T}
                  {es : Slots (t ⊳ Es)} {os : Stk S} {e′ : Slots (t ⊳ [])} {b : MV B} {n fs}
                  {σ′} {κ′ : Key σ′} (p′ : (σ′ , κ′) ∈ allK U) (s : Sub (blockᴵ κ′) (call κ ⨾ k))
                  (e : Sub (blockᴵ κ) (end {sh = t ⊳ [] ∣ B ∷ []}))
                  (p : (bsig t A B , κ) ∈ allK U) → FrK.callee p′ s ≡ p
              → ∀ (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
              → ptFin (p-block p (at e)) ≡ blockFin κ
              → K.Here p e (e′ ∥ b ∷ˢ []ˢ) fs
              → fret fs ≡ FrK.C.pos p′ (next s) ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
              → AllocState.current-frame (falloc fs) ≺ cfc
              → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ κ)))
                ≡ just (SV-Ptr (AtStack cfc (Tp (frameOf (blockᴵ κ′)) S ∸ (wsz A ⊔ wsz B))))
              → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
              → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (frameOf (blockᴵ κ′)) os
              → FreshR r (AllocState.next-heap-ref (falloc fs))
              → RetOK (rblock p′) (KA.lfin {p = p′} (K.lowAt p′ s)) r cfc rets′ sv′ fs
              → AllocState.next-heap-ref (falloc fs) ≡ n
              → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
      gret-sb p′ s e p eC cfc sl sv′ rets′ eF H eRets eSv abv area ev sk fr rest nx =
        case FrK.return p′ s e cfc rets′ sv′ sl p eC eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) area ev sk of λ where
          (N , fs′ , run , H′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-block p′ (at (next s)) ; g-here = H′ ; g-next = trans (co-next CO) nx
                                   ; g-ret = back CO tk fr rest }

    -- a block's return, by the point and the call site
    private
      -- what a block's return owes, by its call site (split once: `site-elim`)
      GretC : ∀ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} → Site κ k → Set
      GretC {t} {A} {B} {Es} {S} {V} {κ} {k} st =
        ∀ {T} {r : Ret V T} {es : Slots (t ⊳ Es)} {os : Stk S} {e′ : Slots (t ⊳ [])} {b : MV B} {n fs}
          (P : Pnt (end {sh = t ⊳ [] ∣ B ∷ []})) (p : (bsig t A B , κ) ∈ allK U)
          (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
        → rootOf P ≡ rblock p → ptFin P ≡ blockFin κ → siteCallee st ≡ p
        → HereP P (e′ ∥ b ∷ˢ []ˢ) fs
        → fret fs ≡ sitePos st ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
        → AllocState.current-frame (falloc fs) ≺ cfc
        → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ κ)))
          ≡ just (SV-Ptr (AtStack cfc (Tp (siteφ st) S ∸ (wsz A ⊔ wsz B))))
        → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
        → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (siteφ st) os
        → FreshR r (AllocState.next-heap-ref (falloc fs))
        → RetOK (siteRoot st) (siteFin st) r cfc rets′ sv′ fs
        → AllocState.next-heap-ref (falloc fs) ≡ n
        → ArrivesAt k r (es ∥ b ∷ˢ os) n fs

      rc-start : ∀ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} (s : Sub main (call κ ⨾ k)) → GretC (s-start s)
      rc-start s (p-block p (at e)) _ cfc sl sv′ rets′ refl eF eC H eRets eSv abv area ev sk fr rest nx =
        gret-ss s e p eC cfc sl sv′ rets′ eF H eRets eSv abv area ev sk fr rest nx
      rc-start s (p-start (at e)) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx
      rc-start s (p-tramp _ _) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx

      rc-block : ∀ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {σ′} {κ′ : Key σ′}
                (p′ : (σ′ , κ′) ∈ allK U) (s : Sub (blockᴵ κ′) (call κ ⨾ k)) → GretC (s-block p′ s)
      rc-block p′ s (p-block p (at e)) _ cfc sl sv′ rets′ refl eF eC H eRets eSv abv area ev sk fr rest nx =
        gret-sb p′ s e p eC cfc sl sv′ rets′ eF H eRets eSv abv area ev sk fr rest nx
      rc-block p′ s (p-start (at e)) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx
      rc-block p′ s (p-tramp _ _) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx

      -- a trampoline's inner return (D421): by the generic `tr-back′` over the site's own key (no second
      -- spelling of it: a key compared across spellings unfolds the block's labels and frame)
      area0 : ∀ (fs : FlatState) {x cfc z}
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) x ≡ just (SV-Ptr (AtStack cfc z)) → z ≡ 0
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) x ≡ just (SV-Ptr (AtStack cfc 0))
      area0 fs a refl = a

      rc-tramp : ∀ {Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b}
                (p₂ : under (ktr1 ds′ b γ) ∈ allK U) → GretC (s-tramp p₂)
      rc-tramp p₂ {es = []ᵉ} {os = []ˢ} {fs = fs} (p-block p (at e)) _ cfc sl sv′ rets′ refl eF eC H eRets eSv abv area ev sk fr rest nx =
        case tr-back′ p e cfc (sitePos (s-tramp p₂)) rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) (area0 fs area (Data.Nat.Properties.n∸n≡0 (Tp (siteφ (s-tramp p₂)) []))) of λ where
          (N , fs′ , run , H′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-tramp p₂ (at (next (next whole))) ; g-here = (tp2 p₂ , H′)
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }
      rc-tramp p₂ (p-start (at e)) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx
      rc-tramp p₂ (p-tramp _ _) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx

      rc-trampo : ∀ {Γ′} {ds′ : Defs Γ′} {F S′} (p₂ : under (ktro ds′ F S′) ∈ allK U) → GretC (s-trampo p₂)
      rc-trampo p₂ {es = []ᵉ} {os = []ˢ} {fs = fs} (p-block p (at e)) _ cfc sl sv′ rets′ refl eF eC H eRets eSv abv area ev sk fr rest nx =
        case tr-back′ p e cfc (sitePos (s-trampo p₂)) rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) (area0 fs area (Data.Nat.Properties.n∸n≡0 (Tp (siteφ (s-trampo p₂)) []))) of λ where
          (N , fs′ , run , H′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-tramp p₂ (at (next (next whole))) ; g-here = (to2 p₂ , H′)
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }
      rc-trampo p₂ (p-start (at e)) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx
      rc-trampo p₂ (p-tramp _ _) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx

      gret-cases : SiteCases
      gret-cases = record { SP = GretC ; on-start = rc-start ; on-block = rc-block ; on-tramp = rc-tramp ; on-trampo = rc-trampo }

      -- a trampoline's way out, by its point
      gret-t : ∀ {T σ} {κ : Key σ} {Es D B S V} {i : Insᴵ (Es ∣ D ∷ S) (Es ∣ B ∷ S)} {k : Codeᴵ (Es ∣ B ∷ S) V} {r : Ret V T}
                 {es : Slots Es} {os : Stk S} {e′ : Slots []} {b : MV B} {n fs}
                 (P : Pnt (end {sh = [] ∣ B ∷ []})) (d : DSite i k) (p : under κ ∈ allK U)
                 (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
             → rootOf P ≡ rtramp {κ = κ} p → ptFin P ≡ trFin (idx p) κ
             → HereP P (e′ ∥ b ∷ˢ []ˢ) fs
             → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
             → AllocState.current-frame (falloc fs) ≺ cfc
             → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (suc (trM κ))
               ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ trMc κ)))
             → trMc κ + ws S ≤ OP (dsiteφ d)
             → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
             → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
             → FreshR r (AllocState.next-heap-ref (falloc fs))
             → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
             → AllocState.next-heap-ref (falloc fs) ≡ n
             → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
      gret-t {e′ = []ᵉ} (p-tramp p₂ _) d p cfc sl sv′ rets′ refl eF (tp2 _ , H) eRets eSv abv area fit ev sk fr rest nx =
        gret-out p d cfc sl sv′ rets′ H eRets eSv abv area fit ev sk fr rest nx
      gret-t {e′ = []ᵉ} (p-tramp p₂ _) d p cfc sl sv′ rets′ refl eF (to2 _ , H) eRets eSv abv area fit ev sk fr rest nx =
        gret-outo p d cfc sl sv′ rets′ H eRets eSv abv area fit ev sk fr rest nx
      gret-t (p-start (at e)) d p cfc sl sv′ rets′ () eF H eRets eSv abv area fit ev sk fr rest nx
      gret-t (p-block _ (at e)) d p cfc sl sv′ rets′ () eF H eRets eSv abv area fit ev sk fr rest nx

    gret : ∀ {T t B Es S V} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {r : Ret V T} {es : Slots (t ⊳ Es)} {os : Stk S}
             {e′ : Slots (t ⊳ [])} {b : MV B} {n h fs} (P : Pnt (end {sh = t ⊳ [] ∣ B ∷ []}))
         → InvI (e′ ∥ b ∷ˢ []ˢ) (frm {t = t} {Es = Es} k es os r) n h → HereP P (e′ ∥ b ∷ˢ []ˢ) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) (frm {t = t} {Es = Es} k es os r)
                 (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
    -- by the return stack's top first (one split of `RetOK`), then the point
    gret {t = t} {Es = Es} {k = k} {r = r} {es = es} {os = os} {fs = fs} P inv H nx
         (ok-call p st cfc sl sv′ rets′ eR eF eC eRets eSv abv area ev sk rest) =
      site-elim gret-cases st P p cfc sl sv′ rets′ eR eF eC H eRets eSv abv area ev sk
        (proj₂ (subst (FreshR (frm {t = t} {Es = Es} k es os r)) (sym nx) (fresh-ret inv))) rest nx
    gret {t = t} {Es = Es} {k = k} {r = r} {es = es} {os = os} {fs = fs} P inv H nx
         (ok-tramp p d cfc sl sv′ rets′ eR eF eRets eSv abv area fit ev sk rest) =
      gret-t P d p cfc sl sv′ rets′ eR eF H eRets eSv abv area fit ev sk
        (proj₂ (subst (FreshR (frm {t = t} {Es = Es} k es os r)) (sym nx) (fresh-ret inv))) rest nx

