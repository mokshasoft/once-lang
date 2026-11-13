-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalCall — plan 0.146 B1.4b (D417 step 3, D420): A CALL AND A RETURN: the callee's frame opened, the caller's saved
-- (split from `Global` for its build time; over `Global.Relate`).
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


module Once.LinCore.GlobalCall
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

module CallR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin)
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

  private
    nat-r0 : ∀ {a b : ℕ} → a + b ≡ 0 → b ≡ 0
    nat-r0 {zero} e = e
    nat-r0 {suc a} ()

  -- ★ the caller's frame, as the new top of the return stack
  mk-call : ∀ {T t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {es : Slots (t ⊳ Es)} {a : MV A} {os : Stk S}
              {r : Ret V T} {fs fs′} (p : (bsig t A B , κ) ∈ allK U) (st : Site κ k) → siteCallee st ≡ p
          → Called fs fs′ (sitePos st) (fbudget (frameOf (blockᴵ κ))) (sv₁ (frameOf (blockᴵ κ))) (Tp (siteφ st) S ∸ (wsz A ⊔ wsz B))
          → CfgW (LocState.heapMem (floc fs)) (slot fs) (siteφ st) (es ∥ a ∷ˢ os)
          → (∀ i → AllocState.next-heap-ref (falloc fs) ≤ serial i → cntE es i ≡ 0 × cntS (a ∷ˢ os) i ≡ 0)
          → FreshR r (AllocState.next-heap-ref (falloc fs))
          → RetOK (siteRoot st) (siteFin st) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → RetOK (rblock p) (blockFin κ) (frm {t = t} {Es = Es} k es os r)
                  (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
  mk-call {κ = κ} {es = es} {a} {os} {fs = fs} {fs′} p st eC CD C fr frR ok =
    ok-call p st cfc (AllocState.frame-slots (falloc fs)) (AllocState.saved-frames (falloc fs)) (fret fs)
      refl refl eC (cd-ret CD) (cd-saved CD) under-cfc (cd-area CD)
      (env-stand (λ i le → proj₁ (fr i le)) (cd-old CD) (envW-frame es (λ x _ → kept x) (CfgW.c-env C)))
      (stk-stand (λ i le → nat-r0 (proj₂ (fr i le))) (cd-old CD) (stk-all os kept (proj₂ (CfgW.c-stk C))))
      (ret-deep (AllocState.current-frame (falloc fs′)) under-cfc
         (λ f x ne → cd-others CD f x (λ e → ne (trans (sym e) (sym (cd-frame CD))))) (cd-old CD) frR ok)
    where
      cfc = AllocState.current-frame (falloc fs)
      b = fbudget (frameOf (blockᴵ κ))
      under-cfc : AllocState.current-frame (falloc fs′) ≺ cfc
      under-cfc = subst (_≺ cfc) (sym (cd-frame CD)) (callee-below cfc b)
      kept : ∀ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x
      kept x = cd-others CD cfc x (callee-≢ cfc b)

  module GCall where
    open Related

    ArrivesAt : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
    ArrivesAt c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′

    -- a call's cases, each by itself
    private
      gcall-sn : ∀ {T A B Es S V} {κ : Key (bsig nothing A B)} {k : Codeᴵ (Es ∣ B ∷ S) V} {r : Ret V T}
                   {es : Slots Es} {a : MV A} {os : Stk S} {n h fs} (s : Sub main (call κ ⨾ k))
               → InvI (es ∥ a ∷ˢ os) r n h → S.Here s (es ∥ a ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
               → RetOK rstart (ptFin (p-start (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
               → ArrivesAt (blockᴵ κ) (frm {t = nothing} {Es = Es} k es os r) (topv nothing es ∥ a ∷ˢ []ˢ) n fs
      gcall-sn {r = r} s inv H nx ok = case FrS.call-n s H of λ where
        (N , fs′ , run , H′ , CD) →
          N , fs′ , run , record { g-pt = p-block (FrS.callee s) (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                                 ; g-ret = mk-call (FrS.callee s) (s-start s) refl CD (S.Here.h-cfg H)
                                             (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                             (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }

      gcall-sv : ∀ {T E A B Es S V} {κ : Key (bsig (just E) A B)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V} {r : Ret V T}
                   {es : Slots (E ∷ Es)} {a : MV A} {os : Stk S} {n h fs} (s : Sub main (call κ ⨾ k))
               → InvI (es ∥ a ∷ˢ os) r n h → S.Here s (es ∥ a ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
               → RetOK rstart (ptFin (p-start (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
               → ArrivesAt (blockᴵ κ) (frm {t = just E} {Es = Es} k es os r) (topv (just E) es ∥ a ∷ˢ []ˢ) n fs
      gcall-sv {r = r} s inv H nx ok = case FrS.call-v s H of λ where
        (N , fs′ , run , H′ , CD) →
          N , fs′ , run , record { g-pt = p-block (FrS.callee s) (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                                 ; g-ret = mk-call (FrS.callee s) (s-start s) refl CD (S.Here.h-cfg H)
                                             (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                             (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }

      gcall-bn : ∀ {T A B Es S V} {κ : Key (bsig nothing A B)} {k : Codeᴵ (Es ∣ B ∷ S) V} {r : Ret V T}
                   {es : Slots Es} {a : MV A} {os : Stk S} {n h fs} {σ′} {κ′ : Key σ′} (p′ : (σ′ , κ′) ∈ allK U) (s : Sub (blockᴵ κ′) (call κ ⨾ k))
               → InvI (es ∥ a ∷ˢ os) r n h → K.Here p′ s (es ∥ a ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
               → RetOK (rblock p′) (ptFin (p-block p′ (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
               → ArrivesAt (blockᴵ κ) (frm {t = nothing} {Es = Es} k es os r) (topv nothing es ∥ a ∷ˢ []ˢ) n fs
      gcall-bn {r = r} p′ s inv H nx ok = case FrK.call-n p′ s H of λ where
        (N , fs′ , run , H′ , CD) →
          N , fs′ , run , record { g-pt = p-block (FrK.callee p′ s) (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                                 ; g-ret = mk-call (FrK.callee p′ s) (s-block p′ s) refl CD (K.Here.h-cfg {p = p′} H)
                                             (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                             (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }

      gcall-bv : ∀ {T E A B Es S V} {κ : Key (bsig (just E) A B)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V} {r : Ret V T}
                   {es : Slots (E ∷ Es)} {a : MV A} {os : Stk S} {n h fs} {σ′} {κ′ : Key σ′} (p′ : (σ′ , κ′) ∈ allK U) (s : Sub (blockᴵ κ′) (call κ ⨾ k))
               → InvI (es ∥ a ∷ˢ os) r n h → K.Here p′ s (es ∥ a ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
               → RetOK (rblock p′) (ptFin (p-block p′ (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
               → ArrivesAt (blockᴵ κ) (frm {t = just E} {Es = Es} k es os r) (topv (just E) es ∥ a ∷ˢ []ˢ) n fs
      gcall-bv {r = r} p′ s inv H nx ok = case FrK.call-v p′ s H of λ where
        (N , fs′ , run , H′ , CD) →
          N , fs′ , run , record { g-pt = p-block (FrK.callee p′ s) (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                                 ; g-ret = mk-call (FrK.callee p′ s) (s-block p′ s) refl CD (K.Here.h-cfg {p = p′} H)
                                             (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                             (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }

    -- ★ a call: from either kind of root, into either kind of block
    gcall : ∀ {T t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {r : Ret V T}
              {es : Slots (t ⊳ Es)} {a : MV A} {os : Stk S} {n h fs} (P : Pnt (call κ ⨾ k))
          → InvI (es ∥ a ∷ˢ os) r n h → HereP P (es ∥ a ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → ArrivesAt (blockᴵ κ) (frm {t = t} {Es = Es} k es os r) (topv t es ∥ a ∷ˢ []ˢ) n fs
    gcall {t = nothing} (p-start (at s)) inv H nx ok = gcall-sn s inv H nx ok
    gcall {t = just E} (p-start (at s)) inv H nx ok = gcall-sv s inv H nx ok
    gcall {t = nothing} (p-block p′ (at s)) inv H nx ok = gcall-bn p′ s inv H nx ok
    gcall {t = just E} (p-block p′ (at s)) inv H nx ok = gcall-bv p′ s inv H nx ok
    gcall {r = r} {fs = fs} (p-tramp p _) inv (tp1 {X = X} {A} {B} _ , H) nx ok = case tr-call p H of λ where
      (N , fs′ , run , H′ , CD) →
        N , fs′ , run , record { g-pt = p-block p (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-call p (s-tramp p) refl
                                           (called-re (trans (cong (λ z → suc (suc (suc z))) (HereF.f-pc H)) (sym (tr-pos₂ p)))
                                                      (sym (Data.Nat.Properties.n∸n≡0 (t1M X A B))) CD)
                                           (HereF.f-cfg H)
                                           (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }

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

    -- the body's return into a one-shot trampoline (its frame's empty parts by their only forms)
    gret-tr : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} (p₂ : under (ktr1 ds′ b γ) ∈ allK U)
                (e : Sub (blockᴵ (kbody1 ds′ b γ)) (end {sh = [] ∣ B ∷ []})) {e′ : Slots []} {w : MV B} {es : Slots []} {os : Stk []}
                {r : Ret ([] ∣ B ∷ []) T} {n fs} (cfc : FrameSemantics.Frame FS) (sl : ℕ) (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
                (q : under (ktr1 ds′ b γ) ∈ allK U) → p₂ ≡ q
            → KA.lfin {p = q} (K.lowAt q e) ≡ blockFin (kbody1 ds′ b γ)
            → K.Here q e (e′ ∥ w ∷ˢ []ˢ) fs
            → fret fs ≡ trPos (ktr1 ds′ b γ) p₂ 2 ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
            → AllocState.current-frame (falloc fs) ≺ cfc
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ (kbody1 ds′ b γ))))
              ≡ just (SV-Ptr (AtStack cfc (((wsz X + wsz A) ⊔ wsz B) ∸ ((wsz X + wsz A) ⊔ wsz B))))
            → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
            → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (trφ (ktr1 ds′ b γ)) os
            → FreshR r (AllocState.next-heap-ref (falloc fs))
            → RetOK (rtramp {κ = ktr1 ds′ b γ} p₂) (trAt (idx p₂) (ktr1 ds′ b γ) 2) r cfc rets′ sv′ fs
            → AllocState.next-heap-ref (falloc fs) ≡ n
            → ArrivesAt end r (es ∥ w ∷ˢ os) n fs
    gret-tr {X = X} {A} {B} {ds′} {b} {γ} p₂ e {es = []ᵉ} {os = []ˢ} {fs = fs} cfc sl sv′ rets′ _ refl eF H eRets eSv abv area ev sk fr rest nx =
      case tr-back p₂ e cfc (trPos (ktr1 ds′ b γ) p₂ 2) rets′ sv′ sl eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″))
             (subst (λ z → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (sv₁ (frameOf (blockᴵ (kbody1 ds′ b γ)))) ≡ just (SV-Ptr (AtStack cfc z)))
                    (Data.Nat.Properties.n∸n≡0 (t1M X A B)) area) of λ where
        (N , fs′ , run , H′ , CO , tk) →
          N , fs′ , run , record { g-pt = p-tramp p₂ (at (next (next whole))) ; g-here = (tp2 p₂ , H′)
                                 ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }

    -- ★ a one-shot trampoline's way out: the result into the dispatch's
    -- caller, at the path after its `icall` (D421)
    private
      gret-out : ∀ {T Γ′ g X A B} {ds′ : Defs Γ′} {b : Tm Γ′ One (X ⊗t A) B} {γ : Gd g b} {Es S V} {k : Codeᴵ (Es ∣ B ∷ S) V}
                   {es : Slots Es} {os : Stk S} {r : Ret V T} {w : MV B} {n fs}
                   (p : under (ktr1 ds′ b γ) ∈ allK U) (d : DSite g A k) (cfc : FrameSemantics.Frame FS) (sl : ℕ)
                   (sv′ : List (FrameSemantics.Frame FS × ℕ)) (rets′ : List ℕ)
               → HereF (frame 0 ((wsz X + wsz A) ⊔ wsz B)) (trPos (ktr1 ds′ b γ) p 2) ([]ᵉ ∥ w ∷ˢ []ˢ) fs
               → fret fs ≡ dsitePos d ∷ rets′ → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv′
               → AllocState.current-frame (falloc fs) ≺ cfc
               → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) (suc ((wsz X + wsz A) ⊔ wsz B))
                 ≡ just (SV-Ptr (AtStack cfc (Tp (dsiteφ d) S ∸ (suc (wsz A) ⊔ wsz B))))
               → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
               → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) (dsiteφ d) os
               → FreshR r (AllocState.next-heap-ref (falloc fs))
               → RetOK (dsiteRoot d) (dsiteFin d) r cfc rets′ sv′ fs
               → AllocState.next-heap-ref (falloc fs) ≡ n
               → ArrivesAt k r (es ∥ w ∷ˢ os) n fs
      gret-out {A = A} {B} {S = S} p (d-start s) cfc sl sv′ rets′ H eRets eSv abv area ev sk fr rest nx =
        case tr-end p (frameOf main) cfc (S.pos (next s)) rets′ sv′ sl H eRets eSv (λ e → ≺-≢ abv (sym e)) area ev sk
               fitM (proj₁ (S.shape-fits (next s))) (proj₂ (S.shape-fits (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-start (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }
        where
          import Data.Nat.Properties
          fitM : (suc (wsz A) ⊔ wsz B) + ws S ≤ OP (frameOf main)
          fitM = Data.Nat.Properties.≤-trans
                   (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-distribʳ-⊔ (ws S) (suc (wsz A)) (wsz B)))
                   (Data.Nat.Properties.⊔-lub (proj₂ (S.shape-fits s)) (proj₂ (S.shape-fits (next s))))
      gret-out {A = A} {B} {S = S} p (d-block {κ′ = κ′} p′ s) cfc sl sv′ rets′ H eRets eSv abv area ev sk fr rest nx =
        case tr-end p (frameOf (blockᴵ κ′)) cfc (K.pos p′ (next s)) rets′ sv′ sl H eRets eSv (λ e → ≺-≢ abv (sym e)) area ev sk
               fitM (proj₁ (K.shape-fits p′ (next s))) (proj₂ (K.shape-fits p′ (next s))) of λ where
          (N , fs′ , run , C′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-block p′ (at (next s))
                                   ; g-here = record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (HereF.f-run H) ; h-cfg = C′ }
                                   ; g-next = trans (co-next CO) nx ; g-ret = back CO tk fr rest }
        where
          import Data.Nat.Properties
          fitM : (suc (wsz A) ⊔ wsz B) + ws S ≤ OP (frameOf (blockᴵ κ′))
          fitM = Data.Nat.Properties.≤-trans
                   (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-distribʳ-⊔ (ws S) (suc (wsz A)) (wsz B)))
                   (Data.Nat.Properties.⊔-lub (proj₂ (K.shape-fits p′ s)) (proj₂ (K.shape-fits p′ (next s))))

    gret : ∀ {T t B Es S V} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {r : Ret V T} {es : Slots (t ⊳ Es)} {os : Stk S}
             {e′ : Slots (t ⊳ [])} {b : MV B} {n h fs} (P : Pnt (end {sh = t ⊳ [] ∣ B ∷ []}))
         → InvI (e′ ∥ b ∷ˢ []ˢ) (frm {t = t} {Es = Es} k es os r) n h → HereP P (e′ ∥ b ∷ˢ []ˢ) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) (frm {t = t} {Es = Es} k es os r)
                 (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
    gret {t = t} {Es = Es} {k = k} {r = r} {es = es} {os = os} {fs = fs} (p-block p (at e)) inv H nx
         (ok-call _ (s-start s) cfc sl sv′ rets′ refl eF eC eRets eSv abv area ev sk rest) =
      case FrS.return s e cfc rets′ sv′ sl p eC eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) area ev sk of λ where
        (N , fs′ , run , H′ , CO , tk) →
          N , fs′ , run , record { g-pt = p-start (at (next s)) ; g-here = H′ ; g-next = trans (co-next CO) nx
                                 ; g-ret = back CO tk (proj₂ (subst (FreshR (frm {t = t} {Es = Es} k es os r)) (sym nx) (fresh-ret inv))) rest }
    gret {t = t} {Es = Es} {k = k} {r = r} {es = es} {os = os} {fs = fs} (p-block p (at e)) inv H nx
         (ok-call _ (s-block p′ s) cfc sl sv′ rets′ refl eF eC eRets eSv abv area ev sk rest) =
      case FrK.return p′ s e cfc rets′ sv′ sl p eC eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) area ev sk of λ where
        (N , fs′ , run , H′ , CO , tk) →
          N , fs′ , run , record { g-pt = p-block p′ (at (next s)) ; g-here = H′ ; g-next = trans (co-next CO) nx
                                 ; g-ret = back CO tk (proj₂ (subst (FreshR (frm {t = t} {Es = Es} k es os r)) (sym nx) (fresh-ret inv))) rest }
    gret (p-start (at e)) inv H nx (ok-call _ _ _ _ _ _ () _ _ _ _ _ _ _ _ _)
    gret {k = k} {r = r} {es = es} {os = os} {fs = fs} (p-block p (at e)) inv H nx
         (ok-call _ (s-tramp p₂) cfc sl sv′ rets′ refl eF eC eRets eSv abv area ev sk rest) =
      gret-tr p₂ e cfc sl sv′ rets′ p eC eF H eRets eSv abv area ev sk (proj₂ (subst (FreshR (frm {t = nothing} {Es = []} k es os r)) (sym nx) (fresh-ret inv))) rest nx
    gret (p-tramp _ _) inv H nx (ok-call _ _ _ _ _ _ () _ _ _ _ _ _ _ _ _)
    gret (p-start (at e)) inv H nx (ok-tramp _ _ _ _ _ _ () _ _ _ _ _ _ _ _)
    gret (p-block p (at e)) inv H nx (ok-tramp _ _ _ _ _ _ () _ _ _ _ _ _ _ _)
    gret {k = k} {r = r} {es = es} {os = os} {e′ = []ᵉ} {fs = fs} (p-tramp p₂ _) inv (tp2 _ , H) nx
         (ok-tramp p d cfc sl sv′ rets′ refl eF eRets eSv abv area ev sk rest) =
      gret-out p d cfc sl sv′ rets′ H eRets eSv abv area ev sk
        (proj₂ (subst (FreshR (frm {t = nothing} {Es = _} k es os r)) (sym nx) (fresh-ret inv))) rest nx

