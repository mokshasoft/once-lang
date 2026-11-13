-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalCall — plan 0.146 B1.4b (D417 step 3, D420): A CALL: the callee's frame opened, the caller's saved
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
open import Once.LinCore.GlobalTrampO fmt ans bw using (module TrampO)

module CallR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
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
    gcall {r = r} {fs = fs} (p-tramp p _) inv (to1 {F = F} {S} _ , H) nx ok = case to-call p H of λ where
      (N , fs′ , run , H′ , CD) →
        N , fs′ , run , record { g-pt = p-block p (at whole) ; g-here = H′ ; g-next = trans (cd-next CD) nx
                               ; g-ret = mk-call p (s-trampo p) refl
                                           (called-re (trans (cong (λ z → suc (suc (suc z))) (HereF.f-pc H)) (sym (tO-pos₂ p)))
                                                      (sym (Data.Nat.Properties.n∸n≡0 (tOM F S))) CD)
                                           (HereF.f-cfg H)
                                           (λ i le → fresh-cfg inv i (subst (_≤ serial i) nx le))
                                           (subst (FreshR r) (sym nx) (fresh-ret inv)) ok }
