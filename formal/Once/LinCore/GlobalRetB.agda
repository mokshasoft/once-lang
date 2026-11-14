-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalRetB — plan 0.146 B1.4b: A RETURN, its shared parts (the caller's frame back; the return's motive)
-- (split from `GlobalRet` for its build time).
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


module Once.LinCore.GlobalRetB
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm; _∷ⁱ_)
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw using (Frame; frame; frameOf; budget; wsz; ws; EP; OP; envW; opW)
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
open import Once.LinCore.GlobalTrampF fmt ans bw using (module TrampF)
open import Once.LinCore.GlobalCall fmt ans bw using (module CallR)

module RetB {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampF {FS} ds f ldConst ld-nl wordOf using (tf-end)
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
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; vone; SlotsAt; cellPtr)
  open FlatMachine {FS} using (fpc)
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
  open import Once.LinCore.Moves {FS} using (Keep; k-frame; k-ret; k-saved; k-other)
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret)
  open Img {FS} ds f ldConst ld-nl using (image-label)
  open Frames {FS} using (Called)
  open Called
  open import Once.LinCore.LowerSimE {FS} using (callee-frame; callee-below; callee-≢; CallOut; CallOutA; co-frame; co-ret; co-saved; co-rest; co-next)
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
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt; co-size)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)


  module GRetB where
    open Related
    open GCall using (ArrivesAt)

    -- ★ a return: the caller's frame back, the result on its stack
    module _ where
      frame-eq : ∀ {f g x y} → AtStack {FS} f x ≡ AtStack g y → f ≡ g
      frame-eq refl = refl

      back : ∀ {T U′ R fin} {r : Ret U′ T} {fs fs′ cfc a src o nb pc rets′ sv′ sl}
           → CallOut fs fs′ cfc a src o nb pc rets′ sv′ sl
           → (∀ x → budget (rootφ R) ≤ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x)
           → FreshR r (AllocState.next-heap-ref (falloc fs))
           → RetOK R fin r cfc rets′ sv′ fs
           → RetOK R fin r (AllocState.current-frame (falloc fs′)) (fret fs′) (AllocState.saved-frames (falloc fs′)) fs′
      -- a return writes only frames: the heap's words and blocks stand (D424)
      co-inb : ∀ {fs fs′ cfc af a src o nb pc rets′ sv′ sl} → CallOutA fs fs′ cfc af a src o nb pc rets′ sv′ sl → InBlk fs → InBlk fs′
      co-inb {fs} {fs′} CO = inb-pt {fs} {fs′} (λ hl → co-rest CO (AtDynamic hl) (λ k k< ())) (co-next CO) (co-size CO)

      back {cfc = cfc} CO tk fr ok =
        ctx-to (sym (co-frame CO)) (sym (co-ret CO)) (sym (co-saved CO))
          (ret-top (λ f x ne → co-rest CO (AtStack f x) (λ k k< e → ne (frame-eq e))) tk
                   (λ hl _ → co-rest CO (AtDynamic hl) (λ k k< ())) fr ok)

    -- a block's return, by the point and the call site
    module _ where
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
        → InBlk fs
        → ArrivesAt k r (es ∥ b ∷ˢ os) n fs

    module _ where
      -- a trampoline's inner return (D421): by the generic `tr-back′` over the site's own key (no second
      -- spelling of it: a key compared across spellings unfolds the block's labels and frame)
      area0 : ∀ (fs : FlatState) {x cfc z}
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) x ≡ just (SV-Ptr (AtStack cfc z)) → z ≡ 0
            → LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs)) x ≡ just (SV-Ptr (AtStack cfc 0))
      area0 fs a refl = a


    module _ where
      -- ★ a free's trampoline's way out (D417): a bare return, the result One
      -- (no words), the caller's frame as it was
      one-cfg : ∀ {fs fs′ cfc pc rets′ sv′ sl} {φ : Frame} {Es S} {es : Slots Es} {os : Stk S} (w : MV One)
              → CallOut fs fs′ cfc 0 0 0 0 pc rets′ sv′ sl
              → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
              → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) φ os
              → envW (Es ∣ One ∷ S) ≤ EP φ → opW (Es ∣ One ∷ S) ≤ OP φ
              → CfgW (LocState.heapMem (floc fs′)) (slot fs′) φ (es ∥ w ∷ˢ os)
      one-cfg {fs} {fs′} {cfc} {φ = φ} {es = es} {os} mone CO ev sk fe fb =
        subst (λ g → CfgW (LocState.heapMem (floc fs′)) (LocState.stackMem (floc fs′) g) φ (es ∥ mone ∷ˢ os)) (sym (co-frame CO))
          (record { c-env = envW-heap es (λ i k _ → hp (cellLoc i k)) (envW-frame es (λ x _ → sp x) ev)
                  ; c-stk = (([] , vone , tt) , stkW-heap os (λ i k _ → hp (cellLoc i k)) (stk-all os (λ x → sp x) sk))
                  ; c-efit = fe ; c-sfit = fb })
        where
          hp : ∀ hl → LocState.heapMem (floc fs′) hl ≡ LocState.heapMem (floc fs) hl
          hp hl = co-rest CO (AtDynamic hl) (λ k ())
          sp : ∀ x → LocState.stackMem (floc fs′) cfc x ≡ LocState.stackMem (floc fs) cfc x
          sp x = co-rest CO (AtStack cfc x) (λ k ())

