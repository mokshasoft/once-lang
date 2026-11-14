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
open import Once.LinCore.GlobalRetB fmt ans bw using (module RetB)
open import Once.LinCore.GlobalRetT fmt ans bw using (module RetT)

module RetR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open TrampR {FS} ds f ldConst ld-nl wordOf
  open TrampO {FS} ds f ldConst ld-nl wordOf
  open TrampF {FS} ds f ldConst ld-nl wordOf using (tf-end)
  open CallR {FS} ds f ldConst ld-nl wordOf using (module GCall)
  open RetB {FS} ds f ldConst ld-nl wordOf using (module GRetB)
  open RetT {FS} ds f ldConst ld-nl wordOf using (module GRetT)
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
  open import Once.LinCore.LowerSimE {FS} using (co-pc; co-halt; co-size)
  open import Once.LinCore.LowerSimG {FS} using (ClosIn; closure-in)
  open ClosIn
  open ImgE {FS} ds f ldConst ld-nl using (image-tramp)
  open Sim {FS} U wordOf using (≤∸)


  module GRet where
    open Related
    open GCall using (ArrivesAt)
    open GRetB
    open GRetT

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
              → InBlk fs
              → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
      gret-ss s e p eC cfc sl sv′ rets′ eF H eRets eSv abv area ev sk fr rest nx I =
        case FrS.return s e cfc rets′ sv′ sl p eC eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) area ev sk of λ where
          (N , fs′ , run , H′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-start (at (next s)) ; g-here = H′ ; g-next = trans (co-next CO) nx
                                   ; g-ret = back CO tk fr rest ; g-blk = co-inb CO I }

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
              → InBlk fs
              → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
      gret-sb p′ s e p eC cfc sl sv′ rets′ eF H eRets eSv abv area ev sk fr rest nx I =
        case FrK.return p′ s e cfc rets′ sv′ sl p eC eF H eRets eSv (λ e″ → ≺-≢ abv (sym e″)) area ev sk of λ where
          (N , fs′ , run , H′ , CO , tk) →
            N , fs′ , run , record { g-pt = p-block p′ (at (next s)) ; g-here = H′ ; g-next = trans (co-next CO) nx
                                   ; g-ret = back CO tk fr rest ; g-blk = co-inb CO I }

    private
      rc-start : ∀ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} (s : Sub main (call κ ⨾ k)) → GretC (s-start s)
      rc-start s (p-block p (at e)) _ cfc sl sv′ rets′ refl eF eC H eRets eSv abv area ev sk fr rest nx I =
        gret-ss s e p eC cfc sl sv′ rets′ eF H eRets eSv abv area ev sk fr rest nx I
      rc-start s (p-start (at e)) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx I
      rc-start s (p-tramp _ _) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx I

      rc-block : ∀ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {σ′} {κ′ : Key σ′}
                (p′ : (σ′ , κ′) ∈ allK U) (s : Sub (blockᴵ κ′) (call κ ⨾ k)) → GretC (s-block p′ s)
      rc-block p′ s (p-block p (at e)) _ cfc sl sv′ rets′ refl eF eC H eRets eSv abv area ev sk fr rest nx I =
        gret-sb p′ s e p eC cfc sl sv′ rets′ eF H eRets eSv abv area ev sk fr rest nx I
      rc-block p′ s (p-start (at e)) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx I
      rc-block p′ s (p-tramp _ _) _ cfc sl sv′ rets′ () eF eC H eRets eSv abv area ev sk fr rest nx I

    private
      gret-cases : SiteCases
      gret-cases = record { SP = GretC ; on-start = rc-start ; on-block = rc-block ; on-tramp = rc-tramp ; on-trampo = rc-trampo ; on-trampf = rc-trampf }

    gret : ∀ {T t B Es S V} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} {r : Ret V T} {es : Slots (t ⊳ Es)} {os : Stk S}
             {e′ : Slots (t ⊳ [])} {b : MV B} {n h fs} (P : Pnt (end {sh = t ⊳ [] ∣ B ∷ []}))
         → InvI (e′ ∥ b ∷ˢ []ˢ) (frm {t = t} {Es = Es} k es os r) n h → HereP P (e′ ∥ b ∷ˢ []ˢ) fs
         → AllocState.next-heap-ref (falloc fs) ≡ n
         → RetOK (rootOf P) (ptFin P) (frm {t = t} {Es = Es} k es os r)
                 (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → InBlk fs
         → ArrivesAt k r (es ∥ b ∷ˢ os) n fs
    -- by the return stack's top first (one split of `RetOK`), then the point
    gret {t = t} {Es = Es} {k = k} {r = r} {es = es} {os = os} {fs = fs} P inv H nx
         (ok-call p st cfc sl sv′ rets′ eR eF eC eRets eSv abv area ev sk rest) I =
      site-elim gret-cases st P p cfc sl sv′ rets′ eR eF eC H eRets eSv abv area ev sk
        (proj₂ (subst (FreshR (frm {t = t} {Es = Es} k es os r)) (sym nx) (fresh-ret inv))) rest nx I
    gret {t = t} {Es = Es} {k = k} {r = r} {es = es} {os = os} {fs = fs} P inv H nx
         (ok-tramp p o d cfc sl sv′ rets′ eR eF eRets eSv abv area fit ev sk rest) I =
      gret-t P d p cfc sl sv′ rets′ eR eF H o eRets eSv abv area fit ev sk
        (proj₂ (subst (FreshR (frm {t = t} {Es = Es} k es os r)) (sym nx) (fresh-ret inv))) rest nx I

    gret {t = t} {Es = Es} {k = k} {r = r} {es = es} {os = os} {fs = fs} P inv H nx
         (ok-trampf p d cfc sl sv′ rets′ eR eF eRets eSv abv ev sk rest) I =
      gret-tf P d p cfc sl sv′ rets′ eR eF H eRets eSv abv ev sk
        (proj₂ (subst (FreshR (frm {t = t} {Es = Es} k es os r)) (sym nx) (fresh-ret inv))) rest nx I
