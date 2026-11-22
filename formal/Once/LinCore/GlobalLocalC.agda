-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalLocalC — plan 0.146 B1.4b (D434 step 3, D437): THE STEPS AT A `case` (a loop's dispatch) AND A LOOP'S TURN
-- (split from `GlobalLocal` for its build time: each module under 60 s alone).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}


open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
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
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
import Data.Nat
import Once.Memory.HeapAddress
import Once.LinCore.Moves
import Data.Nat.Properties


module Once.LinCore.GlobalLocalC
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)
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

open import Once.LinCore.GlobalLocal fmt ans bw using (module LocalR)

module CaseR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin)
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
  open Rel {FS} U wordOf using (CfgW; VW; vpair; vfn; SlotsAt; cellPtr)
  open import Once.LinCore.Moves {FS} using (slot; InBlk)
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
  open import Once.LinCore.StepEpop fmt ans bw using (epop-inv)
  open import Once.LinCore.HeldI fmt ans bw using (InvI)
  open import Once.LinCore.LabelsI fmt ans bw using (module Img)
  open import Once.LinCore.LowAt fmt ans bw using (Inside)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Once.LinCore.Moves {FS} using (Keep; module Keep)
  open Keep using (k-frame; k-saved; k-ret; k-other; k-log; k-inb)
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret; away-[])
  open Img {FS} ds f ldConst ld-nl using (image-label)

  ----------------------------------------------------------------------
  -- 6. ★ THE STEP THEOREM, for the steps that stay in their root.
  ----------------------------------------------------------------------

  -- no trampoline's point is at a `case` (by its code)
  NotCase : ∀ {sh U′} → Codeᴵ sh U′ → Set
  NotCase (case _ _) = ⊥
  {-# CATCHALL #-}
  NotCase _          = ⊤

  tr-notcase : ∀ {σ sh U′} {κ : Key σ} {c : Codeᴵ sh U′} {p : under κ ∈ allK U} {pt : Pt (blockᴵ κ) c}
             → TrPt p pt → NotCase c
  tr-notcase (tp0 _) = tt
  tr-notcase (tp1 _) = tt
  tr-notcase (tp2 _) = tt
  tr-notcase (to0 _) = tt
  tr-notcase (to1 _) = tt
  tr-notcase (to2 _) = tt
  tr-notcase (tf0 _) = tt
  tr-notcase (tf1 _) = tt
  tr-notcase (tf2 _) = tt
  tr-notcase (tw0 _) = tt
  tr-notcase (tw1 _) = tt
  tr-notcase (tw2 _) = tt
  tr-notcase (tw3 _) = tt
  tr-notcase (tc0 _) = tt
  tr-notcase (tc1 _) = tt
  tr-notcase (tc2 _) = tt
  tr-notcase (tc3 _) = tt
  tr-notcase (tc4 _) = tt

  module Whole (ld : ∀ {b} (v : Lit b) (fs : FlatState)
                    → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                      ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf (lit v)) } ; fpc = suc (FlatMachine.FlatState.fpc fs) }) where
    open LocalR.Whole {FS} ds f ldConst ld-nl wordOf ld using (Onward; gat-start; gat-block)
    open Related

    private
      fresh-at : ∀ {T sh U′} {m : Cfg sh} {r : Ret U′ T} {n h fs} → InvI m r n h → AllocState.next-heap-ref (falloc fs) ≡ n
               → FreshR r (AllocState.next-heap-ref (falloc fs))
      fresh-at {r = r} inv nx = subst (FreshR r) (sym nx) (fresh-ret inv)

    -- ★ a `case`'s left: a local step at a path, or a loop's dispatch out
    gcase₁ : ∀ {T Es A B S U′} {c₁ : Codeᴵ (Es ∣ A ∷ S) U′} {c₂ : Codeᴵ (Es ∣ B ∷ S) U′} {r : Ret U′ T}
               {es : Slots Es} {a : MV A} {os : Stk S} {n h fs} (P : Pnt (case c₁ c₂))
           → InvI (es ∥ minl {B = B} a ∷ˢ os) r n h → HereP P (es ∥ minl {B = B} a ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs → LiveG r (es ∥ minl {B = B} a ∷ˢ os) fs → FreshAl (falloc fs)
           → Onward c₁ r (es ∥ a ∷ˢ os) n fs
    gcase₁ (p-start (at s)) inv H nx ok I lv F = gat-start s StepI.i-case₁ tt inv H nx ok I lv F
    gcase₁ (p-block p (at s)) inv H nx ok I lv F = gat-block p s StepI.i-case₁ tt inv H nx ok I lv F
    gcase₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {a = a} {os = os} {n = n} {fs = fs} (p-start (disp s)) inv H nx ok I lv F = case SL.disp-exit image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , _ , old , tp) →
        N , fs′ , run , record { g-pt = p-start (at (next s)) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) (away-[] r) ok ; g-blk = k-inb K I ; g-live = proj₁ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-case₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {a = a} {os = os} {n = n}) inv nx lv F K) ; g-fal = proj₂ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-case₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {a = a} {os = os} {n = n}) inv nx lv F K) } , k-log K
    gcase₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {a = a} {os = os} {n = n} {fs = fs} (p-block p (disp s)) inv H nx ok I lv F = case KL.disp-exit p image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , _ , old , tp) →
        N , fs′ , run , record { g-pt = p-block p (at (next s)) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) (away-[] r) ok ; g-blk = k-inb K I ; g-live = proj₁ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-case₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {a = a} {os = os} {n = n}) inv nx lv F K) ; g-fal = proj₂ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-case₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {a = a} {os = os} {n = n}) inv nx lv F K) } , k-log K
    gcase₁ (p-tramp p pt) inv (tp , H) nx ok I lv F = ⊥-elim (tr-notcase tp)

    -- ★ a `case`'s right: a local step at a path, or a loop's dispatch again
    gcase₂ : ∀ {T Es A B S U′} {c₁ : Codeᴵ (Es ∣ A ∷ S) U′} {c₂ : Codeᴵ (Es ∣ B ∷ S) U′} {r : Ret U′ T}
               {es : Slots Es} {b : MV B} {os : Stk S} {n h fs} (P : Pnt (case c₁ c₂))
           → InvI (es ∥ minr {A = A} b ∷ˢ os) r n h → HereP P (es ∥ minr {A = A} b ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → InBlk fs → LiveG r (es ∥ minr {A = A} b ∷ˢ os) fs → FreshAl (falloc fs)
           → Onward c₂ r (es ∥ b ∷ˢ os) n fs
    gcase₂ (p-start (at s)) inv H nx ok I lv F = gat-start s StepI.i-case₂ tt inv H nx ok I lv F
    gcase₂ (p-block p (at s)) inv H nx ok I lv F = gat-block p s StepI.i-case₂ tt inv H nx ok I lv F
    gcase₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {b = b} {os = os} {n = n} {fs = fs} (p-start (disp s)) inv H nx ok I lv F = case SL.disp-again image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , _ , old , tp) →
        N , fs′ , run , record { g-pt = p-start (at s) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) (away-[] r) ok ; g-blk = k-inb K I ; g-live = proj₁ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-case₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {b = b} {os = os} {n = n}) inv nx lv F K) ; g-fal = proj₂ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-case₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {b = b} {os = os} {n = n}) inv nx lv F K) } , k-log K
    gcase₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {b = b} {os = os} {n = n} {fs = fs} (p-block p (disp s)) inv H nx ok I lv F = case KL.disp-again p image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , _ , old , tp) →
        N , fs′ , run , record { g-pt = p-block p (at s) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) (away-[] r) ok ; g-blk = k-inb K I ; g-live = proj₁ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-case₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {b = b} {os = os} {n = n}) inv nx lv F K) ; g-fal = proj₂ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-case₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {b = b} {os = os} {n = n}) inv nx lv F K) } , k-log K
    gcase₂ (p-tramp p pt) inv (tp , H) nx ok I lv F = ⊥-elim (tr-notcase tp)

    -- ★ the loop's turn: the body, its dispatch pushed
    gloop : ∀ {T E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
              {r : Ret V T} {m n h fs} (P : Pnt (loop b ⨾ k))
          → InvI m r n h → HereP P m fs → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs → LiveG r m fs → FreshAl (falloc fs)
          → Onward b (case k (loop b ⨾ k) ∷ⁱ r) m n fs
    gloop {b = b} {k = k} {r = r} {m = m} {n = n} {fs = fs} (p-start (at s)) inv H nx ok I lv F = case SL.loop-enter s H of λ where
      (N , fs′ , run , H′ , K , nx′ , _ , old , tp) →
        N , fs′ , run , record { g-pt = p-start (at (body s)) ; g-here = H′ ; g-next = trans nx′ nx
                               ; g-ret = ok-loop (p-start (disp s)) (refl , refl) (ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) (away-[] r) ok) ; g-blk = k-inb K I ; g-live = proj₁ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-loop {body = b} {k = k} {r = r} {m = m} {n = n}) inv nx lv F K) ; g-fal = proj₂ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-loop {body = b} {k = k} {r = r} {m = m} {n = n}) inv nx lv F K) } , k-log K
    gloop {b = b} {k = k} {r = r} {m = m} {n = n} {fs = fs} (p-block p (at s)) inv H nx ok I lv F = case KL.loop-enter p s H of λ where
      (N , fs′ , run , H′ , K , nx′ , _ , old , tp) →
        N , fs′ , run , record { g-pt = p-block p (at (body s)) ; g-here = H′ ; g-next = trans nx′ nx
                               ; g-ret = ok-loop (p-block p (disp s)) (refl , refl) (ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) (away-[] r) ok) ; g-blk = k-inb K I ; g-live = proj₁ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-loop {body = b} {k = k} {r = r} {m = m} {n = n}) inv nx lv F K) ; g-fal = proj₂ (live-quiet {fs = fs} {fs′ = fs′} (StepI.i-loop {body = b} {k = k} {r = r} {m = m} {n = n}) inv nx lv F K) } , k-log K
    gloop (p-tramp _ _) inv () nx ok I lv F

    -- ★ a loop's entry takes a control step (its label: master's budget is read in control steps, D447)
    gloop-ctrl : ∀ {T E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
                   {r : Ret V T} {m n h fs} (P : Pnt (loop b ⨾ k))
               → (inv : InvI m r n h) (H : HereP P m fs) (nx : AllocState.next-heap-ref (falloc fs) ≡ n)
               → (ok : RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs)
               → (I : InBlk fs) (lv : LiveG r m fs) (F : FreshAl (falloc fs))
               → 1 ≤ FlatEventTrace.chain-ctrls {FS} (proj₁ (proj₂ (proj₂ (gloop P inv H nx ok I lv F))))
    gloop-ctrl (p-start (at s)) inv H nx ok I lv F = Data.Nat.s≤s Data.Nat.z≤n
    gloop-ctrl (p-block p (at s)) inv H nx ok I lv F = Data.Nat.s≤s Data.Nat.z≤n
    gloop-ctrl (p-tramp _ _) inv () nx ok I lv F
