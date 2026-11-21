-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalLocalR — plan 0.146 B1.4b (D434 step 3, D437): A BODY'S END (the jump to its loop's dispatch)
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


module Once.LinCore.GlobalLocalR
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
open import Once.LinCore.Layout fmt bw using (Frame; frame; frameOf; budget; wsz; ws; module Frame)
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
open import Once.LinCore.GlobalLocal fmt ans bw using (module LocalR)

module EndR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
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
  open Cells {FS} U wordOf using (fresh-cfg; fresh-ret)
  open Img {FS} ds f ldConst ld-nl using (image-label)

  ----------------------------------------------------------------------
  -- 6. ★ THE STEP THEOREM, for the steps that stay in their root.
  ----------------------------------------------------------------------

  -- a trampoline's body has no loop to end in
  loop-not-tramp : ∀ {σ sh V fin} {κ : Key σ} {p : under κ ∈ allK U} {k : Codeᴵ sh V} (K : Pnt k) → LoopTo (rtramp p) fin K → ⊥
  loop-not-tramp (p-start (at _))   ()
  loop-not-tramp (p-start (disp _)) (() , _)
  loop-not-tramp (p-block _ (at _))   ()
  loop-not-tramp (p-block _ (disp _)) (() , _)
  loop-not-tramp (p-tramp _ _) ()
  loop-not-tramp p-halt ()

  module Whole (ld : ∀ {b} (v : Lit b) (fs : FlatState)
                    → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                      ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf (lit v)) } ; fpc = suc (FlatMachine.FlatState.fpc fs) }) where
    open LocalR.Whole {FS} ds f ldConst ld-nl wordOf ld using (Onward; gat-start; gat-block)
    open Related

    private
      fresh-at : ∀ {T sh U′} {m : Cfg sh} {r : Ret U′ T} {n h fs} → InvI m r n h → AllocState.next-heap-ref (falloc fs) ≡ n
               → FreshR r (AllocState.next-heap-ref (falloc fs))
      fresh-at {r = r} inv nx = subst (FreshR r) (sym nx) (fresh-ret inv)

    -- ★ a body's end: the jump to its loop's dispatch
    greti : ∀ {T sh U′} {k : Codeᴵ sh U′} {r : Ret U′ T} {m n h fs} (P : Pnt (end {sh}))
          → InvI m (k ∷ⁱ r) n h → HereP P m fs → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) (k ∷ⁱ r) (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → InBlk fs
          → Onward k r m n fs
    greti {k = k} {r = r} {fs = fs} (p-start (at e)) inv H nx (ok-loop (p-start (disp s′)) (refl , efin) rest) I =
      case SL.end-jump e image-label efin (SL.dispIn s′) H of λ where
        (fs′ , run , Hq , K , nx′ , old , tp) →
          1 , fs′ , run , record { g-pt = p-start (disp s′) ; g-here = Hq ; g-next = trans nx′ nx
                                 ; g-ret = ret-step K old tp (fresh-at {r = k ∷ⁱ r} {fs = fs} inv nx) rest ; g-blk = k-inb K I } , k-log K
    greti {k = k} {r = r} {fs = fs} (p-block p (at e)) inv H nx (ok-loop (p-block p′ (disp s′)) (refl , efin) rest) I =
      case KL.end-jump p e image-label efin (KL.dispIn p s′) H of λ where
        (fs′ , run , Hq , K , nx′ , old , tp) →
          1 , fs′ , run , record { g-pt = p-block p (disp s′) ; g-here = Hq ; g-next = trans nx′ nx
                                 ; g-ret = ret-step K old tp (fresh-at {r = k ∷ⁱ r} {fs = fs} inv nx) rest ; g-blk = k-inb K I } , k-log K
    greti (p-start (at e)) inv H nx (ok-loop (p-block _ (disp _)) (() , _) rest) I
    greti (p-start (at e)) inv H nx (ok-loop (p-start (at _)) () rest) I
    greti (p-start (at e)) inv H nx (ok-loop (p-block _ (at _)) () rest) I
    greti (p-start (at e)) inv H nx (ok-loop (p-tramp _ _) () rest) I
    greti (p-start (at e)) inv H nx (ok-loop p-halt () rest) I
    greti (p-block p (at e)) inv H nx (ok-loop (p-start (disp _)) (() , _) rest) I
    greti (p-block p (at e)) inv H nx (ok-loop (p-start (at _)) () rest) I
    greti (p-block p (at e)) inv H nx (ok-loop (p-block _ (at _)) () rest) I
    greti (p-block p (at e)) inv H nx (ok-loop (p-tramp _ _) () rest) I
    greti (p-block p (at e)) inv H nx (ok-loop p-halt () rest) I
    greti (p-tramp _ _) inv H nx (ok-loop K lt rest) I = ⊥-elim (loop-not-tramp K lt)
