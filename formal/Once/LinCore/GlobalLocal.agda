-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalLocal — plan 0.146 B1.4b (D434 step 3, D437): THE STEPS THAT STAY IN THEIR ROOT: a local step (at a path or a trampoline); a `case`, a loop's turn: `GlobalLocalC`; a body's end: `GlobalLocalR`
-- (split from `Global` for its build time; over `Global.Relate`).
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


module Once.LinCore.GlobalLocal
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

module LocalR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
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

  module Whole (ld : ∀ {b} (v : Lit b) (fs : FlatState)
                    → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                      ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf (lit v)) } ; fpc = suc (FlatMachine.FlatState.fpc fs) }) where
    module AS = AtRoot ld rstart main j₀ L₀ˢ start-root refl using (glocal; module LS)
    module AK {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = AtRoot ld (rblock p) (blockᴵ κ) (idx p) (L₀ᵇ κ p) (blockR p) refl using (glocal; module LS)
    open Related

    Onward : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
    Onward c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′ × LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

    private
      fresh-at : ∀ {T sh U′} {m : Cfg sh} {r : Ret U′ T} {n h fs} → InvI m r n h → AllocState.next-heap-ref (falloc fs) ≡ n
               → FreshR r (AllocState.next-heap-ref (falloc fs))
      fresh-at {r = r} inv nx = subst (FreshR r) (sym nx) (fresh-ret inv)

    -- a local step at a path of the start's or a block's code
    gat-start : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
                (s : Sub main c) (st : StepI c r m n t c′ r′ m′ n′) (l : Local st)
              → InvI m r n h → S.Here s m fs → AllocState.next-heap-ref (falloc fs) ≡ n
              → RetOK rstart (ptFin (p-start (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
              → InBlk fs
              → Onward c′ r′ m′ n′ fs
    gat-start s st l inv H nx ok I = case AS.glocal st l s inv H nx ok I of λ where
      (N , fs′ , run , H′ , nx′ , ok′ , I′ , lg) → N , fs′ , run , record { g-pt = p-start (at (AS.LS.succ st l s)) ; g-here = H′ ; g-next = nx′ ; g-ret = ok′ ; g-blk = I′ } , lg

    gat-block : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
                  {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) (s : Sub (blockᴵ κ) c) (st : StepI c r m n t c′ r′ m′ n′) (l : Local st)
              → InvI m r n h → K.Here p s m fs → AllocState.next-heap-ref (falloc fs) ≡ n
              → RetOK (rblock p) (ptFin (p-block p (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
              → InBlk fs
              → Onward c′ r′ m′ n′ fs
    gat-block p s st l inv H nx ok I = case AK.glocal p st l s inv H nx ok I of λ where
      (N , fs′ , run , H′ , nx′ , ok′ , I′ , lg) → N , fs′ , run , record { g-pt = p-block p (at (AK.LS.succ p st l s)) ; g-here = H′ ; g-next = nx′ ; g-ret = ok′ ; g-blk = I′ } , lg

    -- ★ the one step that stays at a trampoline's point: a many-use body's
    -- `epop` (D442), no flat step (its code is the way out's: one address)
    gtr-local : ∀ {T σ sh U′ sh′ U″} {κ : Key σ} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T}
                  {m′ n′ fs} {p : under κ ∈ allK U} {pt : Pt (blockᴵ κ) c}
                (tp : TrPt p pt) (st : StepI c r m n t c′ r′ m′ n′) → LocalC c
              → HereTr tp m fs → AllocState.next-heap-ref (falloc fs) ≡ n
              → RetOK (rtramp p) (ptFin (p-tramp p pt)) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
              → InBlk fs
              → Onward c′ r′ m′ n′ fs
    gtr-local (tp0 _) st () H nx ok I
    gtr-local (tp1 _) st () H nx ok I
    gtr-local (tp2 _) st () H nx ok I
    gtr-local (to0 _) st () H nx ok I
    gtr-local (to1 _) st () H nx ok I
    gtr-local (to2 _) st () H nx ok I
    gtr-local (tf0 _) st () H nx ok I
    gtr-local (tf1 _) st () H nx ok I
    gtr-local (tf2 _) st () H nx ok I
    gtr-local (tw0 _) st () H nx ok I
    gtr-local (tw1 _) st () H nx ok I
    gtr-local (tw3 _) st () H nx ok I
    gtr-local (tc0 _) st () H nx ok I
    gtr-local (tc1 _) st () H nx ok I
    gtr-local (tc3 _) st () H nx ok I
    gtr-local (tc4 _) st () H nx ok I
    gtr-local {r = r} {n = n} {fs = fs} (tw2 p) st _ H nx ok I =
      epop-inv (λ m₀ c′ r′ m′ n′ → HereTr (tw2 p) m₀ fs → AllocState.next-heap-ref (falloc fs) ≡ n → Onward c′ r′ m′ n′ fs)
        (λ { {os = v ∷ˢ os′} H′ nx′ →
               0 , fs , FlatStepsAPI.[] ,
               record { g-pt = p-tramp p (at (next (next (next whole)))) ; g-here = tw3 p , H′ ; g-next = nx′ ; g-ret = ok ; g-blk = I } , refl })
        st H nx
    -- a copy's `epop` (its contents' view dropped)
    gtr-local {r = r} {n = n} {fs = fs} (tc2 p) st _ H nx ok I =
      epop-inv (λ m₀ c′ r′ m′ n′ → HereTr (tc2 p) m₀ fs → AllocState.next-heap-ref (falloc fs) ≡ n → Onward c′ r′ m′ n′ fs)
        (λ { {es = vw cv es′} {os = v ∷ˢ os′} H′ nx′ →
               0 , fs , FlatStepsAPI.[] ,
               record { g-pt = p-tramp p (at (next (next (next whole)))) ; g-here = tc3 p , H′ ; g-next = nx′ ; g-ret = ok ; g-blk = I } , refl })
        st H nx

    -- ★ a straight step (local, not a `case`): only at a path; no case
    -- split on the step (StepKinds)
    gstep-at : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
               (P : Pnt c) (st : StepI c r m n t c′ r′ m′ n′) (l : StraightC c)
             → InvI m r n h → HereP P m fs → AllocState.next-heap-ref (falloc fs) ≡ n
             → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
             → InBlk fs
             → Onward c′ r′ m′ n′ fs
    gstep-at {c = c} (p-start (at s)) st l inv H nx ok I = gat-start s st (straight-local c l) inv H nx ok I
    gstep-at {c = c} (p-block p (at s)) st l inv H nx ok I = gat-block p s st (straight-local c l) inv H nx ok I
    gstep-at (p-start (disp s)) st () inv H nx ok I
    gstep-at (p-block p (disp s)) st () inv H nx ok I
    gstep-at {c = c} (p-tramp p pt) st l inv (tp , H) nx ok I = gtr-local tp st (straight-local c l) H nx ok I
    -- explicit: else coverage splits the step at `halted` (a costly split)
    gstep-at p-halt st () inv H nx ok I

    gstep-local : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
                  (st : StepI c r m n t c′ r′ m′ n′) → StraightC c → InvI m r n h → Related c r m n fs → Onward c′ r′ m′ n′ fs
    gstep-local st l inv G = gstep-at (g-pt G) st l inv (g-here G) (g-next G) (g-ret G) (g-blk G)
