-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.GlobalLocal — plan 0.146 B1.4b (D417 step 3, D420): THE STEPS THAT STAY IN THEIR ROOT: a local step, a `case` (a loop's dispatch), a loop's turn, a body's end
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


module Once.LinCore.GlobalLocal
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

module LocalR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
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

  -- no step that stays in its root runs at a trampoline's point (by its code)
  tr-nolocal : ∀ {σ sh U′} {κ : Key σ} {c : Codeᴵ sh U′} {p : under κ ∈ allK U} {pt : Pt (blockᴵ κ) c}
             → TrPt p pt → LocalC c → ⊥
  tr-nolocal (tp0 _) ()
  tr-nolocal (tp1 _) ()
  tr-nolocal (tp2 _) ()

  module Whole (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                    → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                      ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (FlatMachine.fpc fs) }) where
    module AS = AtRoot ld rstart main j₀ L₀ˢ start-root refl using (glocal; module LS)
    module AK {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = AtRoot ld (rblock p) (blockᴵ κ) (idx p) (L₀ᵇ κ p) (blockR p) refl using (glocal; module LS)
    open Related

    Onward : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
    Onward c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × Related c r m n fs′

    private
      fresh-at : ∀ {T sh U′} {m : Cfg sh} {r : Ret U′ T} {n h fs} → InvI m r n h → AllocState.next-heap-ref (falloc fs) ≡ n
               → FreshR r (AllocState.next-heap-ref (falloc fs))
      fresh-at {r = r} inv nx = subst (FreshR r) (sym nx) (fresh-ret inv)

    -- a local step at a path of the start's or a block's code
    gat-start : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
                (s : Sub main c) (st : StepI c r m n t c′ r′ m′ n′) (l : Local st)
              → InvI m r n h → S.Here s m fs → AllocState.next-heap-ref (falloc fs) ≡ n
              → RetOK rstart (ptFin (p-start (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
              → Onward c′ r′ m′ n′ fs
    gat-start s st l inv H nx ok = case AS.glocal st l s inv H nx ok of λ where
      (N , fs′ , run , H′ , nx′ , ok′) → N , fs′ , run , record { g-pt = p-start (at (AS.LS.succ st l s)) ; g-here = H′ ; g-next = nx′ ; g-ret = ok′ }

    gat-block : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
                  {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) (s : Sub (blockᴵ κ) c) (st : StepI c r m n t c′ r′ m′ n′) (l : Local st)
              → InvI m r n h → K.Here p s m fs → AllocState.next-heap-ref (falloc fs) ≡ n
              → RetOK (rblock p) (ptFin (p-block p (at s))) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
              → Onward c′ r′ m′ n′ fs
    gat-block p s st l inv H nx ok = case AK.glocal p st l s inv H nx ok of λ where
      (N , fs′ , run , H′ , nx′ , ok′) → N , fs′ , run , record { g-pt = p-block p (at (AK.LS.succ p st l s)) ; g-here = H′ ; g-next = nx′ ; g-ret = ok′ }

    -- ★ a straight step (local, not a `case`): only at a path; no case
    -- split on the step (StepKinds)
    gstep-at : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
               (P : Pnt c) (st : StepI c r m n t c′ r′ m′ n′) (l : StraightC c)
             → InvI m r n h → HereP P m fs → AllocState.next-heap-ref (falloc fs) ≡ n
             → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
             → Onward c′ r′ m′ n′ fs
    gstep-at {c = c} (p-start (at s)) st l inv H nx ok = gat-start s st (straight-local c l) inv H nx ok
    gstep-at {c = c} (p-block p (at s)) st l inv H nx ok = gat-block p s st (straight-local c l) inv H nx ok
    gstep-at (p-start (disp s)) st () inv H nx ok
    gstep-at (p-block p (disp s)) st () inv H nx ok
    gstep-at {c = c} (p-tramp p pt) st l inv (tp , H) nx ok = ⊥-elim (tr-nolocal tp (straight-local c l))
    -- explicit: else coverage splits the step at `halted` (a costly split)
    gstep-at p-halt st () inv H nx ok

    gstep-local : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
                  (st : StepI c r m n t c′ r′ m′ n′) → StraightC c → InvI m r n h → Related c r m n fs → Onward c′ r′ m′ n′ fs
    gstep-local st l inv G = gstep-at (g-pt G) st l inv (g-here G) (g-next G) (g-ret G)

    -- ★ a `case`'s left: a local step at a path, or a loop's dispatch out
    gcase₁ : ∀ {T Es A B S U′} {c₁ : Codeᴵ (Es ∣ A ∷ S) U′} {c₂ : Codeᴵ (Es ∣ B ∷ S) U′} {r : Ret U′ T}
               {es : Slots Es} {a : MV A} {os : Stk S} {n h fs} (P : Pnt (case c₁ c₂))
           → InvI (es ∥ minl {B = B} a ∷ˢ os) r n h → HereP P (es ∥ minl {B = B} a ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → Onward c₁ r (es ∥ a ∷ˢ os) n fs
    gcase₁ (p-start (at s)) inv H nx ok = gat-start s StepI.i-case₁ tt inv H nx ok
    gcase₁ (p-block p (at s)) inv H nx ok = gat-block p s StepI.i-case₁ tt inv H nx ok
    gcase₁ {r = r} {fs = fs} (p-start (disp s)) inv H nx ok = case SL.disp-exit image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-start (at (next s)) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok }
    gcase₁ {r = r} {fs = fs} (p-block p (disp s)) inv H nx ok = case KL.disp-exit p image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-block p (at (next s)) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok }
    gcase₁ (p-tramp p pt) inv (tp , H) nx ok = ⊥-elim (tr-nolocal tp tt)

    -- ★ a `case`'s right: a local step at a path, or a loop's dispatch again
    gcase₂ : ∀ {T Es A B S U′} {c₁ : Codeᴵ (Es ∣ A ∷ S) U′} {c₂ : Codeᴵ (Es ∣ B ∷ S) U′} {r : Ret U′ T}
               {es : Slots Es} {b : MV B} {os : Stk S} {n h fs} (P : Pnt (case c₁ c₂))
           → InvI (es ∥ minr {A = A} b ∷ˢ os) r n h → HereP P (es ∥ minr {A = A} b ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n
           → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
           → Onward c₂ r (es ∥ b ∷ˢ os) n fs
    gcase₂ (p-start (at s)) inv H nx ok = gat-start s StepI.i-case₂ tt inv H nx ok
    gcase₂ (p-block p (at s)) inv H nx ok = gat-block p s StepI.i-case₂ tt inv H nx ok
    gcase₂ {r = r} {fs = fs} (p-start (disp s)) inv H nx ok = case SL.disp-again image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-start (at s) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok }
    gcase₂ {r = r} {fs = fs} (p-block p (disp s)) inv H nx ok = case KL.disp-again p image-label s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-block p (at s) ; g-here = H′ ; g-next = trans nx′ nx ; g-ret = ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok }
    gcase₂ (p-tramp p pt) inv (tp , H) nx ok = ⊥-elim (tr-nolocal tp tt)

    -- ★ the loop's turn: the body, its dispatch pushed
    gloop : ∀ {T E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
              {r : Ret V T} {m n h fs} (P : Pnt (loop b ⨾ k))
          → InvI m r n h → HereP P m fs → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) r (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → Onward b (case k (loop b ⨾ k) ∷ⁱ r) m n fs
    gloop {r = r} {fs = fs} (p-start (at s)) inv H nx ok = case SL.loop-enter s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-start (at (body s)) ; g-here = H′ ; g-next = trans nx′ nx
                               ; g-ret = ok-loop (p-start (disp s)) (refl , refl) (ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok) }
    gloop {r = r} {fs = fs} (p-block p (at s)) inv H nx ok = case KL.loop-enter p s H of λ where
      (N , fs′ , run , H′ , K , nx′ , old , tp) →
        N , fs′ , run , record { g-pt = p-block p (at (body s)) ; g-here = H′ ; g-next = trans nx′ nx
                               ; g-ret = ok-loop (p-block p (disp s)) (refl , refl) (ret-step K old tp (fresh-at {r = r} {fs = fs} inv nx) ok) }
    gloop (p-tramp _ _) inv () nx ok

    -- ★ a body's end: the jump to its loop's dispatch
    greti : ∀ {T sh U′} {k : Codeᴵ sh U′} {r : Ret U′ T} {m n h fs} (P : Pnt (end {sh}))
          → InvI m (k ∷ⁱ r) n h → HereP P m fs → AllocState.next-heap-ref (falloc fs) ≡ n
          → RetOK (rootOf P) (ptFin P) (k ∷ⁱ r) (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
          → Onward k r m n fs
    greti {k = k} {r = r} {fs = fs} (p-start (at e)) inv H nx (ok-loop (p-start (disp s′)) (refl , efin) rest) =
      case SL.end-jump e image-label efin (SL.dispIn s′) H of λ where
        (fs′ , run , Hq , K , nx′ , old , tp) →
          1 , fs′ , run , record { g-pt = p-start (disp s′) ; g-here = Hq ; g-next = trans nx′ nx
                                 ; g-ret = ret-step K old tp (fresh-at {r = k ∷ⁱ r} {fs = fs} inv nx) rest }
    greti {k = k} {r = r} {fs = fs} (p-block p (at e)) inv H nx (ok-loop (p-block p′ (disp s′)) (refl , efin) rest) =
      case KL.end-jump p e image-label efin (KL.dispIn p s′) H of λ where
        (fs′ , run , Hq , K , nx′ , old , tp) →
          1 , fs′ , run , record { g-pt = p-block p (disp s′) ; g-here = Hq ; g-next = trans nx′ nx
                                 ; g-ret = ret-step K old tp (fresh-at {r = k ∷ⁱ r} {fs = fs} inv nx) rest }
    greti (p-start (at e)) inv H nx (ok-loop (p-block _ (disp _)) (() , _) rest)
    greti (p-start (at e)) inv H nx (ok-loop (p-start (at _)) () rest)
    greti (p-start (at e)) inv H nx (ok-loop (p-block _ (at _)) () rest)
    greti (p-start (at e)) inv H nx (ok-loop (p-tramp _ _) () rest)
    greti (p-start (at e)) inv H nx (ok-loop p-halt () rest)
    greti (p-block p (at e)) inv H nx (ok-loop (p-start (disp _)) (() , _) rest)
    greti (p-block p (at e)) inv H nx (ok-loop (p-start (at _)) () rest)
    greti (p-block p (at e)) inv H nx (ok-loop (p-block _ (at _)) () rest)
    greti (p-block p (at e)) inv H nx (ok-loop (p-tramp _ _) () rest)
    greti (p-block p (at e)) inv H nx (ok-loop p-halt () rest)
    greti (p-tramp _ _) inv H nx (ok-loop K lt rest) = ⊥-elim (loop-not-tramp K lt)

