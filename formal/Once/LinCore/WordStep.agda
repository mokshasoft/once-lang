-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.WordStep — plan 0.146 B1.4b (D417 step 3, D420): ★★ THE STEP THEOREM: every covered image step is matched by flat steps that keep the relation
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
open import Data.Sum using (_⊎_; inj₁; inj₂)
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
import Level


module Once.LinCore.WordStep
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
open import Once.LinCore.GlobalLocal fmt ans bw using (module LocalR)
open import Once.LinCore.GlobalCall fmt ans bw using (module CallR)
open import Once.LinCore.GlobalRet fmt ans bw using (module RetR)
open import Once.LinCore.GlobalDispatch fmt ans bw using (module DispR)
open import Once.LinCore.GlobalDispatchF fmt ans bw using (module DispF)
open import Once.LinCore.GlobalDispatchW fmt ans bw using (module DispW)
open import Once.LinCore.GlobalDispatchC fmt ans bw using (module DispC)
open import Once.LinCore.GlobalOpenC fmt ans bw using (module OpenC)
open import Once.LinCore.GlobalRecloseC fmt ans bw using (module RecloseC)
open import Once.LinCore.GlobalOp fmt ans bw using (module OpG)
open import Once.LinCore.StepOp fmt ans bw using (module Agree)

module StepR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf
  open LocalR {FS} ds f ldConst ld-nl wordOf using (module Whole)
  open CallR {FS} ds f ldConst ld-nl wordOf using (module GCall)
  open RetR {FS} ds f ldConst ld-nl wordOf using (module GRet)
  open DispR {FS} ds f ldConst ld-nl wordOf using (gicall; gopen1; gnopen; giobs)
  open DispF {FS} ds f ldConst ld-nl wordOf using (gcfree; gnfree; gfopen; gfopenν)
  open DispW {FS} ds f ldConst ld-nl wordOf using (gicallω; gopenω)
  open DispC {FS} ds f ldConst ld-nl wordOf using (gccopy; gncopy)
  open OpenC {FS} ds f ldConst ld-nl wordOf using (gcopen; gcopenν)
  open RecloseC {FS} ds f ldConst ld-nl wordOf using (greclose; grecloseν)
  open OpG {FS} ds f ldConst ld-nl wordOf using (gop; gopend)
  open Ctl {FS} ds f ldConst ld-nl using (main; L₀ˢ; L₀ᵇ; start-root; blockFin; Pnt; p-start; p-block; p-tramp; p-halt; ptFin)
  open Program ds f using (U)
  open Agree {FS} U wordOf using (Agrees)
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
  open import Once.LinCore.StepKinds fmt ans bw using (Local; LocalC; StraightC; straight-local; CoveredC; Motive; CoveredCases; covered-elim)
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

  ----------------------------------------------------------------------
  -- 8. ★★ THE STEP THEOREM: every covered image step is matched by flat
  -- steps that keep the relation. Covered: the one-shot and the observation
  -- dispatches (`icall`, `iobs`, `icallω`, `cfree`, `nfree`) and their trampolines
  -- (`open1`, `nopen`, `openω`, `fopen`, the inner call, the way out; D421, D423,
  -- D417, D425), and the copy's (`ccopy`, `ncopy`, `copen`, `reclose`; D417); an op
  -- (`lop`), relative to the machine's world (D426: `Agrees`), a halting op landing in a
  -- halted machine (`Lands`).
  ----------------------------------------------------------------------

  module Theorem (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                       → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                         ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (FlatMachine.fpc fs) }) where
    open Whole ld using (gstep-local; gcase₁; gcase₂; gloop; greti)
    open GCall using (gcall; ArrivesAt)
    open GRet using (gret)
    open Related
    -- where a step lands: related, or (the image halted) a halted machine
    HaltC : ∀ {sh U′} → Codeᴵ sh U′ → FlatState → Set
    HaltC halted fs = LocState.halted (floc fs) ≡ Data.Bool.true
    {-# CATCHALL #-}
    HaltC _      fs = Data.Empty.⊥

    Lands : ∀ {T sh U′} → Codeᴵ sh U′ → Ret U′ T → Cfg sh → ℕ → FlatState → Set
    Lands c r m n fs = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × (Related c r m n fs′ ⊎ HaltC c fs′)

    lift : ∀ {T sh U′} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n fs} → ArrivesAt c r m n fs → Lands c r m n fs
    lift (N , fs′ , st , G) = N , fs′ , st , inj₁ G

    -- what a step owes: from a related state, in the machine's world (D426), where it lands
    Owes : ∀ {T} → Motive {Level.zero} {T}
    Owes {c = c} {r = r} {m = m} {n = n} {c′ = c′} {r′ = r′} {m′ = m′} {n′ = n′} st =
      ∀ {h fs} → InvI m r n h → Related c r m n fs → Agrees st fs → Lands c′ r′ m′ n′ fs

    -- the cases, by the step's kind
    private
      halt-out : ∀ {T sh U′} {r : Ret U′ T} {m : Cfg sh} {n fs}
           → Σ ℕ (λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × LocState.halted (floc fs′) ≡ Data.Bool.true)
           → Lands (halted {sh = sh}) r m n fs
      halt-out (N , fs′ , st , hlt) = N , fs′ , st , inj₂ hlt

    word-cases : ∀ {T} → CoveredCases {Level.zero} {T}
    word-cases = record
      { P   = Owes
      ; loc = λ st l inv G _ → lift (gstep-local st l inv G)
      ; cs₁ = λ inv G _ → lift (gcase₁ (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; cs₂ = λ inv G _ → lift (gcase₂ (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; lp  = λ inv G _ → lift (gloop (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; rti = λ inv G _ → lift (greti (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; cl  = λ inv G _ → lift (gcall (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; rt  = λ inv G _ → lift (gret (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; ic  = λ inv G _ → lift (gicall (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; op1 = λ inv G _ → lift (gopen1 (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; nop = λ inv G _ → lift (gnopen (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; iob = λ inv G _ → lift (giobs (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; cf  = λ inv G _ → lift (gcfree (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; nf  = λ inv G _ → lift (gnfree (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; fo  = λ inv G _ → lift (gfopen (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; foν = λ inv G _ → lift (gfopenν (g-pt G) inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; icω = λ eq inv G _ → lift (gicallω (g-pt G) eq inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; opω = λ eq inv G _ → lift (gopenω (g-pt G) eq inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; cc  = λ eq inv G _ → lift (gccopy (g-pt G) eq inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; nc  = λ eq inv G _ → lift (gncopy (g-pt G) eq inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; co  = λ eq inv G _ → lift (gcopen (g-pt G) eq inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; coν = λ eq inv G _ → lift (gcopenν (g-pt G) eq inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; rc  = λ eq inv G _ → lift (greclose (g-pt G) eq inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; rcν = λ eq inv G _ → lift (grecloseν (g-pt G) eq inv (g-here G) (g-next G) (g-ret G) (g-blk G))
      ; op  = λ run inv G ag → lift (gop (g-pt G) run inv (g-here G) (g-next G) (g-ret G) (g-blk G) ag)
      ; ope = λ p inv G ag → halt-out (gopend (g-pt G) (g-here G) ag)
      }

    -- ★ by the step's kind (the one split on a step is StepKinds')
    word-step : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
           (st : StepI c r m n t c′ r′ m′ n′) → CoveredC c → InvI m r n h → Related c r m n fs → Agrees st fs → Lands c′ r′ m′ n′ fs
    word-step st cv inv G ag = covered-elim word-cases st cv inv G ag
