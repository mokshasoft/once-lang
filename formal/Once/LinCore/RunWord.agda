-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.RunWord — plan 0.146 B1.5: A WHOLE IMAGE RUN, on the flat
-- machine. From a related state, every image run (`StepsI`) is matched by
-- flat steps that land related, or (the image halted) in a halted machine —
-- relative to the machine's world at each op step (D426: `AgreesAll`). From
-- the start (`Start.start-related`): the image's whole run from main's
-- first point, from the flat machine's first state.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; _+_)
open import Data.Maybe using (nothing)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.RunWord
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; mone)
open import Once.LinCore.Machine fmt ans bw using (Sh; Cfg; vw; []ᵉ; _∷ˢ_; []ˢ; _∥_)
open import Once.LinCore.Image fmt ans bw using (Codeᴵ; halted)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; StepI)
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; done; _⟫_; start)
open import Once.LinCore.HeldI fmt ans bw using (InvI; inv-stepI; start-invI)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.PointAt fmt ans bw using (module Ctl)
open import Once.LinCore.Global fmt ans bw using (module Relate)
open import Once.LinCore.WordStep fmt ans bw using (module StepR)
open import Once.LinCore.StepCov fmt ans bw using (step-covered)
open import Once.LinCore.StepOp fmt ans bw using (module Agree)
open import Once.LinCore.Start fmt ans bw using (module StartR)

module RunW {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
            (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
            (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
            (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf using (Related)
  open Ctl {FS} ds f ldConst ld-nl using (main)
  open Program ds f using (U)
  open Program′ ds f ldConst using (image)
  open Agree {FS} U wordOf using (Agrees)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open FlatStepsAPI {FS} using (FlatSteps; FlatSteps-++)
  open StepR {FS} ds f ldConst ld-nl wordOf using (module Theorem)

  -- the machine's world agrees at every step of a run, from any related state
  AgreesAll : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
            → StepsI c r m n t c′ r′ m′ n′ → Set
  AgreesAll done = ⊤
  AgreesAll (_⟫_ {c = c} {r = r} {m = m} {n = n} st rest) = (∀ fs → Related c r m n fs → Agrees st fs) × AgreesAll rest

  -- a run from a halted image has no step
  rest-halt : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
            → StepsI c r m n t c′ r′ m′ n′ → c ≡ halted → c′ ≡ halted
  rest-halt done e = e
  rest-halt (() ⟫ _) refl

  module _ (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                 → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                   ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = Data.Nat.suc (fpc fs) }) where
    open Theorem ld using (word-step; Lands; HaltC)

    -- ★ a whole run, from a related state
    whole : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs}
          → (run : StepsI c r m n t c′ r′ m′ n′) → InvI m r n h → AgreesAll run → Related c r m n fs
          → Lands c′ r′ m′ n′ fs
    whole done inv ag G = 0 , _ , FlatStepsAPI.[] , inj₁ G
    whole (st ⟫ rest) inv (a₁ , ag) G = go (word-step st (step-covered st) inv G (a₁ _ G))
      where
        go : _ → _
        go (N₁ , fs₁ , st₁ , inj₁ G₁) = case whole rest (proj₂ (inv-stepI st inv)) ag G₁ of λ where
          (N₂ , fs₂ , st₂ , L) → N₁ + N₂ , fs₂ , FlatSteps-++ st₁ st₂ , L
        go (N₁ , fs₁ , st₁ , inj₂ (e , hlt)) = N₁ , fs₁ , st₁ , inj₂ (rest-halt rest e , hlt)

    -- ★ the image's run from main's first point, from the flat machine's first state
    module _ (entry-frame : FrameSemantics.Frame FS) (entry-regs : Registers FS) where
      open StartR {FS} ds f ldConst ld-nl wordOf entry-frame entry-regs using (start-fs; start-related)

      from-start : ∀ {sh U′} {t} {c′ : Codeᴵ sh U′} {r′} {m′ n′}
                 → (run : StepsI main []ʳ start 0 t c′ r′ m′ n′) → AgreesAll run
                 → Lands c′ r′ m′ n′ start-fs
      from-start run ag = case start-related of λ where
        (fs₁ , st₁ , G₁) → case whole run start-invI ag G₁ of λ where
          (N , fs′ , st , L) → 1 + N , fs′ , FlatSteps-++ st₁ st , L
