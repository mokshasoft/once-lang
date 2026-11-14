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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.List using (List; []; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Once.IR.Semantics.Event using (SigOpEvent)
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
open import Once.LinCore.Events fmt ans bw using (MV; mone; Trace; ios; ios-++)
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
open import Once.LinCore.StepOp fmt ans bw using (module Agree; evsOf; ioEvent)
open import Once.LinCore.Start fmt ans bw using (module StartR)

-- the events a trace shows the log: a homomorphism of free monoids
evsOf-++ : ∀ t₁ t₂ → evsOf (t₁ ++ t₂) ≡ evsOf t₁ ++ evsOf t₂
evsOf-++ t₁ t₂ = trans (cong (map ioEvent) (ios-++ t₁ t₂)) (map-++ ioEvent (ios t₁) (ios t₂))

-- the log over two runs, one after the other
log-join : ∀ {a b c : List SigOpEvent} t₁ t₂ → b ≡ a ++ evsOf t₁ → c ≡ b ++ evsOf t₂ → c ≡ a ++ evsOf (t₁ ++ t₂)
log-join {a} t₁ t₂ e₁ e₂ =
  trans e₂ (trans (cong (_++ evsOf t₂) e₁) (trans (++-assoc a (evsOf t₁) (evsOf t₂)) (cong (a ++_) (sym (evsOf-++ t₁ t₂)))))

-- the log over a run whose rest shows nothing
log-halt : ∀ {a b : List SigOpEvent} t₁ {t₂ : Trace} → b ≡ a ++ evsOf t₁ → t₂ ≡ [] → b ≡ a ++ evsOf (t₁ ++ t₂)
log-halt {a} t₁ e refl = trans e (cong (λ z → a ++ evsOf z) (sym (++-identityʳ t₁)))

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

  -- the machine's world agrees at every step of a run, from a related state whose log is the
  -- run's events so far (D429: an answer depends on the history)
  AgreesAll : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
            → List SigOpEvent → StepsI c r m n t c′ r′ m′ n′ → Set
  AgreesAll L done = ⊤
  AgreesAll L (_⟫_ {c = c} {r = r} {m = m} {n = n} {t₁ = t₁} st rest) =
    (∀ fs → Related c r m n fs → LocState.ev-log (floc fs) ≡ L → Agrees st fs) × AgreesAll (L ++ evsOf t₁) rest

  -- a run from a halted image has no step
  rest-halt : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
            → StepsI c r m n t c′ r′ m′ n′ → c ≡ halted → (c′ ≡ halted) × (t ≡ [])
  rest-halt done e = e , refl
  rest-halt (() ⟫ _) refl

  module _ (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                 → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                   ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = Data.Nat.suc (fpc fs) }) where
    open Theorem ld using (word-step; Lands; HaltC)

    -- ★ a whole run, from a related state
    whole : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′ h fs L}
          → (run : StepsI c r m n t c′ r′ m′ n′) → InvI m r n h → AgreesAll L run → Related c r m n fs
          → LocState.ev-log (floc fs) ≡ L
          → Lands (evsOf t) c′ r′ m′ n′ fs
    whole {fs = fs} done inv ag G _ = 0 , _ , FlatStepsAPI.[] , inj₁ G , sym (++-identityʳ (LocState.ev-log (floc fs)))
    whole (_⟫_ {t₁ = t₁} {t₂ = t₂} st rest) inv (a₁ , ag) G lL = go (word-step st (step-covered st) inv G (a₁ _ G lL))
      where
        go : _ → _
        go (N₁ , fs₁ , st₁ , inj₁ G₁ , lg₁) = case whole rest (proj₂ (inv-stepI st inv)) ag G₁ (trans lg₁ (cong (_++ evsOf t₁) lL)) of λ where
          (N₂ , fs₂ , st₂ , L , lg₂) → N₁ + N₂ , fs₂ , FlatSteps-++ st₁ st₂ , L , log-join t₁ t₂ lg₁ lg₂
        go (N₁ , fs₁ , st₁ , inj₂ (e , hlt) , lg₁) =
          N₁ , fs₁ , st₁ , inj₂ (proj₁ (rest-halt rest e) , hlt) , log-halt t₁ lg₁ (proj₂ (rest-halt rest e))

    -- ★ the image's run from main's first point, from the flat machine's first state
    module _ (entry-frame : FrameSemantics.Frame FS) (entry-regs : Registers FS) where
      open StartR {FS} ds f ldConst ld-nl wordOf entry-frame entry-regs using (start-fs; start-related)

      from-start : ∀ {sh U′} {t} {c′ : Codeᴵ sh U′} {r′} {m′ n′}
                 → (run : StepsI main []ʳ start 0 t c′ r′ m′ n′) → AgreesAll [] run
                 → Lands (evsOf t) c′ r′ m′ n′ start-fs
      from-start {t = t} run ag = case start-related of λ where
        (fs₁ , st₁ , G₁ , lg₀) → case whole run start-invI ag G₁ lg₀ of λ where
          (N , fs′ , st , L , lg) → 1 + N , fs′ , FlatSteps-++ st₁ st , L , trans lg (cong (_++ evsOf t) lg₀)
