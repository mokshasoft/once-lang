-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.End — plan 0.146 B1.5: THE RUN'S END, on the flat machine.
-- An image run from main's first point ends at main's `end` with nothing
-- to return to, or `halted` (a halting op). At main's `end` the flat pc is
-- at the start's way out (`c-leave`): one step, and the machine has halted
-- and left, its log kept. A related state is never at `halted` (no root's
-- code holds it: `NoCell`). So the whole run: from the flat machine's first
-- state, flat steps to a halted machine whose log is the run's observable
-- events (D427), relative to the machine's world at each op (D426).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool using (true)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.End
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Machine fmt ans bw using (Sh; Cfg; _∣_)
open import Once.LinCore.Image fmt ans bw using (Codeᴵ; end; halted)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ)
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; start)
open import Once.LinCore.ImagePt fmt ans bw using (at)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.Keys fmt ans bw using (module Program)
open import Once.LinCore.Lower fmt ans bw using (module Program′)
open import Once.LinCore.PointAt fmt ans bw using (module Ctl)
open import Once.LinCore.Global fmt ans bw using (module Relate)
open import Once.LinCore.NoCell fmt ans bw using (sub-nc; comp-nc; block-nc; allK-nt)
open import Once.LinCore.StepOp fmt ans bw using (evsOf)
open import Once.LinCore.RunWord fmt ans bw using (module RunW)
open import Once.LinCore.WordStep fmt ans bw using (module StepR)
open import Once.LinCore.Start fmt ans bw using (module StartR)

-- where a whole image run ends: main's `end` with nothing to return to, or `halted`
data Final {T : Sh} : ∀ {sh U′} → Codeᴵ sh U′ → Ret U′ T → Set where
  f-end  : Final (end {sh = T}) []ʳ
  f-halt : ∀ {sh U′} {r : Ret U′ T} → Final (halted {sh} {U′}) r

module EndR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
            (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
            (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
            (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Relate {FS} ds f ldConst ld-nl wordOf using (Related; HereP; RetOK; ok-top; rootOf; module Related; module S)
  open Ctl {FS} ds f ldConst ld-nl using (main; Pnt; p-start; p-block; p-tramp; p-halt; ptFin)
  open Program′ ds f ldConst using (image)
  open FlatMachine {FS} using (FlatState; floc; falloc; fret; fpc)
  open FlatStepsAPI {FS} using (FlatSteps; FlatSteps-++)
  open import Once.LinCore.Moves {FS} using (Seg)

  -- the machine halted and left, its log kept
  Left : FlatState → FlatState → Set
  Left fs fs′ = LocState.halted (floc fs′) ≡ true × LocState.left (floc fs′) ≡ true
                × LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)

  private
    leave : ∀ {fs} → Seg image (fpc fs) (instr-ctrl c-leave ∷ []) → LocState.halted (floc fs) ≡ Data.Bool.false
          → Σ FlatState λ fs′ → FlatSteps image 1 fs fs′ × Left fs fs′
    leave {fs} (g , _) h =
      record fs { floc = record (floc fs) { halted = true ; left = true } } ,
      FlatStepsAPI.step-at {FS} _ (h , g) refl FlatStepsAPI.[] , refl , refl , refl

  -- ★ main's `end`, nothing to return to: the start's way out
  g-end : ∀ {T} {m : Cfg T} {n fs} → Related (end {sh = T}) ([]ʳ {T = T}) m n fs
        → Σ FlatState λ fs′ → FlatSteps image 1 fs fs′ × Left fs fs′
  g-end {T} {m} {n} {fs} G = go (Related.g-pt G) (Related.g-here G) (Related.g-ret G)
    where
      go : (P : Pnt (end {sh = T})) → HereP P m fs
         → RetOK (rootOf P) (ptFin P) ([]ʳ {T = T}) (AllocState.current-frame (falloc fs)) (fret fs) (AllocState.saved-frames (falloc fs)) fs
         → Σ FlatState λ fs′ → FlatSteps image 1 fs fs′ × Left fs fs′
      go (p-start (at s)) H (ok-top _ eF) = leave (subst (Seg image (fpc fs)) eF (S.seg-at s H)) (S.Here.h-run H)
      go (p-block p (at s)) H (ok-top () _)
      go (p-tramp p pt) H (ok-top () _)

  -- ★ no related state is at `halted`
  no-halted : ∀ {T sh U′} {r : Ret U′ T} {m : Cfg sh} {n fs} → Related (halted {sh} {U′}) r m n fs → ⊥
  no-halted {sh = sh} {U′} {m = m} {fs = fs} G = go (Related.g-pt G) (Related.g-here G)
    where
      go : (P : Pnt (halted {sh} {U′})) → HereP P m fs → ⊥
      go (p-start (at s)) _ = sub-nc s (comp-nc ds f tt)
      go (p-block p (at s)) _ = sub-nc s (block-nc _ (allK-nt ds f p))
      go (p-tramp p pt) (() , _)
      go p-halt ()

  -- ★★ THE WHOLE RUN: from the flat machine's first state to a halted machine whose log is the run's
  -- observable events, relative to the machine's world at each op (D426)
  module _ (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                 → FlatMachine.flat-exec-instr {FS} (ldConst v) image fs
                   ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = Data.Nat.suc (fpc fs) })
           (entry-frame : FrameSemantics.Frame FS) (entry-regs : Registers FS) where
    open RunW {FS} ds f ldConst ld-nl wordOf using (AgreesAll; from-start)
    open StepR {FS} ds f ldConst ld-nl wordOf using (module Theorem)
    open Theorem ld using (Lands)
    open StartR {FS} ds f ldConst ld-nl wordOf entry-frame entry-regs using (start-fs)

    ends : ∀ {sh U′ t} {c′ : Codeᴵ sh U′} {r′ : Ret U′ (One ∷ [] ∣ One ∷ [])} {m′ n′}
         → (run : StepsI main []ʳ start 0 t c′ r′ m′ n′) → AgreesAll run → Final c′ r′
         → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N start-fs fs′
             × LocState.halted (floc fs′) ≡ true × LocState.ev-log (floc fs′) ≡ evsOf t
    ends {t = t} {c′ = c′} {r′} {m′} {n′} run ag fin = fin-case fin (from-start ld entry-frame entry-regs run ag)
      where
        fin-case : Final c′ r′ → Lands (evsOf t) c′ r′ m′ n′ start-fs
                 → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N start-fs fs′
                     × LocState.halted (floc fs′) ≡ true × LocState.ev-log (floc fs′) ≡ evsOf t
        fin-case f-end (N , fs₁ , st₁ , inj₁ G , lg) = case g-end G of λ where
          (fs′ , st₂ , hlt , _ , lg₂) → N + 1 , fs′ , FlatSteps-++ st₁ st₂ , hlt , trans lg₂ lg
        fin-case f-end (_ , _ , _ , inj₂ (() , _) , _)
        fin-case f-halt (_ , _ , _ , inj₁ G , _) = ⊥-elim (no-halted G)
        fin-case f-halt (N , fs₁ , st₁ , inj₂ (_ , hlt) , lg) = N , fs₁ , st₁ , hlt , lg
