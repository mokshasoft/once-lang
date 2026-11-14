-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.FlatTop — plan 0.146 B1.5 (D429): ★ THE FLAT THEOREM FOR THE
-- NEW IMAGE, IN THE SHAPE THE APEX CONSUMES (master's `FlatFromObs.flat-ends`).
--
-- Top-down: the statement first, composed from what is proved — the world's
-- run of the compiled program (`Total.exec` in the world the machine's
-- interpretation is, its state the log), the image on it (`ImageSim`), the
-- flat machine on the image (`End.ends`) — with every link still owed a
-- named field of `Owed`. The fields are the work list: each is discharged in
-- place, so every lemma below is reachable from this statement.
--
-- For a budget `k`: some fuel at which the flat run's events and its end are
-- the meaning's at that budget (master's `eventsAt`/`endAp` of `⟪ m ⟫ k`, from
-- the empty log). The meaning is the pass's (`Pass.ev`); master's `evalᴰ` is
-- one link above (`BridgeProof.bridge`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
import Data.Bool
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Function using (case_of_)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; fs-numerics; fs-ffi; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.IR.Semantics.Event using (SigOpEvent)
import Once.IR.Semantics.Trace as TM
open import Once.IR.Semantics.Out using (end-of-left)
open import Once.Spec.Trace using (End; returned)
import Once.Spec.Trace
open import Once.Denotation.Approx using (approx; endAp)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)

module Once.LinCore.FlatTop (Mach : FrameSemantics) (bw : Base → ℕ) where

private
  fmt = fs-numerics Mach
  ans = fs-ffi Mach
  ι   = FrameSemantics.fs-interp Mach

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; mone; Run; Trace; ios; Outcome; gives; stop)
import Once.LinCore.Events
open import Once.LinCore.Machine fmt ans bw using (Plain; _∣_)
open import Once.LinCore.Total fmt ans bw using (World; exec; module Ran)
open import Once.LinCore.Pass fmt ans using (Prog; IR; ⟦_⟧P; ev; trP; tr)
open import Once.LinCore.Image fmt ans bw using (Codeᴵ; halted)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ)
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; start; image-noleak)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.Lower fmt ans bw using (module Program′)
open import Once.LinCore.PointAt fmt ans bw using (module Ctl)
open import Once.LinCore.StepOp fmt ans bw using (evsOf; ioEvent)
open import Once.LinCore.RunWord fmt ans bw using (module RunW)
open import Once.LinCore.Start fmt ans bw using (module StartR)
open import Once.LinCore.End fmt ans bw using (module EndR; Final; f-end; f-halt)

-- ★ the world the machine's interpretation is: its state the log so far, its answer the
-- interpretation's given that history (D429)
Wι : World
Wι = record { WSt = List SigOpEvent
            ; answer = λ h o a → Data.Maybe.map (λ b → b , (h ++ TM.callEvent o a ∷ [])) (TM.callAnswer ι h o a) }

-- how a run's outcome is observed to end
endO : ∀ {B} → Outcome B → Maybe (End Data.Unit.⊤)
endO (gives _ _)                               = just (returned tt)
endO (stop Once.LinCore.Events.halted)         = just Once.Spec.Trace.halted
endO (stop Once.LinCore.Events.exhausted)      = nothing

module Top {Γ} (P : Prog Γ) (f : IR Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {Mach} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue Mach)
           (entry-frame : FrameSemantics.Frame Mach) (entry-regs : Registers Mach) where
  open FlatMachine {Mach} using (FlatState; floc; fpc)
  open FlatStepsAPI {Mach} using (FlatSteps)
  open FlatEventTrace {Mach} using (flat-events)

  ds = trP P
  f₀ = tr f
  open Program′ ds f₀ ldConst using (image)
  open Ctl {Mach} ds f₀ ldConst ld-nl using (main)
  open StartR {Mach} ds f₀ ldConst ld-nl wordOf entry-frame entry-regs using (start-fs)
  open RunW {Mach} ds f₀ ldConst ld-nl wordOf using (AgreesAll)

  -- the meaning, and what it shows at a budget from the empty log
  obs : ℕ → TM.Run (Once.Denotation.Approx.Ap Data.Unit.⊤)
  obs k = TM.run ι [] (approx k (ev ⟦ P ⟧P f tt))

  -- the compiled program's run in the world, at a fuel
  R : ℕ → _
  R K = exec Wι ds K f₀ mone mone 0 []

  module _ (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                 → FlatMachine.flat-exec-instr {Mach} (ldConst v) image fs
                   ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (fpc fs) }) where
    open EndR {Mach} ds f₀ ldConst ld-nl wordOf using (ends)

    -- ★ WHAT IS OWED: the links from the meaning to the flat run not yet proved
    record Owed : Set where
      field
        -- the world's run at a fuel shows the meaning's observation at the budget
        o-run   : ∀ k → Σ ℕ λ K → (evsOf (Ran.trace (R K)) ≡ proj₁ (obs k))
                                  × (endO (Ran.out (R K)) ≡ endAp (proj₂ (obs k)))
        -- the runs the world allows are the lowering's (every fold plain)
        o-plain : ∀ K → Plain (Ran.run (R K))
        -- the machine agrees with an image run that shows the world's run
        o-agree : ∀ K {mt sh U′} {c′ : Codeᴵ sh U′} {r′ : Ret U′ (One ∷ [] ∣ One ∷ [])} {m′ n′}
                  (st : StepsI main []ʳ start 0 mt c′ r′ m′ n′) → ios mt ≡ ios (Ran.trace (R K)) → AgreesAll [] st
        -- a halting run: the image reaches `halted`, showing what the run shows
        o-halt  : ∀ {t} (run : Run ds f₀ mone mone 0 (stop Once.LinCore.Events.halted) t) → Plain run
                → Σ Trace λ mt → Σ _ λ sh → Σ _ λ U′ → Σ (Ret U′ (One ∷ [] ∣ One ∷ [])) λ r′ → Σ _ λ m′ → Σ ℕ λ n′
                    → StepsI main []ʳ start 0 mt (halted {sh} {U′}) r′ m′ n′ × ios mt ≡ ios t
        -- the machine: a running state the start reaches has not left (only `c-leave` leaves, and it halts)
        o-running : ∀ {M fs₀} → FlatSteps image M start-fs fs₀ → LocState.halted (floc fs₀) ≡ Data.Bool.false
                  → LocState.left (floc fs₀) ≡ Data.Bool.false
        -- a cut run: the flat run, at some fuel, shows its events and is cut
        o-cut   : ∀ (K : ℕ) {t} (run : Run ds f₀ mone mone 0 (stop Once.LinCore.Events.exhausted) t) → Plain run
                → Σ ℕ λ N → flat-events N image start-fs ≡ (evsOf t , nothing)
        -- the machine: flat steps from the start to a halted machine are its events and its end
        o-flat  : ∀ {N fs′} → FlatSteps image N start-fs fs′ → LocState.halted (floc fs′) ≡ Data.Bool.true
                → flat-events (suc N) image start-fs ≡ (LocState.ev-log (floc fs′) , just (end-of-left (LocState.left (floc fs′))))

    -- ★★ THE FLAT THEOREM, relative to what is owed
    flat-top : Owed → ∀ k → Σ ℕ λ N → flat-events N image start-fs ≡ (proj₁ (obs k) , endAp (proj₂ (obs k)))
    flat-top O k = by (Ran.run (R K)) (Owed.o-plain O K) (λ st e → Owed.o-agree O K st e) eE eO
      where
        K  = proj₁ (Owed.o-run O k)
        eE = proj₁ (proj₂ (Owed.o-run O k))
        eO = proj₂ (proj₂ (Owed.o-run O k))
        by : ∀ {o t} (run : Run ds f₀ mone mone 0 o t) → Plain run
           → (∀ {mt sh U′} {c′ : Codeᴵ sh U′} {r′ : Ret U′ (One ∷ [] ∣ One ∷ [])} {m′ n′}
                (st : StepsI main []ʳ start 0 mt c′ r′ m′ n′) → ios mt ≡ ios t → AgreesAll [] st)
           → evsOf t ≡ proj₁ (obs k) → endO o ≡ endAp (proj₂ (obs k))
           → Σ ℕ λ N → flat-events N image start-fs ≡ (proj₁ (obs k) , endAp (proj₂ (obs k)))
        by {gives mone n′} {t} run pl ag ee eo = case image-noleak run pl of λ where
          (mt , st , _ , _ , _ , eio) → case ends ld entry-frame entry-regs st (ag st eio) f-end of λ where
            (N , fs′ , fst , hlt , lg , lft) →
              suc N , trans (Owed.o-flat O fst hlt)
                            (cong₂ _,_ (trans lg (trans (cong (map ioEvent) eio) ee))
                                       (trans (cong (λ b → just (end-of-left b)) lft) eo))
        by {stop Once.LinCore.Events.halted} {t} run pl ag ee eo = case Owed.o-halt O run pl of λ where
          (mt , sh , U′ , r′ , m′ , n′ , st , eio) → case ends ld entry-frame entry-regs st (ag st eio) f-halt of λ where
            (N , fs′ , fst , hlt , lg , (fs₀ , M , st₀ , r₀ , l₀)) →
              suc N , trans (Owed.o-flat O fst hlt)
                            (cong₂ _,_ (trans lg (trans (cong (map ioEvent) eio) ee))
                                       (trans (cong (λ b → just (end-of-left b)) (trans l₀ (Owed.o-running O st₀ r₀))) eo))
        by {stop Once.LinCore.Events.exhausted} {t} run pl ag ee eo = case Owed.o-cut O K run pl of λ where
          (N , e) → N , trans e (cong₂ _,_ ee eo)
