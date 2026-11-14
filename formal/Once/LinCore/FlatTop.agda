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

open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Empty using (⊥; ⊥-elim)
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
open import Once.IR.Semantics.Out using (end-of-left; _▹_)
open import Data.Nat.Properties using (+-comm)
open import Data.List.Properties using (++-identityʳ)
open import Once.Spec.Trace using (End; returned)
import Once.Spec.Trace
open import Once.Denotation.Approx using (approx; endAp)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
import Once.IR
import Once.IRTy
open import Once.Denotation.Program using (IRFun; tableEnv; tableCalls)
import Once.LinCore.BridgeProof
import Once.Denotation.DenotTrace as DT

module Once.LinCore.FlatTop (Mach : FrameSemantics) (bw : Base → ℕ) where

private
  fmt = fs-numerics Mach
  ans = fs-ffi Mach
  ι   = FrameSemantics.fs-interp Mach

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; mone; Run; Trace; ios; Outcome; gives; stop)
import Once.LinCore.Events
open import Once.LinCore.Machine fmt ans bw using (Plain; _∣_)
open import Once.LinCore.Total fmt ans bw using (World; exec; Ran; module Ran)
open import Once.LinCore.Pass fmt ans using (Prog; IR; ⟦_⟧P; ev; trP; tr; pass-okᶠ; pass-okP)
import Once.LinCore.BudgetSound
open import Once.LinCore.Spends fmt ans bw using (spends-plain; UnCut)
module BudgetSound = Once.LinCore.BudgetSound fmt ans bw
open import Once.LinCore.Image fmt ans bw using (Codeᴵ; halted)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ)
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; start; image-noleak; image-halts)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.Lower fmt ans bw using (module Program′)
open import Once.LinCore.PointAt fmt ans bw using (module Ctl)
open import Once.LinCore.StepOp fmt ans bw using (evsOf; ioEvent)
open import Once.LinCore.RunWord fmt ans bw using (module RunW)
open import Once.LinCore.Start fmt ans bw using (module StartR)
open import Once.LinCore.End fmt ans bw using (module EndR; Final; f-end; f-halt)
import Once.LinCore.FromIR
import Once.LinCore.Pass
module BP = Once.LinCore.BridgeProof fmt ans
open import Once.LinCore.Casts fmt ans using (casts)
open import Once.LinCore.Table fmt ans using (env-ok)
open import Once.LinCore.RunBisim fmt ans using (run-≈)
module FromIR = Once.LinCore.FromIR fmt ans

-- ★ the world the machine's interpretation is: its state the log so far, its answer the
-- interpretation's given that history (D429)
Wι : World
Wι = BudgetSound.W.Wι ι

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
  image = Program′.image ds f₀ ldConst
  open Ctl {Mach} ds f₀ ldConst ld-nl using (main)
  start-fs = StartR.start-fs {Mach} ds f₀ ldConst ld-nl wordOf entry-frame entry-regs
  open RunW {Mach} ds f₀ ldConst ld-nl wordOf using (AgreesAll)

  -- the meaning, and what it shows at a budget from the empty log
  obs : ℕ → TM.Run (Once.Denotation.Approx.Ap Data.Unit.⊤)
  obs k = TM.run ι [] (approx k (ev ⟦ P ⟧P f tt))

  -- the compiled program's run in the world, at a budget (D430)
  R : (K : ℕ) → Ran Wι ds f₀ mone mone 0 K []
  R K = exec Wι ds K f₀ mone mone 0 []

  module _ (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatState)
                 → FlatMachine.flat-exec-instr {Mach} (ldConst v) image fs
                   ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf v) } ; fpc = suc (fpc fs) }) where
    open EndR {Mach} ds f₀ ldConst ld-nl wordOf using (ends)
    open FlatEventTrace {Mach} using (flat-ctrls; flat-events-steps; flat-events-step; chain-events; chain-log; chain-left)
    open FlatStepsAPI {Mach} using (Sound)

    private
      just≢nothing : ∀ {A : Set} {a : A} → just a ≡ nothing → ⊥
      just≢nothing ()

    -- ★ WHAT IS OWED: the links from the meaning to the flat run not yet proved
    record Owed : Set where
      field
        -- the world's run meets no call the interpretation leaves unanswered (the program is linked)
        o-uncut : ∀ k → UnCut (Ran.run (R k))
        -- the machine agrees with an image run that shows the world's run
        o-agree : ∀ K {mt sh U′} {c′ : Codeᴵ sh U′} {r′ : Ret U′ (One ∷ [] ∣ One ∷ [])} {m′ n′}
                  (st : StepsI main []ʳ start 0 mt c′ r′ m′ n′) → ios mt ≡ ios (Ran.trace (R K)) → AgreesAll [] st
        -- the world's run cut at the budget: the flat run, at some fuel, shows its events, is cut, and has
        -- taken a control step per unit of the budget (master's `flat-cut`)
        o-cut   : ∀ k → Ran.out (R k) ≡ stop Once.LinCore.Events.exhausted
                → Σ ℕ λ N → flat-events N image start-fs ≡ (evsOf (Ran.trace (R k)) , nothing)
                            × k ≤ flat-ctrls N image start-fs
        -- the machine's run from the start never faults (master's `start-sound`)
        o-sound : Sound image start-fs

    -- ★ THE MACHINE: a running state the start reaches has not left (only `c-leave` leaves, and it
    -- halts: master's `chain-left`)
    o-running : ∀ {M fs₀} → FlatSteps image M start-fs fs₀ → LocState.halted (floc fs₀) ≡ Data.Bool.false
              → LocState.left (floc fs₀) ≡ Data.Bool.false
    o-running st₀ r₀ = cong proj₁ (chain-left st₀ r₀)

    -- ★ THE MACHINE: flat steps from the start to a halted machine are its log and its end
    -- (master's `flat-events-steps`, `chain-log`; the start's log empty)
    o-flat : ∀ {N fs′} → FlatSteps image N start-fs fs′ → LocState.halted (floc fs′) ≡ Data.Bool.true
           → flat-events (suc N) image start-fs ≡ (LocState.ev-log (floc fs′) , just (end-of-left (LocState.left (floc fs′))))
    o-flat {N} {fs′} st hlt =
      trans (cong (λ z → flat-events z image start-fs) (+-comm 1 N))
        (trans (flat-events-steps st 1)
          (trans (cong (λ b → chain-events st ▹ flat-events-step b 0 image fs′) hlt)
            (cong (λ z → (z , just (end-of-left (LocState.left (floc fs′))))) (trans (++-identityʳ (chain-events st)) (sym (chain-log st))))))

    -- how an outcome's observation ends
    private
      end-out : ∀ {B} (o : Outcome B) l → endO o ≡ endAp (BudgetSound.W.outAp ι o l)
      end-out (gives _ _)                          l = refl
      end-out (stop Once.LinCore.Events.halted)    l = refl
      end-out (stop Once.LinCore.Events.exhausted) l = refl

    -- ★ THE WORLD'S RUN SHOWS THE MEANING at its budget (D429, D430): the budgeted soundness on the
    -- evaluator's own run (`BudgetSound.soundₖ`: its spends and the world's answers), the core's meaning
    -- the pass's (`Pass.pass-okᶠ`, bisimilar computations run alike)
    run-shows : Owed → ∀ k → (evsOf (Ran.trace (R k)) ≡ proj₁ (obs k)) × (endO (Ran.out (R k)) ≡ endAp (proj₂ (obs k)))
    run-shows O k = sym (cong proj₁ eq) , trans (end-out (Ran.out (R k)) (Ran.left (R k))) (sym (cong (λ r → endAp (proj₂ r)) eq))
      where
        eq : obs k ≡ (evsOf (Ran.trace (R k)) , BudgetSound.W.outAp ι (Ran.out (R k)) (Ran.left (R k)))
        eq = trans (sym (BudgetSound.W.run-≈ ι k (pass-okᶠ (pass-okP P) funit funit f tt) []))
                   (proj₁ (BudgetSound.S.soundₖ ι (Ran.run (R k)) (Ran.spends (R k)) (Owed.o-uncut O k) (Ran.world (R k))))

    -- ★★ THE FLAT THEOREM, relative to what is owed: at some fuel the flat run shows the meaning's
    -- events and end at the budget, and, where the budget cut it, a control step per unit
    -- (master's `flat-ends` and `flat-cut`, at one fuel)
    Shows : ℕ → ℕ → Set
    Shows k N = (flat-events N image start-fs ≡ (proj₁ (obs k) , endAp (proj₂ (obs k))))
                × (endAp (proj₂ (obs k)) ≡ nothing → k ≤ flat-ctrls N image start-fs)

    flat-top : Owed → ∀ k → Σ ℕ (Shows k)
    flat-top O k = by (Ran.run (R K)) refl (spends-plain (Ran.run (R K)) (Ran.spends (R K)) (Owed.o-uncut O K)) (λ st e → Owed.o-agree O K st e) eE eO
      where
        K  = k
        eE = proj₁ (run-shows O k)
        eO = proj₂ (run-shows O k)
        by : ∀ {o t} (run : Run ds f₀ mone mone 0 o t) → Ran.out (R K) ≡ o → Plain run
           → (∀ {mt sh U′} {c′ : Codeᴵ sh U′} {r′ : Ret U′ (One ∷ [] ∣ One ∷ [])} {m′ n′}
                (st : StepsI main []ʳ start 0 mt c′ r′ m′ n′) → ios mt ≡ ios t → AgreesAll [] st)
           → evsOf t ≡ proj₁ (obs k) → endO o ≡ endAp (proj₂ (obs k))
           → Σ ℕ (Shows k)
        by {gives mone n′} {t} run _ pl ag ee eo = case image-noleak run pl of λ where
          (mt , st , _ , _ , _ , eio) → case ends ld entry-frame entry-regs st (ag st eio) f-end of λ where
            (N , fs′ , fst , hlt , lg , lft) →
              suc N , trans (o-flat fst hlt)
                            (cong₂ _,_ (trans lg (trans (cong (map ioEvent) eio) ee))
                                       (trans (cong (λ b → just (end-of-left b)) lft) eo)) ,
              λ e → ⊥-elim (just≢nothing (trans eo e))
        by {stop Once.LinCore.Events.halted} {t} run _ pl ag ee eo = case image-halts run pl of λ where
          (mt , sh , U′ , r′ , m′ , n′ , st , eio) → case ends ld entry-frame entry-regs st (ag st eio) f-halt of λ where
            (N , fs′ , fst , hlt , lg , (fs₀ , M , st₀ , r₀ , l₀)) →
              suc N , trans (o-flat fst hlt)
                            (cong₂ _,_ (trans lg (trans (cong (map ioEvent) eio) ee))
                                       (trans (cong (λ b → just (end-of-left b)) (trans l₀ (o-running st₀ r₀))) eo)) ,
              λ e → ⊥-elim (just≢nothing (trans eo e))
        by {stop Once.LinCore.Events.exhausted} {t} run eq pl ag ee eo = case Owed.o-cut O k eq of λ where
          (N , e , c) → N , trans e (cong₂ _,_ eE (trans (sym (cong endO eq)) eO)) , λ _ → c

------------------------------------------------------------------------
-- ★ ONE LINK UP: master's IR program and its meaning (`evalᴰ` at the table's
-- environment, as the apex states it). The program translates (`FromIR`);
-- the pass's meaning and master's show the same at every budget (owed:
-- `BridgeProof.bridge`, its casts and the table's `EnvOK`).
------------------------------------------------------------------------

module IRTop (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
             (tp : FromIR.TrProg) (etp : FromIR.trTable tbl ≡ just tp)
             (f : IR (FromIR.TrProg.Γ tp) One One) (ef : FromIR.trI (FromIR.TrProg.rs tp) ir ≡ just f)
             (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
             (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {Mach} (ldConst v) ≡ nothing)
             (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue Mach)
             (entry-frame : FrameSemantics.Frame Mach) (entry-regs : Registers Mach) where
  module TP = Top (FromIR.TrProg.prog tp) f ldConst ld-nl wordOf entry-frame entry-regs

  -- master's meaning, and what it shows at a budget from the empty log
  obsᴰ : ℕ → TM.Run (Once.Denotation.Approx.Ap Data.Unit.⊤)
  obsᴰ k = TM.run ι [] (approx k (DT.evalᴰ fmt (tableEnv fmt ans tbl) ir tt))

  module _ (ld : ∀ {b} (v : ⟦ b ⟧b) (fs : FlatMachine.FlatState {Mach})
                 → FlatMachine.flat-exec-instr {Mach} (ldConst v) TP.image fs
                   ≡ record fs { floc = record (FlatMachine.floc fs) { regs = writeReg (LocState.regs (FlatMachine.floc fs)) Output (wordOf v) }
                               ; fpc = suc (FlatMachine.fpc fs) }) where
    open FlatEventTrace {Mach} using (flat-events; flat-ctrls)
    open FlatMachine {Mach} using (FlatState)

    -- the translation means what master's program means, at every budget (B1.3's bridge, its
    -- casts and the table's `EnvOK`; bisimilar computations show the same: `RunBisim`)
    o-bridge : ∀ k → TP.obs k ≡ obsᴰ k
    o-bridge k = run-≈ ι k (BP.bridge (Once.LinCore.Pass.⟦_⟧P fmt ans (FromIR.TrProg.prog tp)) (tableCalls fmt ans tbl)
                                     (casts (Once.LinCore.Pass.⟦_⟧P fmt ans (FromIR.TrProg.prog tp)) (tableCalls fmt ans tbl))
                                     (env-ok tbl etp) (FromIR.trI-Tr (FromIR.TrProg.rs tp) ir ef) tt) []

    record OwedIR : Set where
      field
        o-top    : TP.Owed ld

    -- ★★ THE FLAT THEOREM AT MASTER'S MEANING (master's `flat-ends` and `flat-cut`)
    flat-ir : OwedIR → ∀ k → Σ ℕ λ N → (flat-events N TP.image TP.start-fs ≡ (proj₁ (obsᴰ k) , endAp (proj₂ (obsᴰ k))))
                                     × (endAp (proj₂ (obsᴰ k)) ≡ nothing → k ≤ flat-ctrls N TP.image TP.start-fs)
    flat-ir O k = case TP.flat-top ld (OwedIR.o-top O) k of λ where
      (N , e , c) → N , trans e (cong (λ r → (proj₁ r , endAp (proj₂ r))) (o-bridge k))
                      , λ z → c (trans (cong (λ r → endAp (proj₂ r)) (o-bridge k)) z)

    flat-sound : OwedIR → FlatStepsAPI.Sound {Mach} TP.image TP.start-fs
    flat-sound O = TP.Owed.o-sound (OwedIR.o-top O)
