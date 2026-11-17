-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.FlatTop — plan 0.146 B1.5 (D443): ★ THE FLAT THEOREM FOR THE
-- NEW IMAGE, IN THE SHAPE THE APEX CONSUMES (master's `FlatFromObs.flat-ends`).
--
-- Top-down: the statement first, composed from what is proved — the world's
-- run of the compiled program (`Total.exec` in the world the machine's
-- interpretation is, its state the log), the image on it (`ImageSim`), the
-- flat machine on the image (`End.ends`). Every link was first owed as a named
-- field and discharged in place, so every lemma below is reachable from this
-- statement; none is owed now (D446 discharged the last, structured answers).
--
-- For a budget `k`: some fuel at which the flat run's events and its end are
-- the meaning's at that budget (master's `eventsAt`/`endAp` of `⟪ m ⟫ k`, from
-- the empty log). The meaning is the pass's (`Pass.ev`); master's `evalᴰ` is
-- one link above (`BridgeProof.bridge`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _≤_; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
import Data.Bool
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Maybe.Properties
import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Function using (case_of_)
open import Once.LinCore.Flat using (Base)
open import Once.Type using (fits-int; fits-float)
open import Once.CCC.FrameSemantics using (FrameSemantics; fs-numerics; fs-ffi; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.IR.Semantics.Event using (SigOpEvent)
import Once.IR.Semantics.Trace as TM
open import Once.IR.Semantics.Out using (end-of-left; _▹_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; ≤-trans; m≤m+n)
open import Data.List.Properties using (++-identityʳ)
open import Once.Spec.Trace using (End; returned)
import Once.Spec.Trace
open import Once.Denotation.Approx using (approx; endAp)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
import Once.IR
import Once.IRTy
open import Once.Denotation.Program using (IRFun; tableEnv; tableCalls; LinkedProgram; irProgram)
import Once.LinCore.LinkedCore
import Once.LinCore.RunOps
import Once.LinCore.BridgeProof
import Once.Denotation.DenotTrace as DT

module Once.LinCore.FlatTop (Mach : FrameSemantics) (bw : Base → ℕ) where

private
  fmt = fs-numerics Mach
  ans = fs-ffi Mach
  ι   = FrameSemantics.fs-interp Mach

open import Once.LinCore.Core fmt
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (Run; ios; Outcome; gives; stop; OpPath; er)
open import Once.LinCore.Values fmt bw using (MV; mone; Trace; mvF)
import Once.LinCore.Events
open import Once.LinCore.Machine fmt ans bw using (Plain)
open import Once.LinCore.Code fmt bw using (_∣_; Sh; Cfg)
open import Once.LinCore.Total fmt ans bw using (World; exec; Ran; module Ran)
open import Once.LinCore.Pass fmt ans using (⟦_⟧P; ev; pass-okᶠ; pass-okP)
open import Once.LinCore.PassTr fmt using (Prog; IR; trP; tr)
import Once.LinCore.BudgetSound
import Once.LinCore.AgreeRun
import Once.LinCore.OpMachine
module AgreeRun = Once.LinCore.AgreeRun fmt ans bw
open import Once.LinCore.Total fmt ans bw using (WTr)
open import Once.LinCore.StepOp fmt ans bw using (module Agree)
open import Once.LinCore.Keys fmt bw using (module Program; ops; ps; defsGot)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Denotation.Program using (Declared-at)
open import Once.SigOp.Info using (module SigOpInfo)
open import Once.LinCore.Spends fmt ans bw using (module Budget; UnCut; CutsIn; rounds)
open import Once.LinCore.Total fmt ans bw using (CutOp)
module BudgetSound = Once.LinCore.BudgetSound fmt ans bw
open import Once.LinCore.Image fmt bw using (Codeᴵ; halted)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ)
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; start; image-noleak; image-halts; image-cut; loops)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.Lower fmt bw using (module Program′)
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
module FromIR = Once.LinCore.FromIR fmt
module LinkedCore = Once.LinCore.LinkedCore fmt ans bw
module RunOps = Once.LinCore.RunOps fmt ans bw

-- ★ the world the machine's interpretation is: its state the log so far, its answer the
-- interpretation's given that history (D443)
Wι : World
Wι = BudgetSound.W.Wι ι

open Budget (λ {s} {x} {t} p → CutOp Wι {s} {x} {t} p) using (spends-plain; spends-uncut; spent-rounds; cut-zero; Exh)

-- how a run's outcome is observed to end
endO : ∀ {B} → Outcome B → Maybe (End Data.Unit.⊤)
endO (gives _ _)                               = just (returned tt)
endO (stop Once.LinCore.Events.halted)         = just Once.Spec.Trace.halted
endO (stop Once.LinCore.Events.exhausted)      = nothing

module Top {Γ} (ds : Defs Γ) (f₀ : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {Mach} (ldConst v) ≡ nothing)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue Mach)
           (w-int   : ∀ (n : ⟦ int ⟧b)   → wordOf {int} n ≡ SV-Lit fits-int n)
           (w-float : ∀ (n : ⟦ float ⟧b) → wordOf {float} n ≡ SV-Lit fits-float n)
           (entry-frame : FrameSemantics.Frame Mach) (entry-regs : Registers Mach) where
  open FlatMachine {Mach} using (FlatState; floc; fpc)
  open FlatStepsAPI {Mach} using (FlatSteps)
  open FlatEventTrace {Mach} using (flat-events)

  image = Program′.image ds f₀ ldConst
  open Ctl {Mach} ds f₀ ldConst ld-nl using (main)
  start-fs = StartR.start-fs {Mach} ds f₀ ldConst ld-nl wordOf entry-frame entry-regs
  open RunW {Mach} ds f₀ ldConst ld-nl wordOf using (AgreesAll)
  module OM = Once.LinCore.OpMachine.OM Mach bw (Program.U ds f₀) wordOf w-int w-float

  -- the meaning, and what it shows at a budget from the empty log
  obs : ℕ → TM.Run (Once.Denotation.Approx.Ap Data.Unit.⊤)
  obs k = TM.run ι [] (approx k (Sem.Lᶜ ⟦ ds ⟧D f₀ tt tt))

  -- the compiled program's run in the world, at a budget (D444)
  R : (K : ℕ) → Ran Wι ds f₀ mone mone 1 K []
  R K = exec Wι ds K f₀ mone mone 1 []

  module _ (ld : ∀ {b} (v : Lit b) (fs : FlatState)
                 → FlatMachine.flat-exec-instr {Mach} (ldConst v) image fs
                   ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf (lit v)) } ; fpc = suc (fpc fs) })
              -- ★ LINKED (D445): the program's ops are declared by the interpretation the machine runs against
              (decl : ∀ {s} → s ∈ ops (Program.U ds f₀) → Declared-at (TM.Interp.sig ι) (info s) (SigOpInfo.sem (info s))) where
    open EndR {Mach} ds f₀ ldConst ld-nl wordOf using (ends)
    open RunW {Mach} ds f₀ ldConst ld-nl wordOf using (from-startC)
    open FlatEventTrace {Mach} using (flat-ctrls; flat-events-steps; flat-events-step; chain-events; chain-log; chain-left; chain-ctrls; flat-ctrls-steps; chain-ctrls-≤)
    open FlatStepsAPI {Mach} using (Sound)

    private
      just≢nothing : ∀ {A : Set} {a : A} → just a ≡ nothing → ⊥
      just≢nothing ()

    -- the world's run cuts only at the program's ops: it stays inside the universe (`RunOps.run-ok`)
    o-cutsin : ∀ k → CutsIn (λ s → s ∈ ops (Program.U ds f₀)) (Ran.run (R k))
    o-cutsin k = proj₁ (RunOps.run-ok (λ s → s ∈ ops (Program.U ds f₀)) (Ran.run (R k))
                         ((λ m → ∈-++⁺ʳ (ps (defsGot ds)) m) , (λ m → ∈-++⁺ˡ m)) tt tt)

    -- ★ LINKED (D445): the world's run meets no call the interpretation leaves unanswered — it cuts only at
    -- the program's ops, each declared, whose calls the world answers (`OpMachine.Linked.no-cut`)
    o-uncut : ∀ k → UnCut (Ran.run (R k))
    o-uncut k = spends-uncut (λ {s} {x} {t} {p} → OM.Linked.no-cut decl {s} {x} {t} {p}) (Ran.run (R k)) (Ran.spends (R k)) (o-cutsin k)

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

    -- ★ THE WORLD'S RUN SHOWS THE MEANING at its budget (D443, D444): the budgeted soundness on the
    -- evaluator's own run (`BudgetSound.soundₖ`: its spends and the world's answers), the core's meaning
    -- the pass's (`Pass.pass-okᶠ`, bisimilar computations run alike)
    run-shows : ∀ k → (evsOf (Ran.trace (R k)) ≡ proj₁ (obs k)) × (endO (Ran.out (R k)) ≡ endAp (proj₂ (obs k)))
    run-shows k = sym (cong proj₁ eq) , trans (end-out (Ran.out (R k)) (Ran.left (R k))) (sym (cong (λ r → endAp (proj₂ r)) eq))
      where
        eq : obs k ≡ (evsOf (Ran.trace (R k)) , BudgetSound.W.outAp ι (Ran.out (R k)) (Ran.left (R k)))
        eq = proj₁ (BudgetSound.S.soundₖ ι (Ran.run (R k)) (Ran.spends (R k)) (o-uncut k) (Ran.world (R k)))

    -- ★★ THE FLAT THEOREM, relative to what is owed: at some fuel the flat run shows the meaning's
    -- events and end at the budget, and, where the budget cut it, a control step per unit
    -- (master's `flat-ends` and `flat-cut`, at one fuel)
    Shows : ℕ → ℕ → Set
    Shows k N = (flat-events (suc N) image start-fs ≡ (proj₁ (obs k) , endAp (proj₂ (obs k))))
                × (endAp (proj₂ (obs k)) ≡ nothing → k ≤ flat-ctrls (suc N) image start-fs)

    -- the flat run at a chain's length: its events, cut; its control steps
    private
      cut-events : ∀ {N fs′} (fl : FlatSteps image N start-fs fs′) → flat-events N image start-fs ≡ (LocState.ev-log (floc fs′) , nothing)
      cut-events {N} {fs′} fl =
        trans (cong (λ z → flat-events z image start-fs) (sym (+-identityʳ N)))
          (trans (flat-events-steps fl 0) (cong (λ z → (z , nothing)) (trans (++-identityʳ (chain-events fl)) (sym (chain-log fl)))))

      cut-ctrls : ∀ {N fs′} (fl : FlatSteps image N start-fs fs′) → chain-ctrls fl ≤ flat-ctrls N image start-fs
      cut-ctrls {N} {fs′} fl =
        subst (chain-ctrls fl ≤_) (trans (sym (flat-ctrls-steps fl 0)) (cong (λ z → flat-ctrls z image start-fs) (+-identityʳ N)))
              (m≤m+n (chain-ctrls fl) 0)

    flat-top : ∀ k → Σ ℕ (Shows k)
    flat-top k = by (Ran.run (R K)) refl (spends-plain (Ran.run (R K)) (Ran.spends (R K)) (o-uncut K)) (λ {mt} st e → AR.agrees-all st (AR.wtr-ios (Ran.trace (R K)) mt (sym e) (Ran.world (R K)))) eE eO
                      (λ ex → subst (K ≤_) (trans (cong (rounds (Ran.run (R K)) +_) (cut-zero (Ran.run (R K)) (Ran.spends (R K)) (o-uncut K) ex)) (+-identityʳ _))
                                    (spent-rounds (Ran.run (R K)) (Ran.spends (R K))))
      where
        module AR = AgreeRun.AR {Mach} ds f₀ ldConst ld-nl wordOf ι
                      (λ {s} {x} {y₀} {tp} {L} {L′} → OM.Dispatch.o-op decl {s} {x} {y₀} {tp} {L} {L′})
                      (λ {s} {x} {tp} {L} {L′} → OM.Dispatch.o-opend decl {s} {x} {tp} {L} {L′})
        K  = k
        eE = proj₁ (run-shows k)
        eO = proj₂ (run-shows k)
        by : ∀ {o t} (run : Run ds f₀ mone mone 1 o t) → Ran.out (R K) ≡ o → Plain run
           → (∀ {mt sh U′} {c′ : Codeᴵ sh U′} {r′ : Ret U′ (One ∷ [] ∣ One ∷ [])} {m′ n′}
                (st : StepsI main []ʳ start 1 mt c′ r′ m′ n′) → ios mt ≡ ios t → AgreesAll [] st)
           → evsOf t ≡ proj₁ (obs k) → endO o ≡ endAp (proj₂ (obs k)) → (Exh o → k ≤ rounds run)
           → Σ ℕ (Shows k)
        by {gives mone n′} {t} run _ pl ag ee eo _ = case image-noleak run pl of λ where
          (mt , st , _ , _ , _ , eio) → case ends ld entry-frame entry-regs st (ag st eio) f-end of λ where
            (N , fs′ , fst , hlt , lg , lft) →
              N , trans (o-flat fst hlt)
                            (cong₂ _,_ (trans lg (trans (cong (map ioEvent) eio) ee))
                                       (trans (cong (λ b → just (end-of-left b)) (cong proj₁ (proj₂ (proj₂ (proj₂ (proj₂ lft)))))) eo)) ,
              λ e → ⊥-elim (just≢nothing (trans eo e))
        by {stop Once.LinCore.Events.halted} {t} run _ pl ag ee eo _ = case image-halts run pl of λ where
          (mt , sh , U′ , r′ , m′ , n′ , st , eio) → case ends ld entry-frame entry-regs st (ag st eio) f-halt of λ where
            (N , fs′ , fst , hlt , lg , (fs₀ , M , st₀ , r₀ , l₀)) →
              N , trans (o-flat fst hlt)
                            (cong₂ _,_ (trans lg (trans (cong (map ioEvent) eio) ee))
                                       (trans (cong (λ b → just (end-of-left b)) (trans (cong proj₁ l₀) (o-running st₀ r₀))) eo)) ,
              λ e → ⊥-elim (just≢nothing (trans eo e))
        -- ★ the budget's cut (D444): the image pauses with exactly the run's events, a loop entry for each
        -- round the run started, at least one per unit of the budget (`image-cut`, `spent-rounds`)
        by {stop Once.LinCore.Events.exhausted} {t} run eq pl ag ee eo kr = case image-cut run pl of λ where
          (mt , sh , U′ , c′ , r′ , m′ , n′ , st , eio , rl) →
            case from-startC ld entry-frame entry-regs st (ag st eio) of λ where
              (N , fs′ , fl , lg , cc) →
                N , trans (cut-events fl) (cong₂ _,_ (trans lg (trans (cong (map ioEvent) eio) ee)) eo) ,
                λ _ → ≤-trans (kr tt) (≤-trans rl (≤-trans cc (cut-ctrls fl)))

    -- ★★ THE MACHINE NEVER FAULTS (master's `start-sound`): a running state the start reaches has not
    -- (`chain-left`); a halted one is where the world's run at a budget past it ends, unfaulted — were that
    -- run cut, the machine would have taken more control steps than it had steps to that state
    module ARo = AgreeRun.AR {Mach} ds f₀ ldConst ld-nl wordOf ι
                      (λ {s} {x} {y₀} {tp} {L} {L′} → OM.Dispatch.o-op decl {s} {x} {y₀} {tp} {L} {L′})
                      (λ {s} {x} {tp} {L} {L′} → OM.Dispatch.o-opend decl {s} {x} {tp} {L} {L′})

    private
      true≢false : Data.Bool.true ≡ Data.Bool.false → ⊥
      true≢false ()

      -- the machine is deterministic: the shorter chain is the longer's start
      mutual
        meet : ∀ {n N a b c} → FlatSteps image n a b → FlatSteps image N a c → n ≤ N
             → Σ ℕ λ k → FlatSteps image k b c × N ≡ n + k
        meet FlatStepsAPI.[] W le = _ , W , refl
        meet (FlatStepsAPI._∷_ (h , f) p) (FlatStepsAPI._∷_ (h′ , f′) w) (Data.Nat.s≤s le) =
          meet-at (Data.Maybe.Properties.just-injective (trans (sym f) f′)) p w le

        meet-at : ∀ {n N a b c i i′} → i ≡ i′
                → FlatSteps image n (FlatMachine.flat-exec-instr {Mach} i image a) b
                → FlatSteps image N (FlatMachine.flat-exec-instr {Mach} i′ image a) c → n ≤ N
                → Σ ℕ λ k → FlatSteps image k b c × suc N ≡ suc n + k
        meet-at refl p w le = let (k , q , e) = meet p w le in k , q , cong suc e

      stuck-at : ∀ {k b c} → FlatSteps image k b c → LocState.halted (floc b) ≡ Data.Bool.true → b ≡ c
      stuck-at FlatStepsAPI.[] h = refl
      stuck-at (FlatStepsAPI._∷_ (h′ , _) _) h = ⊥-elim (true≢false (trans (sym h) h′))

      same-end : ∀ {n N b c} → FlatSteps image n start-fs b → FlatSteps image N start-fs c
               → LocState.halted (floc b) ≡ Data.Bool.true → LocState.halted (floc c) ≡ Data.Bool.true → b ≡ c
      same-end {n} {N} P W h h′ = by (Data.Nat.Properties.≤-total n N)
        where
          by : _ → _
          by (inj₁ le) = let (k , Q , _) = meet P W le in stuck-at Q h
          by (inj₂ le) = let (k , Q , _) = meet W P le in sym (stuck-at Q h′)

      cut-past : ∀ {n N b c} → FlatSteps image n start-fs b → FlatSteps image N start-fs c
               → LocState.halted (floc b) ≡ Data.Bool.true → suc n ≤ N → ⊥
      cut-past {n} P W h le = at (meet P W (Data.Nat.Properties.≤-trans (Data.Nat.Properties.n≤1+n n) le))
        where
          at : _ → ⊥
          at (zero , FlatStepsAPI.[] , e) =
            Data.Nat.Properties.1+n≰n (subst (suc n ≤_) (trans e (+-identityʳ n)) le)
          at (suc _ , FlatStepsAPI._∷_ (h′ , _) _ , _) = true≢false (trans (sym h) h′)

      unfaulted : ∀ {M fs₀ fs′} → FlatSteps image M start-fs fs₀ → LocState.halted (floc fs₀) ≡ Data.Bool.false
                → LocState.faulted (floc fs′) ≡ LocState.faulted (floc fs₀) → LocState.faulted (floc fs′) ≡ Data.Bool.false
      unfaulted st₀ r₀ e = trans e (cong proj₂ (chain-left st₀ r₀))

      -- what the world's run at a budget leaves the machine: halted unfaulted, or cut a control step a unit
      Witness : ℕ → Set
      Witness K = (Σ ℕ λ N → Σ FlatState λ fs → FlatSteps image N start-fs fs
                     × LocState.halted (floc fs) ≡ Data.Bool.true × LocState.faulted (floc fs) ≡ Data.Bool.false)
                ⊎ (Σ ℕ λ N → Σ FlatState λ fs → Σ (FlatSteps image N start-fs fs) λ W → K ≤ chain-ctrls W)

      witness : ∀ K → Witness K
      witness K = wb (Ran.run (R K)) (spends-plain (Ran.run (R K)) (Ran.spends (R K)) (o-uncut K))
                      (λ {mt} st e → ARo.agrees-all st (ARo.wtr-ios (Ran.trace (R K)) mt (sym e) (Ran.world (R K))))
                      (λ ex → subst (K ≤_) (trans (cong (rounds (Ran.run (R K)) +_) (cut-zero (Ran.run (R K)) (Ran.spends (R K)) (o-uncut K) ex)) (+-identityʳ _))
                                    (spent-rounds (Ran.run (R K)) (Ran.spends (R K))))
        where
          wb : ∀ {o t} (run : Run ds f₀ mone mone 1 o t) → Plain run
             → (∀ {mt sh U′} {c′ : Codeᴵ sh U′} {r′ : Ret U′ (One ∷ [] ∣ One ∷ [])} {m′ n′}
                  (st : StepsI main []ʳ start 1 mt c′ r′ m′ n′) → ios mt ≡ ios t → AgreesAll [] st)
             → (Exh o → K ≤ rounds run) → Witness K
          wb {gives mone n′} run pl ag kr = case image-noleak run pl of λ where
            (mt , st , _ , _ , _ , eio) → case ends ld entry-frame entry-regs st (ag st eio) f-end of λ where
              (N , fs′ , fst , hlt , lg , (fs₀ , M , st₀ , r₀ , e)) → inj₁ (N , fs′ , fst , hlt , unfaulted {fs′ = fs′} st₀ r₀ (cong proj₂ e))
          wb {stop Once.LinCore.Events.halted} run pl ag kr = case image-halts run pl of λ where
            (mt , sh , U′ , r′ , m′ , n′ , st , eio) → case ends ld entry-frame entry-regs st (ag st eio) f-halt of λ where
              (N , fs′ , fst , hlt , lg , (fs₀ , M , st₀ , r₀ , l₀)) → inj₁ (N , fs′ , fst , hlt , unfaulted {fs′ = fs′} st₀ r₀ (cong proj₂ l₀))
          wb {stop Once.LinCore.Events.exhausted} run pl ag kr = case image-cut run pl of λ where
            (mt , sh , U′ , c′ , r′ , m′ , n′ , st , eio , rl) →
              case from-startC ld entry-frame entry-regs st (ag st eio) of λ where
                (N , fs′ , fl , lg , cc) → inj₂ (suc N , fs′ , fl , ≤-trans (kr tt) (≤-trans rl cc))

    o-sound : Sound image start-fs
    o-sound {n} {fs′} P = by-halt (LocState.halted (floc fs′)) refl
      where
        on : LocState.halted (floc fs′) ≡ Data.Bool.true → Witness (suc n) → LocState.faulted (floc fs′) ≡ Data.Bool.false
        on h (inj₁ (N , fsₑ , W , he , fe)) = subst (λ z → LocState.faulted (floc z) ≡ Data.Bool.false) (sym (same-end P W h he)) fe
        on h (inj₂ (N , fsₑ , W , c)) = ⊥-elim (cut-past P W h (≤-trans c (chain-ctrls-≤ W)))

        by-halt : ∀ b → LocState.halted (floc fs′) ≡ b → LocState.faulted (floc fs′) ≡ Data.Bool.false
        by-halt Data.Bool.false h = cong proj₂ (chain-left P h)
        by-halt Data.Bool.true  h = on h (witness (suc n))

------------------------------------------------------------------------
-- ★ ONE LINK UP: master's IR program and its meaning (`evalᴰ` at the table's
-- environment, as the apex states it). The program translates (`FromIR`);
-- the pass's meaning and master's show the same at every budget (owed:
-- `BridgeProof.bridge`, its casts and the table's `EnvOK`).
------------------------------------------------------------------------

module IRTop (tbl : List IRFun) (ir : Once.IR.IR Once.IRTy.Unit Once.IRTy.Unit)
             (tp : FromIR.TrProg) (etp : FromIR.trTable tbl ≡ just tp)
             (f : IR (FromIR.TrProg.Γ tp) One One) (ef : FromIR.trI (FromIR.TrProg.rs tp) ir ≡ just f)
             (ldConst : ∀ {b} → Lit b → AbstractInstr)
             (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {Mach} (ldConst v) ≡ nothing)
             (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue Mach)
             (w-int   : ∀ (n : ⟦ int ⟧b)   → wordOf {int} n ≡ SV-Lit fits-int n)
             (w-float : ∀ (n : ⟦ float ⟧b) → wordOf {float} n ≡ SV-Lit fits-float n)
             (entry-frame : FrameSemantics.Frame Mach) (entry-regs : Registers Mach)
             -- ★ master's premise: the program is linked (every call names an entry, every FFI op declared)
             (linked : LinkedProgram (TM.Interp.sig ι) (irProgram tbl ir)) where
  ds = trP (FromIR.TrProg.prog tp)
  f₀ = tr f
  module TP = Top ds f₀ ldConst ld-nl wordOf w-int w-float entry-frame entry-regs

  -- ★ LINKED AT THE CORE (D445): the core program's ops are its IR's, each declared
  decl : ∀ {s} → s ∈ ops (Program.U ds f₀) → Declared-at (TM.Interp.sig ι) (info s) (SigOpInfo.sem (info s))
  decl = LinkedCore.univ-ps (LinkedCore.FromLinked.Dc (TM.Interp.sig ι)) (FromIR.TrProg.prog tp) f
           (LinkedCore.FromLinked.table-ok (TM.Interp.sig ι) tbl etp (proj₁ (proj₂ (proj₂ linked))))
           (LinkedCore.FromLinked.tr-ok (TM.Interp.sig ι) (FromIR.trI-Tr (FromIR.TrProg.rs tp) ir ef) (proj₁ linked))

  -- master's meaning, and what it shows at a budget from the empty log
  obsᴰ : ℕ → TM.Run (Once.Denotation.Approx.Ap Data.Unit.⊤)
  obsᴰ k = TM.run ι [] (approx k (DT.evalᴰ fmt (tableEnv fmt ans tbl) ir tt))

  module _ (ld : ∀ {b} (v : Lit b) (fs : FlatMachine.FlatState {Mach})
                 → FlatMachine.flat-exec-instr {Mach} (ldConst v) TP.image fs
                   ≡ record fs { floc = record (FlatMachine.floc fs) { regs = writeReg (LocState.regs (FlatMachine.floc fs)) Output (wordOf (lit v)) }
                               ; fpc = suc (FlatMachine.fpc fs) }) where
    open FlatEventTrace {Mach} using (flat-events; flat-ctrls)
    open FlatMachine {Mach} using (FlatState)

    -- the translation means what master's program means, at every budget (B1.3's bridge, its
    -- casts and the table's `EnvOK`; bisimilar computations show the same: `RunBisim`)
    o-bridge : ∀ k → TP.obs k ≡ obsᴰ k
    o-bridge k = trans (BudgetSound.W.run-≈ ι k (pass-okᶠ (pass-okP (FromIR.TrProg.prog tp)) funit funit f tt) []) (run-≈ ι k (BP.bridge (Once.LinCore.Pass.⟦_⟧P fmt ans (FromIR.TrProg.prog tp)) (tableCalls fmt ans tbl)
                                     (casts (Once.LinCore.Pass.⟦_⟧P fmt ans (FromIR.TrProg.prog tp)) (tableCalls fmt ans tbl))
                                     (env-ok tbl etp) (FromIR.trI-Tr (FromIR.TrProg.rs tp) ir ef) tt) [])

    -- ★★ THE FLAT THEOREM AT MASTER'S MEANING (master's `flat-ends` and `flat-cut`)
    flat-ir : ∀ k → Σ ℕ λ N → (flat-events (suc N) TP.image TP.start-fs ≡ (proj₁ (obsᴰ k) , endAp (proj₂ (obsᴰ k))))
                                     × (endAp (proj₂ (obsᴰ k)) ≡ nothing → k ≤ flat-ctrls (suc N) TP.image TP.start-fs)
    flat-ir k = case TP.flat-top ld decl k of λ where
      (N , e , c) → N , trans e (cong (λ r → (proj₁ r , endAp (proj₂ r))) (o-bridge k))
                      , λ z → c (trans (cong (λ r → endAp (proj₂ r)) (o-bridge k)) z)

    flat-sound : FlatStepsAPI.Sound {Mach} TP.image TP.start-fs
    flat-sound = TP.o-sound ld decl
