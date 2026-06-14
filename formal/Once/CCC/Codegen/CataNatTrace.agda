-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatTrace — the TRACE side of `cata-correct` for the
-- strat-nat catamorphism (the trace analogue of `CataNatValue`'s
-- `cata-nat-value-realized`).
--
-- The strat-nat cata's machine trace is `prelude ∷ descend ++ base ++
-- ascend` (IRToTrace.cata-trace-nat): the prelude (`scratch-one`,
-- `input2-zero`) and the descend phase are SILENT (CataNatDescend.
-- descend-loop-silent), the base phase emits `E_base` (CataNatAscend.
-- base-phase-runs), and the ascend loop emits `loop-events E n`
-- (CataNatAscend.ascend-loop-runs). So the run's SigOp trace is exactly
-- `E_base ++ loop-events E n`.
--
-- `cata-nat-flat-events` ASSEMBLES this: given the four phases as a chain
-- to a halted final state (with their per-phase events), `flat-events`
-- reads off the concatenation. The INTER-PHASE STATE FLOW — the heap-pushed
-- Nat spine that descend builds and base/ascend consume — is the caller's
-- to supply (exactly as `cata-nat-value-realized` takes `vstep`); this
-- lemma is the event-bookkeeping that turns those phase chains into the
-- machine's observable trace.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatTrace where

open import Data.Nat using (ℕ; _+_)
open import Data.Bool using (true)
open import Data.List using (List; []; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Verified.Trace using (SigOpEvent)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (halted; AbstractTrace)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.Verified.FlatEvents using (module FlatEventTrace)

module CataNatTrace {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}
  open FlatEventTrace {FS}

  -- The strat-nat cata run emits `Ebase ++ Easc`. Generic in the per-phase
  -- event lists: the caller passes `Ebase` (base) and `Easc` (= `loop-events
  -- E n` from `ascend-loop-runs`). prelude + descend silent ⇒ they vanish; the
  -- halted final state ⇒ no trailing events.
  cata-nat-flat-events :
    ∀ (prog : AbstractTrace) (s0 s1 s2 s3 sH : FlatState)
      (kp kd kb ka : ℕ) (Ebase Easc : List SigOpEvent)
      (prel : FlatSteps prog kp s0 s1) (desc : FlatSteps prog kd s1 s2)
      (base : FlatSteps prog kb s2 s3) (asc  : FlatSteps prog ka s3 sH)
    → chain-events prel ≡ []
    → chain-events desc ≡ []
    → chain-events base ≡ Ebase
    → chain-events asc  ≡ Easc
    → halted (floc sH) ≡ true
    → ∀ (b : ℕ) →
        flat-events (kp + (kd + (kb + (ka + b)))) prog s0 ≡ Ebase ++ Easc
  cata-nat-flat-events prog s0 s1 s2 s3 sH kp kd kb ka Ebase Easc
                       prel desc base asc pe de be ae hH b =
    trans (flat-events-steps prel (kd + (kb + (ka + b))))
    (trans (cong (chain-events prel ++_) (flat-events-steps desc (kb + (ka + b))))
    (trans (cong (λ z → chain-events prel ++ (chain-events desc ++ z))
                 (flat-events-steps base (ka + b)))
    (trans (cong (λ z → chain-events prel ++ (chain-events desc ++ (chain-events base ++ z)))
                 (flat-events-steps asc b))
    (trans (cong (λ z → chain-events prel ++ (chain-events desc ++ (chain-events base ++ (chain-events asc ++ z))))
                 (flat-events-settled prog sH b (inj₁ hH)))
           events-eq))))
    where
      -- after peeling all four phases + the settled tail, fold the events:
      -- ce prel ++ (ce desc ++ (ce base ++ (ce asc ++ []))) ≡ Ebase ++ Easc.
      events-eq :
        chain-events prel ++ (chain-events desc ++ (chain-events base ++ (chain-events asc ++ [])))
          ≡ Ebase ++ Easc
      events-eq
        rewrite pe | de | be | ae = cong (Ebase ++_) (++-identityʳ Easc)
