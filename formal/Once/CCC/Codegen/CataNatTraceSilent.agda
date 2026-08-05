-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatTraceSilent — the descend phase emits NO
-- SigOp events (Plan 0.36 task #8, traces-agree).
--
-- This is the end-to-end check that the trace bridge `flat-events-steps`
-- (Once.Adequacy.FlatEvents) composes with the state chains built in
-- `CataNatDescend`: a continue descend iteration (`descend-iter-flat`) is
-- 9 control/reg/load instructions, none an `instr-sigop`, so its
-- `chain-events` reduce to `[]` DEFINITIONALLY and `flat-events` skips
-- the whole iteration to its end state — contributing nothing to the
-- machine trace. (The trace's content comes solely from the algebra `at`
-- in the base + ascend phases; the descend phase only sets up the depth
-- counter.) So `flat-events` of the descend phase factors out of
-- `traces-agree` entirely.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatTraceSilent where

open import Once.CCC.Label using (LabelId)

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.List using ([]; _++_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (LocState; AllocState; halted; regs; readReg; Input1; Scratch;
         sv-as-loc; sucLoc; StoredValue; ValueLocation; AbstractTrace;
         instr-reg-op; count-inc; load-indirect-suc; mov-to-input;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero;
         module MemOps)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.CataNatDescend using (module CataNatDescend)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)

module CataNatTraceSilent {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}
  open MemOps {FS} using (readLoc)
  open CataNatDescend {FS}
  open FlatEventTrace {FS}

  -- A `flat-step1` link whose instruction emits no event is silent: its
  -- `chain-events` reduce to `[]`. (`chain-events-subst` sees through the
  -- `flat-step1` transport; then the lone link's events are `event-of i
  -- fs ++ []`, which the `event-of i fs ≡ []` hypothesis collapses.)
  step1-silent : ∀ {prog fs fs'} {i} (h : halted (floc fs) ≡ false)
                   (f : fetch prog (fpc fs) ≡ just i) (eq : flat-exec-instr i prog fs ≡ fs')
               → event-of i fs ≡ []
               → chain-events (flat-step1 h f eq) ≡ []
  step1-silent {fs = fs} {i = i} h f eq ev =
    trans (chain-events-subst eq ((h , f) ∷ [])) (cong (_++ []) ev)

  -- `FlatSteps-++` of two silent chains is silent.
  ++-silent : ∀ {prog k₁ k₂ fs₁ fs₂ fs₃}
                (xs : FlatSteps prog k₁ fs₁ fs₂) (ys : FlatSteps prog k₂ fs₂ fs₃)
            → chain-events xs ≡ [] → chain-events ys ≡ []
            → chain-events (FlatSteps-++ xs ys) ≡ []
  ++-silent xs ys px py =
    trans (chain-events-++ xs ys) (trans (cong (_++ chain-events ys) px) py)

  -- The descend PRE-control phase is silent: its three links are control
  -- instructions (label, two branch-not), each emitting nothing.
  descend-pre-silent : ∀ (prog : AbstractTrace) (fs : FlatState) (ld-top ld-end ld-base : LabelId)
                         (hf : halted (floc fs) ≡ false)
                         (scond : sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false)
                         (tcond : tag-zf (flat-read-tag (floc fs)) ≡ false)
                         (fL  : fetch prog (fpc fs)             ≡ just (instr-ctrl (c-label ld-top)))
                         (fB1 : fetch prog (suc (fpc fs))       ≡ just (instr-ctrl (c-branch-scratch-zero ld-end)))
                         (fB2 : fetch prog (suc (suc (fpc fs))) ≡ just (instr-ctrl (c-branch-tag-zero ld-base)))
                     → chain-events (descend-pre-flat prog fs ld-top ld-end ld-base hf scond tcond fL fB1 fB2) ≡ []
  descend-pre-silent prog fs ld-top ld-end ld-base hf scond tcond fL fB1 fB2 =
    ++-silent L (FlatSteps-++ B1 B2)
      (step1-silent {prog = prog} hf fL eqL refl)
      (++-silent B1 B2
        (step1-silent {prog = prog} {fs = record fs { fpc = suc (fpc fs) }}       hf fB1 eqB1 refl)
        (step1-silent {prog = prog} {fs = record fs { fpc = suc (suc (fpc fs)) }} hf fB2 eqB2 refl))
    where
      eqL  = flat-label               prog fs ld-top
      eqB1 = flat-scratch-branch-not  prog (record fs { fpc = suc (fpc fs) })       ld-end  scond
      eqB2 = flat-tag-branch-not      prog (record fs { fpc = suc (suc (fpc fs)) }) ld-base tcond
      L  = flat-step1 {prog = prog} hf fL  eqL
      B1 = flat-step1 {prog = prog} hf fB1 eqB1
      B2 = flat-step1 {prog = prog} hf fB2 eqB2

  -- The descend POST-control phase is silent: jmp / label / jmp.
  descend-post-silent : ∀ (prog : AbstractTrace) (fs : FlatState) (ld-de ld-top : LabelId) (q-de q-top : ℕ)
                          (hf : halted (floc fs) ≡ false)
                          (fJ1 : fetch prog (fpc fs)      ≡ just (instr-ctrl (c-jmp ld-de)))
                          (de-res : find-label prog ld-de ≡ just q-de)
                          (fL : fetch prog q-de           ≡ just (instr-ctrl (c-label ld-de)))
                          (fJ2 : fetch prog (suc q-de)    ≡ just (instr-ctrl (c-jmp ld-top)))
                          (top-res : find-label prog ld-top ≡ just q-top)
                      → chain-events (descend-post-flat prog fs ld-de ld-top q-de q-top hf fJ1 de-res fL fJ2 top-res) ≡ []
  descend-post-silent prog fs ld-de ld-top q-de q-top hf fJ1 de-res fL fJ2 top-res =
    ++-silent P1 (FlatSteps-++ P2 P3)
      (step1-silent {prog = prog} hf fJ1 eqP1 refl)
      (++-silent P2 P3
        (step1-silent {prog = prog} {fs = record fs { fpc = q-de }}     hf fL  eqP2 refl)
        (step1-silent {prog = prog} {fs = record fs { fpc = suc q-de }} hf fJ2 eqP3 refl))
    where
      eqP1 = trans (flat-jmp prog fs ld-de) (cong (λ m → do-jump m fs) de-res)
      eqP2 = flat-label prog (record fs { fpc = q-de }) ld-de
      eqP3 = trans (flat-jmp prog (record fs { fpc = suc q-de }) ld-top)
                   (cong (λ m → do-jump m (record fs { fpc = suc q-de })) top-res)
      P1 = flat-step1 {prog = prog} hf fJ1 eqP1
      P2 = flat-step1 {prog = prog} hf fL  eqP2
      P3 = flat-step1 {prog = prog} hf fJ2 eqP3

  -- One continue descend iteration emits no events: `flat-events` of the
  -- 9-step iteration (from the loop head `fs`) skips straight to the end
  -- state `record (body-result …) {fpc = q-top}`. Proved by feeding
  -- `descend-iter-flat` to `flat-events-steps`; `chain-events` of that
  -- silent chain reduces to `[]`, so the prepended events vanish.
  descend-iter-silent : ∀ (prog : AbstractTrace) (fs : FlatState)
                          (ld-top ld-end ld-inl ld-de : LabelId) (q-de q-top : ℕ)
                          (loc : ValueLocation FS) (v : StoredValue FS)
    → halted (floc fs) ≡ false
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false
    → tag-zf (flat-read-tag (floc fs)) ≡ false
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → fetch prog (fpc fs)                               ≡ just (instr-ctrl (c-label ld-top))
    → fetch prog (suc (fpc fs))                         ≡ just (instr-ctrl (c-branch-scratch-zero ld-end))
    → fetch prog (suc (suc (fpc fs)))                   ≡ just (instr-ctrl (c-branch-tag-zero ld-inl))
    → fetch prog (suc (suc (suc (fpc fs))))             ≡ just (instr-reg-op count-inc)
    → fetch prog (suc (suc (suc (suc (fpc fs)))))       ≡ just load-indirect-suc
    → fetch prog (suc (suc (suc (suc (suc (fpc fs)))))) ≡ just mov-to-input
    → fetch prog (suc (suc (suc (suc (suc (suc (fpc fs))))))) ≡ just (instr-ctrl (c-jmp ld-de))
    → find-label prog ld-de   ≡ just q-de
    → fetch prog q-de         ≡ just (instr-ctrl (c-label ld-de))
    → fetch prog (suc q-de)   ≡ just (instr-ctrl (c-jmp ld-top))
    → find-label prog ld-top  ≡ just q-top
    → ∀ (b : ℕ)
    → flat-events (9 + b) prog fs
        ≡ flat-events b prog
            (record (body-result prog (record fs { fpc = suc (suc (suc (fpc fs))) })) { fpc = q-top })
  descend-iter-silent prog fs ld-top ld-end ld-inl ld-de q-de q-top loc v
                      hf scond tcond ptr child fL0 fB0 fB1 fi fl fm fJ1 de-res fLde fJ2 top-res b =
    trans
      (flat-events-steps
        (descend-iter-flat prog fs ld-top ld-end ld-inl ld-de q-de q-top loc v
          hf scond tcond ptr child fL0 fB0 fB1 fi fl fm fJ1 de-res fLde fJ2 top-res) b)
      (cong (_++ flat-events b prog _) iter-chain-[])
    where
      fsB : FlatState
      fsB = record fs { fpc = suc (suc (suc (fpc fs))) }
      PRE  = descend-pre-flat prog fs ld-top ld-end ld-inl hf scond tcond fL0 fB0 fB1
      BODY = descend-body-flat prog fsB loc v hf ptr child fi fl fm
      POST = descend-post-flat prog (body-result prog fsB) ld-de ld-top q-de q-top
               (trans (body-keeps-halted prog fsB loc v ptr child) hf) fJ1 de-res fLde fJ2 top-res
      -- The whole iteration's events are empty: pre (control) ++ body
      -- (reg/load, refl) ++ post (control), each silent.
      iter-chain-[] :
        chain-events (descend-iter-flat prog fs ld-top ld-end ld-inl ld-de q-de q-top loc v
                       hf scond tcond ptr child fL0 fB0 fB1 fi fl fm fJ1 de-res fLde fJ2 top-res) ≡ []
      iter-chain-[] =
        ++-silent PRE (FlatSteps-++ BODY POST)
          (descend-pre-silent prog fs ld-top ld-end ld-inl hf scond tcond fL0 fB0 fB1)
          (++-silent BODY POST refl
            (descend-post-silent prog (body-result prog fsB) ld-de ld-top q-de q-top
              (trans (body-keeps-halted prog fsB loc v ptr child) hf) fJ1 de-res fLde fJ2 top-res))
