-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32.Sim — plan 0.146 B1.7c (D460): ★
-- x86-32 AS AN ARCH (`Interface.ArchSim`).
--
-- Over its code generator (`Target.X86-32.Backend`); its flat machine and
-- entry are master's (`ArchCorrectness.X86-32`); its table is the
-- arch layer's (`ConcFlatSim.x86-32-arith-table`, at a block list's table:
-- D459); its theorem composes master's arch simulation (`events-agree-boot`,
-- generic in the image) with the boot's room check and the budget apex, from
-- the image's facts.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Name using (CanonicalName)
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB
open import Data.List using (List; []; _∷_)
open import Once.Denotation.Program using (IRFun; IRProgram; runIR)
open import Once.IR.Semantics.Trace using (Interp; pureHalf)

module Once.Adequacy.ArchCorrectness.X86-32.Sim
  (o : CanonicalName) (tbl : List IRFun) (ι : Interp)
  (x86-32-reg-range : RB.RegRange o ι)
  (x86-32-addr-no-wrap : RB.AddrNoWrap o ι)
  (x86-32-lit-fits : RB.LitFits o ι)
  where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function using (case_of_)
open import Once.Target.Arch using (x86-32; arch-numerics)
open import Once.Adequacy.BudgetApex (arch-numerics x86-32) using (budget-apex-⊑; budget-fact-of)
open import Once.Arith.Backend.CallAnswer using (answer-at)
open import Once.Adequacy.CPU.X86-32 using (call-at-x86-32; ev-x86-32; block-env)
open import Once.Adequacy.ArchCorrectness.ArithSimX86-32 using (val-x86-32)
import Once.Arith.Backend.X86-32.RunTrace as RTx
import Once.CCC.Target.X86-32.Semantics as X
open import Once.CCC.Target.X86-32.Syntax using (slot-size)
open import Once.CCC.Target.X86-32.AbstractToX86-32 using (compile-trace; compile-trace-cnt-agrees)
open import Once.Compile using (entry-owner)
open import Once.Adequacy.CPU.Interface using (module ArchSemantics)
open import Once.Adequacy.CPU using (arch-semantics)
open import Once.Adequacy.MachineTrace using (module Machine)
open import Once.Target.Backend using (file-table; module Backend)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-start)
open import Once.Adequacy.RoomChecksEvents using (module RoomEvents)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.Adequacy.ArchCorrectness.Interface using (ArchSim)
import Once.Adequacy.CoreFileWF
import Once.Target.X86-32.Backend

-- master's x86-32 apex: its machine, its entry, its arch simulation
open import Once.Adequacy.ArchCorrectness.X86-32 o tbl ι x86-32-reg-range x86-32-addr-no-wrap x86-32-lit-fits
  using (x86-32-frame-semantics; entry-frame-x86-32; module FFOx; entry-corr; entry-wf; entry-like)
open import Once.Adequacy.ArchCorrectness.X86-32.ConcFlatSim o
  x86-32-frame-semantics refl refl
  x86-32-reg-range
  (RB.AddrNoWrap.ret-no-wrap x86-32-addr-no-wrap)
  (RB.LitFits.tag-fits x86-32-lit-fits) (RB.LitFits.lit-fits x86-32-lit-fits) (RB.float-fits o ι)
  (RB.LitFits.room-fits x86-32-lit-fits)
  using (events-agree-boot; AgreeAt; reach-start; mkRunAt; x86-32-arith-table)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunLow o x86-32-frame-semantics slot-size refl using (RunLow; low-start)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o x86-32-frame-semantics slot-size refl using (Emitted; module Emitted)

private
  retarget : ∀ {A : ℕ → _} {o o′ c c′} → o ≡ o′ → c ≡ c′
           → Σ ℕ (λ M → AgreeAt (A M) o c M) → Σ ℕ (λ M → AgreeAt (A M) o′ c′ M)
  retarget refl refl x = x

  run-of = λ env → RTx.Run.δ val-x86-32 (answer-at (arch-numerics x86-32) ι call-at-x86-32) ev-x86-32 env

-- ★ x86-32
x86-32-sim : ArchSim o Once.Target.X86-32.Backend.backend
x86-32-sim = record
  { FS = x86-32-frame-semantics ; slot-size = slot-size ; word-eq = refl
  ; entry-frame = entry-frame-x86-32 ; entry-regs = FFOx.entry-regs
  ; block-env = block-env
  ; ArithTable = x86-32-arith-table
  ; table = λ prog bs nm em → inj₂ (bs , nm , refl , em)
  ; Code = _ ; compile = compile-trace
  ; S = _ ; δ = run-of ; init = [] , X.initState
  ; run-file = λ F → ArchSemantics.run-trace (arch-semantics x86-32) ι F (ArchSemantics.initialState (arch-semantics x86-32) F)
  ; file-runs = λ t bs ex → cong (λ cd → Machine.trace (run-of (block-env (file-table (Backend.payload Once.Target.X86-32.Backend.backend) bs)) cd) ([] , X.initState))
                                 (cong proj₂ (compile-trace-cnt-agrees entry-owner 0 t))
  ; file-wf = Once.Adequacy.CoreFileWF.X8632.core-wf
  ; sim = sim
  }
  where
    sim : _
    sim q b tail env em tb snd fl =
      budget-apex-⊑ (run-of env (compile-trace (room-checks (instr-ctrl (c-start b) ∷ tail)))) ([] , X.initState) ι (runIR (arch-numerics x86-32) (pureHalf ι) q) fact
      where
        image = instr-ctrl (c-start b) ∷ tail
        P′ = room-checks image
        run₀ : RunLow P′ FFOx.start-flat
        run₀ = low-start image FFOx.start-flat (mkRunAt em (reach-start FFOx.start-flat (entry-like 0) refl snd)) refl
        fact = λ k → case fl k of λ where
          (N , e , c) →
            let open RoomEvents {x86-32-frame-semantics} image using (ev-boot)
                boot = ev-boot N FFOx.start-flat 0 refl _ refl
                agree₀ = events-agree-boot (proj₁ boot) ev-x86-32 env P′ FFOx.start-flat X.initState _ _ (entry-corr P′)
                           (entry-wf 0) tt refl tb run₀ refl refl refl refl refl refl
                agree = retarget (proj₁ (proj₂ boot)) (proj₂ (proj₂ boot)) agree₀
            in budget-fact-of (run-of env (compile-trace P′)) ([] , X.initState) ι (runIR (arch-numerics x86-32) (pureHalf ι) q) k (proj₁ agree) _
                 -- (the run's events named, so they are matched, not computed)
                 (RTx.run-events val-x86-32 (answer-at (arch-numerics x86-32) ι call-at-x86-32) ev-x86-32 env [] (proj₁ agree) (compile-trace P′) X.initState) _
                 (RTx.Run.runN-events val-x86-32 (answer-at (arch-numerics x86-32) ι call-at-x86-32) ev-x86-32 env (compile-trace P′) (proj₁ agree) [] X.initState)
                 (cong (RTx.Run.outObs val-x86-32 (answer-at (arch-numerics x86-32) ι call-at-x86-32) ev-x86-32 env (compile-trace P′)) e)
                 c (proj₂ agree)
