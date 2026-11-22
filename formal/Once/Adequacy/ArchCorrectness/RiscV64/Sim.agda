-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.Sim — plan 0.146 B1.7c (D463): ★
-- riscv64 AS AN ARCH (`Interface.ArchSim`).
--
-- Over its code generator (`Target.RiscV64.Backend`); its flat machine and
-- entry are master's (`ArchCorrectness.RiscV64`); its table is the
-- arch layer's (`ConcFlatSim.riscv64-arith-table`, at a block list's table:
-- D462); its theorem composes master's arch simulation (`events-agree-boot`,
-- generic in the image) with the boot's room check and the budget apex, from
-- the image's facts.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Name using (CanonicalName)
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RB
open import Data.List using (List; []; _∷_)
open import Once.Denotation.Program using (IRFun; IRProgram; runIR)
open import Once.IR.Semantics.Trace using (Interp; pureHalf)

module Once.Adequacy.ArchCorrectness.RiscV64.Sim
  (o : CanonicalName) (tbl : List IRFun) (ι : Interp)
  (riscv64-reg-range : RB.RegRange o ι)
  (riscv64-slot-addr-no-wrap : RB.SlotAddrNoWrap o ι)
  (riscv64-addr-no-wrap : RB.AddrNoWrap o ι)
  (riscv64-lit-fits : RB.LitFits o ι)
  where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function using (case_of_)
open import Once.Target.Arch using (riscv64; arch-numerics)
open import Once.Adequacy.BudgetApex (arch-numerics riscv64) using (budget-apex-⊑; budget-fact-of)
open import Once.Arith.Backend.CallAnswer using (answer-at)
open import Once.Adequacy.CPU.RiscV64 using (call-at-riscv64; ev-riscv64; block-env)
open import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 using (val-riscv64)
import Once.Arith.Backend.RiscV64.RunTrace as RTx
import Once.CCC.Target.RiscV64.Semantics as X
open import Once.CCC.Target.RiscV64.Syntax using (slot-size)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace; compile-trace-cnt-agrees)
open import Once.Compile.Emit using (entry-owner)
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
import Once.Target.RiscV64.Backend

-- master's riscv64 apex: its machine, its entry, its arch simulation
open import Once.Adequacy.ArchCorrectness.RiscV64.Entry o ι riscv64-reg-range riscv64-slot-addr-no-wrap riscv64-addr-no-wrap riscv64-lit-fits
  using (rv64-frame-semantics; entry-frame-riscv64; entry-regs; start-flat; entry-corr; entry-wf; entry-like)
open import Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim o
  rv64-frame-semantics refl refl riscv64-slot-addr-no-wrap
  riscv64-reg-range
  (RB.AddrNoWrap.ret-no-wrap riscv64-addr-no-wrap)
  (RB.LitFits.tag-fits riscv64-lit-fits) (RB.LitFits.lit-fits riscv64-lit-fits) (RB.float-fits o ι)
  (RB.LitFits.room-fits riscv64-lit-fits)
  using (module Dispatch′; riscv64-arith-table)
open Dispatch′ using (events-agree-boot; AgreeAt)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunLow o rv64-frame-semantics slot-size refl using (RunLow; low-start)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o rv64-frame-semantics slot-size refl using (Emitted; module Emitted; mkRunAt; reach-start)

private
  retarget : ∀ {A : ℕ → _} {o o′ c c′} → o ≡ o′ → c ≡ c′
           → Σ ℕ (λ M → AgreeAt (A M) o c M) → Σ ℕ (λ M → AgreeAt (A M) o′ c′ M)
  retarget refl refl x = x

  run-of = λ env → RTx.Run.δ val-riscv64 (answer-at (arch-numerics riscv64) ι call-at-riscv64) ev-riscv64 env

-- ★ riscv64
riscv64-sim : ArchSim o Once.Target.RiscV64.Backend.backend
riscv64-sim = record
  { FS = rv64-frame-semantics ; slot-size = slot-size ; word-eq = refl
  ; entry-frame = entry-frame-riscv64 ; entry-regs = entry-regs
  ; block-env = block-env
  ; ArithTable = riscv64-arith-table
  ; table = λ prog bs nm em → bs , nm , refl , em
  ; Code = _ ; compile = compile-trace
  ; S = _ ; δ = run-of ; init = [] , X.initState
  ; run-file = λ F → ArchSemantics.run-trace (arch-semantics riscv64) ι F (ArchSemantics.initialState (arch-semantics riscv64) F)
  ; file-runs = λ t bs ex → cong (λ cd → Machine.trace (run-of (block-env (file-table (Backend.payload Once.Target.RiscV64.Backend.backend) bs)) cd) ([] , X.initState))
                                 (cong proj₂ (compile-trace-cnt-agrees entry-owner 0 t))
  ; file-wf = Once.Adequacy.CoreFileWF.RiscV64.core-wf
  ; empty-wf = Once.Adequacy.CoreFileWF.RiscV64.empty-wf
  ; entry-like = entry-like 0 ; entry-wf = entry-wf 0 ; entry-cl = tt
  ; sim = sim
  }
  where
    sim : _
    sim q b tail env em tb snd fl =
      budget-apex-⊑ (run-of env (compile-trace (room-checks (instr-ctrl (c-start b) ∷ tail)))) ([] , X.initState) ι (runIR (arch-numerics riscv64) (pureHalf ι) q) fact
      where
        image = instr-ctrl (c-start b) ∷ tail
        P′ = room-checks image
        run₀ : RunLow P′ start-flat
        run₀ = low-start image start-flat (mkRunAt em (reach-start start-flat (entry-like 0) refl snd)) refl
        fact = λ k → case fl k of λ where
          (N , e , c) →
            let open RoomEvents {rv64-frame-semantics} image using (ev-boot)
                boot = ev-boot N start-flat 0 refl _ refl
                agree₀ = events-agree-boot (proj₁ boot) ev-riscv64 env P′ start-flat X.initState _ _ (entry-corr P′)
                           (entry-wf 0) tt refl tb run₀ refl refl refl refl refl refl
                agree = retarget (proj₁ (proj₂ boot)) (proj₂ (proj₂ boot)) agree₀
            in budget-fact-of (run-of env (compile-trace P′)) ([] , X.initState) ι (runIR (arch-numerics riscv64) (pureHalf ι) q) k (proj₁ agree) _
                 -- (the run's events named, so they are matched, not computed)
                 (RTx.RunTrace.run-events val-riscv64 (answer-at (arch-numerics riscv64) ι call-at-riscv64) ev-riscv64 env [] (proj₁ agree) (compile-trace P′) X.initState) _
                 (RTx.Run.runN-events val-riscv64 (answer-at (arch-numerics riscv64) ι call-at-riscv64) ev-riscv64 env (compile-trace P′) (proj₁ agree) [] X.initState)
                 (cong (RTx.Run.outObs val-riscv64 (answer-at (arch-numerics riscv64) ι call-at-riscv64) ev-riscv64 env (compile-trace P′)) e)
                 c (proj₂ agree)
