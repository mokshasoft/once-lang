-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.FlatSim
--
-- Plan 0.32 machine-side: the fuel-induction that lifts the per-instruction
-- `block-step` lemmas (FlatSimulation) over a WHOLE flat program into the
-- top-level abstract↔x86 plus-simulation `flat-sim`. This is the
-- correspondence that actually runs the loop — the replacement for
-- DirectSimulation.trace-sim.
--
--   flat-sim : … → CompiledCorr prog fs s
--     → ∃ m s'. X.exec m (compile-trace prog) s ≡ just s'
--              × CompiledCorr prog (exec-flat fuel prog fs) s'
--
-- One flat step ↦ a contiguous x86 block (NOT 1-to-1 lockstep), chained by
-- `exec-just-compose` on the x86 fuel and `exec-flat-step` on the flat side.
--
-- The induction takes three CLEARLY-PROVABLE inputs as hypotheses
-- (Plan 0.32 minimal swap path), to be discharged separately:
--   * block-step-all : the per-instruction dispatcher (block-step lemmas
--     are done for the cata instructions; alloc-heap/stack-ops deferred —
--     0.35 M6 / mechanical).
--   * flat-no-halt   : a fetched compiled instruction never halts the flat
--     machine (it halts only by running off the end).
--   * end-corr       : at end-of-program the x86 machine halts in
--     correspondence (the `fetch ≡ nothing` boundary).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.CCC.Target.X86-64.FlatSim
  (FS : FrameSemantics)
  (enc-hl : HeapLocation → ℕ)
  (enc-hl-inj : ∀ {a b : HeapLocation} → enc-hl a ≡ enc-hl b → a ≡ b)
  (enc-hl-suc : ∀ (hl : HeapLocation) → enc-hl (sucHL hl) ≡ enc-hl hl + slot-size)
  where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; subst)

open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace)
open import Once.CCC.Target.X86-64.FlatComposition FS using (x86-len)
open import Once.CCC.Target.X86-64.ExecCompose using (exec-just-compose)
open import Once.CCC.Target.X86-64.FlatSimulation FS enc-hl enc-hl-inj enc-hl-suc
  using (CompiledCorr; BlockStep; dataCorr; pc-off)
import Once.CCC.Target.X86-64.FlatCorrespondence as FC
module C = FC FS enc-hl enc-hl-inj

------------------------------------------------------------------------
-- The simulation goal: the flat final state after `fuel` steps corresponds
-- to SOME x86 execution from `s`.
------------------------------------------------------------------------
FlatSimGoal : AbstractTrace → FlatState → ℕ → X.State → Set
FlatSimGoal prog fs fuel s =
  ∃[ m ] ∃[ s' ] (X.exec m (compile-trace prog) s ≡ just s'
               × CompiledCorr prog (exec-flat fuel prog fs) s')

------------------------------------------------------------------------
-- Clearly-provable inputs (Plan 0.32 minimal swap path).
------------------------------------------------------------------------
BlockStepAll : AbstractTrace → Set
BlockStepAll prog = ∀ (fs : FlatState) (s : X.State) (i : AbstractInstr)
  → CompiledCorr prog fs s → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just i
  → BlockStep prog fs s i

FlatNoHalt : AbstractTrace → Set
FlatNoHalt prog = ∀ (fs : FlatState) (i : AbstractInstr)
  → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just i
  → halted (floc (flat-exec-instr i prog fs)) ≡ false

EndCorr : AbstractTrace → Set
EndCorr prog = ∀ (fs : FlatState) (s : X.State)
  → CompiledCorr prog fs s → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ nothing
  → ∃[ m ] ∃[ s' ] (X.exec m (compile-trace prog) s ≡ just s'
                 × CompiledCorr prog (record fs { floc = record (floc fs) { halted = true } }) s')

------------------------------------------------------------------------
-- The fuel induction.
------------------------------------------------------------------------
flat-sim : ∀ (prog : AbstractTrace)
  → BlockStepAll prog → FlatNoHalt prog → EndCorr prog
  → ∀ (fuel : ℕ) (fs : FlatState) (s : X.State)
  → CompiledCorr prog fs s
  → FlatSimGoal prog fs fuel s
-- The `with halted … | fetch …` matches reduce `exec-flat (suc n) prog fs`
-- in the goal (step-dispatch/fetch-dispatch), so each branch's CompiledCorr
-- already has the right index — no transport needed.
flat-sim prog bsa fnh ec zero fs s cc = 0 , s , refl , cc
flat-sim prog bsa fnh ec (suc n) fs s cc with halted (floc fs) in hf
... | true = 0 , s , refl , cc
... | false with fetch prog (fpc fs) in ft
...   | nothing = ec fs s cc hf ft
...   | just i =
  let s''        = proj₁ bs
      exec-eq''  = proj₁ (proj₂ bs)
      cc''       = proj₂ (proj₂ bs)
      nonhalt''  = trans (C.halt-eq (dataCorr cc'')) (fnh fs i hf ft)
      m' , s' , exec-eq' , cc' = flat-sim prog bsa fnh ec n (flat-exec-instr i prog fs) s'' cc''
      composed   = trans (exec-just-compose (compile-trace prog) (x86-len i) m' exec-eq'' nonhalt'')
                         exec-eq'
  in x86-len i + m' , s' , composed , cc'
  where
    bs = bsa fs s i cc hf ft
