-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.StatePreserve  (Plan 0.54 Phase B / Option 2)
--
-- Unify register- and memory-preservation into ONE `State`-level property over
-- the real `X64.State`: the arith subroutine preserves CCC STATE = it agrees on
-- the 7 CCC registers AND on all memory at/above the entry `%sp` frontier.
--
-- Both halves compose (transitively), so a whole arith block — a sequence of
-- steps each writing only non-`ccc` registers and only scratch (`< sp`) —
-- preserves CCC state. This is the concrete-machine statement the apex needs;
-- what remains is the per-instruction step semantics (`exec-arith-instr`) filling
-- in that each step is exactly such a write, plus the whole-program dispatch.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.StatePreserve where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.CCC.Target.RiscV64.Semantics using (State; RegFile; Memory; Word)
open State
open import Once.Arith.Backend.RiscV64.Preserve using (AgreeCCC; agree-refl-ccc; AgreeCCC-trans)
open import Once.Arith.Backend.RiscV64.MemPreserve using (AgreeMemFrom)

------------------------------------------------------------------------
-- Memory-region agreement is reflexive and transitive.
------------------------------------------------------------------------

AgreeMemFrom-refl : ∀ fr m → AgreeMemFrom fr m m
AgreeMemFrom-refl fr m a _ = refl

AgreeMemFrom-trans : ∀ {fr m₁ m₂ m₃} →
                     AgreeMemFrom fr m₁ m₂ → AgreeMemFrom fr m₂ m₃ → AgreeMemFrom fr m₁ m₃
AgreeMemFrom-trans p q a fr≤a = trans (p a fr≤a) (q a fr≤a)

------------------------------------------------------------------------
-- CCC-state preservation: agree on the 7 CCC registers AND on memory ≥ frontier.
------------------------------------------------------------------------

record PreservesCCCState (fr : Word) (s s' : State) : Set where
  constructor mkPresState
  field
    regs≈ : AgreeCCC   (regs s)   (regs s')
    mem≈  : AgreeMemFrom fr (memory s) (memory s')
open PreservesCCCState public

preserves-state-refl : ∀ fr s → PreservesCCCState fr s s
preserves-state-refl fr s = mkPresState (agree-refl-ccc (regs s)) (AgreeMemFrom-refl fr (memory s))

preserves-state-trans : ∀ {fr s₁ s₂ s₃} →
                        PreservesCCCState fr s₁ s₂ → PreservesCCCState fr s₂ s₃ →
                        PreservesCCCState fr s₁ s₃
preserves-state-trans (mkPresState r1 m1) (mkPresState r2 m2) =
  mkPresState (AgreeCCC-trans r1 r2) (AgreeMemFrom-trans m1 m2)
