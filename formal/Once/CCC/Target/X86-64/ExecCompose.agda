-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.ExecCompose
--
-- Plan 0.32 machine-side: fuel composition for `Semantics.exec`.
--
-- The per-instruction `block-step` lemmas (FlatSimulation) produce the
-- form `exec (x86-len i) prog s ≡ just s'` for an x86 BLOCK. To lift them
-- over the whole program by fuel-induction we must CHAIN such blocks:
--
--   exec-just-compose : exec a prog s ≡ just s' → halted s' ≡ false
--                     → exec (a + b) prog s ≡ exec b prog s'
--
-- This is the `exec ≡ just` counterpart of StepLemmas.exec-steps (which
-- chains `Steps` evidence). `halted s' ≡ false` rules out an early halt —
-- if `exec a` had halted before `a` steps, its result would be a halted
-- state, contradicting the hypothesis — so all `a` steps were genuine and
-- the tail picks up exactly at `s'`.
--
-- with-free helpers reduce `exec (suc n)` under the three decisions
-- (halted / step-not-halted / next halted), each by `rewrite`.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.ExecCompose where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.Target.X86-64.Syntax using (Program)
import Once.CCC.Target.X86-64.Semantics as X
open X using (State; mkstate; exec; step-not-halted)
open X.State using (halted)

private
  just-inj : ∀ {s s' : State} → (just s) ≡ (just s') → s ≡ s'
  just-inj refl = refl

  false≢true : false ≡ true → ⊥
  false≢true ()

  nothing≢just : ∀ {s' : State} → nothing ≡ just s' → ⊥
  nothing≢just ()

-- KEY: the `suc` clause matches the State as `mkstate … h` so `halted s` is
-- a literal and `exec (suc n)` reduces WITHOUT eta-expanding `s` inside
-- `just s` (the trap that defeats a `subst`/`cong` over abstract `halted s`).
-- The `with … in` abstractions then reduce `eq` itself in each branch
-- (nothing ⇒ `nothing ≡ just s'`; just/true ⇒ `just s'' ≡ just s'`;
-- just/false ⇒ `exec a P s'' ≡ just s'`), so no further reduction lemmas.
exec-just-compose : ∀ (P : Program) a {s s' : State} (b : ℕ)
  → exec a P s ≡ just s'
  → halted s' ≡ false
  → exec (a + b) P s ≡ exec b P s'
exec-just-compose P zero {s} {s'} b eq hf =
  cong (λ z → exec b P z) (just-inj eq)
exec-just-compose P (suc a) {mkstate rg mm fl pc true}  {s'} b eq hf =
  -- halted ⇒ exec ≡ just s ⇒ s ≡ s' ⇒ halted s' ≡ true, contradicting hf.
  ⊥-elim (false≢true (trans (sym hf) (cong halted (sym (just-inj eq)))))
exec-just-compose P (suc a) {mkstate rg mm fl pc false} {s'} b eq hf
  with step-not-halted P (mkstate rg mm fl pc false) in snh
... | nothing = ⊥-elim (nothing≢just eq)
... | just s'' with halted s'' in hs''
...   | true =
  ⊥-elim (false≢true (trans (sym hf) (trans (cong halted (sym (just-inj eq))) hs'')))
  -- the `with` substitutions already reduced the goal's LHS to
  -- `exec (a + b) P s''`, so the goal IS exactly the IH.
...   | false = exec-just-compose P a b eq hf
