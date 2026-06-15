-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.AnaTrace — the PRODUCTIVE simulation for `ana` (Plan 0.46).
--
-- The corecursive counterpart of the finite bridge: the denotational
-- `evalᴰ`-trace of an anamorphism (`ana-events`, depth-bounded unfold) agrees,
-- EVENT-PREFIX-wise, with the operational `SS.eval` unfold (`anaUnfold`) at SOME
-- fuel. Genuine `∀k → ∃s`: the trace GROWS with the observation depth `k`,
-- matched by a larger operational fuel. Discharges the `ana` case of
-- `elaborate-trace-correct`.
--
-- WHY TAKE-BASED, NOT FULL EQUALITY (lesson, 2026-06-15): an earlier draft tried
-- to decompose the step via a `functor-walk` claiming `mapAnaF`'s trace equals
-- `events-F` FULLY (∀ fuel). That is FALSE: at an `Id` position `mapAnaF s` is
-- `anaUnfold s`, whose trace GROWS with the fuel `s`, while `events-F` is the
-- fixed depth-`k` trace. The operational fuel ≠ the denotational depth, so the
-- two agree only on the OBSERVED PREFIX (`take`). Hence the relation is
-- `∃ s, take k … ≡ take k …`, and the inductive step is a genuine prefix
-- simulation (the hard core, kept as ONE honest postulate below — NOT a
-- full-equality functor-walk).
--
-- It also needs the coalgebra+seed CORRESPONDENCE (`CoalgSeedCorr`): for
-- UNRELATED `coalgD`/`coalgV` or `a`/`av` the unfolds are unrelated, so the
-- statement is false without it. `CoalgSeedCorr` is abstract here; its concrete
-- definition is the bridge's value-sim at the coalgebra `A → F(A)` together with
-- the seed value-sim (to be supplied when wiring into `elaborate-trace-correct`).
------------------------------------------------------------------------

module Once.Verified.AnaTrace where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; take)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Functor; ⟦_⟧T)
open import Once.CCC.IR using (IR)
open import Once.CCC.Eval as Val using ()
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.DenotTrace using (ana-events; evalᴰ; inject)
open import Once.Verified.SourceSemantics
  using (Value; Defs; Result; runTraceEval; anaUnfold; apply)
import Once.Verified.ElaborateTrace as ET

module _ (defs : Defs) where

  -- The coalgebra + seed correspondence, CONCRETE: the coalgebra `A → F(A)` is a
  -- FINITE morphism, so its correspondence is exactly the finite bridge's CompSim
  -- at the coalgebra — `evalᴰ coalgD` (denotationally, from the seed) simulates
  -- `apply coalgV` (operationally). Its value-sim component sits at `⟦F⟧T A`, which
  -- IS the per-layer correspondence the unfold recursion consumes (it recurses the
  -- type structure of `F`, relating seeds at the `Id`/`A` positions). The seed
  -- relation is folded in via the closed coalgebra applied to `inject a` / `av`.
  CoalgSeedCorr :
    ∀ {F : Functor} {A : Type} → IR A (⟦ F ⟧T A) → Value → Val.⟦ A ⟧ → Value → Set
  CoalgSeedCorr {F} {A} coalgD coalgV a av =
    ET.CompSim defs (⟦ F ⟧T A) (evalᴰ coalgD (inject a)) (λ s → apply s defs coalgV av)

  postulate
    -- THE PRODUCTIVE INDUCTIVE STEP — the genuine hard core. Given the operands
    -- correspond, at depth `suc k` the take-`(suc k)` event prefixes agree at SOME
    -- operational fuel `s`. TAKE-based (the operational fuel ≠ the denotational
    -- depth; the traces agree only on the observed prefix). Proof = a prefix
    -- simulation threading `take` through one unfold layer (coalgebra step +
    -- functor-recursive unfolds) and the depth IH — still open.
    ana-trace-step :
      ∀ {F : Functor} {A : Type} (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value)
        (a : Val.⟦ A ⟧) (av : Value) (k : ℕ)
      → CoalgSeedCorr {F} {A} coalgD coalgV a av
      → ∃[ s ] take (suc k) (ana-events {F} {A} coalgD a (suc k))
                 ≡ take (suc k) (runTraceEval (anaUnfold s defs F coalgV av))

  -- THE PRODUCTIVE CORRESPONDENCE. `∀k∃s`, conditional on the correspondence.
  -- Base (k=0): both prefixes are `take 0 _ = []`. Step: `ana-trace-step`.
  ana-trace-correct :
    ∀ {F : Functor} {A : Type} (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value)
      (a : Val.⟦ A ⟧) (av : Value) (k : ℕ)
    → CoalgSeedCorr {F} {A} coalgD coalgV a av
    → ∃[ s ] take k (ana-events {F} {A} coalgD a k)
               ≡ take k (runTraceEval (anaUnfold s defs F coalgV av))
  ana-trace-correct coalgD coalgV a av zero    cc = zero , refl
  ana-trace-correct coalgD coalgV a av (suc k) cc = ana-trace-step coalgD coalgV a av k cc
