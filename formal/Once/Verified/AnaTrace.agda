-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.AnaTrace — the PRODUCTIVE simulation for `ana` (Plan 0.46).
--
-- This is the corecursive counterpart of the finite bridge (`ElaborateTrace`):
-- the denotational `evalᴰ`-trace of an anamorphism (`ana-events`, the
-- depth-bounded unfold) agrees, EVENT-PREFIX-wise, with the operational
-- `SS.eval` unfold (`anaUnfold`) at SOME fuel. This is the genuine `∀k → ∃s`
-- form — the trace GROWS with the observation depth `k` (productive), matched
-- by a larger operational fuel `s`. (The finite bridge's terminating `CompSim`
-- can't express this; that is why `ana` gets its own sim, per the apex's
-- already-productive `elaborate-trace-correct`.)
--
-- It discharges the `ana` case of `elaborate-trace-correct`; the `νF` value is
-- NOT observed (we read the SigOp trace), so no value relation is needed.
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
open import Once.Verified.DenotTrace using (ana-events)
open import Once.Verified.SourceSemantics
  using (Value; Defs; Result; runTraceEval; anaUnfold)

module _ (defs : Defs) where

  -- THE PRODUCTIVE CORRESPONDENCE. At observation depth `k`, the denotational
  -- ana-trace prefix equals the operational unfold's trace prefix at some fuel
  -- `s`. (`coalgD`/`coalgV` are the denotational IR coalgebra and its operational
  -- Value; `a`/`av` the corresponding seeds.) Proven by induction on `k`.
  --
  -- BASE (`k = 0`): both prefixes are `[]` — `take 0` of anything, and
  -- `ana-events … 0 = []`. So any fuel works (`s = 0`).
  --
  -- STEP (`k = suc k'`): `ana-events … (suc k') = (one coalgebra step's events at
  -- depth k') ++ (events-F: recursive unfolds at depth k')`; `anaUnfold (suc s')
  -- = (apply coalgV's events) ++ (mapAnaF: recursive unfolds)`. The two match by:
  -- (a) the coalgebra step corresponds (`evalᴰ coalgD` ↔ `apply coalgV`, the
  -- finite bridge IH — a coalgebra `A → F(A)` is one finite step); (b) the
  -- functor-walk corresponds (`events-F F` ↔ `mapAnaF F`, both recursing over
  -- `F`'s `Id` positions); (c) the depth IH on `k'`. NAMED hole until those three
  -- are assembled.
  postulate
    ana-trace-step :
      ∀ {F : Functor} {A : Type} (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value)
        (a : Val.⟦ A ⟧) (av : Value) (k : ℕ)
      → ∃[ s ] take (suc k) (ana-events {F} {A} coalgD a (suc k))
                 ≡ take (suc k) (runTraceEval (anaUnfold s defs F coalgV av))

  ana-trace-correct :
    ∀ {F : Functor} {A : Type} (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value)
      (a : Val.⟦ A ⟧) (av : Value) (k : ℕ)
    → ∃[ s ] take k (ana-events {F} {A} coalgD a k)
               ≡ take k (runTraceEval (anaUnfold s defs F coalgV av))
  ana-trace-correct coalgD coalgV a av zero    = zero , refl
  ana-trace-correct coalgD coalgV a av (suc k) = ana-trace-step coalgD coalgV a av k
