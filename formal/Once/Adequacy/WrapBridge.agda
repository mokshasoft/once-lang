-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.WrapBridge — the `maybeWrapMain` denotation lemma
-- (Plan 0.49 Phase 1, part of `sd-bridge`).
--
-- `wrapMainAsEntry X = apply ∘ ⟨ X , terminal ⟩ Stack` is the entry wrapper
-- that RUNS the `Eff Unit Unit` action `X` by applying it to the Unit input.
-- Its denotational trace equals that of binding `evalᴰ X` and applying the
-- resulting closure to `tt` — i.e. the IR-level entry application traces the
-- same as the denotational closure application. By the `evalᴰ` clauses for
-- `∘`/`⟨,⟩`/`terminal`/`apply` the two sides differ only by a trailing
-- `++ []` (the `terminal` component emits nothing), discharged by
-- `++-identityʳ`. No monad laws beyond right-identity of `_++_` are needed.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.WrapBridge (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Once.Type using (Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.Compile as C
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace)
open import Once.Res using (Res; stopped; returns)

EffUU : _
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- The entry-wrap trace = the closure-application run trace, pointwise in `n`.
wrap-trace : ∀ (X : IR ⌊ Unit ⌋ ⌊ EffUU ⌋) (n : ℕ) →
  projTrace (evalᴰ fmt (C.wrapMainAsEntry X) tt) n
  ≡ projTrace (evalᴰ fmt X tt >>=T (λ clo → clo tt)) n
-- plan 0.98: the split is on `X`'s RESULT. The pair-build's `++ []` only
-- exists on the branch where `X` RETURNED a closure — on the stopped branch
-- the pair was never built, so there is nothing to remove and the equation is
-- `refl`. (0.97 split on a boolean and got the same two branches for a
-- different reason: there the sequel WAS built and then discarded.)
wrap-trace X n = go refl
  where
    go : ∀ {r} → T.resT (evalᴰ fmt X tt) ≡ r
       → projTrace (evalᴰ fmt (C.wrapMainAsEntry X) tt) n
         ≡ projTrace (evalᴰ fmt X tt >>=T (λ clo → clo tt)) n
    go {stopped}   q rewrite q = refl
    go {returns v} q rewrite q | ++-identityʳ (projTrace (evalᴰ fmt X tt) n) = refl
