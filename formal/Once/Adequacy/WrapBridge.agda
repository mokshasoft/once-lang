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
open import Once.Denotation.TraceMonad using (_>>=T_; projTrace; stoppedT; Stopped; join-es)

EffUU : _
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- The entry-wrap trace = the closure-application run trace, pointwise in `n`.
wrap-trace : ∀ (X : IR ⌊ Unit ⌋ ⌊ EffUU ⌋) (n : ℕ) →
  projTrace (evalᴰ fmt (C.wrapMainAsEntry X) tt) n
  ≡ projTrace (evalᴰ fmt X tt >>=T (λ clo → clo tt)) n
-- plan 0.97: the wrap's trace is a `join-es` now, so the `++ []` that
-- `++-identityʳ` removed only appears on the not-stopped branch — and on the
-- stopped one `join-es true es _` IS `es`, with nothing to remove. Split.
-- plan 0.97: the wrap's trace is a `join-es` now, so the `++ []` the
-- pair-build leaves only appears on the branch where `X` did NOT stop; on the
-- stopped branch `join-es true es _` IS `es` and there is nothing to remove.
-- The boolean comes in with its own equation so both `join-es` and `join-st`
-- reduce inside each branch.
wrap-trace X n = go (stoppedT (evalᴰ fmt X tt) n) refl
  where
    go : ∀ (b : Stopped) → stoppedT (evalᴰ fmt X tt) n ≡ b
       → projTrace (evalᴰ fmt (C.wrapMainAsEntry X) tt) n
         ≡ projTrace (evalᴰ fmt X tt >>=T (λ clo → clo tt)) n
    go false q rewrite q | ++-identityʳ (projTrace (evalᴰ fmt X tt) n) = refl
    go true  q rewrite q = refl
