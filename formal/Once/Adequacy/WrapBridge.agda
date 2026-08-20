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

open import Once.Float.Dyadic using (FloatFormat)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.WrapBridge (fmt : FloatFormat) where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import Once.Type using (Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.Compile as C
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.TraceMonad using (_>>=T_; projTrace)

EffUU : _
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- The entry-wrap trace = the closure-application run trace, pointwise in `n`.
wrap-trace : ∀ (X : IR ⌊ Unit ⌋ ⌊ EffUU ⌋) (n : ℕ) →
  projTrace (evalᴰ fmt (C.wrapMainAsEntry X) tt) n
  ≡ projTrace (evalᴰ fmt X tt >>=T (λ clo → clo tt)) n
wrap-trace X n =
  cong (_++ proj₁ (proj₂ (evalᴰ fmt X tt n) tt n))
       (++-identityʳ (proj₁ (evalᴰ fmt X tt n)))
