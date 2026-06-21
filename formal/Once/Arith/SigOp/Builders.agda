-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.SigOp.Builders
--
-- SigOpInfo values for the arithmetic operations emitted by the
-- frontend elaborator (Surface.Elaborate).
--
-- For plan 0.2.4.1 Phase A, the semantic fields are **postulated**
-- — the goal of this phase is only to eliminate the omnibus
-- `defaultEvalSigOp` postulate in favor of per-SigOp semantics.
-- Plan 0.2.4.2 will make each `semI` / `semM` below definitional
-- (e.g. `add-semI (a,b) = a +ℤ b`) and replace these postulates
-- with proved correctness lemmas against x86-64 codegen.
--
-- String-literal handling is parallel to IntLit (see IntLit.agda):
-- `str-lit-info s` encodes the literal as a `SigOpInfo Unit Str`.
-- Semantics are postulated for now.
------------------------------------------------------------------------

module Once.Arith.SigOp.Builders where

open import Data.Integer using (ℤ)
import Data.Integer as ℤ
open import Data.Nat using (ℕ)
import Data.Nat as ℕ
open import Data.Product using (_,_)
open import Data.String using (String; _++_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)

open import Once.Type using (Type; Unit; Int; Str; _*_; _+_;
                              ArrowKind; mk-kind; Purity; pure; eff)
open import Once.SigOp.Info using (SigOpInfo; mk-info; EffectShape; Pure; Halts)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Word using (Carrier)
import Once.Semantics.Value Carrier as M
-- (Core ℤ `as I` removed: semI deleted — `semM` (ℕ/Word) is the meaning.)

------------------------------------------------------------------------
-- Arithmetic semantics
--
-- Plan 0.20 (2026-05-27): the four arith ops we extract into blocks
-- (add, sub, mul, neg) get their semI/semM definitionally. Recognition
-- lifts these into `arith.block.<digest>` SigOps for blocked use, but
-- per-op SigOps remain in the IR for cases recognition can't lift —
-- those need real semantics too.
--
-- semM convention (matches `Once.Arith.SigOp.IntLit`):
--   - `+` / `*` map to `ℕ._+_` / `ℕ._*_` directly.
--   - `-` maps to `ℕ._∸_` (monus, truncated to 0). This is conservative
--     and only accurate when `a ≥ b`. Honest ℕ semantics matching x86
--     two's-complement is the I-arith-cleanup item.
--   - `neg` on ℕ has no natural meaning; return `0` (consistent with
--     `0 ∸ z = 0` for any `z : ℕ`).
------------------------------------------------------------------------

-- Binary arithmetic — Int * Int → Int
add-semM : M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
add-semM (a , b) = a ℕ.+ b

sub-semM : M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
sub-semM (a , b) = a ℕ.∸ b

mul-semM : M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
mul-semM (a , b) = a ℕ.* b

-- Unary: Int → Int
neg-semM : M.⟦ Int ⟧ → M.⟦ Int ⟧
neg-semM _ = 0

------------------------------------------------------------------------
-- Postulated semantics (still placeholders — div/mod need a div-by-
-- zero policy, comparisons need a Bool encoding decision, generic-sem
-- is the unresolved-SigOp fallback).
------------------------------------------------------------------------

postulate
  -- Binary arithmetic with division-by-zero edge case still pending
  div-semM mod-semM : M.⟦ Int * Int ⟧ → M.⟦ Int ⟧

  -- Comparisons: Int * Int → (Unit + Unit) ≡ Bool
  lt-semM le-semM gt-semM ge-semM eq-semM ne-semM : M.⟦ Int * Int ⟧ → M.⟦ Unit + Unit ⟧

-- | String literal semantics. `M.⟦ Str ⟧ = String` (Semantics.Core), so a
-- string literal denotes ITSELF — concrete, no postulate. (The machine's
-- byte/pointer representation is a codegen concern, a different layer; the
-- denotational value is the string.)
str-lit-semM : String → M.⟦ Unit ⟧ → M.⟦ Str ⟧
str-lit-semM s _ = s

------------------------------------------------------------------------
-- SigOpInfo builders
------------------------------------------------------------------------

-- Binary arithmetic
add-info : SigOpInfo (Int * Int) Int
add-info = mk-info "arith.add.int" add-semM Pure

sub-info : SigOpInfo (Int * Int) Int
sub-info = mk-info "arith.sub.int" sub-semM Pure

mul-info : SigOpInfo (Int * Int) Int
mul-info = mk-info "arith.mul.int" mul-semM Pure

div-info : SigOpInfo (Int * Int) Int
div-info = mk-info "arith.div.int" div-semM Pure

mod-info : SigOpInfo (Int * Int) Int
mod-info = mk-info "arith.mod.int" mod-semM Pure

-- Unary arithmetic
neg-info : SigOpInfo Int Int
neg-info = mk-info "arith.neg.int" neg-semM Pure

-- Comparisons
lt-info : SigOpInfo (Int * Int) (Unit + Unit)
lt-info = mk-info "arith.lt.int" lt-semM Pure

le-info : SigOpInfo (Int * Int) (Unit + Unit)
le-info = mk-info "arith.le.int" le-semM Pure

gt-info : SigOpInfo (Int * Int) (Unit + Unit)
gt-info = mk-info "arith.gt.int" gt-semM Pure

ge-info : SigOpInfo (Int * Int) (Unit + Unit)
ge-info = mk-info "arith.ge.int" ge-semM Pure

eq-info : SigOpInfo (Int * Int) (Unit + Unit)
eq-info = mk-info "arith.eq.int" eq-semM Pure

ne-info : SigOpInfo (Int * Int) (Unit + Unit)
ne-info = mk-info "arith.ne.int" ne-semM Pure

-- String literal family
str-lit-info : String → SigOpInfo Unit Str
str-lit-info s = mk-info ("lit.str." ++ s) (str-lit-semM s) Pure

------------------------------------------------------------------------
-- Generic placeholder for unresolved / user-imported SigOps
--
-- Used by Surface.Elaborate for legacy `sigOp name` and `poly name`
-- forms whose SigOpInfo is not yet known at elaboration time.
-- Phase D (external syscalls) and a future registry-lookup phase will
-- replace these placeholders with concrete SigOpInfos.
------------------------------------------------------------------------

-- | The opaque value of a SigOp referenced as a NAMED PURE VALUE — a
-- `closure`/`poly`/non-arrow `sigOp`, a separately-linked function whose
-- value Once does not inline (function-linking opacity). This is the ONLY
-- surviving `generic-semM` position: an EFFECTFUL op carries a contract,
-- not a value (`SigOpSem.emitsV`/`haltsV`), so this can no longer launder a
-- syscall's value. (Eliminating it too — sourcing closure/poly values from
-- the module environment — is a separate axis, the deferred follow-on.)
postulate
  generic-semM : ∀ {A B} → String → M.⟦ A ⟧ → M.⟦ B ⟧

-- | A SigOp referenced as a VALUE — at non-arrow type, or as a `closure` /
-- `poly` reference. Its effect is `Pure`: an effect lives on an *arrow*
-- (realized only on application, D018 suspended-Eff), so a bare value
-- reference emits nothing at build. INTERPRETATION-AGNOSTIC — no
-- effect-from-name guess. Plan 0.38 M0.2: `classify-name` (the
-- exit-syscall → Halts string match) is RETIRED; an external arrow's effect
-- now comes from its DECLARED `! <shape>`, built at the elaborate site
-- (`ext-arrow-info` in `TypeCheck.Elaborate`).
value-info : ∀ {A B} → String → SigOpInfo A B
value-info name = mk-info name (generic-semM name) Pure

-- | Compat shims for the surface/meaning sites (`Surface.Desugar`,
-- `Surface.Elaborate`, `Denotation.SourceDenote`) that still name these.
-- Surface `sigOp`/`closure`/`poly` are value positions ⇒ `Pure`; a surface
-- *arrow* `sigOp` is unreachable at Layer 0 (external `Eff` arrows are
-- `Many` and take the qualified-ref IR path in `TypeCheck.Elaborate`,
-- where the declared shape is read), so `arrow-info` is `value-info` too.
-- Keeping the names (vs. inlining) avoids churning those three modules and
-- keeps `faithful` definitionally `refl` (both presentations use the same
-- shim).
generic-info : ∀ {A B} → String → SigOpInfo A B
generic-info = value-info

arrow-info : ∀ {A B} → ArrowKind → String → SigOpInfo A B
arrow-info _ name = value-info name
