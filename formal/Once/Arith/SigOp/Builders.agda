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

open import Once.Type using (Type; Unit; Int; Str; _*_; _+_)
open import Once.CCC.SigOp.Info using (SigOpInfo; mk-info)

import Once.Semantics.Core ℤ as I
import Once.Semantics.Core ℕ as M

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
add-semI : I.⟦ Int * Int ⟧ → I.⟦ Int ⟧
add-semI (a , b) = a ℤ.+ b

sub-semI : I.⟦ Int * Int ⟧ → I.⟦ Int ⟧
sub-semI (a , b) = a ℤ.- b

mul-semI : I.⟦ Int * Int ⟧ → I.⟦ Int ⟧
mul-semI (a , b) = a ℤ.* b

add-semM : M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
add-semM (a , b) = a ℕ.+ b

sub-semM : M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
sub-semM (a , b) = a ℕ.∸ b

mul-semM : M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
mul-semM (a , b) = a ℕ.* b

-- Unary: Int → Int
neg-semI : I.⟦ Int ⟧ → I.⟦ Int ⟧
neg-semI z = ℤ.- z

neg-semM : M.⟦ Int ⟧ → M.⟦ Int ⟧
neg-semM _ = 0

------------------------------------------------------------------------
-- Postulated semantics (still placeholders — div/mod need a div-by-
-- zero policy, comparisons need a Bool encoding decision, generic-sem
-- is the unresolved-SigOp fallback).
------------------------------------------------------------------------

postulate
  -- Binary arithmetic with division-by-zero edge case still pending
  div-semI mod-semI : I.⟦ Int * Int ⟧ → I.⟦ Int ⟧
  div-semM mod-semM : M.⟦ Int * Int ⟧ → M.⟦ Int ⟧

  -- Comparisons: Int * Int → (Unit + Unit) ≡ Bool
  lt-semI le-semI gt-semI ge-semI eq-semI ne-semI : I.⟦ Int * Int ⟧ → I.⟦ Unit + Unit ⟧
  lt-semM le-semM gt-semM ge-semM eq-semM ne-semM : M.⟦ Int * Int ⟧ → M.⟦ Unit + Unit ⟧

  -- String literal semantics (the value is the string; type ⟦Str⟧ is
  -- abstract at both layers).
  str-lit-semI : String → I.⟦ Unit ⟧ → I.⟦ Str ⟧
  str-lit-semM : String → M.⟦ Unit ⟧ → M.⟦ Str ⟧

------------------------------------------------------------------------
-- SigOpInfo builders
------------------------------------------------------------------------

-- Binary arithmetic
add-info : SigOpInfo (Int * Int) Int
add-info = mk-info "arith.add.int" add-semI add-semM

sub-info : SigOpInfo (Int * Int) Int
sub-info = mk-info "arith.sub.int" sub-semI sub-semM

mul-info : SigOpInfo (Int * Int) Int
mul-info = mk-info "arith.mul.int" mul-semI mul-semM

div-info : SigOpInfo (Int * Int) Int
div-info = mk-info "arith.div.int" div-semI div-semM

mod-info : SigOpInfo (Int * Int) Int
mod-info = mk-info "arith.mod.int" mod-semI mod-semM

-- Unary arithmetic
neg-info : SigOpInfo Int Int
neg-info = mk-info "arith.neg.int" neg-semI neg-semM

-- Comparisons
lt-info : SigOpInfo (Int * Int) (Unit + Unit)
lt-info = mk-info "arith.lt.int" lt-semI lt-semM

le-info : SigOpInfo (Int * Int) (Unit + Unit)
le-info = mk-info "arith.le.int" le-semI le-semM

gt-info : SigOpInfo (Int * Int) (Unit + Unit)
gt-info = mk-info "arith.gt.int" gt-semI gt-semM

ge-info : SigOpInfo (Int * Int) (Unit + Unit)
ge-info = mk-info "arith.ge.int" ge-semI ge-semM

eq-info : SigOpInfo (Int * Int) (Unit + Unit)
eq-info = mk-info "arith.eq.int" eq-semI eq-semM

ne-info : SigOpInfo (Int * Int) (Unit + Unit)
ne-info = mk-info "arith.ne.int" ne-semI ne-semM

-- String literal family
str-lit-info : String → SigOpInfo Unit Str
str-lit-info s = mk-info ("lit.str." ++ s) (str-lit-semI s) (str-lit-semM s)

------------------------------------------------------------------------
-- Generic placeholder for unresolved / user-imported SigOps
--
-- Used by Surface.Elaborate for legacy `sigOp name` and `poly name`
-- forms whose SigOpInfo is not yet known at elaboration time.
-- Phase D (Linux syscalls) and a future registry-lookup phase will
-- replace these placeholders with concrete SigOpInfos.
------------------------------------------------------------------------

postulate
  generic-semI : ∀ {A B} → String → I.⟦ A ⟧ → I.⟦ B ⟧
  generic-semM : ∀ {A B} → String → M.⟦ A ⟧ → M.⟦ B ⟧

generic-info : ∀ {A B} → String → SigOpInfo A B
generic-info name = mk-info name (generic-semI name) (generic-semM name)
