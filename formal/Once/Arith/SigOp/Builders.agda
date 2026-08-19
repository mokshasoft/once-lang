-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
                              ArrowKind; mk-kind; Purity; pure; eff; isUnit?)
open import Relation.Nullary using (Dec; yes; no)
open import Once.SigOp.Info using (SigOpInfo; mk-info; mk-info'; pureV; emitsV; EffectShape; Pure; Halts; Linkage; ffi-concrete; internal-ref)
open import Once.Functor.Translate using (IsBaseType; IsConcrete; con-base;
  base-Unit; base-Int; base-Str; base-Prod; base-Sum)
open import Once.CanonicalName using (CanonicalName; bare; showCanonical)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
import Once.Semantics.Value Carrier Carrier as M
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
-- string literal denotes ITSELF — a concrete definition. (The machine's
-- byte/pointer representation is a codegen concern, a different layer; the
-- denotational value is the string.)
str-lit-semM : String → M.⟦ Unit ⟧ → M.⟦ Str ⟧
str-lit-semM s _ = s

------------------------------------------------------------------------
-- SigOpInfo builders
------------------------------------------------------------------------

-- Concreteness witnesses for the internal arith SigOp types (all base). The
-- domain is `IsBaseType`; the codomain is `IsConcrete` (here always `con-base`).
base-I×I : IsBaseType (Int * Int)
base-I×I = base-Prod base-Int base-Int
con-Int : IsConcrete Int
con-Int = con-base base-Int
con-U+U : IsConcrete (Unit + Unit)
con-U+U = con-base (base-Sum base-Unit base-Unit)

-- Binary arithmetic
add-info : SigOpInfo (Int * Int) Int
add-info = mk-info (bare "arith.add.int") add-semM Pure base-I×I con-Int

sub-info : SigOpInfo (Int * Int) Int
sub-info = mk-info (bare "arith.sub.int") sub-semM Pure base-I×I con-Int

mul-info : SigOpInfo (Int * Int) Int
mul-info = mk-info (bare "arith.mul.int") mul-semM Pure base-I×I con-Int

div-info : SigOpInfo (Int * Int) Int
div-info = mk-info (bare "arith.div.int") div-semM Pure base-I×I con-Int

mod-info : SigOpInfo (Int * Int) Int
mod-info = mk-info (bare "arith.mod.int") mod-semM Pure base-I×I con-Int

-- Unary arithmetic
neg-info : SigOpInfo Int Int
neg-info = mk-info (bare "arith.neg.int") neg-semM Pure base-Int con-Int

-- Comparisons
lt-info : SigOpInfo (Int * Int) (Unit + Unit)
lt-info = mk-info (bare "arith.lt.int") lt-semM Pure base-I×I con-U+U

le-info : SigOpInfo (Int * Int) (Unit + Unit)
le-info = mk-info (bare "arith.le.int") le-semM Pure base-I×I con-U+U

gt-info : SigOpInfo (Int * Int) (Unit + Unit)
gt-info = mk-info (bare "arith.gt.int") gt-semM Pure base-I×I con-U+U

ge-info : SigOpInfo (Int * Int) (Unit + Unit)
ge-info = mk-info (bare "arith.ge.int") ge-semM Pure base-I×I con-U+U

eq-info : SigOpInfo (Int * Int) (Unit + Unit)
eq-info = mk-info (bare "arith.eq.int") eq-semM Pure base-I×I con-U+U

ne-info : SigOpInfo (Int * Int) (Unit + Unit)
ne-info = mk-info (bare "arith.ne.int") ne-semM Pure base-I×I con-U+U

-- String literal family
str-lit-info : String → SigOpInfo Unit Str
str-lit-info s = mk-info (bare ("lit.str." ++ s)) (str-lit-semM s) Pure base-Unit (con-base base-Str)

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
value-info : ∀ {A B} → CanonicalName → IsBaseType A → IsConcrete B → SigOpInfo A B
value-info name bA cB = mk-info name (generic-semM (showCanonical name)) Pure bA cB

-- | Plan 0.58 / D071: a SAME-MODULE definition reference (`closure`/`poly`)
-- as an internal-linkage value. Domain is `Unit` (the closure-returner ABI
-- calls `once_<name>()`); the result type `A` is UNCONSTRAINED — an internal
-- reference is a code/closure pointer, representable at ANY type, so it carries
-- NO concreteness witness (`internal-ref` linkage). This is the value-position
-- twin of `value-info` for internal refs: same `Pure`/`generic-semM` shape (so
-- `faithful` stays `refl`), but no FFI concreteness gate — the fix for the
-- non-concrete `cata`/closure reference wall (D071).
internal-info : ∀ {A} → CanonicalName → SigOpInfo Unit A
internal-info name = mk-info' name (pureV (generic-semM (showCanonical name))) base-Unit internal-ref

-- | Compat shims for the surface/meaning sites (`Surface.Desugar`,
-- `Surface.Elaborate`, `Denotation.SourceDenote`) that still name these.
-- Surface `sigOp`/`closure`/`poly` are value positions ⇒ `Pure`; a surface
-- *arrow* `sigOp` is unreachable at Layer 0 (external `Eff` arrows are
-- `Many` and take the qualified-ref IR path in `TypeCheck.Elaborate`,
-- where the declared shape is read), so `arrow-info` is `value-info` too.
-- Keeping the names (vs. inlining) avoids churning those three modules and
-- keeps `faithful` definitionally `refl` (both presentations use the same
-- shim).
generic-info : ∀ {A B} → CanonicalName → IsBaseType A → IsConcrete B → SigOpInfo A B
generic-info = value-info

-- The effect is a LEAF annotation read off the arrow's `Purity` (the only
-- effect bit the OBSERVABLE TRACE sees — `emit-D` collapses `Emits`/`Halts` to
-- the same event, distinguishing only pure-vs-effectful). So a `pure` arrow is
-- a pure value; an `eff` arrow with `Unit` codomain emits (an effect contract);
-- an `eff` non-`Unit` arrow is the deferred-data case (a pure value). The
-- `emits`-vs-`halts` refinement is codegen-only and never needs to reach here
-- or `realize` — it stays in the typing context. (Plan 0.50 effect-axis: a
-- referenced morphism's effect is intrinsic to its arrow, not a name lookup.)
-- Dispatch the `eff` codomain check through the shared `isUnit?` decision (a
-- top-level aux on the `Dec`, NOT a pattern-match on `B` — so it reduces given
-- the decision, and the masquerade proof folds it via the SAME `isUnit? B`
-- the elaborator's `ext-resolved-info` uses).
arrow-info-eff : ∀ {A B} → CanonicalName → Dec (B ≡ Unit) → IsBaseType A → IsConcrete B → SigOpInfo A B
arrow-info-eff name (yes refl) bA cB = mk-info' name (emitsV refl) bA (ffi-concrete cB)
arrow-info-eff name (no _)     bA cB = value-info name bA cB

arrow-info : ∀ {A B} → ArrowKind → CanonicalName → IsBaseType A → IsConcrete B → SigOpInfo A B
arrow-info (mk-kind _ pure) name bA cB = value-info name bA cB
arrow-info {A} {B} (mk-kind _ eff) name bA cB = arrow-info-eff name (isUnit? B) bA cB
