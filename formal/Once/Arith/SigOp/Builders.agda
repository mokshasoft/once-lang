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

open import Once.Type using (Type; Unit; Void; Int; Str; _*_; _+_;
                              ArrowKind; mk-kind; Purity; pure; eff; isUnit?; isVoid?)
open import Relation.Nullary using (Dec; yes; no)
open import Once.SigOp.Info using (SigOpInfo; mk-info; mk-info'; pureV; primV; emitsV; haltsV; ffiV; callsV; EffectShape; Pure; Halts)
open import Once.Arith.Prim using (ArithPrim; p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f)
open import Once.Functor.Translate using (IsBaseType;
  base-Unit; base-Int; base-Float; base-Str; base-Prod; base-Sum)
open import Once.CanonicalName using (CanonicalName; bare; showCanonical)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Word using (Carrier)
import Once.Word as OnceWord
-- PLAN 0.74 J5: `module W = OnceWord.Word64` USED TO BE HERE, and it was the
-- bug. These descriptors serve all three targets and one of them is 32-bit;
-- the width now arrives as the `TargetNum` every `semM` takes.
open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- | This target's modular arithmetic. The ONLY place the width is read.
module W (tn : TargetNum) = OnceWord.Width (int-bits tn)
open import Once.Float.Dyadic using (Dyadic)
import Once.Float.Arith as FA
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
-- semM IS THE MODULAR WORD EVALUATOR (D054). Once's integers are SIGNED
-- two's-complement machine words, so these are `Once.Word`'s modular ops —
-- the SAME ones `Once.Arith.SigOp.Block.block-semM` already uses, so the
-- per-op and blocked arith paths now agree instead of diverging.
--
-- They used to be raw ℕ operations, and that was not a simplification, it was
-- WRONG on exactly the inputs Once admits:
--   - `-` was `ℕ._∸_` (monus), so `3 - 8` denoted 0 rather than −5;
--   - `neg` returned 0 for every input, so negation denoted nothing at all;
--   - `+` / `*` never wrapped, promising unbounded arithmetic the hardware
--     does not provide.
-- The MACHINE was right throughout — `emit (3 - 8)` writes two's-complement
-- −5 — so this is the spec being brought up to meet the machine, not a
-- behaviour change. `TraceSpec`'s negative-argument cases pin it.
--
-- WIDTH — PLAN 0.74 J5, and the comment that used to be here was wrong.
--
-- It said: "Width: `Word64`, matching `block-semM`. Threading the target's
-- width here (D059) is the open Int-width bill; baking 64 is what the blocked
-- path already does, so this changes no promise, it only stops two paths from
-- disagreeing." Every clause of that is true and the conclusion is false. Two
-- paths agreeing on 64 is not "no promise changed" when one of the targets is
-- 32-bit — it is both paths being wrong together, which is what made it
-- invisible. `Denotation/Meaning`'s `⟦ t-neg d ⟧ᵢ` reads these functions, so
-- on x86-32 the SPEC said `⟦ neg (int 5) ⟧ = 2^64 - 5`, not a 32-bit word at
-- all, while `⟦ int 5 ⟧` in the same expression was already width-correct.
--
-- The width is now THREADED (D059, properly): every `semM` takes the target's
-- `TargetNum`, and `W tn` is the only place it is read.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Postulated semantics (still placeholders — div/mod need a div-by-
-- zero policy, comparisons need a Bool encoding decision, generic-sem
-- is the unresolved-SigOp fallback).
------------------------------------------------------------------------

postulate

  -- Comparisons: Int * Int → (Unit + Unit) ≡ Bool
  lt-semM le-semM gt-semM ge-semM eq-semM ne-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Unit + Unit ⟧

-- | String literal semantics. `M.⟦ Str ⟧ = String` (Semantics.Core), so a
-- string literal denotes ITSELF — a concrete definition. (The machine's
-- byte/pointer representation is a codegen concern, a different layer; the
-- denotational value is the string.)
-- A string literal denotes itself at every width, so the `TargetNum` is taken
-- and ignored. Taken anyway: the uniform shape is what lets `semM` be one
-- accessor rather than two.
str-lit-semM : String → TargetNum → M.⟦ Unit ⟧ → M.⟦ Str ⟧
str-lit-semM s _ _ = s

------------------------------------------------------------------------
-- SigOpInfo builders
------------------------------------------------------------------------

-- Base-type witnesses for the internal arith SigOp types (both sides are base:
-- plan 0.105 makes every SigOp first-order).
base-I×I : IsBaseType (Int * Int)
base-I×I = base-Prod base-Int base-Int
base-U+U : IsBaseType (Unit + Unit)
base-U+U = base-Sum base-Unit base-Unit

-- Binary arithmetic
add-info : SigOpInfo (Int * Int) Int
add-info = mk-info' (bare "arith.add.int") (primV p-add) base-I×I base-Int

sub-info : SigOpInfo (Int * Int) Int
sub-info = mk-info' (bare "arith.sub.int") (primV p-sub) base-I×I base-Int

mul-info : SigOpInfo (Int * Int) Int
mul-info = mk-info' (bare "arith.mul.int") (primV p-mul) base-I×I base-Int

div-info : SigOpInfo (Int * Int) Int
div-info = mk-info' (bare "arith.div.int") (primV p-div) base-I×I base-Int

mod-info : SigOpInfo (Int * Int) Int
mod-info = mk-info' (bare "arith.mod.int") (primV p-mod) base-I×I base-Int

-- Unary arithmetic
neg-info : SigOpInfo Int Int
neg-info = mk-info' (bare "arith.neg.int") (primV p-neg) base-Int base-Int

-- Float arithmetic (plan 0.75 F4). Distinct NAMES, not overloads: the SigOp
-- name is the identity the backend dispatches on, and `arith.add.int` and
-- `arith.add.float` are different instructions on every target.
base-F×F : IsBaseType (Once.Type.Float * Once.Type.Float)
base-F×F = base-Prod base-Float base-Float

fadd-info : SigOpInfo (Once.Type.Float * Once.Type.Float) Once.Type.Float
fadd-info = mk-info' (bare "arith.add.float") (primV p-fadd) base-F×F base-Float

fsub-info : SigOpInfo (Once.Type.Float * Once.Type.Float) Once.Type.Float
fsub-info = mk-info' (bare "arith.sub.float") (primV p-fsub) base-F×F base-Float

fmul-info : SigOpInfo (Once.Type.Float * Once.Type.Float) Once.Type.Float
fmul-info = mk-info' (bare "arith.mul.float") (primV p-fmul) base-F×F base-Float

fdiv-info : SigOpInfo (Once.Type.Float * Once.Type.Float) Once.Type.Float
fdiv-info = mk-info' (bare "arith.div.float") (primV p-fdiv) base-F×F base-Float

i2f-info : SigOpInfo Int Once.Type.Float
i2f-info = mk-info' (bare "arith.i2f") (primV p-i2f) base-Int base-Float

-- Comparisons
lt-info : SigOpInfo (Int * Int) (Unit + Unit)
lt-info = mk-info (bare "arith.lt.int") lt-semM Pure base-I×I base-U+U

le-info : SigOpInfo (Int * Int) (Unit + Unit)
le-info = mk-info (bare "arith.le.int") le-semM Pure base-I×I base-U+U

gt-info : SigOpInfo (Int * Int) (Unit + Unit)
gt-info = mk-info (bare "arith.gt.int") gt-semM Pure base-I×I base-U+U

ge-info : SigOpInfo (Int * Int) (Unit + Unit)
ge-info = mk-info (bare "arith.ge.int") ge-semM Pure base-I×I base-U+U

eq-info : SigOpInfo (Int * Int) (Unit + Unit)
eq-info = mk-info (bare "arith.eq.int") eq-semM Pure base-I×I base-U+U

ne-info : SigOpInfo (Int * Int) (Unit + Unit)
ne-info = mk-info (bare "arith.ne.int") ne-semM Pure base-I×I base-U+U

-- String literal family
str-lit-info : String → SigOpInfo Unit Str
str-lit-info s = mk-info (bare ("lit.str." ++ s)) (str-lit-semM s) Pure base-Unit base-Str

------------------------------------------------------------------------
-- Generic placeholder for unresolved / user-imported SigOps
--
-- Used by Surface.Elaborate for legacy `sigOp name` and `poly name`
-- forms whose SigOpInfo is not yet known at elaboration time.
-- Phase D (external syscalls) and a future registry-lookup phase will
-- replace these placeholders with concrete SigOpInfos.
------------------------------------------------------------------------

-- | A SigOp referenced as a VALUE — at non-arrow type, or through an erased
-- arrow — or applied at a `pure` arrow: a PURE FFI CONTRACT (`ffiV`, plan
-- 0.105). Its value is the interpretation's, not a postulate's: the meaning
-- reads it from the call environment's pure half, the machine from its
-- interpretation, and correctness quantifies over it. (This retired
-- `generic-semM`, the postulated value every such reference used to denote.)
-- Its effect is `Pure`: an effect lives on an *arrow* (realized only on
-- application, D018 suspended-Eff), and an effectful arrow's effect comes from
-- its DECLARED `! <shape>` (`arrow-info`, `ext-arrow-info`).
value-info : ∀ {A B} → CanonicalName → IsBaseType A → IsBaseType B → SigOpInfo A B
value-info name bA bB = mk-info' name ffiV bA bB


-- | Compat shims for the surface/meaning sites (`Surface.Desugar`,
-- `Surface.Elaborate`, `Denotation.SourceDenote`) that still name these.
-- Surface `sigOp`/`closure`/`poly` are value positions ⇒ `Pure`; a surface
-- *arrow* `sigOp` is unreachable at Layer 0 (external `Eff` arrows are
-- `Many` and take the qualified-ref IR path in `TypeCheck.Elaborate`,
-- where the declared shape is read), so `arrow-info` is `value-info` too.
-- Keeping the names (vs. inlining) avoids churning those three modules and
-- keeps `faithful` definitionally `refl` (both presentations use the same
-- shim).
generic-info : ∀ {A B} → CanonicalName → IsBaseType A → IsBaseType B → SigOpInfo A B
generic-info = value-info

-- The effect is a LEAF annotation read off the arrow's `Purity`; WHICH effect
-- is read off the CODOMAIN (D225). A `pure` arrow is a pure value. An `eff`
-- arrow into `Void` HALTS: `⟦ Void ⟧ = ⊥`, so `Res ⟦ Void ⟧` has exactly one
-- inhabitant, `stopped` — the type leaves no other meaning to choose. An `eff`
-- arrow into `Unit` emits (an effect contract); any other `eff` arrow ANSWERS
-- (`callsV`, plan 0.105): a call whose result is the interpretation's answer,
-- so two reads may differ. Before D225 this split only on `Unit`, so
-- an effectful op into `Void` denoted as a VALUE of `⊥` — a value only the
-- `generic-semM` postulate could supply — while the elaborator emitted
-- `haltsV`: plan 0.98 §2's "inhabited by fiat", one layer below stage E.
-- Dispatched through the shared `isVoid?`/`isUnit?` decisions (a top-level aux
-- on the two `Dec`s, NOT a pattern-match on `B`) — the SAME pair, in the same
-- order, that the elaborator's `ext-resolved-info` hands `ext-resolved-info-aux`,
-- so the masquerade proof folds both with one split.
arrow-info-eff : ∀ {A B} → CanonicalName → Dec (B ≡ Void) → Dec (B ≡ Unit)
               → IsBaseType A → IsBaseType B → SigOpInfo A B
arrow-info-eff name (yes refl) _          bA bB = mk-info' name (haltsV refl) bA bB
arrow-info-eff name (no _)     (yes refl) bA bB = mk-info' name (emitsV refl) bA bB
arrow-info-eff name (no _)     (no _)     bA bB = mk-info' name callsV bA bB

arrow-info : ∀ {A B} → ArrowKind → CanonicalName → IsBaseType A → IsBaseType B → SigOpInfo A B
arrow-info (mk-kind _ pure) name bA bB = value-info name bA bB
arrow-info {A} {B} (mk-kind _ eff) name bA bB = arrow-info-eff name (isVoid? B) (isUnit? B) bA bB
