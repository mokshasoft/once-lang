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

-- Binary arithmetic — Int * Int → Int
add-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
add-semM tn (a , b) = W._⊕_ tn a b

sub-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
sub-semM tn (a , b) = W._⊖_ tn a b

mul-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Int ⟧
mul-semM tn (a , b) = W._⊗_ tn a b

-- Unary: Int → Int
neg-semM : TargetNum → M.⟦ Int ⟧ → M.⟦ Int ⟧
neg-semM tn x = W.⊝_ tn x

------------------------------------------------------------------------
-- FLOAT arithmetic (plan 0.75 F4)
--
-- The same shape as the integer family above and for the same reason. `⊕` is
-- `norm tn (x + y)` — the exact operation in a scaffolding domain, then the
-- target's normalisation — and `Once.Float.Arith.fadd` is that sentence with
-- "rounding at the format" in place of "reduction mod 2^w". Neither is a
-- postulate; both read the target out of the `TargetNum` they are handed.
--
-- ONE fact comes off `tn`: the format. An invalid operation gives THE
-- canonical NaN at every target, by D055's rule — the targets genuinely
-- disagree in hardware (x86 sets the sign and propagates payloads, RISC-V
-- canonicalises), and D055 says the answer is to pick one and make the
-- backends conform, not to let the meaning vary by backend.
------------------------------------------------------------------------

fadd-semM : TargetNum → M.⟦ Once.Type.Float * Once.Type.Float ⟧ → M.⟦ Once.Type.Float ⟧
fadd-semM tn (a , b) = FA.fadd (float-format tn) a b

fsub-semM : TargetNum → M.⟦ Once.Type.Float * Once.Type.Float ⟧ → M.⟦ Once.Type.Float ⟧
fsub-semM tn (a , b) = FA.fsub (float-format tn) a b

fmul-semM : TargetNum → M.⟦ Once.Type.Float * Once.Type.Float ⟧ → M.⟦ Once.Type.Float ⟧
fmul-semM tn (a , b) = FA.fmul (float-format tn) a b

------------------------------------------------------------------------
-- Postulated semantics (still placeholders — div/mod need a div-by-
-- zero policy, comparisons need a Bool encoding decision, generic-sem
-- is the unresolved-SigOp fallback).
------------------------------------------------------------------------

postulate
  -- Binary arithmetic with division-by-zero edge case still pending
  div-semM mod-semM : TargetNum → M.⟦ Int * Int ⟧ → M.⟦ Int ⟧

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

-- Float arithmetic (plan 0.75 F4). Distinct NAMES, not overloads: the SigOp
-- name is the identity the backend dispatches on, and `arith.add.int` and
-- `arith.add.float` are different instructions on every target.
base-F×F : IsBaseType (Once.Type.Float * Once.Type.Float)
base-F×F = base-Prod base-Float base-Float
con-Float : IsConcrete Once.Type.Float
con-Float = con-base base-Float

fadd-info : SigOpInfo (Once.Type.Float * Once.Type.Float) Once.Type.Float
fadd-info = mk-info (bare "arith.add.float") fadd-semM Pure base-F×F con-Float

fsub-info : SigOpInfo (Once.Type.Float * Once.Type.Float) Once.Type.Float
fsub-info = mk-info (bare "arith.sub.float") fsub-semM Pure base-F×F con-Float

fmul-info : SigOpInfo (Once.Type.Float * Once.Type.Float) Once.Type.Float
fmul-info = mk-info (bare "arith.mul.float") fmul-semM Pure base-F×F con-Float

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
  generic-semM : ∀ {A B} → String → TargetNum → M.⟦ A ⟧ → M.⟦ B ⟧

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
