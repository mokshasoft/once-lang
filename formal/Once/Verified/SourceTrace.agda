-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.SourceTrace — the source semantics `⟦_⟧` (Plan 0.24,
-- Phase C). Discharges the former `Once.Verified.Behavior.⟦_⟧`
-- postulate.
--
-- `⟦ src ⟧` is the SigOp trace of the source program (its meaning),
-- read off its IR via `obs`. Option (a) "IR pivot": `sourceToIR` reuses
-- the compiler's own front-end (`gmoduleToModule` →
-- `compileResolvedModule` → the IR of `main`). The front-end is thus a
-- shared/trusted reference; `correct` verifies the backend against this
-- IR-level meaning (see plan 0.24's TCB section).
--
-- This module lives separately from `Behavior.agda` (which stays light,
-- as the per-arch CPU instances import it) because `sourceToIR` pulls
-- in the whole compiler front-end via `Once.Compile`.
--
-- Plan 0.44: `Behavior = ℕ → List SigOpEvent` (the step-indexed SigOp
-- trace). `⟦ src ⟧ n` is the trace prefix `obs` observes within `n` steps
-- — no projection. (Was `exitCodeOf (proj₁ (obs 0 …))` under the old
-- `Behavior = Maybe ℕ`; the projection is gone with the observable.)
------------------------------------------------------------------------

module Once.Verified.SourceTrace where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using () renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit)
open import Once.CCC.IR using (IR)
import Once.Compile as C
open import Once.Grammar.ModuleConvert using (gmoduleToModule)
open import Once.Verified.Behavior using (Source; Behavior)
open import Once.Verified.TraceDenote using (obs)
open import Once.Verified.SourceSemantics as SS using (runTrace)

------------------------------------------------------------------------
-- Source → IR of `main` (option (a): reuse the compiler's elaborator).
------------------------------------------------------------------------

-- | Recognise the `Unit` codomain so `main`'s entry IR (wrapped to
-- `IR Unit Unit` by `maybeWrapMain`) can be coerced.
isUnit? : (T : Type) → Maybe (T ≡ Unit)
isUnit? Unit = just refl
isUnit? _    = nothing

open C.CompiledFun using (cfName; cfType; cfIR)

findMain : List C.CompiledFun → Maybe (IR Unit Unit)
findMain []         = nothing
findMain (cf ∷ rest) with cfName cf ≟str "main" | isUnit? (cfType cf)
... | yes _ | just refl = just (cfIR cf)
... | _     | _         = findMain rest

sourceToIR : Source → Maybe (IR Unit Unit)
sourceToIR src with gmoduleToModule src
... | nothing  = nothing
... | just mod with C.compileResolvedModule C.Heap false mod
...   | inj₁ _    = nothing
...   | inj₂ funs = findMain funs

------------------------------------------------------------------------
-- The source semantics (discharges the `Behavior.⟦_⟧` postulate).
------------------------------------------------------------------------

-- Plan 0.45 Phase 1 — re-anchor the source meaning at the SOURCE level.
--
-- WAS: `⟦ src ⟧ = obs (elaborate src)` (the IR pivot) — the spec moved with
-- the elaborator, so the typechecker could elaborate to the wrong IR and
-- `correct` still held. The typechecker was NOT load-bearing.
--
-- NOW: `⟦ src ⟧ = sourceTrace src`, where `sourceTrace` is a SOURCE-LEVEL
-- SigOp-trace reference computed INDEPENDENTLY of the elaborator. The full
-- `compile` (typechecker included) must then be proven to preserve it
-- (`elaborate-preserves-trace`, inside `Compile.module-to-asm-correct`) — so
-- the typechecker becomes load-bearing.
--
-- `sourceTrace` is DECLARED here and DEFINED in Part A (Plan 0.45 Phase 2).
-- Leaving it undefined deliberately breaks the build: the honest spec, with
-- the gap explicit (definition-first, as in Plan 0.44).
sourceTrace : Source → Behavior
sourceTrace src with gmoduleToModule src
... | just m  = SS.runTrace m
... | nothing = λ _ → []

-- `abstract`: keep `⟦_⟧` opaque downstream. Otherwise `⟦ src ⟧` unfolds
-- to `sourceTrace src`'s `with gmoduleToModule src …`, and
-- `Verified.Compile.correct`'s own `with gmoduleToModule src in g-eq`
-- reduces the goal's `⟦ src ⟧` while the per-stage postulate's stays
-- unreduced → `UnequalTerms`. Opacity makes both sides the same term.
abstract
  ⟦_⟧ : Source → Behavior
  ⟦ src ⟧ = sourceTrace src
