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
-- NOTE (Phase C scope): `Behavior` is currently `Maybe ℕ` (the exit
-- code), shared with the machine side `exec`. So `⟦_⟧` here is the
-- full trace **projected** to the exit code (`exitCodeOf`). Widening
-- `Behavior` to the trace-prefix family — and making `exec` trace-
-- valued — is Phases D/E. `⟦_⟧` is already *defined via the trace*;
-- only the observable is projected for now.
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
open import Once.Verified.Trace using (exitCodeOf)
open import Once.Verified.TraceDenote using (obs)

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

-- `abstract`: `⟦_⟧` is a real definition, but opaque to downstream
-- proofs. Without this, `⟦ src ⟧` unfolds to `… with gmoduleToModule
-- src …`, and `Verified.Compile.correct`'s own `with gmoduleToModule
-- src in g-eq` would reduce the goal's `⟦ src ⟧` while the per-stage
-- postulate's `⟦ src ⟧` stays unreduced → `UnequalTerms`. Keeping
-- `⟦_⟧` opaque means both sides see the same term. (It still reduces
-- *inside* this module, e.g. for the Layer-0 evaluation check.)
abstract
  ⟦_⟧ : Source → Behavior
  ⟦ src ⟧ with sourceToIR src
  ... | just ir = exitCodeOf (proj₁ (obs 0 ir tt))
  ... | nothing = nothing
