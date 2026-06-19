-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.SourceTrace — the source semantics `⟦_⟧` (Plan 0.24,
-- Phase C). Discharges the former `Once.Denotation.Behavior.⟦_⟧`
-- postulate.
--
-- `⟦ src ⟧` is the SigOp trace of the source program (its meaning), read
-- off its IR via the DENOTATIONAL `evalᴰ`. Option (a) "IR pivot":
-- `moduleToIR` reuses the compiler's own front-end (`gmoduleToModule` →
-- `compileResolvedModule` → the IR of `main`). The front-end is thus a
-- shared/trusted reference; `correct` verifies the backend against this
-- IR-level meaning (see plan 0.24's TCB section).
--
-- This module lives separately from `Behavior.agda` (which stays light,
-- as the per-arch CPU instances import it) because `moduleToIR` pulls in
-- the whole compiler front-end via `Once.Compile`.
--
-- D060 (2026-06-16): there is now ONE denotational meaning. The surface
-- `⟦_⟧ˢ` and IR `⟦_⟧ᴰ` are two presentations of it, tied by the proven
-- `faithful` (`Once.Denotation.SourceFaithful`). The old independent
-- `SS.eval`/`runTrace` reference (and the `ElaborateFaithful` conjunct it
-- backed) is retired: `SourceSemantics`/`AnaTrace`/`ElaborateTrace` are
-- gone, and `faithful` is the standalone load-bearing fact rather than a
-- conjunct bolted onto the compiler theorem.
--
-- Plan 0.44: `Behavior = ℕ → List SigOpEvent` (the step-indexed SigOp
-- trace). `⟦ src ⟧ n` is the trace prefix `evalᴰ` observes within `n`
-- steps — no projection.
------------------------------------------------------------------------

module Once.Verified.SourceTrace where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit)
open import Once.CCC.IR using (IR)
import Once.Compile as C
import Once.Parser.Module.Core as P
open import Once.Grammar.ModuleConvert using (gmoduleToModule)
open import Once.Denotation.Behavior using (Source; Behavior)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.TraceMonad using (projTrace)

------------------------------------------------------------------------
-- Source → IR of `main` (option (a): reuse the compiler's elaborator).
------------------------------------------------------------------------

-- | Recognise the `Unit` codomain so `main`'s entry IR (wrapped to
-- `IR Unit Unit` by `maybeWrapMain`) can be coerced.
isUnit? : (T : Type) → Maybe (T ≡ Unit)
isUnit? Unit = just refl
isUnit? _    = nothing

open C.CompiledFun using (cfName; cfType; cfIR; cfIsPrimitive)

-- Explicit dispatch on the three decisions (no `with`-opacity, no dependent
-- `just refl` buried in a `with`), so `findMain`'s "is this the entry?" choice
-- is analyzable. `just refl` refines `cfType cf` to `Unit`, coercing
-- `cfIR cf : IR Unit (cfType cf)` to `IR Unit Unit`.
--
-- The FIRST argument is `cfIsPrimitive cf`: a PRIMITIVE is never the entry —
-- its body is not emitted at codegen (`CompiledFun.cfIsPrimitive`), so it has
-- no real `_start` to run. Skipping primitives aligns this spec with the
-- backend and makes the entry provably trace back to a `DFunDef`.
findMain-here :
  (cf : C.CompiledFun) → Bool → Dec (cfName cf ≡ "main") → Maybe (cfType cf ≡ Unit)
  → Maybe (IR Unit Unit) → Maybe (IR Unit Unit)
findMain-here cf false (yes _) (just refl) cont = just (cfIR cf)
findMain-here cf false (yes _) nothing     cont = cont
findMain-here cf false (no  _) _           cont = cont
findMain-here cf true  _       _           cont = cont   -- primitive: never the entry

findMain : List C.CompiledFun → Maybe (IR Unit Unit)
findMain []         = nothing
findMain (cf ∷ rest) =
  findMain-here cf (cfIsPrimitive cf) (cfName cf ≟str "main") (isUnit? (cfType cf)) (findMain rest)

-- Explicit dispatch on the compile result (no `with`-opacity).
moduleToIR-aux : String ⊎ List C.CompiledFun → Maybe (IR Unit Unit)
moduleToIR-aux (inj₁ _)    = nothing
moduleToIR-aux (inj₂ funs) = findMain funs

moduleToIR : P.Module → Maybe (IR Unit Unit)
moduleToIR mod = moduleToIR-aux (C.compileResolvedModule C.Heap false mod)

------------------------------------------------------------------------
-- IR-level meaning (the source observable).
------------------------------------------------------------------------

-- The SigOp trace the denotational `evalᴰ` reads off `main`'s IR (the
-- elaborated meaning), at observation depth `n` (Plan 0.46: the monadic
-- `⟦_⟧ᴰ` is THE source observable; the operational `otrace` is retired).
⟦_⟧IR : Maybe (IR Unit Unit) → Behavior
⟦ just ir ⟧IR = λ n → take n (projTrace (evalᴰ ir tt) n)
⟦ nothing ⟧IR = λ _ → []

------------------------------------------------------------------------
-- The source semantics (discharges the `Behavior.⟦_⟧` postulate).
------------------------------------------------------------------------

-- D059/D060: the source meaning is the DENOTATIONAL `evalᴰ` (compositional →
-- reasons about Once programs; observation-depth → commensurable apex meter),
-- via `⟦_⟧IR ∘ moduleToIR`. The surface presentation `⟦_⟧ˢ` agrees with this
-- IR presentation by the proven `faithful` (a standalone fact, no longer a
-- conjunct of the compiler theorem).
-- J-style dispatch on the parse result (explicit `Maybe`, no `with`), so
-- `⟦⟧-via-module` below can `rewrite` the parse equation through it.
sourceTrace-aux : Maybe P.Module → Behavior
sourceTrace-aux (just m) = ⟦ moduleToIR m ⟧IR
sourceTrace-aux nothing  = λ _ → []

sourceTrace : Source → Behavior
sourceTrace src = sourceTrace-aux (gmoduleToModule src)

-- `abstract`: keep `⟦_⟧` opaque downstream. Otherwise `⟦ src ⟧` unfolds
-- to `sourceTrace src`'s `with gmoduleToModule src …`, and
-- `Verified.Compile.correct`'s own `with gmoduleToModule src in g-eq`
-- reduces the goal's `⟦ src ⟧` while the per-stage postulate's stays
-- unreduced → `UnequalTerms`. Opacity makes both sides the same term.
abstract
  ⟦_⟧ : Source → Behavior
  ⟦ src ⟧ = sourceTrace src

  -- Reduction lemma (exported): when `src` parses to module `m`, its meaning
  -- IS `m`'s source trace. Proven INSIDE the `abstract` block (where `⟦_⟧`
  -- reduces to `sourceTrace`); the J-style `sourceTrace-aux` makes the parse
  -- equation `rewrite`-able with no `with`-opacity. This discharges
  -- `Compile.gmoduleToModule-correct`.
  ⟦⟧-via-module :
    ∀ (src : Source) (m : P.Module) → gmoduleToModule src ≡ just m →
    ∀ (n : ℕ) → ⟦ src ⟧ n ≡ ⟦ moduleToIR m ⟧IR n
  ⟦⟧-via-module src m eq n rewrite eq = refl
