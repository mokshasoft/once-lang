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
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₁; ∃; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Once.TypeCheck.Raw using (RawExpr)
open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Once.Type using (Type; Unit)
open import Once.CCC.IR using (IR)
import Once.Compile as C
import Once.Parser.Module.Core as P
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

-- Explicit dispatch on the two decisions (no `with`-opacity, no dependent
-- `just refl` buried in a `with`), so `findMain`'s "is this the entry?" choice
-- is analyzable. `just refl` refines `cfType cf` to `Unit`, coercing
-- `cfIR cf : IR Unit (cfType cf)` to `IR Unit Unit`.
findMain-here :
  (cf : C.CompiledFun) → Dec (cfName cf ≡ "main") → Maybe (cfType cf ≡ Unit)
  → Maybe (IR Unit Unit) → Maybe (IR Unit Unit)
findMain-here cf (yes _) (just refl) cont = just (cfIR cf)
findMain-here cf (yes _) nothing     cont = cont
findMain-here cf (no  _) _           cont = cont

findMain : List C.CompiledFun → Maybe (IR Unit Unit)
findMain []         = nothing
findMain (cf ∷ rest) =
  findMain-here cf (cfName cf ≟str "main") (isUnit? (cfType cf)) (findMain rest)

-- Link 1 of main-exists-align: a successful `findMain` means a `main`-named
-- (Unit-typed) function is present in the compiled list.
findMain-name :
  ∀ (funs : List C.CompiledFun) (ir : IR Unit Unit)
  → findMain funs ≡ just ir
  → Any (λ cf → cfName cf ≡ "main") funs
findMain-name [] ir ()
findMain-name (cf ∷ rest) ir eq with cfName cf ≟str "main" | isUnit? (cfType cf)
... | yes p | just refl = here p
... | yes _ | nothing   = there (findMain-name rest ir eq)
... | no  _ | _         = there (findMain-name rest ir eq)

-- Explicit dispatch on the compile result (no `with`-opacity), so the IR side
-- of `elaborate-preserves-trace` can be characterised (analogous to the
-- `runTraceMain`/`runTraceEval` source-side helpers).
moduleToIR-aux : String ⊎ List C.CompiledFun → Maybe (IR Unit Unit)
moduleToIR-aux (inj₁ _)    = nothing
moduleToIR-aux (inj₂ funs) = findMain funs

moduleToIR : P.Module → Maybe (IR Unit Unit)
moduleToIR mod = moduleToIR-aux (C.compileResolvedModule C.Heap false mod)

-- IR-side characterization: when the module compiles to `funs`, `moduleToIR` is
-- exactly `findMain funs`. The IR-side analog of `runTrace-main`; reduces the
-- IR side of `elaborate-preserves-trace` to `findMain` of the compiled funs.
moduleToIR-compiled :
  ∀ (mod : P.Module) (funs : List C.CompiledFun)
  → C.compileResolvedModule C.Heap false mod ≡ inj₂ funs
  → moduleToIR mod ≡ findMain funs
moduleToIR-compiled mod funs eq rewrite eq = refl

sourceToIR : Source → Maybe (IR Unit Unit)
sourceToIR src with gmoduleToModule src
... | nothing  = nothing
... | just mod = moduleToIR mod

------------------------------------------------------------------------
-- IR-level meaning and the FRONTEND obligation (Plan 0.45 Part B, factor 1).
------------------------------------------------------------------------

-- The SigOp trace `obs` reads off `main`'s IR (the elaborated meaning).
⟦_⟧IR : Maybe (IR Unit Unit) → Behavior
⟦ just ir ⟧IR = λ n → proj₁ (obs n ir tt)
⟦ nothing ⟧IR = λ _ → []

-- FACTOR 1 of `module-to-asm-correct`: typecheck + elaborate preserve the
-- source trace — `obs` of `main`'s IR equals the source-level reference. THE
-- load-bearing frontend obligation, now NAMED (Plan 0.45 Phase 2 deliverable).
-- Discharge = structural induction over `checkElabV` + `Surface.Elaborate`
-- (the ~2700-line frontend); this is where the typechecker becomes
-- load-bearing and the `ErrorProofs`-class proof structure surfaces.
-- Multi-session.
--
-- CONDITIONED on the module compiling (`moduleToIR m ≡ just ir`). The
-- unconditional `∀ m n → ⟦ moduleToIR m ⟧IR n ≡ runTrace m n` is UNSOUND: a
-- type-erroring program with a `main` has `moduleToIR m ≡ nothing`
-- (`⟦⟧IR = []`), yet `runTrace` (untyped) still evaluates its `main` to a
-- non-empty trace. `correct` only claims compiling programs (its hypothesis
-- `compile ≡ just bytes`), so the `just ir` condition is exactly available
-- (threaded by `Compile.module-to-asm-correct` via `built⇒moduleToIR-just`).
-- Factored (Plan 0.45 #10) into two precise obligations + a connecting proof
-- that uses the proven source-side reduction `runTrace-main`.
postulate
  -- (#9) Main-finding alignment — the PROGRAM case (D008: `--exe` needs a
  -- `main`; a library `--lib`, with no `main`, gives `moduleToIR m ≡ nothing`
  -- and the empty-trace `no-main-empty` branch instead). When `moduleToIR m`
  -- produces an entry IR the module IS a program, so it has a source `main`
  -- definition and `runTrace` runs it. Discharge: extractFunctions /
  -- compileAllFuns / findMain ↔ extractDefs / lookupDef.
  main-exists-align :
    ∀ (m : P.Module) (ir : IR Unit Unit) → moduleToIR m ≡ just ir
    → ∃ λ (body : RawExpr) →
        SS.lookupDef (SS.extractDefs (P.Module.decls m)) "main" ≡ just body

  -- (#10) The obs↔eval CORE: the compiled entry IR's SigOp trace equals the
  -- source interpreter's trace of the SAME `main` body. THE load-bearing
  -- obligation — the `obs(elaborate(checkElab …)) ≈ eval` induction over the
  -- elaborate pipeline, where checkElab's proof structure becomes load-bearing.
  compiled-main-trace :
    ∀ (m : P.Module) (ir : IR Unit Unit) → moduleToIR m ≡ just ir
    → ∀ (body : RawExpr)
    → SS.lookupDef (SS.extractDefs (P.Module.decls m)) "main" ≡ just body
    → ∀ (n : ℕ)
    → proj₁ (obs n ir tt)
        ≡ SS.runTraceEval (SS.eval n (SS.extractDefs (P.Module.decls m)) [] body)

-- Factor 1, now a THEOREM: compose the main-finding alignment, the obs↔eval
-- core, and the proven `runTrace-main` reduction. The monolithic frontend
-- postulate is gone; the remaining work is the two named obligations above.
elaborate-preserves-trace :
  ∀ (m : P.Module) (ir : IR Unit Unit) (n : ℕ)
  → moduleToIR m ≡ just ir
  → proj₁ (obs n ir tt) ≡ SS.runTrace m n
elaborate-preserves-trace m ir n mj with main-exists-align m ir mj
... | (body , lk) =
  trans (compiled-main-trace m ir mj body lk n) (sym (SS.runTrace-main m n body lk))

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
-- J-style dispatch on the parse result (explicit `Maybe`, no `with`), so
-- `⟦⟧-via-module` below can `rewrite` the parse equation through it.
sourceTrace-aux : Maybe P.Module → Behavior
sourceTrace-aux (just m) = SS.runTrace m
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
    ∀ (n : ℕ) → ⟦ src ⟧ n ≡ SS.runTrace m n
  ⟦⟧-via-module src m eq n rewrite eq = refl
