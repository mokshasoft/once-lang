-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SourceTrace — the source semantics `⟦_⟧` (Plan 0.24,
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
-- `faithful` (`Once.Adequacy.SourceFaithful`). The old independent
-- `SS.eval`/`runTrace` reference (and the `ElaborateFaithful` conjunct it
-- backed) is retired: `SourceSemantics`/`AnaTrace`/`ElaborateTrace` are
-- gone, and `faithful` is the standalone load-bearing fact rather than a
-- conjunct bolted onto the compiler theorem.
--
-- Plan 0.44: `Behavior = ℕ → List SigOpEvent` (the step-indexed SigOp
-- trace). `⟦ src ⟧ n` is the trace prefix `evalᴰ` observes within `n`
-- steps — no projection.
------------------------------------------------------------------------

module Once.Adequacy.SourceTrace where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit using (tt)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Once.CanonicalName using (CanonicalName; bare) renaming (_≟ᶜ_ to _≟cn_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type; Unit)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- Plan 0.52: pull the LEXER+PARSER into the verified front-end — `srcToModule`
-- runs the executable `parseStrict` on the source TEXT (a front-end bug reds the
-- apex via `Once.Adequacy.FrontEndBridge`). Plan 0.51: and then the resolver, so
-- `moduleToIR` compiles the SAME (resolved) module the binary runs.
open import Once.Parser using (parseStrict)
open import Once.Parser.Module.Resolve using (resolveImports; ModuleMap)
open import Once.Denotation.Behavior using (Source; Behavior)
open import Once.Denotation.DenotTrace using (evalᴰ)
-- Plan 0.73 (D113): the meaning is target-relative at `Float`, so the format
-- is threaded in. An explicit ARGUMENT, not a module parameter — these are
-- recursive and a parameterised module stops reducing at a variable instance.
open import Once.Target.Arch using (TargetNum; int-bits; float-format)
open import Once.Denotation.TraceMonad using (projTrace)

------------------------------------------------------------------------
-- Source → IR of `main` (option (a): reuse the compiler's elaborator).
------------------------------------------------------------------------

-- | Recognise the `Unit` codomain so `main`'s entry IR (wrapped to
-- `IR ⌊ Unit ⌋ ⌊ Unit ⌋` by `maybeWrapMain`) can be coerced.
isUnit? : (T : Type) → Maybe (T ≡ Unit)
isUnit? Unit = just refl
isUnit? _    = nothing

open C.CompiledFun using (cfName; cfType; cfIR; cfIsPrimitive)

-- Explicit dispatch on the three decisions (no `with`-opacity, no dependent
-- `just refl` buried in a `with`), so `findMain`'s "is this the entry?" choice
-- is analyzable. `just refl` refines `cfType cf` to `Unit`, coercing
-- `cfIR cf : IR Unit (cfType cf)` to `IR ⌊ Unit ⌋ ⌊ Unit ⌋`.
--
-- The FIRST argument is `cfIsPrimitive cf`: a PRIMITIVE is never the entry —
-- its body is not emitted at codegen (`CompiledFun.cfIsPrimitive`), so it has
-- no real `_start` to run. Skipping primitives aligns this spec with the
-- backend and makes the entry provably trace back to a `DFunDef`.
findMain-here :
  (cf : C.CompiledFun) → Bool → Dec (cfName cf ≡ bare "main") → Maybe (cfType cf ≡ Unit)
  → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
findMain-here cf false (yes _) (just refl) cont = just (cfIR cf)
findMain-here cf false (yes _) nothing     cont = cont
findMain-here cf false (no  _) _           cont = cont
findMain-here cf true  _       _           cont = cont   -- primitive: never the entry

-- | The Boolean predicate `findMain` selects on: a non-primitive `main`-named
-- function whose (entry-wrapped) codomain is `Unit`. `findMain` returns the IR
-- of the FIRST such function. Factored out (Plan 0.55) so the SAME notion of
-- "which function is the entry" is nameable for the deterministic `mainRealized`
-- selector's alignment. Behaviour-preserving: `findMain`/`findMain-here` are
-- unchanged — `isMain cf ≡ true` exactly when `findMain-here cf … ≡ just (cfIR cf)`.
isMain : C.CompiledFun → Bool
isMain cf with cfIsPrimitive cf | cfName cf ≟cn bare "main" | isUnit? (cfType cf)
... | false | yes _ | just _ = true
... | _     | _     | _      = false

findMain : List C.CompiledFun → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
findMain []         = nothing
findMain (cf ∷ rest) =
  findMain-here cf (cfIsPrimitive cf) (cfName cf ≟cn bare "main") (isUnit? (cfType cf)) (findMain rest)

-- Explicit dispatch on the compile result (no `with`-opacity).
moduleToIR-aux : String ⊎ List C.CompiledFun → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
moduleToIR-aux (inj₁ _)    = nothing
moduleToIR-aux (inj₂ funs) = findMain funs

-- Non-resolving: the IR of `main` in an ALREADY-RESOLVED module. The
-- module-level proofs (`AcceptSound`/`MainBuilds`/`ModuleComplete`) reason
-- about THIS over a module `mod` (interpreted as the RESOLVED module);
-- resolution is confined to `srcToModule` below, so those proofs are untouched.
moduleToIR : P.Module → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
moduleToIR mod = moduleToIR-aux (C.compileResolvedModule C.Heap false mod)

------------------------------------------------------------------------
-- IR-level meaning (the source observable).
------------------------------------------------------------------------

-- The SigOp trace the denotational `evalᴰ` reads off `main`'s IR (the
-- elaborated meaning), at observation depth `n` (Plan 0.46: the monadic
-- `⟦_⟧ᴰ` is THE source observable; the operational `otrace` is retired).
⟦_⟧IR : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → TargetNum → Behavior
⟦ just ir ⟧IR fmt = λ n → take n (projTrace (evalᴰ fmt ir tt) n)
⟦ nothing ⟧IR _   = λ _ → []

------------------------------------------------------------------------
-- The verified front-end (Plan 0.51): parse the user's grammar module,
-- THEN resolve its imports against the in-`Source` `ModuleMap`. This is the
-- resolution step the binary runs — now INSIDE the verified pipeline, so a
-- resolver bug is the apex's concern (`Once.Spec.Resolution` + its bridge), not a
-- trusted-I/O step. The INDEPENDENT meaning (`_⊢R_`/`⟦_⟧ˢ`) instead anchors on
-- the UN-resolved `gmoduleToModule (Source.srcModule src)`, so completeness is
-- not resolver-vacuous; `Once.Adequacy.ResolveBridge` proves the resolver right.
------------------------------------------------------------------------

eitherToMaybe : String ⊎ P.Module → Maybe P.Module
eitherToMaybe (inj₁ _) = nothing
eitherToMaybe (inj₂ m) = just m

srcToModule-aux : ModuleMap → Maybe P.Module → Maybe P.Module
srcToModule-aux mm nothing  = nothing
srcToModule-aux mm (just m) = eitherToMaybe (resolveImports mm m)

-- The verified front-end: lex+parse the source TEXT (`parseStrict`), then resolve
-- imports. Both the lexer and parser now run INSIDE `compile`; their correctness
-- is the apex's concern (`Once.Adequacy.FrontEndBridge`), as the resolver's is
-- (`Once.Adequacy.ResolveBridge`).
srcToModule : Source → Maybe P.Module
srcToModule src =
  srcToModule-aux (Source.srcImports src) (eitherToMaybe (parseStrict (Source.srcText src)))

-- The front-end SUCCEEDS to `mR` exactly when the source text parses to `mU`
-- and the resolver maps it to `mR`. (Reduction lemma the apex completeness path
-- uses to rewrite `srcToModule src` once both halves are known.)
srcToModule-just : ∀ (src : Source) (mU mR : P.Module) →
  parseStrict (Source.srcText src) ≡ inj₂ mU →
  resolveImports (Source.srcImports src) mU ≡ inj₂ mR →
  srcToModule src ≡ just mR
srcToModule-just src mU mR p-eq r-eq rewrite p-eq | r-eq = refl

-- Inversion: a successful front-end (`srcToModule src ≡ just mR`) DECOMPOSES
-- into a successful parse (`parseStrict text ≡ inj₂ mU`) and a successful
-- resolve (`resolveImports … mU ≡ inj₂ mR`). The apex soundness path uses this
-- to recover the un-resolved parsed module `mU` (for `_⊢R_`/the FrontEndBridge).
-- Clause-based on the `⊎` results (no `with`-opacity).
eitherToMaybe-inv : ∀ (e : String ⊎ P.Module) (m : P.Module) →
  eitherToMaybe e ≡ just m → e ≡ inj₂ m
eitherToMaybe-inv (inj₁ _)  m ()
eitherToMaybe-inv (inj₂ m') m eq = cong inj₂ (just-injective eq)

srcToModule-inv-p : ∀ (mm : ModuleMap) (pr : String ⊎ P.Module) (mR : P.Module) →
  srcToModule-aux mm (eitherToMaybe pr) ≡ just mR →
  Σ-syntax P.Module (λ mU → (pr ≡ inj₂ mU) × (resolveImports mm mU ≡ inj₂ mR))
srcToModule-inv-p mm (inj₁ _)  mR ()
srcToModule-inv-p mm (inj₂ mU) mR eq = mU , refl , eitherToMaybe-inv (resolveImports mm mU) mR eq

srcToModule-inv : ∀ (src : Source) (mR : P.Module) →
  srcToModule src ≡ just mR →
  Σ-syntax P.Module (λ mU →
    (parseStrict (Source.srcText src) ≡ inj₂ mU)
    × (resolveImports (Source.srcImports src) mU ≡ inj₂ mR))
srcToModule-inv src mR eq =
  srcToModule-inv-p (Source.srcImports src) (parseStrict (Source.srcText src)) mR eq

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
sourceTrace-aux : Maybe P.Module → TargetNum → Behavior
sourceTrace-aux (just m) fmt = ⟦ moduleToIR m ⟧IR fmt
sourceTrace-aux nothing  _   = λ _ → []

sourceTrace : Source → TargetNum → Behavior
sourceTrace src fmt = sourceTrace-aux (srcToModule src) fmt

-- `abstract`: keep `⟦_⟧` opaque downstream. Otherwise `⟦ src ⟧` unfolds
-- to `sourceTrace src`'s `with gmoduleToModule src …`, and
-- `Verified.Compile.correct`'s own `with gmoduleToModule src in g-eq`
-- reduces the goal's `⟦ src ⟧` while the per-stage postulate's stays
-- unreduced → `UnequalTerms`. Opacity makes both sides the same term.
abstract
  ⟦_⟧ : Source → TargetNum → Behavior
  ⟦ src ⟧ = sourceTrace src

  -- Reduction lemma (exported): when `src` parses AND RESOLVES to module `m`
  -- (`srcToModule src ≡ just m`), its meaning IS `m`'s source trace. Proven
  -- INSIDE the `abstract` block (where `⟦_⟧` reduces to `sourceTrace`); the
  -- J-style `sourceTrace-aux` makes the front-end equation `rewrite`-able with
  -- no `with`-opacity. This discharges `Compile.gmoduleToModule-correct`.
  ⟦⟧-via-module :
    ∀ (src : Source) (m : P.Module) → srcToModule src ≡ just m →
    ∀ (fmt : TargetNum) → ⟦ src ⟧ fmt ≡ ⟦ moduleToIR m ⟧IR fmt
  ⟦⟧-via-module src m eq fmt rewrite eq = refl
