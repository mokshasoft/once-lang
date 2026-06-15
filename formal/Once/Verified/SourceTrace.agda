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

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₁; proj₂; ∃; ∃-syntax; Σ-syntax; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.TypeCheck.Raw using (RawExpr)
open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Once.Type using (Type; Unit)
open import Once.CCC.IR using (IR)
import Once.Compile as C
import Once.Parser.Module.Core as P
open import Once.Grammar.ModuleConvert using (gmoduleToModule)
open import Once.Verified.Behavior using (Source; Behavior)
open import Once.Verified.DenotTrace using (evalᴰ)
open import Once.Verified.TraceMonad using (projTrace)
open import Once.Verified.SourceSemantics as SS using (runTrace)
import Once.Verified.MainAlign as MA
import Once.Verified.ElaborateTrace as ET
import Once.Surface.Elaborate as Surface
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Data.Nat.Properties using (≤-refl)

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
-- no real `_start` to run. Skipping primitives (a) aligns this spec with the
-- backend and (b) makes the entry provably trace back to a `DFunDef` (a
-- primitive `main` would be a `DSignature`, leaving no source `main` body —
-- the soundness gap `main-exists-align` would otherwise hit).
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

-- Link 1 of main-exists-align: a successful `findMain` means a `main`-named,
-- Unit-typed, NON-PRIMITIVE function is present in the compiled list. The
-- `cfIsPrimitive ≡ false` is what lets the compiler side conclude the entry
-- came from a `DFunDef` (not a `DSignature` primitive).
findMain-name :
  ∀ (funs : List C.CompiledFun) (ir : IR Unit Unit)
  → findMain funs ≡ just ir
  → Any (λ cf → cfName cf ≡ "main" × cfIsPrimitive cf ≡ false) funs
findMain-name [] ir ()
findMain-name (cf ∷ rest) ir eq
  with cfIsPrimitive cf in primEq | cfName cf ≟str "main" | isUnit? (cfType cf)
... | false | yes p | just refl = here (p , primEq)
... | false | yes _ | nothing   = there (findMain-name rest ir eq)
... | false | no  _ | _         = there (findMain-name rest ir eq)
... | true  | _     | _         = there (findMain-name rest ir eq)

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

-- The SigOp trace the denotational `evalᴰ` reads off `main`'s IR (the
-- elaborated meaning), at observation depth `n` (Plan 0.46: the monadic
-- `⟦_⟧ᴰ` is THE source observable; the operational `otrace` is retired).
⟦_⟧IR : Maybe (IR Unit Unit) → Behavior
⟦ just ir ⟧IR = λ n → take n (projTrace (evalᴰ ir tt) n)
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
-- (#9) Main-finding alignment — DISCHARGED (Plan 0.45). The PROGRAM case
-- (D008: `--exe` needs a `main`; a library `--lib`, with no `main`, gives
-- `moduleToIR m ≡ nothing` and the empty-trace `no-main-empty` branch). When
-- `moduleToIR m` produces an entry IR the module IS a program, so it has a
-- source `main` `DFunDef` and `runTrace` runs it. Chains the compiler-side
-- correspondence (`MainAlign.compileResolvedModule-main`: a non-primitive entry
-- traces back to a `DFunDef "main"`) with the source-side
-- (`SS.lookup-main-of-dfundef`). The J-style `aux` unfolds `moduleToIR` =
-- `moduleToIR-aux (compileResolvedModule …)` so its result is analysable.
main-exists-align :
  ∀ (m : P.Module) (ir : IR Unit Unit) → moduleToIR m ≡ just ir
  → ∃ λ (body : RawExpr) →
      SS.lookupDef (SS.extractDefs (P.Module.decls m)) "main" ≡ just body
main-exists-align m ir mj = aux (C.compileResolvedModule C.Heap false m) refl mj
  where
    aux : (r : String ⊎ List C.CompiledFun)
        → C.compileResolvedModule C.Heap false m ≡ r
        → moduleToIR-aux r ≡ just ir
        → ∃ λ body → SS.lookupDef (SS.extractDefs (P.Module.decls m)) "main" ≡ just body
    aux (inj₁ _)    crm ()
    aux (inj₂ funs) crm fm =
      SS.lookup-main-of-dfundef (P.Module.decls m)
        (MA.compileResolvedModule-main m C.Heap false funs crm (findMain-name funs ir fm))

-- (#10), now TOP-DOWN: the monolithic `compiled-main-trace` postulate becomes a
-- THEOREM assembled from `ET.bridge-main` (the proven `evalᴰ (elaborate …) ↔
-- SS.eval (erase …)` bridge over the typed `Expr`) and two smaller, named
-- obligations:
--
--   * `compiler-faithful` — the compiled entry IR IS the elaboration of a closed
--     typed `Expr` (`checkElab` of `main`), and that expr's canonical erasure
--     runs (under `SS.eval`) like the source `main` body. Bundles the compiler
--     identity (`ir = elaborate Heap (checkElab body)`, a lemma over
--     `compileResolvedModule`) with α-invariance (raw body ↔ canonical erasure).
--   * `elaborate-trace-correct` — the PRODUCTIVE trace correspondence: for the
--     elaboration of a closed `Expr`, the depth-`k` denotational trace prefix
--     agrees with `SS.eval` of its canonical erasure at SOME fuel `s`. This is
--     the genuine load-bearing statement and it is TRUE for BOTH finite mains
--     (the trace stabilises) AND productive `Ana` mains (the trace grows with
--     `k`, matched by a larger `s`) — it bakes in NO finiteness. (Earlier draft
--     folded a `budget-stable` conjunct into `compiler-faithful`; that was
--     UNSOUND — productive programs compile, and for them budget-stability is
--     false, so the postulate would prove ⊥. The `∀ k → ∃ s` shape IS the
--     productive form; that is where `Ana` is handled, not assumed away.) The
--     finite fragment of this is what `ET.bridge-main`'s terminating CompSim
--     proves; the `Ana` case is the productive sim — both discharge THIS, with
--     no finiteness baked into the apex.
postulate
  compiler-faithful :
    ∀ (m : P.Module) (ir : IR Unit Unit) → moduleToIR m ≡ just ir
    → (body : RawExpr)
    → SS.lookupDef (SS.extractDefs (P.Module.decls m)) "main" ≡ just body
    → Σ[ Ψ ∈ Usage 0 ] Σ[ eE ∈ Expr ∅ Ψ Unit ]
        (ir ≡ Surface.elaborate C.Heap eE)
        × (∀ s → SS.eval s (SS.extractDefs (P.Module.decls m)) [] body
                 ≡ SS.eval s (SS.extractDefs (P.Module.decls m)) []
                            (ET.erase (SS.extractDefs (P.Module.decls m)) eE))

  elaborate-trace-correct :
    ∀ {Ψ : Usage 0} (eE : Expr ∅ Ψ Unit) (defs : SS.Defs) (k : ℕ)
    → ∃[ s ] take k (proj₁ (evalᴰ (Surface.elaborate C.Heap eE) tt k))
               ≡ take k (SS.runTraceEval (SS.eval s defs [] (ET.erase defs eE)))

compiled-main-trace :
  ∀ (m : P.Module) (ir : IR Unit Unit) → moduleToIR m ≡ just ir
  → ∀ (body : RawExpr)
  → SS.lookupDef (SS.extractDefs (P.Module.decls m)) "main" ≡ just body
  → ∀ (k : ℕ)
  → ∃[ s ] take k (projTrace (evalᴰ ir tt) k)
             ≡ take k (SS.runTraceEval (SS.eval s (SS.extractDefs (P.Module.decls m)) [] body))
-- `ir = elaborate eE` (compiler identity); the depth-`k` trace prefix matches
-- `SS.eval (erase eE)` at fuel `s` (`elaborate-trace-correct`); and `erase eE`
-- runs like the source `body` (α-invariance). No budget-stability, no finiteness.
compiled-main-trace m ir mj body lk k
  with compiler-faithful m ir mj body lk
... | (Ψ , eE , refl , α)
    with elaborate-trace-correct eE (SS.extractDefs (P.Module.decls m)) k
...   | (s , eq) =
      s , trans eq (cong (λ r → take k (SS.runTraceEval r)) (sym (α s)))

-- Factor 1 (`elaborate-faithful`), a REQUIRED CONJUNCT of the grand theorem
-- (D059): the elaborated IR's denotational trace agrees, event-prefix-wise, with
-- the independent `SS.eval` reference. Composes the main-finding alignment, the
-- `#10` core, and the proven `runTrace-main` reduction (threaded at the
-- productivity witness `s`).
elaborate-preserves-trace :
  ∀ (m : P.Module) (ir : IR Unit Unit) → moduleToIR m ≡ just ir
  → ∀ (k : ℕ) → ∃[ s ] take k (projTrace (evalᴰ ir tt) k) ≡ take k (SS.runTrace m s)
elaborate-preserves-trace m ir mj k with main-exists-align m ir mj
... | (body , lk) with compiled-main-trace m ir mj body lk k
...   | (s , eq) = (s , trans eq (sym (cong (take k) (SS.runTrace-main m s body lk))))

-- The load-bearing cross-check as a NAMED type (D059): the elaborated IR's
-- denotational trace agrees, event-prefix-wise, with the independent `SS.eval`
-- reference. `Compile.compiler-correct` bundles this as a REQUIRED CONJUNCT of
-- the grand theorem so it cannot be dropped (silently losing load-bearing).
-- `elaborate-preserves-trace m ir mj : ElaborateFaithful ir m` definitionally.
ElaborateFaithful : IR Unit Unit → P.Module → Set
ElaborateFaithful ir m =
  ∀ (k : ℕ) → ∃[ s ] take k (projTrace (evalᴰ ir tt) k) ≡ take k (SS.runTrace m s)

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
-- D059: the source meaning is the DENOTATIONAL `evalᴰ` (compositional →
-- reasons about Once programs; observation-depth → commensurable apex meter),
-- via `⟦_⟧IR ∘ moduleToIR`. `SS.eval`/`SS.runTrace` is NOT the apex meaning —
-- it is the required cross-check (`elaborate-preserves-trace`, the #10 conjunct).
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
