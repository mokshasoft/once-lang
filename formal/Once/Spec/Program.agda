-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Program — WHAT A TYPED PROGRAM IS, and WHEN A SOURCE DENOTES ONE
-- (OCP-0006, spec). Plan 0.81.
--
-- SPEC (trust boundary). `Once.Spec.Correct` exports `CorrectCompiler`, whose
-- `Typed` and `_⊢_` are ABSTRACT FIELDS — so the record alone does not say what
-- the theorem claims. The instance's filling of those fields does, and until
-- this module existed it lived in `Once.Adequacy.Compile`, OUTSIDE the boundary
-- it constitutes. `Spec/Correct.agda`'s own header names the risk: "a
-- wrong/vacuous statement here would make every instance proof worthless".
-- This module closes that gap: the two definitions live here, and the four
-- predicates they are built from are NAMED here.
--
-- `Typed` and `_⊢R_` were also inside `Compile.WithCPU`, an ARCH-PARAMETERISED
-- module, though neither mentions the architecture. `CorrectCompiler`'s comment
-- says outright that `Typed` is target-FREE; being defined here makes that
-- manifest rather than incidental.
--
-- NOTE on `ModuleTyped` (plan 0.59): it is DEFINED by running the front end —
-- `ModuleTyped m = ModuleTyped-ef m (extractFunctions (extractAliases m) m)` —
-- so the spec's notion of "well-typed" depends on an executable, and
-- transitively on the principality oracle. That is a real hole, larger than
-- anything plan 0.81 touches, and it is why `_⊢R_` may use `polyDefNames`
-- without making things worse: the dependency is already there, one field over.
--
-- NOTE on `ParsesText`: it is the independent GRAMMAR relation, but its leaves
-- still mention executable helpers (`skipNewlines toks ≡ just …`,
-- `headK c ≡ hkWS`). It is therefore weaker than a fully independent grammar,
-- and that is a real limit on how much `_⊢R_` pins the front end. Recorded
-- rather than hidden; see plan 0.81.
------------------------------------------------------------------------

module Once.Spec.Program where

open import Data.Product using (Σ-syntax; _,_; _×_)

import Once.Parser.Module.Core as P

-- The four predicates `Typed` / `_⊢R_` are built from. Named explicitly, so a
-- reader of the criterion has the whole statement in one place.
open import Once.Spec.Parsing public using (ParsesText)
open import Once.Spec.Module public using (ModuleTyped; HasValidMain-decl)
open import Once.Denotation.Behavior     public using (Source)
open import Once.Spec.Resolution         public using (ResolvesModule; rm)
open import Once.Parser.Module.Resolve   using (polyDefNames)
open Once.Denotation.Behavior.Source public using (srcText; srcImports)

------------------------------------------------------------------------
-- A typed program: a module that is DECLARATIVELY well-typed (`ModuleTyped`,
-- an ∃ over `⊢ᶜ` derivations — no elaborator appears) and has a
-- declaratively-valid `main`. The compiler fact `moduleToIR ≡ just` is DERIVED
-- from these, never assumed.
------------------------------------------------------------------------

Typed : Set
Typed = Σ-syntax P.Module (λ m →
          Σ-syntax (ModuleTyped m) (λ mt → HasValidMain-decl m mt))

------------------------------------------------------------------------
-- `src ⊢R tp` — the source TEXT denotes `tp`'s module, by the grammar
-- relation. NOT the executable `parseStrict`, NOT the typechecker, NOT the
-- import resolver.
--
-- Plan 0.52 / THE TRAP: anchoring on the executable front end (or the
-- resolver) would put it symmetrically on both sides of the criterion and
-- CANCEL — completeness would be front-end/resolver-vacuous. The gaps to the
-- executable front end and to resolved compilation are the named
-- `FrontEndBridge` / `ResolverBridge` obligations, and that is the whole reason
-- this relation is stated independently.
--
-- Plan 0.81: it covers RESOLUTION as well, and `Typed` holds the RESOLVED
-- module. Two things follow.
--
-- The name → CanonicalName map is now under specification: a resolver that
-- sent `foo` to the wrong module fails `ResolvesModule`, where before it
-- satisfied all three "something survives resolution" obligations.
--
-- And it is what makes the criterion say anything at all about a program that
-- uses a generator. D136 makes bare `fst` mean `Generators.fst`, so
-- `ModuleTyped` over the UN-resolved module is underivable for such a program:
-- with `Typed` holding `mU`, both conjuncts would be silent about essentially
-- every real Once program.
--
-- The scope argument is `polyDefNames`, the same classification `ModuleTyped`
-- already reaches through `extractFunctions` — they share `siglessSchema` BY
-- CONSTRUCTION — so the principality oracle enters this boundary once, not
-- twice. Making that classification independent is plan 0.59's subject; see
-- the note on `ModuleTyped` below.
------------------------------------------------------------------------

_⊢R_ : Source → Typed → Set
src ⊢R (mR , _ , _) =
  Σ-syntax P.Module (λ mU →
    ParsesText (Source.srcText src) mU
    × ResolvesModule (Source.srcImports src) (polyDefNames (P.Module.decls mU)) mU mR)
