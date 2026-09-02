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
-- NOTE on `ParsesText`: it is the independent GRAMMAR relation, but its leaves
-- still mention executable helpers (`skipNewlines toks ≡ just …`,
-- `headK c ≡ hkWS`). It is therefore weaker than a fully independent grammar,
-- and that is a real limit on how much `_⊢R_` pins the front end. Recorded
-- rather than hidden; see plan 0.81.
------------------------------------------------------------------------

module Once.Spec.Program where

open import Data.Product using (Σ-syntax; _,_)

import Once.Parser.Module.Core as P

-- The four predicates `Typed` / `_⊢R_` are built from. Named explicitly, so a
-- reader of the criterion has the whole statement in one place.
open import Once.Adequacy.FrontEndBridge public using (ParsesText)
open import Once.Adequacy.AcceptSound    public using (ModuleTyped)
open import Once.Adequacy.ModuleComplete public using (HasValidMain-decl)
open import Once.Denotation.Behavior     public using (Source)
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
-- Plan 0.81 will extend this to cover RESOLUTION as well (`m` is currently the
-- UN-resolved parsed module), which is what puts the name → CanonicalName map
-- under specification.
------------------------------------------------------------------------

_⊢R_ : Source → Typed → Set
src ⊢R (m , _ , _) = ParsesText (Source.srcText src) m
