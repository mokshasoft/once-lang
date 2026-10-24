-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Program — WHAT A TYPED PROGRAM IS, and WHEN A SOURCE DENOTES ONE
-- in the compiler's internal language. Plan 0.81.
--
-- The compiler's own correctness (`Compile.correctᵈ`) is stated over these:
-- `Typed` and `_⊢R_`. They are no longer the shipped theorem's — that is the
-- Spec's (`Once.Certified.once-compiler`, D332), reached from this one by the
-- proved bridges (`Once.Adequacy.SpecApex`). The four predicates they are
-- built from are named here.
--
-- `Typed` and `_⊢R_` were also inside `Compile.WithCPU`, an ARCH-PARAMETERISED
-- module, though neither mentions the architecture. `CorrectCompiler`'s comment
-- says outright that `Typed` is target-FREE; being defined here makes that
-- manifest rather than incidental.
--
-- NOTE on `ModuleTyped` (plan 0.59): it is DEFINED by running the front end —
-- `ModuleTyped m = ModuleTyped-ef m (extractFunctions m)` —
-- so the spec's notion of "well-typed" depends on an executable. (The
-- principality oracle is gone, D323; resolution no longer needs the module's
-- polymorphic names, D330.)
--
-- NOTE on `ParsesText`: it is the independent GRAMMAR relation, but its leaves
-- still mention executable helpers (`skipNewlines toks ≡ just …`,
-- `headK c ≡ hkWS`). It is therefore weaker than a fully independent grammar,
-- and that is a real limit on how much `_⊢R_` pins the front end. Recorded
-- rather than hidden; see plan 0.81.
------------------------------------------------------------------------

module Once.Internal.Program where

open import Data.Product using (Σ-syntax; _,_; _×_)

import Once.Parser.Module.Core as P

-- The four predicates `Typed` / `_⊢R_` are built from. Named explicitly, so a
-- reader of the criterion has the whole statement in one place.
open import Once.Internal.Parsing public using (ParsesText)
open import Once.Internal.Module public using (ModuleTyped; HasValidMain)
open import Once.Denotation.Behavior     public using (Source)
open import Once.Internal.Resolution         public using (ResolvesModule; rm)
open Once.Denotation.Behavior.Source public using (srcText; srcImports)

------------------------------------------------------------------------
-- A typed program: a module that is DECLARATIVELY well-typed (`ModuleTyped`,
-- an ∃ over `⊢ᶜ` derivations — no elaborator appears) and has a
-- declaratively-valid `main`. The compiler fact `moduleToIR ≡ just` is DERIVED
-- from these, never assumed.
------------------------------------------------------------------------

-- D241/D243 (plan 0.103 6c′): `ModuleTyped m` is the module TELESCOPE — every
-- definition, monomorphic or polymorphic, typed ONCE in the scope of the
-- definitions declared before it, used or not.
Typed : Set
Typed = Σ-syntax P.Resolved (λ m → Σ-syntax (ModuleTyped m) (λ mt → HasValidMain m mt))

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
------------------------------------------------------------------------

_⊢R_ : Source → Typed → Set
src ⊢R (mR , _ , _) =
  Σ-syntax P.Module (λ mU →
    ParsesText (Source.srcText src) mU
    × ResolvesModule (Source.srcImports src) mU mR)
