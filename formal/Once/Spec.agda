{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec — the definition of the Once language.
--
-- The Spec is the modules under `Once/Spec`; this is their index, in reading
-- order. It defines nothing and re-exports nothing. Everything else (the
-- parser, the checker, the compiler, the machine models, every proof) is the
-- implementation, checked against the Spec and never trusted in its place.
--
-- A program is a composition of morphisms: a telescope of definitions over a
-- signature Σ of operations, built from a cartesian closed core with initial
-- algebras and final coalgebras, whose effects are the free monad on Σ (a
-- finite block of calls) and the resumption monad over it (blocks forever,
-- the stream of blocks). What it means is its trace against an
-- Interpretation of Σ: the operations it performs, in a run that may go on
-- forever.
------------------------------------------------------------------------

module Once.Spec where

-- The objects.
import Once.Spec.Grade           -- usage and effect grades
import Once.Spec.Type            -- the types, over type variables
import Once.Spec.Type.Substitution  -- substitution is functorial (the one proof, D335)
import Once.Spec.Sub             -- subtyping
import Once.Spec.Name            -- canonical names
import Once.Spec.Word            -- `Int`: the target's machine word
import Once.Spec.Float.Dyadic    -- `Float`: the target's format …
import Once.Spec.Float.Decimal   -- … its literals, rounded once …
import Once.Spec.Float.Arith     -- … and its arithmetic
import Once.Spec.Numerics        -- the target's numbers
import Once.Spec.Bool            -- truth values

-- Effects, and what is observed.
import Once.Spec.Signature       -- the operations Σ and their functor H_Σ
import Once.Spec.Effect          -- T = μ(X + H_Σ), streams, T∞ = νY. T(X + Y), the grades' monads
import Once.Spec.Delay           -- a value that may never arrive
import Once.Spec.Trace           -- traces and weak bisimilarity
import Once.Spec.Observation     -- the world, and a computation's trace in it
import Once.Spec.Polynomial      -- polynomial functors and their initial algebras
import Once.Spec.Domain          -- the value of each type
import Once.Spec.Equivalence     -- when two meanings are the same

-- The core calculus.
import Once.Spec.Context         -- contexts and usages
import Once.Spec.Core.Syntax     -- terms
import Once.Spec.Core.Typing     -- the typing judgment
import Once.Spec.Core.Meaning    -- the meaning of a derivation
import Once.Spec.Core.Derived    -- the categorical combinators, as terms
import Once.Spec.Core.Program    -- a program, and what it does

-- What a programmer writes.
import Once.Spec.Surface.Syntax      -- the syntax tree
import Once.Spec.Surface.Lexing      -- text to tokens
import Once.Spec.Surface.Grammar     -- tokens to a module
import Once.Spec.Surface.Resolution  -- what each name denotes
import Once.Spec.Surface.Typing      -- which expressions are typed, and their core terms
import Once.Spec.Surface.Program     -- the program a module denotes
import Once.Spec.Source              -- what a source text denotes

-- What a correct compiler is, and what the language promises about itself.
import Once.Spec.Correct
import Once.Spec.Examples
import Once.Spec.Metatheory
