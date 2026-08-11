-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec — ONE HOME FOR THE LANGUAGE DEFINITION (OCP-0006).
--
-- The single, namespaced, auditable door to *what a Once program is*: the two
-- faces a reader must trust and read — WHAT YOU MAY WRITE (the type/syntax
-- grammar + typing rules) and WHAT IT MEANS (the denotation) — plus the
-- top-level CORRECTNESS CRITERION the compiler is verified against.
--
-- The trust boundary is enumerable: it is exactly the imports below (and, one
-- hop down, each leaf's imports). Everything else — the elaborator, classifier,
-- soundness/completeness proofs, the parser, `Once.IR`, codegen, the abstract
-- machine, all simulation proofs — is IMPLEMENTATION, checked against this spec,
-- never trusted in its place.
--
-- Purely organizational (OCP-0006 re-export cut): no logic lives here.
------------------------------------------------------------------------

module Once.Spec where

open import Once.Spec.Type    public   -- the type / functor-type grammar
open import Once.Spec.Syntax  public   -- Raw (written) + Surface (denoted) terms
open import Once.Spec.Typing  public   -- the declarative typing judgment
open import Once.Spec.Meaning public   -- the denotation (source meaning)
open import Once.Spec.Correct public   -- the CorrectCompiler criterion
