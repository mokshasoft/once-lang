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
open import Once.Spec.Resolution public -- what each written reference DENOTES
  using ( ResolvesVar ; rv-binder ; rv-gen ; rv-import ; rv-own
        ; ResolvesExpr ; re-var ; re-this ; re-qual ; re-qual-unknown ; re-res
        ; re-app ; re-lam ; re-let ; re-pair ; re-destruct ; re-annot
        ; re-binop ; re-unop ; re-ana ; re-unit ; re-int ; re-float ; re-str
        ; ResolvesDecl ; rd-fundef ; rd-typesig ; rd-signature
        ; rd-typealias ; rd-import
        ; ResolvesDecls ; rds-nil ; rds-cons ; rds-import
        ; ResolvesModule ; rm ; NotImport
        ; nim-typesig ; nim-fundef ; nim-sig ; nim-alias
        ; ExpandsTo ; ex-nil ; ex-I ; ex-other
        ; AliasMap ; UnaliasedMap ; Absent ; FirstAt ; fa-here ; fa-there )
open import Once.Spec.Meaning public   -- the denotation (source meaning)
open import Once.Spec.Correct public   -- the CorrectCompiler criterion
open import Once.Spec.Program public   -- WHAT a typed program is, and WHEN a
  using ( Typed ; _⊢R_               -- source denotes one: the criterion's own
        ; ParsesText ; ModuleTyped   -- `Typed`/`_⊢_`, which used to live in a
        ; HasValidMain-decl )        -- PROOF module, outside this boundary
