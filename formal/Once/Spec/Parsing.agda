-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Parsing — what it MEANS for source text to parse (Plan 0.84).
--
-- This is the spec reviewer's single entry point into the front-end grammar:
-- `ParsesText` is what the apex `_⊢R_` anchors on, and everything it names is
-- re-exported here, so the whole claim is reachable from one module.
--
-- No proof lives here or in anything it re-exports. The bridges that force
-- the executable front end to agree — `lexer-sound`/`-complete`,
-- `sound-decl`/`complete-decl`, `parseStrict-sound`/`-complete` — are in
-- `Once.Adequacy.*` / `Once.Grammar.*` and are NOT part of what is claimed.
--
-- KNOWN WEAKNESS (plan 0.59): the relations are phrased against the parser's
-- own helpers (`skipNewlines`, `parseDeclB`, `allTrailing`, the lexer's
-- classifiers). A spec that names the implementation's functions is weaker
-- than one that does not. It is recorded, not hidden — the imports below say
-- exactly which helpers the claim depends on.
------------------------------------------------------------------------

module Once.Spec.Parsing where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token using (Token)
open import Once.Parser.Module.Core using (Decl; Module)
open Module using (decls)
open import Once.Parser.Core using (skipNewlines)
open import Once.Parser.Module using (parseDeclB)
open import Once.Parser using (allTrailing)

open import Once.Spec.Lexing       public using (Lexes)
open import Once.Spec.Grammar.Decl public
  using (ParsesDecl; ParsesImport; ParsesTypeAliasDecl; ParsesSignature;
         ParsesFunDef; ParsesOpDecl)

------------------------------------------------------------------------
-- The declaration loop. (`skipNewlines` never returns `nothing`, so
-- `pds-noskip` aligns the relation with an unreachable parser clause.)
------------------------------------------------------------------------

data ParsesDecls : List Token → List Decl → List Token → Set where
  pds-noskip : ∀ {toks} → skipNewlines toks ≡ nothing → ParsesDecls toks [] toks
  pds-stop : ∀ {toks nl toks'} →
    skipNewlines toks ≡ just (nl , toks') → parseDeclB toks' ≡ nothing →
    ParsesDecls toks [] toks'
  pds-cons : ∀ {toks nl toks' d rest ds rest'} →
    skipNewlines toks ≡ just (nl , toks') → ParsesDecl toks' d rest →
    ParsesDecls rest ds rest' →
    ParsesDecls toks (d ∷ ds) rest'

------------------------------------------------------------------------
-- A module is its declaration list (via the record accessor, so it reduces
-- for an abstract `m`).
------------------------------------------------------------------------

ParsesModule : List Token → Module → List Token → Set
ParsesModule toks m rest = ParsesDecls toks (decls m) rest

------------------------------------------------------------------------
-- The apex anchor: text lexes, the tokens parse, and nothing but trailing
-- filler is left over.
------------------------------------------------------------------------

ParsesText : String → Module → Set
ParsesText text m =
  Σ[ toks ∈ List Token ] Σ[ rest ∈ List Token ]
    (Lexes text toks × ParsesModule toks m rest × (allTrailing rest ≡ true))
