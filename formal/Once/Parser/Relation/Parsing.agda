-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Relation.Parsing — what it MEANS for source text to parse (Plan 0.84).
--
-- The waypoint of the front end's proof: `ParsesText` says what the lexer
-- and the parser do, as a relation, phrased with the parser's own helpers
-- (`skipNewlines`, `parseDeclB`, `allTrailing`, the lexer's classifiers).
-- The executable front end meets it (`lexer-sound`/`-complete`,
-- `sound-decl`/`complete-decl`, `parseStrict-sound`/`-complete`, in
-- `Once.Adequacy.*` / `Once.Grammar.*`), and it meets the Spec's grammar
-- (`Once.Spec.Surface.Grammar`) by `Once.Adequacy.SpecGrammar.Decl`.
------------------------------------------------------------------------

module Once.Parser.Relation.Parsing where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token using (Token)
open import Once.Spec.Surface.Syntax using (Decl; Module)
open Module using (decls)
open import Once.Parser.Core using (skipNewlines)
open import Once.Parser.Module using (parseDeclB)
open import Once.Parser using (allTrailing)

open import Once.Parser.Relation.Lexing using (Lexes)
open import Once.Parser.Relation.Decl using (ParsesDecl)

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
