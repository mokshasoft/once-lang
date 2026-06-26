-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.FrontEndBridge — the NAMED front-end (lexer + parser)
-- correctness obligations (Plan 0.52, scaffold stage).
--
-- The lexer (`tokenizeString`) and parser (`parseModule`/`parseStrict`) were
-- the last region of OUR compiler code OUTSIDE the verified apex: the apex used
-- to anchor at a `GModule` taken as given, never running the executable parser,
-- so the rich parser↔grammar proofs (`Once.Grammar.ParserBridge` sound/complete,
-- `Once.Grammar.Roundtrip`, `Once.Grammar.Convert` conformance) were ISLANDS —
-- typechecked but not consumed by the grand theorem `correct`.
--
-- Plan 0.52 anchors `Source` at the raw program TEXT and runs the executable
-- front-end (`parseStrict`) INSIDE the verified `compile`. The apex's INDEPENDENT
-- meaning is anchored on `ParsesText` — the GRAMMAR/relational spec "this text
-- denotes this AST", INDEPENDENT of `parseStrict` (defining `ParsesText` AS
-- `parseStrict` would make completeness front-end-vacuous — the same trap the
-- resolver `_⊢R_` guards against, see `Once.Adequacy.ResolverBridge`). The two
-- bridges below force the executable lexer+parser to agree with that spec.
--
-- They are POSTULATES for now (scaffold stage, mirroring `ResolverBridge`): the
-- front-end IS structurally in the verified loop, the obligations are EXPLICIT
-- and NAMED (`make postulates` lists them). DISCHARGE PATH — this is exactly
-- where the existing islands get wired in:
--   * `ParsesText` := a module/decl-level parse relation `ParsesModule`
--     (to be built) composing the EXISTING expr/type relations
--     (`Once.Parser.ExprRelation`, `Once.Parser.TypeRelation`) + a relational
--     LEXER spec for `tokenizeString` (text → tokens), which does not yet exist.
--   * `parseStrict-sound`  := `Once.Grammar.ParserBridge.sound-*` (+ `ExprBridge`)
--     lifted from type/expr to the module level, ∘ lexer soundness.
--   * `parseStrict-complete` := `ParserBridge.complete-*` (+ `Roundtrip`
--     `parse ∘ print ≡ id`, `Convert` grammar-conformance) lifted to modules,
--     ∘ lexer completeness.
-- So the type/expr islands stop dangling: they become the named discharge
-- material for these module-level facts. The genuinely-NEW work is the
-- module/decl-level lift and the relational lexer.
------------------------------------------------------------------------

module Once.Adequacy.FrontEndBridge where

open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.Parser.Module.Core as P
open import Once.Parser using (parseStrict)

postulate
  -- INDEPENDENT front-end spec: source `text` denotes AST `m`. MUST be defined
  -- via the grammar / module-level parse relation + relational lexer — NEVER as
  -- `parseStrict` (that re-introduces vacuity).
  ParsesText : String → P.Module → Set

  -- SOUNDNESS — the executable front-end only accepts text the spec accepts
  -- (soundness builds `tp` over the parsed module). Discharge: `ParserBridge`
  -- sound-direction lifted to modules ∘ lexer soundness.
  parseStrict-sound :
    ∀ (text : String) (m : P.Module) →
    parseStrict text ≡ inj₂ m → ParsesText text m

  -- COMPLETENESS — every text the spec accepts the executable front-end parses
  -- (completeness: an independently-parseable text compiles). Discharge:
  -- `ParserBridge` complete-direction + `Roundtrip`/`Convert` lifted to modules
  -- ∘ lexer completeness.
  parseStrict-complete :
    ∀ (text : String) (m : P.Module) →
    ParsesText text m → parseStrict text ≡ inj₂ m
