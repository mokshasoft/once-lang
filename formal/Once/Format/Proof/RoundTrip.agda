-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.RoundTrip — formatting keeps the module (plan 0.124
-- step 4.4).
--
-- A well-formed module, formatted with any comments, is a text that parses
-- (the Spec's `Parses`) as the module: the layout's text lexes as the
-- declarations' tokens (`Proof.Module`), which read as the declarations
-- (`Proof.Decl`). A module the parser reads is well formed (`Proof.WF`), so
-- formatting what the compiler parses gives a text it parses alike
-- (`roundtrip`).
------------------------------------------------------------------------

module Once.Format.Proof.RoundTrip where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Parser using (parseStrict)
open import Once.Adequacy.FrontEndBridge using (parseStrict-sound; parseStrict-complete)
open import Once.Adequacy.SpecGrammar.Decl using (parses→; parses←)
open import Once.Format using (formatSource; formatParsed)
open import Once.Format.Lex using (lexItems)
open import Once.Format.Proof.LexOK using (DigitBound)
open import Once.Format.Proof.WF using (parsed-wf)

open import Once.Spec.Surface.Lexing using (TEOF)
open import Once.Spec.Surface.Grammar using (Parses)
open import Once.Spec.Surface.Syntax using (Decl; Module; mkModule)
open import Once.Format.Lex using (Item)
open import Once.Format.Print using (format; trivia)
open import Once.Format.Proof.Printable using (PD)
open import Once.Format.Proof.Module using (DeclOK; module-lexes)
open import Once.Format.Proof.Decl using (WFD; decl-ok; ds-parses)

private
  oks : ∀ {ds} → All PD ds → All DeclOK ds
  oks []       = []
  oks (p ∷ ps) = decl-ok _ p ∷ oks ps

-- | A well-formed module, formatted with any comments, parses as itself.
format-parses : ∀ ds (is : List Item) → All WFD ds → All PD ds → Parses (format (mkModule ds) is) (mkModule ds)
format-parses ds is wfs pds with module-lexes ds (trivia is) (oks pds)
... | ys , dsys , lx with ds-parses wfs dsys
...   | r , pd , tr = ys ++ TEOF ∷ [] , r , lx , pd , tr

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

-- | Formatting keeps the module: when the compiler's parser reads a text as
-- a module, `once fmt` writes a text, and the parser reads that text as the
-- same module. (`DigitBound`: the primitive `isDigit` accepts the decimal
-- digits only; a fact about the tool, not provable inside Agda.)
roundtrip : DigitBound → ∀ text m → parseStrict text ≡ inj₂ m
          → ∃[ out ] (formatSource text ≡ inj₂ out × parseStrict out ≡ inj₂ m)
roundtrip bound text (mkModule ds) eq with parsed-wf bound {text} {mkModule ds} (parses→ {text} (parseStrict-sound text (mkModule ds) eq))
... | wfs , pds =
  format (mkModule ds) (lexItems (toList text)) ,
  cong (formatParsed text) eq ,
  parseStrict-complete out (mkModule ds) (parses← {out} (format-parses ds (lexItems (toList text)) wfs pds))
  where
    out = format (mkModule ds) (lexItems (toList text))
