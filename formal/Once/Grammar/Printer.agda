-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.Printer
--
-- Plan 0.3, gap G1 (start): a pretty-printer from `GType` to a token
-- stream. Canonical form: ALWAYS emit explicit parentheses around
-- compound types. This avoids any precedence-reconstruction ambiguity
-- at the cost of verbose output.
--
-- Goal: `parseGType (printGType g) ≡ just (g, [])` for every g that
-- satisfies the grammar's constructors. The round-trip proof is the
-- next step (per-constructor induction).
--
-- Note: GType has `TVar` (for grammar-level type variables) and
-- `TEff` (the effect monad constructor). Both are explicitly
-- supported by the parser for `Eff A B` and (partially via
-- `tryParseTypeVar`) uppercase identifiers. The arrow's quantity
-- annotation is always emitted as `^q` for unambiguous parse:
-- `Many → ^w`, `One → ^1`, `Zero → ^0`.
------------------------------------------------------------------------

module Once.Grammar.Printer where

open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)

open import Once.Type using (Quantity; Zero; One; Many)
import Once.Grammar as G
open G using (GType)
open import Once.Parser.Token

------------------------------------------------------------------------
-- Quantity token
------------------------------------------------------------------------

quantityToken : Quantity → Token
quantityToken Zero = TCaret0
quantityToken One  = TCaret1
quantityToken Many = TCaretW

------------------------------------------------------------------------
-- GType printer
------------------------------------------------------------------------

-- | Print a GType as a canonical token stream with explicit parens
-- around every compound type. Base types print as a single token.
printGType : GType → List Token
printGType G.TUnit   = TWord "Unit"   ∷ []
printGType G.TVoid   = TWord "Void"   ∷ []
printGType G.TInt    = TWord "Int"    ∷ []
printGType G.TFloat  = TWord "Float"  ∷ []
printGType G.TBuffer = TWord "Buffer" ∷ []
printGType G.TString = TWord "String" ∷ []
printGType (G.TVar name) = TWord name ∷ []
printGType (A G.⊗ B) =
  TLParen ∷ printGType A ++ TStar ∷ printGType B ++ TRParen ∷ []
printGType (A G.⊕ B) =
  TLParen ∷ printGType A ++ TPlus ∷ printGType B ++ TRParen ∷ []
printGType (A G.⇒[ q ] B) =
  TLParen ∷ printGType A ++ quantityToken q ∷ TArrow ∷ printGType B ++ TRParen ∷ []
printGType (G.TEff A B) =
  TLParen ∷ TWord "Eff" ∷ printGType A ++ printGType B ++ TRParen ∷ []

------------------------------------------------------------------------
-- Round-trip theorem: parseGType ∘ printGType ≡ just
--
-- This is the headline G1 claim. The proof is per-constructor
-- induction on GType. Each compound case threads the parser through
-- the opening paren, recurses into the components, consumes the
-- infix token, and closes with the matching paren.
--
-- **Current status**: theorem statement drafted; proof is future
-- work — the per-step threading requires explicit token-list append
-- manipulation which Agda doesn't automate. Commented here so the
-- shape is visible at review time.
--
-- round-trip : ∀ (g : GType) → parseGType (printGType g) ≡ just (g , [])
--
-- The compound cases need list-append reasoning (++-assoc, ∷-++)
-- plus the parser's step-by-step consumption matched against the
-- printer's output. Each case is 10-20 lines; the full proof is
-- ~200 lines.
--
-- Unblocks G5 integration — once round-trip holds, every GType in
-- the parser's output is grammar-faithful by construction.
------------------------------------------------------------------------
