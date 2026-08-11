-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
printGFunctor : G.GFunctor → List Token
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
printGType (G.GMu gf) =
  TWord "Mu" ∷ TLParen ∷ printGFunctor gf ++ TRParen ∷ []

-- | Print a grammar-level functor (canonical, fully parenthesised).
printGFunctor (G.GFK g) =
  TLParen ∷ TWord "K" ∷ printGType g ++ TRParen ∷ []
printGFunctor G.GFId = TWord "Id" ∷ []
printGFunctor (G.GFSum f g) =
  TLParen ∷ printGFunctor f ++ TPlus ∷ printGFunctor g ++ TRParen ∷ []
printGFunctor (G.GFProd f g) =
  TLParen ∷ printGFunctor f ++ TStar ∷ printGFunctor g ++ TRParen ∷ []

------------------------------------------------------------------------
-- Round-trip theorems: parseGType ∘ printGType ≡ just
--
-- Per-constructor theorems. Base cases are direct refl; the
-- compound cases need explicit list-append reasoning and are
-- drafted for future work.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Once.Grammar.Convert using (parseGType)

round-trip-Unit : parseGType (printGType G.TUnit) ≡ just (G.TUnit , [])
round-trip-Unit = refl

round-trip-Void : parseGType (printGType G.TVoid) ≡ just (G.TVoid , [])
round-trip-Void = refl

round-trip-Int : parseGType (printGType G.TInt) ≡ just (G.TInt , [])
round-trip-Int = refl

round-trip-Float : parseGType (printGType G.TFloat) ≡ just (G.TFloat , [])
round-trip-Float = refl

round-trip-Buffer : parseGType (printGType G.TBuffer) ≡ just (G.TBuffer , [])
round-trip-Buffer = refl

round-trip-String : parseGType (printGType G.TString) ≡ just (G.TString , [])
round-trip-String = refl

-- Compound round-trip smoke tests: specific concrete GTypes whose
-- printed token streams the parser can reduce computationally (refl
-- suffices). These don't prove the general compound case, but they
-- document that the printer + parser agree on canonical inputs.

round-trip-Unit⊗Int-smoke :
  parseGType (printGType (G.TUnit G.⊗ G.TInt)) ≡ just (G.TUnit G.⊗ G.TInt , [])
round-trip-Unit⊗Int-smoke = refl

round-trip-Int⊕Str-smoke :
  parseGType (printGType (G.TInt G.⊕ G.TString)) ≡ just (G.TInt G.⊕ G.TString , [])
round-trip-Int⊕Str-smoke = refl

round-trip-Int⇒Int-smoke :
  parseGType (printGType (G.TInt G.⇒[ Many ] G.TInt))
    ≡ just (G.TInt G.⇒[ Many ] G.TInt , [])
round-trip-Int⇒Int-smoke = refl

round-trip-linear-smoke :
  parseGType (printGType (G.TInt G.⇒[ One ] G.TInt))
    ≡ just (G.TInt G.⇒[ One ] G.TInt , [])
round-trip-linear-smoke = refl

round-trip-erased-smoke :
  parseGType (printGType (G.TInt G.⇒[ Zero ] G.TUnit))
    ≡ just (G.TInt G.⇒[ Zero ] G.TUnit , [])
round-trip-erased-smoke = refl

-- Nested compounds.
round-trip-nested-product-smoke :
  parseGType (printGType ((G.TInt G.⊗ G.TString) G.⊗ G.TUnit))
    ≡ just ((G.TInt G.⊗ G.TString) G.⊗ G.TUnit , [])
round-trip-nested-product-smoke = refl

round-trip-arrow-into-product-smoke :
  parseGType (printGType (G.TInt G.⇒[ Many ] (G.TInt G.⊗ G.TString)))
    ≡ just (G.TInt G.⇒[ Many ] (G.TInt G.⊗ G.TString) , [])
round-trip-arrow-into-product-smoke = refl

round-trip-curried-linear-smoke :
  parseGType (printGType (G.TInt G.⇒[ One ] (G.TInt G.⇒[ One ] G.TInt)))
    ≡ just (G.TInt G.⇒[ One ] (G.TInt G.⇒[ One ] G.TInt) , [])
round-trip-curried-linear-smoke = refl

round-trip-sum-of-arrows-smoke :
  parseGType (printGType
    ((G.TInt G.⇒[ Many ] G.TInt) G.⊕ (G.TString G.⇒[ Many ] G.TUnit)))
    ≡ just
    ((G.TInt G.⇒[ Many ] G.TInt) G.⊕ (G.TString G.⇒[ Many ] G.TUnit) , [])
round-trip-sum-of-arrows-smoke = refl

------------------------------------------------------------------------
-- Concrete GType predicate (`TVar`-free) for the round-trip domain
--
-- Plan 0.2.5 deliberately disabled type-variable parsing in user-
-- written surface types (type variables live only in PolyType
-- signatures now). So parsing a printed `TVar x` would currently
-- fail — the round-trip theorem restricts to the TVar-free subset
-- of GType, which matches the invariant the parser already enforces.
--
-- This mirrors the `NoMuNu` approach for the Type-side conversion.
------------------------------------------------------------------------

data Concrete : GType → Set where
  c-unit   : Concrete G.TUnit
  c-void   : Concrete G.TVoid
  c-int    : Concrete G.TInt
  c-float  : Concrete G.TFloat
  c-buffer : Concrete G.TBuffer
  c-string : Concrete G.TString
  c-prod   : ∀ {A B} → Concrete A → Concrete B → Concrete (A G.⊗ B)
  c-sum    : ∀ {A B} → Concrete A → Concrete B → Concrete (A G.⊕ B)
  c-fun    : ∀ {A B q} → Concrete A → Concrete B → Concrete (A G.⇒[ q ] B)
  c-eff    : ∀ {A B} → Concrete A → Concrete B → Concrete (G.TEff A B)
  -- no c-var: TVar is excluded from the round-trip domain

------------------------------------------------------------------------
-- Claim for the general theorem (future work):
--
--   round-trip-concrete : ∀ {g} → Concrete g
--                       → parseGType (printGType g) ≡ just (g , [])
--
-- Proof: induction on Concrete. Base cases are refl; compound cases
-- require list-append reasoning (++-assoc, ∷-++) to thread the
-- parser's sequential token consumption through the printer's
-- paren-delimited output. Each compound case is ~20 lines of
-- structural reasoning. The smoke tests above demonstrate the shape
-- holds for concrete canonical inputs.
------------------------------------------------------------------------
