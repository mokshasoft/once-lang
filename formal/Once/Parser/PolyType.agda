-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.PolyType
--
-- Parser for polymorphic types (`PolyType` with `PTVar`).
--
-- Separate from `Once.Parser.Type` (which parses ground `Type`)
-- because user-declared polymorphic signatures — `swap : a * b →
-- b * a` — need a type grammar that accepts type variables. Ground
-- `Type` stays TVar-free by design; see plan 0.2.5 for the rationale.
--
-- Grammar (lowercase-TVar convention, plan 0.6):
--   PolyType     ::= PolySum ArrowTail | PolySum
--   ArrowTail    ::= GradeAnn? '->' PolyType
--   GradeAnn     ::= '^1' | '^0' | '^w'
--   PolySum      ::= PolyProd ('+' PolyProd)*
--   PolyProd     ::= PolyAtom ('*' PolyAtom)*
--   PolyAtom     ::= 'Unit' | 'Void' | 'Int' | 'Float' | 'Buffer' | 'String'
--                  | 'Eff' PolyAtom PolyAtom | 'IO' PolyAtom
--                  | lower_ident                                -- type variable
--                  | '(' PolyType ')'
--
-- Termination: structurally recursive on the input token list. Each
-- recursive call is on a strict-suffix of the input. Marked
-- `{-# TERMINATING #-}` pending a proper well-founded rewrite
-- (plan 0.7 Phase 2, which will also add a `ParsesPolyType` relational
-- specification paralleling `ParsesType`).
------------------------------------------------------------------------

module Once.Parser.PolyType where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Char using (isLower)
import Data.String as StrLib
open import Relation.Nullary using (yes; no)

open import Once.Type
open import Once.Parser.Token
open import Once.Parser.Core using (Parser)

------------------------------------------------------------------------
-- Lowercase-identifier test — the lexical distinction between a type
-- variable and a type keyword / alias.
------------------------------------------------------------------------

-- | True iff `s` starts with a lowercase letter (a-z).
-- (Definition relocated to Once.Parser.CharClass; re-exported here so existing
-- importers `Once.Parser.PolyType using (isLowerWord)` keep working.)
open import Once.Parser.CharClass public using (isLowerWord)

------------------------------------------------------------------------
-- Parser state
------------------------------------------------------------------------

PolyParser : Set → Set
PolyParser A = List Token → Maybe (A × List Token)

------------------------------------------------------------------------
-- The parser itself
--
-- Mutual recursion between arrow / sum / product / atom levels.
-- Structurally recursive on the token list (each recursive call is
-- on a strict-suffix). Termination is structural but the `with`
-- chain obscures it from Agda's checker; TERMINATING is used
-- pending the plan 0.7 Phase 2 relational+WF rewrite.
------------------------------------------------------------------------

-- Result wrappers, to keep the functor cases free of nested `with`.
pkOf : Maybe (PolyType × List Token) → Maybe (PolyFunctor × List Token)
pkOf nothing          = nothing
pkOf (just (A , rest)) = just (PK A , rest)

pmuOf : Maybe (PolyFunctor × List Token) → Maybe (PolyType × List Token)
pmuOf nothing          = nothing
pmuOf (just (F , rest)) = just (Pμ-type F , rest)

{-# TERMINATING #-}
parsePolyTypeImpl     : PolyParser PolyType
parsePolySumImpl      : PolyParser PolyType
parsePolyProdImpl     : PolyParser PolyType
parsePolyAtomImpl     : PolyParser PolyType
parsePolyArrowTail    : PolyType → PolyParser PolyType
parsePolySumTail      : PolyType → PolyParser PolyType
parsePolyProdTail     : PolyType → PolyParser PolyType
-- Functor sub-grammar (for `Mu F` μ-type atoms). Mirrors the type
-- levels: funcSum (⊕) over funcProd (⊗) over funcAtom (`Id` | `K`
-- typeAtom | `(` funcSum `)`). `K`'s argument is a (poly)type atom.
parsePolyFuncSum      : PolyParser PolyFunctor
parsePolyFuncProd     : PolyParser PolyFunctor
parsePolyFuncAtom     : PolyParser PolyFunctor
parsePolyFuncSumTail  : PolyFunctor → PolyParser PolyFunctor
parsePolyFuncProdTail : PolyFunctor → PolyParser PolyFunctor

-- parsePolyType: sum-level + optional arrow tail
parsePolyTypeImpl toks with parsePolySumImpl toks
... | nothing = nothing
... | just (A , rest) = parsePolyArrowTail A rest

-- | Arrow tail: optional `^q ->` followed by a recursive PolyType.
parsePolyArrowTail A (TCaret1 ∷ TArrow ∷ rest) with parsePolyTypeImpl rest
... | nothing = nothing
... | just (B , rest') = just (A P⇒[ One ] B , rest')
parsePolyArrowTail A (TCaret0 ∷ TArrow ∷ rest) with parsePolyTypeImpl rest
... | nothing = nothing
... | just (B , rest') = just (A P⇒[ Zero ] B , rest')
parsePolyArrowTail A (TCaretW ∷ TArrow ∷ rest) with parsePolyTypeImpl rest
... | nothing = nothing
... | just (B , rest') = just (A P⇒[ Many ] B , rest')
parsePolyArrowTail A (TArrow ∷ rest) with parsePolyTypeImpl rest
... | nothing = nothing
... | just (B , rest') = just (A P⇒[ Many ] B , rest')
parsePolyArrowTail A toks = just (A , toks)  -- no arrow: A is complete

-- parsePolySum: product-level + left-assoc `+` tail
parsePolySumImpl toks with parsePolyProdImpl toks
... | nothing = nothing
... | just (A , rest) = parsePolySumTail A rest

parsePolySumTail A (TPlus ∷ rest) with parsePolyProdImpl rest
... | nothing = nothing
... | just (B , rest') = parsePolySumTail (A P+ B) rest'
parsePolySumTail A toks = just (A , toks)

-- parsePolyProd: atom-level + left-assoc `*` tail
parsePolyProdImpl toks with parsePolyAtomImpl toks
... | nothing = nothing
... | just (A , rest) = parsePolyProdTail A rest

parsePolyProdTail A (TStar ∷ rest) with parsePolyAtomImpl rest
... | nothing = nothing
... | just (B , rest') = parsePolyProdTail (A P* B) rest'
parsePolyProdTail A toks = just (A , toks)

-- parsePolyAtom: keywords, TVars (lowercase), or parenthesized PolyType.
parsePolyAtomImpl [] = nothing
parsePolyAtomImpl (TWord name ∷ rest) with name ≟ "Unit"
... | yes _ = just (PUnit , rest)
... | no _  with name ≟ "Void"
...   | yes _ = just (PVoid , rest)
...   | no _  with name ≟ "Int"
...     | yes _ = just (PInt , rest)
...     | no _  with name ≟ "Float"
...       | yes _ = just (PFloat , rest)
...       | no _  with name ≟ "Buffer"
...         | yes _ = just (PBuffer , rest)
...         | no _  with name ≟ "String"
...           | yes _ = just (PStr , rest)
...           | no _  with name ≟ "Eff"
...             | yes _ with parsePolyAtomImpl rest
...               | nothing = nothing
...               | just (A , rest1) with parsePolyAtomImpl rest1
...                 | nothing = nothing
...                 | just (B , rest2) = just (PEff A B , rest2)
parsePolyAtomImpl (TWord name ∷ rest) | no _ | no _ | no _ | no _ | no _ | no _ | no _
   with name ≟ "IO"
... | yes _ with parsePolyAtomImpl rest
...   | nothing = nothing
...   | just (A , rest1) = just (PEff PUnit A , rest1)
-- Otherwise: lowercase identifier = type variable; uppercase unknown
-- identifier fails (ground type keyword mis-spelling — surfaces as a
-- real error rather than silently becoming a TVar).
parsePolyAtomImpl (TWord name ∷ rest)
   | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
   with name ≟ "Mu"
... | yes _ = pmuOf (parsePolyFuncAtom rest)
parsePolyAtomImpl (TWord name ∷ rest)
   | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
   with isLowerWord name
...   | true  = just (PTVar name , rest)
...   | false = nothing

parsePolyAtomImpl (TLParen ∷ rest) with parsePolyTypeImpl rest
... | nothing = nothing
... | just (A , TRParen ∷ rest') = just (A , rest')
... | just _ = nothing

-- Other heads: parser rejects.
parsePolyAtomImpl (TInt _ ∷ _)     = nothing
parsePolyAtomImpl (TFloat _ _ _ ∷ _) = nothing
parsePolyAtomImpl (TString _ ∷ _)  = nothing
parsePolyAtomImpl (TRParen ∷ _)    = nothing
parsePolyAtomImpl (TLBrace ∷ _)    = nothing
parsePolyAtomImpl (TRBrace ∷ _)    = nothing
parsePolyAtomImpl (TColon ∷ _)     = nothing
parsePolyAtomImpl (TEquals ∷ _)    = nothing
parsePolyAtomImpl (TArrow ∷ _)     = nothing
parsePolyAtomImpl (TCaret0 ∷ _)    = nothing
parsePolyAtomImpl (TCaret1 ∷ _)    = nothing
parsePolyAtomImpl (TCaretW ∷ _)    = nothing
parsePolyAtomImpl (TLambda ∷ _)    = nothing
parsePolyAtomImpl (TComma ∷ _)     = nothing
parsePolyAtomImpl (TSemicolon ∷ _) = nothing
parsePolyAtomImpl (TAt ∷ _)        = nothing
parsePolyAtomImpl (TPipe ∷ _)      = nothing
parsePolyAtomImpl (TDot ∷ _)       = nothing
parsePolyAtomImpl (TPlus ∷ _)      = nothing
parsePolyAtomImpl (TMinus ∷ _)     = nothing
parsePolyAtomImpl (TStar ∷ _)      = nothing
parsePolyAtomImpl (TSlash ∷ _)     = nothing
parsePolyAtomImpl (TPercent ∷ _)   = nothing
parsePolyAtomImpl (TAmpersand ∷ _) = nothing
parsePolyAtomImpl (TLt ∷ _)        = nothing
parsePolyAtomImpl (TLe ∷ _)        = nothing
parsePolyAtomImpl (TGt ∷ _)        = nothing
parsePolyAtomImpl (TGe ∷ _)        = nothing
parsePolyAtomImpl (TEqEq ∷ _)      = nothing
parsePolyAtomImpl (TNeq ∷ _)       = nothing
parsePolyAtomImpl (TBang ∷ _)      = nothing
parsePolyAtomImpl (TNewline ∷ _)   = nothing
parsePolyAtomImpl (TEOF ∷ _)       = nothing

-- Functor sub-grammar bodies (for `Mu F`).
parsePolyFuncSum toks with parsePolyFuncProd toks
... | nothing = nothing
... | just (F , rest) = parsePolyFuncSumTail F rest

parsePolyFuncSumTail F (TPlus ∷ rest) with parsePolyFuncProd rest
... | nothing = nothing
... | just (G , rest') = parsePolyFuncSumTail (F P⊕ G) rest'
parsePolyFuncSumTail F toks = just (F , toks)

parsePolyFuncProd toks with parsePolyFuncAtom toks
... | nothing = nothing
... | just (F , rest) = parsePolyFuncProdTail F rest

parsePolyFuncProdTail F (TStar ∷ rest) with parsePolyFuncAtom rest
... | nothing = nothing
... | just (G , rest') = parsePolyFuncProdTail (F P⊗ G) rest'
parsePolyFuncProdTail F toks = just (F , toks)

-- funcAtom: `Id` | `K` typeAtom | `(` funcSum `)`.
parsePolyFuncAtom (TWord name ∷ rest) with name ≟ "Id" | name ≟ "K"
... | yes _ | _     = just (PId , rest)
... | no _  | yes _ = pkOf (parsePolyAtomImpl rest)
... | no _  | no _  = nothing
parsePolyFuncAtom (TLParen ∷ rest) with parsePolyFuncSum rest
... | nothing = nothing
... | just (F , TRParen ∷ rest') = just (F , rest')
... | just _ = nothing
parsePolyFuncAtom _ = nothing

-- | Top-level PolyType parser.
parsePolyType : Parser PolyType
parsePolyType = parsePolyTypeImpl

------------------------------------------------------------------------
-- Bounded variant: guarantees strict length decrease on success.
--
-- Needed by downstream WF parsers (`parseDeclB` / `parseDeclsWF`)
-- that derive their own termination proofs from the fact that
-- every successful type parse consumes at least one token.
--
-- Implementation: run the unbounded parser, then runtime-check the
-- length relation. On success the check is always true (every
-- `parsePolyType` success consumes ≥1 token); on the rare "parser
-- returned same-length residual" path (shouldn't happen
-- structurally) we return nothing rather than falsely asserting
-- the bound. Plan 0.7 Phase 2 replaces this runtime check with a
-- structural proof.
------------------------------------------------------------------------

open import Data.Nat using (_<_; _<?_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Parser.Generic.PolyInst
  using (parsePolyTypeP; sound-polyType; ParsesPolyType-shrink)

ParsePolyAtB : List Token → Set
ParsePolyAtB toks =
  Maybe (Σ[ t ∈ PolyType ] Σ[ rest ∈ List Token ] length rest < length toks)

-- Plan 0.7-2: the runtime `<?` check is replaced by a STRUCTURAL bound — the
-- generic bound-free parser `parsePolyTypeP` is now THE PolyType parser, and the
-- length decrease is the relation shrink applied to the soundness witness.
-- De-`with`'d through `ppB-go` (the result Maybe is a parameter) so the bridge
-- lemmas `parsePolyTypeB ↔ ParsesPolyType` can reason about it.
ppB-go : (toks : List Token) (r : Maybe (PolyType × List Token)) →
         parsePolyTypeP toks ≡ r → ParsePolyAtB toks
ppB-go toks nothing          pf = nothing
ppB-go toks (just (t , rest)) pf =
  just (t , rest , ParsesPolyType-shrink (sound-polyType toks (<-wellFounded (length toks)) pf))

parsePolyTypeB : (toks : List Token) → ParsePolyAtB toks
parsePolyTypeB toks = ppB-go toks (parsePolyTypeP toks) refl
