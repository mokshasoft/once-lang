-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Grammar.Roundtrip
--
-- Plan 0.3 gap G1: general per-constructor round-trip theorem. The
-- smoke tests in `Once.Grammar.Printer` show the printer + parser
-- agree on specific canonical inputs. This module states and proves
-- the structural theorem: for every `Concrete g` (TVar-free GType),
--
--   parseType (printGType g) ≡ just (toType g , [])
--
-- Structure:
--   * Three predicates on token lists:
--       `NotStar`      — rejects TStar only   (parseTypeProdTail)
--       `NotStarPlus`  — rejects TStar, TPlus (parseTypeSumTail)
--       `NotCont`      — rejects all continuation tokens
--                        (TStar, TPlus, TArrow, TCaret0/1/W — used by
--                         parseArrowTail and full parseType)
--   * `toType`: the Type corresponding to a Concrete GType.
--   * Mutual round-trip lemmas for parseTypeAtom, parseTypeProd,
--     parseTypeSum, parseType. Each says: consuming `printGType g`
--     from a prefix, the parser leaves `rest` unchanged when the
--     relevant predicate holds on `rest`.
--   * Top-level corollary `round-trip-concrete`: the main theorem.
------------------------------------------------------------------------

module Once.Grammar.Roundtrip where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Once.Type using (Type; Unit; Void; Int; Float; Buffer; Str;
                             _*_; _+_; _⇒[_]_; Eff; Quantity; Zero; One; Many)
import Once.Grammar as G
open G using (GType)
open import Once.Parser.Token
open import Once.Parser.Core using (Parser)
open import Once.Parser.Type
open import Once.Grammar.Printer using (printGType; quantityToken; Concrete;
                                        c-unit; c-void; c-int; c-float;
                                        c-buffer; c-string; c-prod; c-sum;
                                        c-fun; c-eff)
open import Once.Grammar.Convert using (parseGType; gtypeToType; typeToGType)

------------------------------------------------------------------------
-- Concrete GType → Type
------------------------------------------------------------------------

toType : ∀ {g : GType} → Concrete g → Type
toType c-unit   = Unit
toType c-void   = Void
toType c-int    = Int
toType c-float  = Float
toType c-buffer = Buffer
toType c-string = Str
toType (c-prod cA cB) = toType cA * toType cB
toType (c-sum cA cB)  = toType cA + toType cB
toType (c-fun {q = q} cA cB) = toType cA ⇒[ q ] toType cB
toType (c-eff cA cB)  = Eff (toType cA) (toType cB)

------------------------------------------------------------------------
-- Granular predicates on leading tokens
--
-- Each tail-parser examines its first token to decide whether to
-- consume more. We ship the weakest predicate each tail-parser needs,
-- so compound cases can feed the right predicate at each level.
------------------------------------------------------------------------

-- Rejects only TStar. Enough for parseTypeProdTail to return unchanged.
NotStar : List Token → Set
NotStar [] = ⊤
NotStar (TStar ∷ _) = ⊥
NotStar (_ ∷ _) = ⊤

-- Rejects TStar and TPlus. Enough for parseTypeSumTail to return
-- unchanged (parseTypeSumTail scrutinises only TPlus, but for the
-- lemma to typecheck on `NotStar`-admitting lists we also require
-- the product lemma's precondition on the downstream parseTypeProd.)
NotStarPlus : List Token → Set
NotStarPlus [] = ⊤
NotStarPlus (TStar ∷ _) = ⊥
NotStarPlus (TPlus ∷ _) = ⊥
NotStarPlus (_ ∷ _) = ⊤

-- Rejects all continuation tokens. Needed by parseArrowTail.
NotCont : List Token → Set
NotCont [] = ⊤
NotCont (TStar   ∷ _) = ⊥
NotCont (TPlus   ∷ _) = ⊥
NotCont (TArrow  ∷ _) = ⊥
NotCont (TCaret0 ∷ _) = ⊥
NotCont (TCaret1 ∷ _) = ⊥
NotCont (TCaretW ∷ _) = ⊥
NotCont (_ ∷ _) = ⊤

-- NotCont ⇒ NotStarPlus ⇒ NotStar.
NotCont⇒NotStarPlus : ∀ {xs} → NotCont xs → NotStarPlus xs
NotCont⇒NotStarPlus {[]} _ = tt
NotCont⇒NotStarPlus {TLParen    ∷ _} _ = tt
NotCont⇒NotStarPlus {TRParen    ∷ _} _ = tt
NotCont⇒NotStarPlus {TLBrace    ∷ _} _ = tt
NotCont⇒NotStarPlus {TRBrace    ∷ _} _ = tt
NotCont⇒NotStarPlus {TColon     ∷ _} _ = tt
NotCont⇒NotStarPlus {TEquals    ∷ _} _ = tt
NotCont⇒NotStarPlus {TLambda    ∷ _} _ = tt
NotCont⇒NotStarPlus {TComma     ∷ _} _ = tt
NotCont⇒NotStarPlus {TSemicolon ∷ _} _ = tt
NotCont⇒NotStarPlus {TAt        ∷ _} _ = tt
NotCont⇒NotStarPlus {TPipe      ∷ _} _ = tt
NotCont⇒NotStarPlus {TDot       ∷ _} _ = tt
NotCont⇒NotStarPlus {TMinus     ∷ _} _ = tt
NotCont⇒NotStarPlus {TSlash     ∷ _} _ = tt
NotCont⇒NotStarPlus {TPercent   ∷ _} _ = tt
NotCont⇒NotStarPlus {TAmpersand ∷ _} _ = tt
NotCont⇒NotStarPlus {TLt        ∷ _} _ = tt
NotCont⇒NotStarPlus {TLe        ∷ _} _ = tt
NotCont⇒NotStarPlus {TGt        ∷ _} _ = tt
NotCont⇒NotStarPlus {TGe        ∷ _} _ = tt
NotCont⇒NotStarPlus {TEqEq      ∷ _} _ = tt
NotCont⇒NotStarPlus {TNeq       ∷ _} _ = tt
NotCont⇒NotStarPlus {TNewline   ∷ _} _ = tt
NotCont⇒NotStarPlus {TEOF       ∷ _} _ = tt
NotCont⇒NotStarPlus {TWord _    ∷ _} _ = tt
NotCont⇒NotStarPlus {TInt _     ∷ _} _ = tt
NotCont⇒NotStarPlus {TString _  ∷ _} _ = tt
NotCont⇒NotStarPlus {TStar   ∷ _} ()
NotCont⇒NotStarPlus {TPlus   ∷ _} ()
NotCont⇒NotStarPlus {TArrow  ∷ _} ncont = ⊥-elim ncont
NotCont⇒NotStarPlus {TCaret0 ∷ _} ncont = ⊥-elim ncont
NotCont⇒NotStarPlus {TCaret1 ∷ _} ncont = ⊥-elim ncont
NotCont⇒NotStarPlus {TCaretW ∷ _} ncont = ⊥-elim ncont

NotStarPlus⇒NotStar : ∀ {xs} → NotStarPlus xs → NotStar xs
NotStarPlus⇒NotStar {[]} _ = tt
NotStarPlus⇒NotStar {TLParen    ∷ _} _ = tt
NotStarPlus⇒NotStar {TRParen    ∷ _} _ = tt
NotStarPlus⇒NotStar {TLBrace    ∷ _} _ = tt
NotStarPlus⇒NotStar {TRBrace    ∷ _} _ = tt
NotStarPlus⇒NotStar {TColon     ∷ _} _ = tt
NotStarPlus⇒NotStar {TEquals    ∷ _} _ = tt
NotStarPlus⇒NotStar {TLambda    ∷ _} _ = tt
NotStarPlus⇒NotStar {TComma     ∷ _} _ = tt
NotStarPlus⇒NotStar {TSemicolon ∷ _} _ = tt
NotStarPlus⇒NotStar {TAt        ∷ _} _ = tt
NotStarPlus⇒NotStar {TPipe      ∷ _} _ = tt
NotStarPlus⇒NotStar {TDot       ∷ _} _ = tt
NotStarPlus⇒NotStar {TArrow     ∷ _} _ = tt
NotStarPlus⇒NotStar {TMinus     ∷ _} _ = tt
NotStarPlus⇒NotStar {TSlash     ∷ _} _ = tt
NotStarPlus⇒NotStar {TPercent   ∷ _} _ = tt
NotStarPlus⇒NotStar {TAmpersand ∷ _} _ = tt
NotStarPlus⇒NotStar {TLt        ∷ _} _ = tt
NotStarPlus⇒NotStar {TLe        ∷ _} _ = tt
NotStarPlus⇒NotStar {TGt        ∷ _} _ = tt
NotStarPlus⇒NotStar {TGe        ∷ _} _ = tt
NotStarPlus⇒NotStar {TEqEq      ∷ _} _ = tt
NotStarPlus⇒NotStar {TNeq       ∷ _} _ = tt
NotStarPlus⇒NotStar {TNewline   ∷ _} _ = tt
NotStarPlus⇒NotStar {TEOF       ∷ _} _ = tt
NotStarPlus⇒NotStar {TWord _    ∷ _} _ = tt
NotStarPlus⇒NotStar {TInt _     ∷ _} _ = tt
NotStarPlus⇒NotStar {TString _  ∷ _} _ = tt
NotStarPlus⇒NotStar {TCaret0 ∷ _} _ = tt
NotStarPlus⇒NotStar {TCaret1 ∷ _} _ = tt
NotStarPlus⇒NotStar {TCaretW ∷ _} _ = tt
NotStarPlus⇒NotStar {TStar ∷ _} ()
NotStarPlus⇒NotStar {TPlus ∷ _} ()

-- `[]` is NotCont.
NotCont-nil : NotCont []
NotCont-nil = tt

-- `TRParen ∷ xs` is NotCont.
NotCont-rparen : ∀ {xs} → NotCont (TRParen ∷ xs)
NotCont-rparen = tt

------------------------------------------------------------------------
-- parseTypeProdTail returns unchanged on NotStar input.
------------------------------------------------------------------------

parseTypeProdTail-NotStar :
  ∀ (t : Type) (toks : List Token) → NotStar toks
  → parseTypeProdTail t toks ≡ just (t , toks)
parseTypeProdTail-NotStar t [] _ = refl
parseTypeProdTail-NotStar t (TLParen    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TRParen    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TLBrace    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TRBrace    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TColon     ∷ _) _ = refl
parseTypeProdTail-NotStar t (TEquals    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TArrow     ∷ _) _ = refl
parseTypeProdTail-NotStar t (TLambda    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TComma     ∷ _) _ = refl
parseTypeProdTail-NotStar t (TSemicolon ∷ _) _ = refl
parseTypeProdTail-NotStar t (TAt        ∷ _) _ = refl
parseTypeProdTail-NotStar t (TPipe      ∷ _) _ = refl
parseTypeProdTail-NotStar t (TDot       ∷ _) _ = refl
parseTypeProdTail-NotStar t (TPlus      ∷ _) _ = refl
parseTypeProdTail-NotStar t (TMinus     ∷ _) _ = refl
parseTypeProdTail-NotStar t (TSlash     ∷ _) _ = refl
parseTypeProdTail-NotStar t (TPercent   ∷ _) _ = refl
parseTypeProdTail-NotStar t (TAmpersand ∷ _) _ = refl
parseTypeProdTail-NotStar t (TLt        ∷ _) _ = refl
parseTypeProdTail-NotStar t (TLe        ∷ _) _ = refl
parseTypeProdTail-NotStar t (TGt        ∷ _) _ = refl
parseTypeProdTail-NotStar t (TGe        ∷ _) _ = refl
parseTypeProdTail-NotStar t (TEqEq      ∷ _) _ = refl
parseTypeProdTail-NotStar t (TNeq       ∷ _) _ = refl
parseTypeProdTail-NotStar t (TCaret0    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TCaret1    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TCaretW    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TNewline   ∷ _) _ = refl
parseTypeProdTail-NotStar t (TEOF       ∷ _) _ = refl
parseTypeProdTail-NotStar t (TWord _    ∷ _) _ = refl
parseTypeProdTail-NotStar t (TInt _     ∷ _) _ = refl
parseTypeProdTail-NotStar t (TString _  ∷ _) _ = refl
parseTypeProdTail-NotStar t (TStar ∷ _) ()

------------------------------------------------------------------------
-- parseTypeSumTail returns unchanged on NotStarPlus input.
------------------------------------------------------------------------

parseTypeSumTail-NotStarPlus :
  ∀ (t : Type) (toks : List Token) → NotStarPlus toks
  → parseTypeSumTail t toks ≡ just (t , toks)
parseTypeSumTail-NotStarPlus t [] _ = refl
parseTypeSumTail-NotStarPlus t (TLParen    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TRParen    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TLBrace    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TRBrace    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TColon     ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TEquals    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TArrow     ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TLambda    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TComma     ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TSemicolon ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TAt        ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TPipe      ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TDot       ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TMinus     ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TSlash     ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TPercent   ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TAmpersand ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TLt        ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TLe        ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TGt        ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TGe        ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TEqEq      ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TNeq       ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TCaret0    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TCaret1    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TCaretW    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TNewline   ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TEOF       ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TWord _    ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TInt _     ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TString _  ∷ _) _ = refl
parseTypeSumTail-NotStarPlus t (TStar ∷ _) ()
parseTypeSumTail-NotStarPlus t (TPlus ∷ _) ()

------------------------------------------------------------------------
-- parseArrowTail returns unchanged on NotCont input.
------------------------------------------------------------------------

parseArrowTail-NotCont :
  ∀ (t : Type) (toks : List Token) → NotCont toks
  → parseArrowTail t toks ≡ just (t , toks)
parseArrowTail-NotCont t [] _ = refl
parseArrowTail-NotCont t (TLParen    ∷ _) _ = refl
parseArrowTail-NotCont t (TRParen    ∷ _) _ = refl
parseArrowTail-NotCont t (TLBrace    ∷ _) _ = refl
parseArrowTail-NotCont t (TRBrace    ∷ _) _ = refl
parseArrowTail-NotCont t (TColon     ∷ _) _ = refl
parseArrowTail-NotCont t (TEquals    ∷ _) _ = refl
parseArrowTail-NotCont t (TLambda    ∷ _) _ = refl
parseArrowTail-NotCont t (TComma     ∷ _) _ = refl
parseArrowTail-NotCont t (TSemicolon ∷ _) _ = refl
parseArrowTail-NotCont t (TAt        ∷ _) _ = refl
parseArrowTail-NotCont t (TPipe      ∷ _) _ = refl
parseArrowTail-NotCont t (TDot       ∷ _) _ = refl
parseArrowTail-NotCont t (TMinus     ∷ _) _ = refl
parseArrowTail-NotCont t (TSlash     ∷ _) _ = refl
parseArrowTail-NotCont t (TPercent   ∷ _) _ = refl
parseArrowTail-NotCont t (TAmpersand ∷ _) _ = refl
parseArrowTail-NotCont t (TLt        ∷ _) _ = refl
parseArrowTail-NotCont t (TLe        ∷ _) _ = refl
parseArrowTail-NotCont t (TGt        ∷ _) _ = refl
parseArrowTail-NotCont t (TGe        ∷ _) _ = refl
parseArrowTail-NotCont t (TEqEq      ∷ _) _ = refl
parseArrowTail-NotCont t (TNeq       ∷ _) _ = refl
parseArrowTail-NotCont t (TNewline   ∷ _) _ = refl
parseArrowTail-NotCont t (TEOF       ∷ _) _ = refl
parseArrowTail-NotCont t (TWord _    ∷ _) _ = refl
parseArrowTail-NotCont t (TInt _     ∷ _) _ = refl
parseArrowTail-NotCont t (TString _  ∷ _) _ = refl
parseArrowTail-NotCont t (TStar ∷ _) ()
parseArrowTail-NotCont t (TPlus ∷ _) ()
parseArrowTail-NotCont t (TArrow ∷ _) ()
parseArrowTail-NotCont t (TCaret0 ∷ _) ()
parseArrowTail-NotCont t (TCaret1 ∷ _) ()
parseArrowTail-NotCont t (TCaretW ∷ _) ()

------------------------------------------------------------------------
-- Mutual round-trip lemmas for parseTypeAtom, parseTypeProd,
-- parseTypeSum, parseType. The main claim: consuming printGType g
-- leaves `rest` untouched, and recovers the Type corresponding to g.
--
-- Proof strategy per compound constructor:
--   1. Rewrite `(TLParen ∷ xs) ++ rest = TLParen ∷ (xs ++ rest)`
--      (definitional on list append).
--   2. Use ++-assoc to re-associate nested concats matching the
--      parser's dispatch (inner parseType on subsequences).
--   3. Recursively apply the IHs (round-trip-atom / round-trip-type
--      as appropriate) at each stage.
--   4. Apply the tail-parser lemmas (NotStar/NotStarPlus/NotCont)
--      to pass through continuation-free suffixes.
--   5. Close with `expect TRParen` consuming the trailing paren.
--
-- The mutual block terminates structurally on the input `Concrete g`
-- witness: each recursive call (round-trip-atom / round-trip-prod /
-- round-trip-sum / round-trip-type) is made on a subterm `cA` or
-- `cB` of the input compound constructor. No TERMINATING pragma is
-- required.
------------------------------------------------------------------------

round-trip-atom : ∀ {g : GType} (c : Concrete g) (rest : List Token)
                → parseTypeAtom (printGType g ++ rest) ≡ just (toType c , rest)

round-trip-prod : ∀ {g : GType} (c : Concrete g) (rest : List Token)
                → NotStar rest
                → parseTypeProd (printGType g ++ rest) ≡ just (toType c , rest)

round-trip-sum : ∀ {g : GType} (c : Concrete g) (rest : List Token)
               → NotStarPlus rest
               → parseTypeSum (printGType g ++ rest) ≡ just (toType c , rest)

round-trip-type : ∀ {g : GType} (c : Concrete g) (rest : List Token)
                → NotCont rest
                → parseType (printGType g ++ rest) ≡ just (toType c , rest)

------------------------------------------------------------------------
-- round-trip-atom cases
------------------------------------------------------------------------

round-trip-atom c-unit   rest = refl
round-trip-atom c-void   rest = refl
round-trip-atom c-int    rest = refl
round-trip-atom c-float  rest = refl
round-trip-atom c-buffer rest = refl
round-trip-atom c-string rest = refl

-- Product: `(A * B)` prints to `TLParen ∷ printGType A ++ TStar ∷ printGType B ++ TRParen ∷ []`.
-- After `++ rest`, inner parseType sees `printGType A ++ TStar ∷ printGType B ++ TRParen ∷ rest`.
-- Inner parseType = parseSum >>= parseArrowTail
--                 = (parseProd >>= parseSumTail) >>= parseArrowTail
--                 = ((parseAtom >>= parseProdTail) >>= parseSumTail) >>= parseArrowTail
-- parseAtom consumes A, parseProdTail sees TStar and recurses by consuming B
-- (via parseAtom again), then sees TRParen and returns. parseSumTail sees
-- TRParen → NotStarPlus, returns. parseArrowTail sees TRParen → NotCont, returns.
-- expect TRParen consumes the trailing paren.
round-trip-atom (c-prod {A = A} {B = B} cA cB) rest
  rewrite ++-assoc (printGType A) (TStar ∷ printGType B ++ TRParen ∷ []) rest
        | ++-assoc (printGType B) (TRParen ∷ []) rest
        | round-trip-atom cA (TStar ∷ printGType B ++ TRParen ∷ rest)
        | round-trip-atom cB (TRParen ∷ rest)
        | parseTypeProdTail-NotStar (toType cA * toType cB) (TRParen ∷ rest) tt
        | parseTypeSumTail-NotStarPlus (toType cA * toType cB) (TRParen ∷ rest) tt
        | parseArrowTail-NotCont (toType cA * toType cB) (TRParen ∷ rest) tt
  = refl

-- Sum: `(A + B)` prints to `TLParen ∷ printGType A ++ TPlus ∷ printGType B ++ TRParen ∷ []`.
-- Similar flow to product, but with TPlus as the continuation.
-- parseAtom on A → leaves TPlus ∷ …. parseProdTail sees TPlus → NotStar ✓,
-- returns unchanged with (toType cA). Then parseSumTail sees TPlus and
-- recurses: parseProd on `printGType B ++ TRParen ∷ rest` consumes B.
-- Then parseSumTail sees TRParen → NotStarPlus, returns.
-- parseArrowTail sees TRParen → NotCont, returns.
round-trip-atom (c-sum {A = A} {B = B} cA cB) rest
  rewrite ++-assoc (printGType A) (TPlus ∷ printGType B ++ TRParen ∷ []) rest
        | ++-assoc (printGType B) (TRParen ∷ []) rest
        | round-trip-atom cA (TPlus ∷ printGType B ++ TRParen ∷ rest)
        | parseTypeProdTail-NotStar (toType cA) (TPlus ∷ printGType B ++ TRParen ∷ rest) tt
        | round-trip-prod cB (TRParen ∷ rest) tt
        | parseTypeSumTail-NotStarPlus (toType cA + toType cB) (TRParen ∷ rest) tt
        | parseArrowTail-NotCont (toType cA + toType cB) (TRParen ∷ rest) tt
  = refl

-- Arrow: `(A ⇒[ q ] B)` prints to `TLParen ∷ printGType A ++ quantityToken q ∷ TArrow ∷ printGType B ++ TRParen ∷ []`.
-- parseAtom consumes A. parseProdTail sees `quantityToken q` (a TCaret*) → NotStar ✓.
-- parseSumTail sees `quantityToken q` → NotStarPlus ✓.
-- parseArrowTail matches `TCaret{0/1/W} ∷ TArrow ∷ rest'` → parseType on rest'
--   = parseType on `printGType B ++ TRParen ∷ rest`.
-- Use round-trip-type cB (TRParen ∷ rest) (NotCont ✓).
-- Finally expect TRParen consumes the trailing paren.
--
-- We split on `q` because parseArrowTail's clauses match each TCaret*
-- variant separately, and Agda cannot compute through a parameter in
-- the pattern position.
round-trip-atom (c-fun {A = A} {B = B} {q = Zero} cA cB) rest
  rewrite ++-assoc (printGType A) (TCaret0 ∷ TArrow ∷ printGType B ++ TRParen ∷ []) rest
        | ++-assoc (printGType B) (TRParen ∷ []) rest
        | round-trip-atom cA (TCaret0 ∷ TArrow ∷ printGType B ++ TRParen ∷ rest)
        | round-trip-type cB (TRParen ∷ rest) tt
  = refl
round-trip-atom (c-fun {A = A} {B = B} {q = One} cA cB) rest
  rewrite ++-assoc (printGType A) (TCaret1 ∷ TArrow ∷ printGType B ++ TRParen ∷ []) rest
        | ++-assoc (printGType B) (TRParen ∷ []) rest
        | round-trip-atom cA (TCaret1 ∷ TArrow ∷ printGType B ++ TRParen ∷ rest)
        | round-trip-type cB (TRParen ∷ rest) tt
  = refl
round-trip-atom (c-fun {A = A} {B = B} {q = Many} cA cB) rest
  rewrite ++-assoc (printGType A) (TCaretW ∷ TArrow ∷ printGType B ++ TRParen ∷ []) rest
        | ++-assoc (printGType B) (TRParen ∷ []) rest
        | round-trip-atom cA (TCaretW ∷ TArrow ∷ printGType B ++ TRParen ∷ rest)
        | round-trip-type cB (TRParen ∷ rest) tt
  = refl

-- Eff: `Eff A B` prints to `TLParen ∷ TWord "Eff" ∷ printGType A ++ printGType B ++ TRParen ∷ []`.
-- parseAtom matches TLParen → inner parseType. Inner parseType calls
-- parseAtom on `TWord "Eff" ∷ printGType A ++ printGType B ++ TRParen ∷ rest`.
-- The "Eff" clause is `parseAtom >>= λ a → parseAtom >>= λ b → return (Eff a b)`.
-- Use round-trip-atom cA, then round-trip-atom cB, landing on TRParen ∷ rest.
-- Then parseProdTail / parseSumTail / parseArrowTail pass through (TRParen),
-- and the outer LParen branch's `expect TRParen` consumes the trailing paren.
round-trip-atom (c-eff {A = A} {B = B} cA cB) rest
  rewrite ++-assoc (printGType A) (printGType B ++ TRParen ∷ []) rest
        | ++-assoc (printGType B) (TRParen ∷ []) rest
        | round-trip-atom cA (printGType B ++ TRParen ∷ rest)
        | round-trip-atom cB (TRParen ∷ rest)
        | parseTypeProdTail-NotStar (Eff (toType cA) (toType cB)) (TRParen ∷ rest) tt
        | parseTypeSumTail-NotStarPlus (Eff (toType cA) (toType cB)) (TRParen ∷ rest) tt
        | parseArrowTail-NotCont (Eff (toType cA) (toType cB)) (TRParen ∷ rest) tt
  = refl

------------------------------------------------------------------------
-- round-trip-prod: parseTypeProd = parseTypeAtom >>= parseTypeProdTail
------------------------------------------------------------------------

round-trip-prod c rest ns
  rewrite round-trip-atom c rest
        | parseTypeProdTail-NotStar (toType c) rest ns
  = refl

------------------------------------------------------------------------
-- round-trip-sum: parseTypeSum = parseTypeProd >>= parseTypeSumTail
------------------------------------------------------------------------

round-trip-sum c rest nsp
  rewrite round-trip-prod c rest (NotStarPlus⇒NotStar nsp)
        | parseTypeSumTail-NotStarPlus (toType c) rest nsp
  = refl

------------------------------------------------------------------------
-- round-trip-type: parseType = parseTypeSum >>= parseArrowTail
------------------------------------------------------------------------

round-trip-type c rest nc
  rewrite round-trip-sum c rest (NotCont⇒NotStarPlus nc)
        | parseArrowTail-NotCont (toType c) rest nc
  = refl

------------------------------------------------------------------------
-- Top-level theorem: parseType (printGType g) ≡ just (toType c , [])
------------------------------------------------------------------------

round-trip-concrete :
  ∀ {g : GType} (c : Concrete g)
  → parseType (printGType g) ≡ just (toType c , [])
round-trip-concrete {g} c
  rewrite sym (++-identityʳ (printGType g))
  = round-trip-type c [] tt
