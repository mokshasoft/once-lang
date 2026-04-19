-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Expr
--
-- Parser for Once expressions.
-- Produces Once.TypeCheck.Raw.RawExpr directly.
--
-- Precedence (low to high):
--   1. Type annotation (:)
--   2. Composition (.)
--   3. Comparison (<, <=, >, >=, ==, !=)
--   4. Additive (+, -)
--   5. Multiplicative (*, /, %)
--   6. Unary negation (-)
--   7. Application (juxtaposition)
--   8. Atom (var, lit, parens, lambda, let, destruct, pair)
--
-- Termination: well-founded recursion on `length toks`. Every internal
-- parser carries an `Acc _<_ (length toks)` argument and returns a
-- Σ-packaged result that includes a length-bound witness (strict
-- `ParseEL<` for consuming parsers, non-strict `ParseEL≤` for tail
-- parsers that may no-op). Per plan 0.3 task #40.
--
-- External callers use `parseExpr : Parser RawExpr` (the top-level
-- wrapper at the end of this file) which forgets the length bound.
------------------------------------------------------------------------

module Once.Parser.Expr where

open import Data.List using (List; []; _∷_; foldr; reverse; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Char using (Char)
open import Data.String using (String)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans;
                                        ≤-<-trans; <-≤-trans;
                                        n<1+n; n≤1+n; <⇒≤; m≤n⇒m≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr; RVar; RQualified; RApp; RLam; RLet;
                                       RPair; RDestruct; RUnit; RInt;
                                       RStringLit; RAnnot; RBinOp; RUnaryOp;
                                       BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod;
                                       OpLt; OpLe; OpGt; OpGe; OpEq; OpNe;
                                       UnaryOp; OpNeg)
open import Once.Parser.Token
open import Once.Parser.Core
open import Once.Parser.Type using (parseTypeWF)
open import Once.Parser.TypeRelation using (ParsesType-shrinks)

------------------------------------------------------------------------
-- Helpers and lexical-level utilities
------------------------------------------------------------------------

-- | Reserved words that cannot be used as variable names in atom position
isReserved : String → Bool
isReserved "in"       = true   -- let ... in
isReserved "of"       = true   -- destruct ... of
isReserved "let"      = true   -- let keyword
isReserved "destruct" = true   -- destruct keyword
isReserved "Left"     = true   -- pattern branch
isReserved "Right"    = true   -- pattern branch
isReserved _          = false

------------------------------------------------------------------------
-- Length-bounded result types
--
-- ParseEL< : strict decrease (consuming parsers)
-- ParseEL≤ : non-strict (tail parsers that may no-op)
------------------------------------------------------------------------

ParseEL< : List Token → Set
ParseEL< toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] length rest < length toks)

ParseEL≤ : List Token → Set
ParseEL≤ toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] length rest ≤ length toks)

------------------------------------------------------------------------
-- Operator-as-expression parser: (&), (.), (|>), etc.
--
-- Structurally recursive on the token list (each clause consumes at
-- least one token before recursing). Strict-decrease on success.
------------------------------------------------------------------------

parseOpExprWF : (toks : List Token) → List Char → ParseEL< toks
parseOpExprWF (TDot       ∷ rest) a with parseOpExprWF rest ('.' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TPlus      ∷ rest) a with parseOpExprWF rest ('+' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TMinus     ∷ rest) a with parseOpExprWF rest ('-' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TStar      ∷ rest) a with parseOpExprWF rest ('*' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TSlash     ∷ rest) a with parseOpExprWF rest ('/' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TPercent   ∷ rest) a with parseOpExprWF rest ('%' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TLt        ∷ rest) a with parseOpExprWF rest ('<' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TGt        ∷ rest) a with parseOpExprWF rest ('>' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TPipe      ∷ rest) a with parseOpExprWF rest ('|' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TAmpersand ∷ rest) a with parseOpExprWF rest ('&' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
parseOpExprWF (TAt        ∷ rest) a with parseOpExprWF rest ('@' ∷ a)
... | nothing                 = nothing
... | just (e , rest' , lt)   = just (e , rest' , m≤n⇒m≤1+n lt)
-- Closing paren: finish.  Empty operator name → nothing.
parseOpExprWF (TRParen ∷ rest) []      = nothing
parseOpExprWF (TRParen ∷ rest) (c ∷ a) = just (RVar (Data.String.fromList (reverse (c ∷ a))) , rest , s≤s ≤-refl)
-- Any other token kills the operator parse.
parseOpExprWF []               _ = nothing
parseOpExprWF (TWord _    ∷ _) _ = nothing
parseOpExprWF (TInt _     ∷ _) _ = nothing
parseOpExprWF (TString _  ∷ _) _ = nothing
parseOpExprWF (TLParen    ∷ _) _ = nothing
parseOpExprWF (TLBrace    ∷ _) _ = nothing
parseOpExprWF (TRBrace    ∷ _) _ = nothing
parseOpExprWF (TColon     ∷ _) _ = nothing
parseOpExprWF (TEquals    ∷ _) _ = nothing
parseOpExprWF (TArrow     ∷ _) _ = nothing
parseOpExprWF (TCaret1    ∷ _) _ = nothing
parseOpExprWF (TCaret0    ∷ _) _ = nothing
parseOpExprWF (TCaretW    ∷ _) _ = nothing
parseOpExprWF (TLambda    ∷ _) _ = nothing
parseOpExprWF (TComma     ∷ _) _ = nothing
parseOpExprWF (TSemicolon ∷ _) _ = nothing
parseOpExprWF (TLe        ∷ _) _ = nothing
parseOpExprWF (TGe        ∷ _) _ = nothing
parseOpExprWF (TEqEq      ∷ _) _ = nothing
parseOpExprWF (TNeq       ∷ _) _ = nothing
parseOpExprWF (TNewline   ∷ _) _ = nothing
parseOpExprWF (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- Mutual WF parser declarations
------------------------------------------------------------------------

parseExprWF        : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseCompWF        : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseCmpWF         : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseAddWF         : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseMulWF         : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseUnaryWF       : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseAppWF         : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseAtomExprWF    : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks

parseLamParamsWF   : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseLetWF         : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseDestructWF    : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseParenWF       : (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks

parseLetContWF     : (name : String) (val : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseDestructBranchesWF :
                     (scrut : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseDestructOfWF  : (scrut : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseRightBranchWF : (scrut : RawExpr) (x : String) (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseParenTripleWF : (e e2 : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks
parseParenContWF   : (e : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL< toks

-- Tail parsers (may no-op, non-strict decrease)
parseAppTailWF     : (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL≤ toks
parseMulTailWF     : (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL≤ toks
parseAddTailWF     : (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL≤ toks
parseCompTailWF    : (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseEL≤ toks

------------------------------------------------------------------------
-- Named helpers for `parseAtomExprWF` consume-and-recurse cases.
-- Each takes the POST-Acc-destructured sub-Acc, keeping the nested
-- `with` tree out of parseAtomExprWF's body (termination-checker
-- hygiene — same trick Parser/Type.agda uses).
------------------------------------------------------------------------

parseAtomExprWF-TLParen :
    (rest : List Token) → Acc _<_ (length rest)
  → ParseEL< (TLParen ∷ rest)
parseAtomExprWF-TLambda :
    (rest : List Token) → Acc _<_ (length rest)
  → ParseEL< (TLambda ∷ rest)
parseAtomExprWF-TLet :
    (rest : List Token) → Acc _<_ (length rest)
  → ParseEL< (TWord "let" ∷ rest)
parseAtomExprWF-TDestruct :
    (rest : List Token) → Acc _<_ (length rest)
  → ParseEL< (TWord "destruct" ∷ rest)

------------------------------------------------------------------------
-- parseLamParamsWF : \x y z -> body
------------------------------------------------------------------------

parseLamParamsWF (TArrow ∷ rest) (acc rec) with parseExprWF rest (rec (s≤s ≤-refl))
... | nothing               = nothing
... | just (body , rest' , lt) = just (body , rest' , m≤n⇒m≤1+n lt)
parseLamParamsWF (TWord name ∷ rest) (acc rec) with parseLamParamsWF rest (rec (s≤s ≤-refl))
... | nothing                 = nothing
... | just (body , rest' , lt) = just (RLam name body , rest' , m≤n⇒m≤1+n lt)
parseLamParamsWF []               _ = nothing
parseLamParamsWF (TInt _     ∷ _) _ = nothing
parseLamParamsWF (TString _  ∷ _) _ = nothing
parseLamParamsWF (TLParen    ∷ _) _ = nothing
parseLamParamsWF (TRParen    ∷ _) _ = nothing
parseLamParamsWF (TLBrace    ∷ _) _ = nothing
parseLamParamsWF (TRBrace    ∷ _) _ = nothing
parseLamParamsWF (TColon     ∷ _) _ = nothing
parseLamParamsWF (TEquals    ∷ _) _ = nothing
parseLamParamsWF (TCaret1    ∷ _) _ = nothing
parseLamParamsWF (TCaret0    ∷ _) _ = nothing
parseLamParamsWF (TCaretW    ∷ _) _ = nothing
parseLamParamsWF (TLambda    ∷ _) _ = nothing
parseLamParamsWF (TComma     ∷ _) _ = nothing
parseLamParamsWF (TSemicolon ∷ _) _ = nothing
parseLamParamsWF (TAt        ∷ _) _ = nothing
parseLamParamsWF (TPipe      ∷ _) _ = nothing
parseLamParamsWF (TDot       ∷ _) _ = nothing
parseLamParamsWF (TPlus      ∷ _) _ = nothing
parseLamParamsWF (TMinus     ∷ _) _ = nothing
parseLamParamsWF (TStar      ∷ _) _ = nothing
parseLamParamsWF (TSlash     ∷ _) _ = nothing
parseLamParamsWF (TPercent   ∷ _) _ = nothing
parseLamParamsWF (TAmpersand ∷ _) _ = nothing
parseLamParamsWF (TLt        ∷ _) _ = nothing
parseLamParamsWF (TLe        ∷ _) _ = nothing
parseLamParamsWF (TGt        ∷ _) _ = nothing
parseLamParamsWF (TGe        ∷ _) _ = nothing
parseLamParamsWF (TEqEq      ∷ _) _ = nothing
parseLamParamsWF (TNeq       ∷ _) _ = nothing
parseLamParamsWF (TNewline   ∷ _) _ = nothing
parseLamParamsWF (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseLetContWF : (after let name = val) either  `in body`  or
--                  `; more-lets in body`.
------------------------------------------------------------------------

parseLetContWF name val (TWord w ∷ rest) (acc rec) with w ≟ "in"
... | yes _ with parseExprWF rest (rec (s≤s ≤-refl))
...   | nothing                  = nothing
...   | just (body , rest' , lt) = just (RLet name val body , rest' , m≤n⇒m≤1+n lt)
parseLetContWF name val (TWord w ∷ rest) _ | no _ = nothing
parseLetContWF name val (TSemicolon ∷ rest) (acc rec) with parseLetWF rest (rec (s≤s ≤-refl))
... | nothing                  = nothing
... | just (body , rest' , lt) = just (RLet name val body , rest' , m≤n⇒m≤1+n lt)
parseLetContWF _ _ []               _ = nothing
parseLetContWF _ _ (TInt _     ∷ _) _ = nothing
parseLetContWF _ _ (TString _  ∷ _) _ = nothing
parseLetContWF _ _ (TLParen    ∷ _) _ = nothing
parseLetContWF _ _ (TRParen    ∷ _) _ = nothing
parseLetContWF _ _ (TLBrace    ∷ _) _ = nothing
parseLetContWF _ _ (TRBrace    ∷ _) _ = nothing
parseLetContWF _ _ (TColon     ∷ _) _ = nothing
parseLetContWF _ _ (TEquals    ∷ _) _ = nothing
parseLetContWF _ _ (TArrow     ∷ _) _ = nothing
parseLetContWF _ _ (TCaret1    ∷ _) _ = nothing
parseLetContWF _ _ (TCaret0    ∷ _) _ = nothing
parseLetContWF _ _ (TCaretW    ∷ _) _ = nothing
parseLetContWF _ _ (TLambda    ∷ _) _ = nothing
parseLetContWF _ _ (TComma     ∷ _) _ = nothing
parseLetContWF _ _ (TAt        ∷ _) _ = nothing
parseLetContWF _ _ (TPipe      ∷ _) _ = nothing
parseLetContWF _ _ (TDot       ∷ _) _ = nothing
parseLetContWF _ _ (TPlus      ∷ _) _ = nothing
parseLetContWF _ _ (TMinus     ∷ _) _ = nothing
parseLetContWF _ _ (TStar      ∷ _) _ = nothing
parseLetContWF _ _ (TSlash     ∷ _) _ = nothing
parseLetContWF _ _ (TPercent   ∷ _) _ = nothing
parseLetContWF _ _ (TAmpersand ∷ _) _ = nothing
parseLetContWF _ _ (TLt        ∷ _) _ = nothing
parseLetContWF _ _ (TLe        ∷ _) _ = nothing
parseLetContWF _ _ (TGt        ∷ _) _ = nothing
parseLetContWF _ _ (TGe        ∷ _) _ = nothing
parseLetContWF _ _ (TEqEq      ∷ _) _ = nothing
parseLetContWF _ _ (TNeq       ∷ _) _ = nothing
parseLetContWF _ _ (TNewline   ∷ _) _ = nothing
parseLetContWF _ _ (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseLetWF : let x = e1 in e2  (also  let x = e1 ; y = e2 in body)
--
-- Inlines `anyWord` (consume TWord) and `expect TEquals` so length
-- bounds are threaded explicitly.
------------------------------------------------------------------------

-- | Shape view on `TWord name ∷ TEquals ∷ rest`.
data LetShape : List Token → Set where
  let-head  : (name : String) (rest : List Token)
            → LetShape (TWord name ∷ TEquals ∷ rest)
  let-other : (toks : List Token) → LetShape toks

letView : (toks : List Token) → LetShape toks
letView (TWord name ∷ TEquals ∷ rest) = let-head name rest
letView toks                           = let-other toks

parseLetWF toks (acc rec) with letView toks
... | let-other _ = nothing
... | let-head name rest with parseExprWF rest (rec (s≤s (n≤1+n _)))
...   | nothing = nothing
...   | just (val , rest' , lt) with parseLetContWF name val rest'
                                         (rec (<-trans lt (s≤s (n≤1+n _))))
...     | nothing                   = nothing
...     | just (body , rest'' , lt') =
          just (body , rest'' ,
                <-trans lt' (<-trans lt (s≤s (n≤1+n _))))

------------------------------------------------------------------------
-- parseRightBranchWF : Right y -> e2 }
--
-- Split into a tiny view so Agda's coverage checker doesn't drown in
-- the cross-product of residual-token shapes.
------------------------------------------------------------------------

-- | Shape view on a 4-token prefix `TSemicolon ∷ TWord w ∷ TWord y ∷ TArrow ∷ rest`.
-- `rb-head w y rest` matches that shape; `rb-other` covers everything else.
-- Kept out of the mutual block: structurally recursive on the input.
data RBShape : List Token → Set where
  rb-head  : (w y : String) (rest : List Token)
           → RBShape (TSemicolon ∷ TWord w ∷ TWord y ∷ TArrow ∷ rest)
  rb-other : (toks : List Token) → RBShape toks

rbView : (toks : List Token) → RBShape toks
rbView (TSemicolon ∷ TWord w ∷ TWord y ∷ TArrow ∷ rest) = rb-head w y rest
rbView toks = rb-other toks

-- | Body of parseRightBranchWF's "Right"-matched branch, with the
-- expression pre-parsed. Split out so the exhaustiveness checker sees
-- a simpler `rest'`-shape split.
parseRightBranchWF-body :
    (scrut : RawExpr) (x y : String) (left right : RawExpr)
  → (rest' : List Token) → ParseEL< (TRBrace ∷ rest')
parseRightBranchWF-body scrut x y left right rest' =
  just (RDestruct scrut x left y right , rest' , s≤s ≤-refl)

parseRightBranchWF scrut x left toks (acc rec) with rbView toks
... | rb-other _ = nothing
... | rb-head w y rest with w ≟ "Right"
...   | no _ = nothing
...   | yes _ with parseExprWF rest (rec (s≤s (m≤n⇒m≤1+n (m≤n⇒m≤1+n (n≤1+n _)))))
...     | nothing                              = nothing
...     | just (right , TRBrace ∷ final , lt) =
          just (RDestruct scrut x left y right , final ,
                m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (<⇒≤ lt)))))
...     | just (_ , [] , _)              = nothing
...     | just (_ , TWord _    ∷ _ , _)  = nothing
...     | just (_ , TInt _     ∷ _ , _)  = nothing
...     | just (_ , TString _  ∷ _ , _)  = nothing
...     | just (_ , TLParen    ∷ _ , _)  = nothing
...     | just (_ , TRParen    ∷ _ , _)  = nothing
...     | just (_ , TLBrace    ∷ _ , _)  = nothing
...     | just (_ , TColon     ∷ _ , _)  = nothing
...     | just (_ , TEquals    ∷ _ , _)  = nothing
...     | just (_ , TArrow     ∷ _ , _)  = nothing
...     | just (_ , TCaret1    ∷ _ , _)  = nothing
...     | just (_ , TCaret0    ∷ _ , _)  = nothing
...     | just (_ , TCaretW    ∷ _ , _)  = nothing
...     | just (_ , TLambda    ∷ _ , _)  = nothing
...     | just (_ , TComma     ∷ _ , _)  = nothing
...     | just (_ , TSemicolon ∷ _ , _)  = nothing
...     | just (_ , TAt        ∷ _ , _)  = nothing
...     | just (_ , TPipe      ∷ _ , _)  = nothing
...     | just (_ , TDot       ∷ _ , _)  = nothing
...     | just (_ , TPlus      ∷ _ , _)  = nothing
...     | just (_ , TMinus     ∷ _ , _)  = nothing
...     | just (_ , TStar      ∷ _ , _)  = nothing
...     | just (_ , TSlash     ∷ _ , _)  = nothing
...     | just (_ , TPercent   ∷ _ , _)  = nothing
...     | just (_ , TAmpersand ∷ _ , _)  = nothing
...     | just (_ , TLt        ∷ _ , _)  = nothing
...     | just (_ , TLe        ∷ _ , _)  = nothing
...     | just (_ , TGt        ∷ _ , _)  = nothing
...     | just (_ , TGe        ∷ _ , _)  = nothing
...     | just (_ , TEqEq      ∷ _ , _)  = nothing
...     | just (_ , TNeq       ∷ _ , _)  = nothing
...     | just (_ , TNewline   ∷ _ , _)  = nothing
...     | just (_ , TEOF       ∷ _ , _)  = nothing
-- (All remaining shapes covered by `rb-other` in rbView.)

------------------------------------------------------------------------
-- parseDestructBranchesWF : Left x -> e1 ; Right y -> e2 }
------------------------------------------------------------------------

-- | Shape view on a 3-token prefix `TWord w ∷ TWord x ∷ TArrow ∷ rest`.
data DBShape : List Token → Set where
  db-head  : (w x : String) (rest : List Token)
           → DBShape (TWord w ∷ TWord x ∷ TArrow ∷ rest)
  db-other : (toks : List Token) → DBShape toks

dbView : (toks : List Token) → DBShape toks
dbView (TWord w ∷ TWord x ∷ TArrow ∷ rest) = db-head w x rest
dbView toks                                 = db-other toks

parseDestructBranchesWF scrut toks (acc rec) with dbView toks
... | db-other _ = nothing
... | db-head w x rest with w ≟ "Left"
...   | no _ = nothing
...   | yes _ with parseExprWF rest (rec (s≤s (m≤n⇒m≤1+n (n≤1+n _))))
...     | nothing                  = nothing
...     | just (left , rest' , lt) with parseRightBranchWF scrut x left rest'
                                           (rec (<-trans lt (s≤s (m≤n⇒m≤1+n (n≤1+n _)))))
...       | nothing                   = nothing
...       | just (body , rest'' , lt') =
            just (body , rest'' ,
                  <-trans lt' (<-trans lt (s≤s (m≤n⇒m≤1+n (n≤1+n _)))))

------------------------------------------------------------------------
-- parseDestructOfWF : `of { ...branches... `
------------------------------------------------------------------------

-- | Shape view on `TWord w ∷ TLBrace ∷ rest`.
data DOShape : List Token → Set where
  do-head  : (w : String) (rest : List Token)
           → DOShape (TWord w ∷ TLBrace ∷ rest)
  do-other : (toks : List Token) → DOShape toks

doView : (toks : List Token) → DOShape toks
doView (TWord w ∷ TLBrace ∷ rest) = do-head w rest
doView toks                        = do-other toks

parseDestructOfWF scrut toks (acc rec) with doView toks
... | do-other _ = nothing
... | do-head w rest with w ≟ "of"
...   | no _ = nothing
...   | yes _ with parseDestructBranchesWF scrut rest (rec (s≤s (n≤1+n _)))
...     | nothing                  = nothing
...     | just (body , rest' , lt) = just (body , rest' ,
                                            <-trans lt (s≤s (n≤1+n _)))

------------------------------------------------------------------------
-- parseDestructWF : `destruct e of { ... }`
------------------------------------------------------------------------

parseDestructWF toks (acc rec) with parseExprWF toks (acc rec)
... | nothing                   = nothing
... | just (scrut , rest , lt)  with parseDestructOfWF scrut rest (rec lt)
...   | nothing                   = nothing
...   | just (body , rest' , lt') = just (body , rest' , <-trans lt' lt)

------------------------------------------------------------------------
-- parseParenTripleWF : continuation after 2nd tuple element
------------------------------------------------------------------------

parseParenTripleWF e e2 (TRParen ∷ final) _ =
  just (RPair e e2 , final , s≤s ≤-refl)
parseParenTripleWF e e2 (TComma ∷ rest) (acc rec)
  with parseExprWF rest (rec (s≤s ≤-refl))
... | just (e3 , TRParen ∷ final , lt) =
      just (RPair (RPair e e2) e3 , final ,
            s≤s (≤-trans (n≤1+n _) (<⇒≤ lt)))
... | just (_ , []               , _)  = nothing
... | just (_ , TWord _    ∷ _   , _)  = nothing
... | just (_ , TInt _     ∷ _   , _)  = nothing
... | just (_ , TString _  ∷ _   , _)  = nothing
... | just (_ , TLParen    ∷ _   , _)  = nothing
... | just (_ , TLBrace    ∷ _   , _)  = nothing
... | just (_ , TRBrace    ∷ _   , _)  = nothing
... | just (_ , TColon     ∷ _   , _)  = nothing
... | just (_ , TEquals    ∷ _   , _)  = nothing
... | just (_ , TArrow     ∷ _   , _)  = nothing
... | just (_ , TCaret1    ∷ _   , _)  = nothing
... | just (_ , TCaret0    ∷ _   , _)  = nothing
... | just (_ , TCaretW    ∷ _   , _)  = nothing
... | just (_ , TLambda    ∷ _   , _)  = nothing
... | just (_ , TComma     ∷ _   , _)  = nothing
... | just (_ , TSemicolon ∷ _   , _)  = nothing
... | just (_ , TAt        ∷ _   , _)  = nothing
... | just (_ , TPipe      ∷ _   , _)  = nothing
... | just (_ , TDot       ∷ _   , _)  = nothing
... | just (_ , TPlus      ∷ _   , _)  = nothing
... | just (_ , TMinus     ∷ _   , _)  = nothing
... | just (_ , TStar      ∷ _   , _)  = nothing
... | just (_ , TSlash     ∷ _   , _)  = nothing
... | just (_ , TPercent   ∷ _   , _)  = nothing
... | just (_ , TAmpersand ∷ _   , _)  = nothing
... | just (_ , TLt        ∷ _   , _)  = nothing
... | just (_ , TLe        ∷ _   , _)  = nothing
... | just (_ , TGt        ∷ _   , _)  = nothing
... | just (_ , TGe        ∷ _   , _)  = nothing
... | just (_ , TEqEq      ∷ _   , _)  = nothing
... | just (_ , TNeq       ∷ _   , _)  = nothing
... | just (_ , TNewline   ∷ _   , _)  = nothing
... | just (_ , TEOF       ∷ _   , _)  = nothing
... | nothing                            = nothing
parseParenTripleWF _ _ []               _ = nothing
parseParenTripleWF _ _ (TWord _    ∷ _) _ = nothing
parseParenTripleWF _ _ (TInt _     ∷ _) _ = nothing
parseParenTripleWF _ _ (TString _  ∷ _) _ = nothing
parseParenTripleWF _ _ (TLParen    ∷ _) _ = nothing
parseParenTripleWF _ _ (TLBrace    ∷ _) _ = nothing
parseParenTripleWF _ _ (TRBrace    ∷ _) _ = nothing
parseParenTripleWF _ _ (TColon     ∷ _) _ = nothing
parseParenTripleWF _ _ (TEquals    ∷ _) _ = nothing
parseParenTripleWF _ _ (TArrow     ∷ _) _ = nothing
parseParenTripleWF _ _ (TCaret1    ∷ _) _ = nothing
parseParenTripleWF _ _ (TCaret0    ∷ _) _ = nothing
parseParenTripleWF _ _ (TCaretW    ∷ _) _ = nothing
parseParenTripleWF _ _ (TLambda    ∷ _) _ = nothing
parseParenTripleWF _ _ (TSemicolon ∷ _) _ = nothing
parseParenTripleWF _ _ (TAt        ∷ _) _ = nothing
parseParenTripleWF _ _ (TPipe      ∷ _) _ = nothing
parseParenTripleWF _ _ (TDot       ∷ _) _ = nothing
parseParenTripleWF _ _ (TPlus      ∷ _) _ = nothing
parseParenTripleWF _ _ (TMinus     ∷ _) _ = nothing
parseParenTripleWF _ _ (TStar      ∷ _) _ = nothing
parseParenTripleWF _ _ (TSlash     ∷ _) _ = nothing
parseParenTripleWF _ _ (TPercent   ∷ _) _ = nothing
parseParenTripleWF _ _ (TAmpersand ∷ _) _ = nothing
parseParenTripleWF _ _ (TLt        ∷ _) _ = nothing
parseParenTripleWF _ _ (TLe        ∷ _) _ = nothing
parseParenTripleWF _ _ (TGt        ∷ _) _ = nothing
parseParenTripleWF _ _ (TGe        ∷ _) _ = nothing
parseParenTripleWF _ _ (TEqEq      ∷ _) _ = nothing
parseParenTripleWF _ _ (TNeq       ∷ _) _ = nothing
parseParenTripleWF _ _ (TNewline   ∷ _) _ = nothing
parseParenTripleWF _ _ (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseParenContWF : continuation after first `(` + expr
------------------------------------------------------------------------

parseParenContWF e (TComma ∷ rest) (acc rec)
  with parseExprWF rest (rec (s≤s ≤-refl))
... | nothing                = nothing
... | just (e2 , rest' , lt) with parseParenTripleWF e e2 rest'
                                    (rec (m≤n⇒m≤1+n lt))
...   | nothing                   = nothing
...   | just (body , final , lt') =
        just (body , final , <-trans lt' (m≤n⇒m≤1+n lt))
parseParenContWF e (TColon ∷ rest) (acc rec)
  with parseTypeWF rest (<-wellFounded (length rest))
... | just (ty , TRParen ∷ final , dT) =
      just (RAnnot e ty , final ,
            m≤n⇒m≤1+n (<⇒≤ (ParsesType-shrinks dT)))
... | just (_ , []               , _)  = nothing
... | just (_ , TWord _    ∷ _   , _)  = nothing
... | just (_ , TInt _     ∷ _   , _)  = nothing
... | just (_ , TString _  ∷ _   , _)  = nothing
... | just (_ , TLParen    ∷ _   , _)  = nothing
... | just (_ , TLBrace    ∷ _   , _)  = nothing
... | just (_ , TRBrace    ∷ _   , _)  = nothing
... | just (_ , TColon     ∷ _   , _)  = nothing
... | just (_ , TEquals    ∷ _   , _)  = nothing
... | just (_ , TArrow     ∷ _   , _)  = nothing
... | just (_ , TCaret1    ∷ _   , _)  = nothing
... | just (_ , TCaret0    ∷ _   , _)  = nothing
... | just (_ , TCaretW    ∷ _   , _)  = nothing
... | just (_ , TLambda    ∷ _   , _)  = nothing
... | just (_ , TComma     ∷ _   , _)  = nothing
... | just (_ , TSemicolon ∷ _   , _)  = nothing
... | just (_ , TAt        ∷ _   , _)  = nothing
... | just (_ , TPipe      ∷ _   , _)  = nothing
... | just (_ , TDot       ∷ _   , _)  = nothing
... | just (_ , TPlus      ∷ _   , _)  = nothing
... | just (_ , TMinus     ∷ _   , _)  = nothing
... | just (_ , TStar      ∷ _   , _)  = nothing
... | just (_ , TSlash     ∷ _   , _)  = nothing
... | just (_ , TPercent   ∷ _   , _)  = nothing
... | just (_ , TAmpersand ∷ _   , _)  = nothing
... | just (_ , TLt        ∷ _   , _)  = nothing
... | just (_ , TLe        ∷ _   , _)  = nothing
... | just (_ , TGt        ∷ _   , _)  = nothing
... | just (_ , TGe        ∷ _   , _)  = nothing
... | just (_ , TEqEq      ∷ _   , _)  = nothing
... | just (_ , TNeq       ∷ _   , _)  = nothing
... | just (_ , TNewline   ∷ _   , _)  = nothing
... | just (_ , TEOF       ∷ _   , _)  = nothing
... | nothing                            = nothing
parseParenContWF e (TRParen ∷ final) _ = just (e , final , s≤s ≤-refl)
parseParenContWF _ []               _ = nothing
parseParenContWF _ (TWord _    ∷ _) _ = nothing
parseParenContWF _ (TInt _     ∷ _) _ = nothing
parseParenContWF _ (TString _  ∷ _) _ = nothing
parseParenContWF _ (TLParen    ∷ _) _ = nothing
parseParenContWF _ (TLBrace    ∷ _) _ = nothing
parseParenContWF _ (TRBrace    ∷ _) _ = nothing
parseParenContWF _ (TEquals    ∷ _) _ = nothing
parseParenContWF _ (TArrow     ∷ _) _ = nothing
parseParenContWF _ (TCaret1    ∷ _) _ = nothing
parseParenContWF _ (TCaret0    ∷ _) _ = nothing
parseParenContWF _ (TCaretW    ∷ _) _ = nothing
parseParenContWF _ (TLambda    ∷ _) _ = nothing
parseParenContWF _ (TSemicolon ∷ _) _ = nothing
parseParenContWF _ (TAt        ∷ _) _ = nothing
parseParenContWF _ (TPipe      ∷ _) _ = nothing
parseParenContWF _ (TDot       ∷ _) _ = nothing
parseParenContWF _ (TPlus      ∷ _) _ = nothing
parseParenContWF _ (TMinus     ∷ _) _ = nothing
parseParenContWF _ (TStar      ∷ _) _ = nothing
parseParenContWF _ (TSlash     ∷ _) _ = nothing
parseParenContWF _ (TPercent   ∷ _) _ = nothing
parseParenContWF _ (TAmpersand ∷ _) _ = nothing
parseParenContWF _ (TLt        ∷ _) _ = nothing
parseParenContWF _ (TLe        ∷ _) _ = nothing
parseParenContWF _ (TGt        ∷ _) _ = nothing
parseParenContWF _ (TGe        ∷ _) _ = nothing
parseParenContWF _ (TEqEq      ∷ _) _ = nothing
parseParenContWF _ (TNeq       ∷ _) _ = nothing
parseParenContWF _ (TNewline   ∷ _) _ = nothing
parseParenContWF _ (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseParenWF : parse inner expr after `(`, then continuation.
------------------------------------------------------------------------

parseParenWF toks (acc rec) with parseExprWF toks (acc rec)
... | nothing              = nothing
... | just (e , rest , lt) with parseParenContWF e rest (rec lt)
...   | nothing                   = nothing
...   | just (body , rest' , lt') = just (body , rest' , <-trans lt' lt)

------------------------------------------------------------------------
-- parseAtomExprWF helper bodies.
------------------------------------------------------------------------

-- `( ... )` — unit, operator-as-expr, or ordinary paren.
parseAtomExprWF-TLParen (TRParen ∷ rest) _ =
  just (RUnit , rest , s≤s (n≤1+n (length rest)))
parseAtomExprWF-TLParen rest@(TDot       ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TPlus      ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TMinus     ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TStar      ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TSlash     ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TPercent   ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TLt        ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TGt        ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TPipe      ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TAmpersand ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TAt        ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
... | nothing with parseParenWF rest a
...   | nothing                = nothing
...   | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
-- No operator → fall through to parseParenWF.
parseAtomExprWF-TLParen [] _ = nothing
parseAtomExprWF-TLParen rest@(TWord _    ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TInt _     ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TString _  ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TLParen    ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TLBrace    ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TRBrace    ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TColon     ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TEquals    ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TArrow     ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TCaret1    ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TCaret0    ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TCaretW    ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TLambda    ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TComma     ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TSemicolon ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TLe        ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TGe        ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TEqEq      ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TNeq       ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TNewline   ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)
parseAtomExprWF-TLParen rest@(TEOF       ∷ _) a with parseParenWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)

-- Lambda body.
parseAtomExprWF-TLambda rest a with parseLamParamsWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)

-- let-body.
parseAtomExprWF-TLet rest a with parseLetWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)

-- destruct-body.
parseAtomExprWF-TDestruct rest a with parseDestructWF rest a
... | nothing                = nothing
... | just (e , rest' , lt) = just (e , rest' , m≤n⇒m≤1+n lt)

------------------------------------------------------------------------
-- parseAtomExprWF
------------------------------------------------------------------------

parseAtomExprWF [] _ = nothing
parseAtomExprWF (TLParen  ∷ rest) (acc rec) = parseAtomExprWF-TLParen rest (rec (s≤s ≤-refl))
parseAtomExprWF (TLambda  ∷ rest) (acc rec) = parseAtomExprWF-TLambda rest (rec (s≤s ≤-refl))
-- let / destruct dispatched via decidable string equality on "let"/"destruct".
parseAtomExprWF (TWord name ∷ rest) (acc rec) with name ≟ "let"
... | yes refl = parseAtomExprWF-TLet rest (rec (s≤s ≤-refl))
parseAtomExprWF (TWord name ∷ rest) (acc rec) | no _ with name ≟ "destruct"
... | yes refl = parseAtomExprWF-TDestruct rest (rec (s≤s ≤-refl))
-- Qualified reference: name @ alias.
parseAtomExprWF (TWord name ∷ TAt ∷ TWord alias ∷ rest) _ | no _ | no _ =
  if isReserved name then nothing
  else just (RQualified name alias , rest , s≤s (m≤n⇒m≤1+n (n≤1+n _)))
-- Plain variable.
parseAtomExprWF (TWord name ∷ rest) _ | no _ | no _ =
  if isReserved name then nothing else just (RVar name , rest , s≤s ≤-refl)
parseAtomExprWF (TInt n    ∷ rest) _ = just (RInt n , rest , s≤s ≤-refl)
parseAtomExprWF (TString s ∷ rest) _ = just (RStringLit s , rest , s≤s ≤-refl)
parseAtomExprWF (TRParen    ∷ _) _ = nothing
parseAtomExprWF (TLBrace    ∷ _) _ = nothing
parseAtomExprWF (TRBrace    ∷ _) _ = nothing
parseAtomExprWF (TColon     ∷ _) _ = nothing
parseAtomExprWF (TEquals    ∷ _) _ = nothing
parseAtomExprWF (TArrow     ∷ _) _ = nothing
parseAtomExprWF (TCaret1    ∷ _) _ = nothing
parseAtomExprWF (TCaret0    ∷ _) _ = nothing
parseAtomExprWF (TCaretW    ∷ _) _ = nothing
parseAtomExprWF (TComma     ∷ _) _ = nothing
parseAtomExprWF (TSemicolon ∷ _) _ = nothing
parseAtomExprWF (TAt        ∷ _) _ = nothing
parseAtomExprWF (TPipe      ∷ _) _ = nothing
parseAtomExprWF (TDot       ∷ _) _ = nothing
parseAtomExprWF (TPlus      ∷ _) _ = nothing
parseAtomExprWF (TMinus     ∷ _) _ = nothing
parseAtomExprWF (TStar      ∷ _) _ = nothing
parseAtomExprWF (TSlash     ∷ _) _ = nothing
parseAtomExprWF (TPercent   ∷ _) _ = nothing
parseAtomExprWF (TAmpersand ∷ _) _ = nothing
parseAtomExprWF (TLt        ∷ _) _ = nothing
parseAtomExprWF (TLe        ∷ _) _ = nothing
parseAtomExprWF (TGt        ∷ _) _ = nothing
parseAtomExprWF (TGe        ∷ _) _ = nothing
parseAtomExprWF (TEqEq      ∷ _) _ = nothing
parseAtomExprWF (TNeq       ∷ _) _ = nothing
parseAtomExprWF (TNewline   ∷ _) _ = nothing
parseAtomExprWF (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- Application: left-assoc juxtaposition.
------------------------------------------------------------------------

parseAppTailWF f toks (acc rec) with parseAtomExprWF toks (acc rec)
... | just (arg , rest , lt) with parseAppTailWF (RApp f arg) rest (rec lt)
...   | nothing                   = nothing
...   | just (body , rest' , le) = just (body , rest' , ≤-trans le (<⇒≤ lt))
parseAppTailWF f toks _ | nothing = just (f , toks , ≤-refl)

parseAppWF toks (acc rec) with parseAtomExprWF toks (acc rec)
... | nothing                  = nothing
... | just (f , rest , lt) with parseAppTailWF f rest (rec lt)
...   | nothing                   = nothing
...   | just (body , rest' , le) =
        just (body , rest' , ≤-<-trans le lt)

------------------------------------------------------------------------
-- Unary: negation prefix.
------------------------------------------------------------------------

parseUnaryWF (TMinus ∷ rest) (acc rec) with parseUnaryWF rest (rec (s≤s ≤-refl))
... | nothing                  = nothing
... | just (e , rest' , lt)   = just (RUnaryOp OpNeg e , rest' , m≤n⇒m≤1+n lt)
parseUnaryWF []               a = parseAppWF [] a
parseUnaryWF (TWord s    ∷ r) a = parseAppWF (TWord s    ∷ r) a
parseUnaryWF (TInt n     ∷ r) a = parseAppWF (TInt n     ∷ r) a
parseUnaryWF (TString s  ∷ r) a = parseAppWF (TString s  ∷ r) a
parseUnaryWF (TLParen    ∷ r) a = parseAppWF (TLParen    ∷ r) a
parseUnaryWF (TRParen    ∷ r) a = parseAppWF (TRParen    ∷ r) a
parseUnaryWF (TLBrace    ∷ r) a = parseAppWF (TLBrace    ∷ r) a
parseUnaryWF (TRBrace    ∷ r) a = parseAppWF (TRBrace    ∷ r) a
parseUnaryWF (TColon     ∷ r) a = parseAppWF (TColon     ∷ r) a
parseUnaryWF (TEquals    ∷ r) a = parseAppWF (TEquals    ∷ r) a
parseUnaryWF (TArrow     ∷ r) a = parseAppWF (TArrow     ∷ r) a
parseUnaryWF (TCaret1    ∷ r) a = parseAppWF (TCaret1    ∷ r) a
parseUnaryWF (TCaret0    ∷ r) a = parseAppWF (TCaret0    ∷ r) a
parseUnaryWF (TCaretW    ∷ r) a = parseAppWF (TCaretW    ∷ r) a
parseUnaryWF (TLambda    ∷ r) a = parseAppWF (TLambda    ∷ r) a
parseUnaryWF (TComma     ∷ r) a = parseAppWF (TComma     ∷ r) a
parseUnaryWF (TSemicolon ∷ r) a = parseAppWF (TSemicolon ∷ r) a
parseUnaryWF (TAt        ∷ r) a = parseAppWF (TAt        ∷ r) a
parseUnaryWF (TPipe      ∷ r) a = parseAppWF (TPipe      ∷ r) a
parseUnaryWF (TDot       ∷ r) a = parseAppWF (TDot       ∷ r) a
parseUnaryWF (TPlus      ∷ r) a = parseAppWF (TPlus      ∷ r) a
parseUnaryWF (TStar      ∷ r) a = parseAppWF (TStar      ∷ r) a
parseUnaryWF (TSlash     ∷ r) a = parseAppWF (TSlash     ∷ r) a
parseUnaryWF (TPercent   ∷ r) a = parseAppWF (TPercent   ∷ r) a
parseUnaryWF (TAmpersand ∷ r) a = parseAppWF (TAmpersand ∷ r) a
parseUnaryWF (TLt        ∷ r) a = parseAppWF (TLt        ∷ r) a
parseUnaryWF (TLe        ∷ r) a = parseAppWF (TLe        ∷ r) a
parseUnaryWF (TGt        ∷ r) a = parseAppWF (TGt        ∷ r) a
parseUnaryWF (TGe        ∷ r) a = parseAppWF (TGe        ∷ r) a
parseUnaryWF (TEqEq      ∷ r) a = parseAppWF (TEqEq      ∷ r) a
parseUnaryWF (TNeq       ∷ r) a = parseAppWF (TNeq       ∷ r) a
parseUnaryWF (TNewline   ∷ r) a = parseAppWF (TNewline   ∷ r) a
parseUnaryWF (TEOF       ∷ r) a = parseAppWF (TEOF       ∷ r) a

------------------------------------------------------------------------
-- Multiplicative * / %.
------------------------------------------------------------------------

-- Try to parse a multiplicative operator (local, not exported)
tryMulOp : List Token → Maybe (BinOp × List Token)
tryMulOp (TStar ∷ rest) = just (OpMul , rest)
tryMulOp (TSlash ∷ rest) = just (OpDiv , rest)
tryMulOp (TPercent ∷ rest) = just (OpMod , rest)
tryMulOp _ = nothing

parseMulTailWF left (TStar ∷ rest) (acc rec) with parseUnaryWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , lt) with parseMulTailWF (RBinOp OpMul left right) rest'
                                        (rec (m≤n⇒m≤1+n lt))
...   | nothing                    = nothing
...   | just (body , rest'' , le) =
        just (body , rest'' ,
              ≤-trans le (<⇒≤ (m≤n⇒m≤1+n lt)))
parseMulTailWF left (TSlash ∷ rest) (acc rec) with parseUnaryWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , lt) with parseMulTailWF (RBinOp OpDiv left right) rest'
                                        (rec (m≤n⇒m≤1+n lt))
...   | nothing                    = nothing
...   | just (body , rest'' , le) =
        just (body , rest'' ,
              ≤-trans le (<⇒≤ (m≤n⇒m≤1+n lt)))
parseMulTailWF left (TPercent ∷ rest) (acc rec) with parseUnaryWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , lt) with parseMulTailWF (RBinOp OpMod left right) rest'
                                        (rec (m≤n⇒m≤1+n lt))
...   | nothing                    = nothing
...   | just (body , rest'' , le) =
        just (body , rest'' ,
              ≤-trans le (<⇒≤ (m≤n⇒m≤1+n lt)))
parseMulTailWF left []               _ = just (left , [] , ≤-refl)
parseMulTailWF left (TWord s    ∷ r) _ = just (left , TWord s    ∷ r , ≤-refl)
parseMulTailWF left (TInt n     ∷ r) _ = just (left , TInt n     ∷ r , ≤-refl)
parseMulTailWF left (TString s  ∷ r) _ = just (left , TString s  ∷ r , ≤-refl)
parseMulTailWF left (TLParen    ∷ r) _ = just (left , TLParen    ∷ r , ≤-refl)
parseMulTailWF left (TRParen    ∷ r) _ = just (left , TRParen    ∷ r , ≤-refl)
parseMulTailWF left (TLBrace    ∷ r) _ = just (left , TLBrace    ∷ r , ≤-refl)
parseMulTailWF left (TRBrace    ∷ r) _ = just (left , TRBrace    ∷ r , ≤-refl)
parseMulTailWF left (TColon     ∷ r) _ = just (left , TColon     ∷ r , ≤-refl)
parseMulTailWF left (TEquals    ∷ r) _ = just (left , TEquals    ∷ r , ≤-refl)
parseMulTailWF left (TArrow     ∷ r) _ = just (left , TArrow     ∷ r , ≤-refl)
parseMulTailWF left (TCaret1    ∷ r) _ = just (left , TCaret1    ∷ r , ≤-refl)
parseMulTailWF left (TCaret0    ∷ r) _ = just (left , TCaret0    ∷ r , ≤-refl)
parseMulTailWF left (TCaretW    ∷ r) _ = just (left , TCaretW    ∷ r , ≤-refl)
parseMulTailWF left (TLambda    ∷ r) _ = just (left , TLambda    ∷ r , ≤-refl)
parseMulTailWF left (TComma     ∷ r) _ = just (left , TComma     ∷ r , ≤-refl)
parseMulTailWF left (TSemicolon ∷ r) _ = just (left , TSemicolon ∷ r , ≤-refl)
parseMulTailWF left (TAt        ∷ r) _ = just (left , TAt        ∷ r , ≤-refl)
parseMulTailWF left (TPipe      ∷ r) _ = just (left , TPipe      ∷ r , ≤-refl)
parseMulTailWF left (TDot       ∷ r) _ = just (left , TDot       ∷ r , ≤-refl)
parseMulTailWF left (TPlus      ∷ r) _ = just (left , TPlus      ∷ r , ≤-refl)
parseMulTailWF left (TMinus     ∷ r) _ = just (left , TMinus     ∷ r , ≤-refl)
parseMulTailWF left (TAmpersand ∷ r) _ = just (left , TAmpersand ∷ r , ≤-refl)
parseMulTailWF left (TLt        ∷ r) _ = just (left , TLt        ∷ r , ≤-refl)
parseMulTailWF left (TLe        ∷ r) _ = just (left , TLe        ∷ r , ≤-refl)
parseMulTailWF left (TGt        ∷ r) _ = just (left , TGt        ∷ r , ≤-refl)
parseMulTailWF left (TGe        ∷ r) _ = just (left , TGe        ∷ r , ≤-refl)
parseMulTailWF left (TEqEq      ∷ r) _ = just (left , TEqEq      ∷ r , ≤-refl)
parseMulTailWF left (TNeq       ∷ r) _ = just (left , TNeq       ∷ r , ≤-refl)
parseMulTailWF left (TNewline   ∷ r) _ = just (left , TNewline   ∷ r , ≤-refl)
parseMulTailWF left (TEOF       ∷ r) _ = just (left , TEOF       ∷ r , ≤-refl)

parseMulWF toks (acc rec) with parseUnaryWF toks (acc rec)
... | nothing                   = nothing
... | just (first , rest , lt) with parseMulTailWF first rest (rec lt)
...   | nothing                    = nothing
...   | just (body , rest' , le) = just (body , rest' , ≤-<-trans le lt)

------------------------------------------------------------------------
-- Additive + -
------------------------------------------------------------------------

parseAddTailWF left (TPlus ∷ rest) (acc rec) with parseMulWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , lt) with parseAddTailWF (RBinOp OpAdd left right) rest'
                                        (rec (m≤n⇒m≤1+n lt))
...   | nothing                    = nothing
...   | just (body , rest'' , le) =
        just (body , rest'' ,
              ≤-trans le (<⇒≤ (m≤n⇒m≤1+n lt)))
parseAddTailWF left (TMinus ∷ rest) (acc rec) with parseMulWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , lt) with parseAddTailWF (RBinOp OpSub left right) rest'
                                        (rec (m≤n⇒m≤1+n lt))
...   | nothing                    = nothing
...   | just (body , rest'' , le) =
        just (body , rest'' ,
              ≤-trans le (<⇒≤ (m≤n⇒m≤1+n lt)))
parseAddTailWF left []               _ = just (left , [] , ≤-refl)
parseAddTailWF left (TWord s    ∷ r) _ = just (left , TWord s    ∷ r , ≤-refl)
parseAddTailWF left (TInt n     ∷ r) _ = just (left , TInt n     ∷ r , ≤-refl)
parseAddTailWF left (TString s  ∷ r) _ = just (left , TString s  ∷ r , ≤-refl)
parseAddTailWF left (TLParen    ∷ r) _ = just (left , TLParen    ∷ r , ≤-refl)
parseAddTailWF left (TRParen    ∷ r) _ = just (left , TRParen    ∷ r , ≤-refl)
parseAddTailWF left (TLBrace    ∷ r) _ = just (left , TLBrace    ∷ r , ≤-refl)
parseAddTailWF left (TRBrace    ∷ r) _ = just (left , TRBrace    ∷ r , ≤-refl)
parseAddTailWF left (TColon     ∷ r) _ = just (left , TColon     ∷ r , ≤-refl)
parseAddTailWF left (TEquals    ∷ r) _ = just (left , TEquals    ∷ r , ≤-refl)
parseAddTailWF left (TArrow     ∷ r) _ = just (left , TArrow     ∷ r , ≤-refl)
parseAddTailWF left (TCaret1    ∷ r) _ = just (left , TCaret1    ∷ r , ≤-refl)
parseAddTailWF left (TCaret0    ∷ r) _ = just (left , TCaret0    ∷ r , ≤-refl)
parseAddTailWF left (TCaretW    ∷ r) _ = just (left , TCaretW    ∷ r , ≤-refl)
parseAddTailWF left (TLambda    ∷ r) _ = just (left , TLambda    ∷ r , ≤-refl)
parseAddTailWF left (TComma     ∷ r) _ = just (left , TComma     ∷ r , ≤-refl)
parseAddTailWF left (TSemicolon ∷ r) _ = just (left , TSemicolon ∷ r , ≤-refl)
parseAddTailWF left (TAt        ∷ r) _ = just (left , TAt        ∷ r , ≤-refl)
parseAddTailWF left (TPipe      ∷ r) _ = just (left , TPipe      ∷ r , ≤-refl)
parseAddTailWF left (TDot       ∷ r) _ = just (left , TDot       ∷ r , ≤-refl)
parseAddTailWF left (TStar      ∷ r) _ = just (left , TStar      ∷ r , ≤-refl)
parseAddTailWF left (TSlash     ∷ r) _ = just (left , TSlash     ∷ r , ≤-refl)
parseAddTailWF left (TPercent   ∷ r) _ = just (left , TPercent   ∷ r , ≤-refl)
parseAddTailWF left (TAmpersand ∷ r) _ = just (left , TAmpersand ∷ r , ≤-refl)
parseAddTailWF left (TLt        ∷ r) _ = just (left , TLt        ∷ r , ≤-refl)
parseAddTailWF left (TLe        ∷ r) _ = just (left , TLe        ∷ r , ≤-refl)
parseAddTailWF left (TGt        ∷ r) _ = just (left , TGt        ∷ r , ≤-refl)
parseAddTailWF left (TGe        ∷ r) _ = just (left , TGe        ∷ r , ≤-refl)
parseAddTailWF left (TEqEq      ∷ r) _ = just (left , TEqEq      ∷ r , ≤-refl)
parseAddTailWF left (TNeq       ∷ r) _ = just (left , TNeq       ∷ r , ≤-refl)
parseAddTailWF left (TNewline   ∷ r) _ = just (left , TNewline   ∷ r , ≤-refl)
parseAddTailWF left (TEOF       ∷ r) _ = just (left , TEOF       ∷ r , ≤-refl)

parseAddWF toks (acc rec) with parseMulWF toks (acc rec)
... | nothing                   = nothing
... | just (first , rest , lt) with parseAddTailWF first rest (rec lt)
...   | nothing                    = nothing
...   | just (body , rest' , le) = just (body , rest' , ≤-<-trans le lt)

------------------------------------------------------------------------
-- Comparison: non-associative.
------------------------------------------------------------------------

parseCmpOp : List Token → Maybe (BinOp × List Token)
parseCmpOp (TLt ∷ rest) = just (OpLt , rest)
parseCmpOp (TLe ∷ rest) = just (OpLe , rest)
parseCmpOp (TGt ∷ rest) = just (OpGt , rest)
parseCmpOp (TGe ∷ rest) = just (OpGe , rest)
parseCmpOp (TEqEq ∷ rest) = just (OpEq , rest)
parseCmpOp (TNeq ∷ rest) = just (OpNe , rest)
parseCmpOp _ = nothing

-- | Strict-< length bound on parseCmpOp's return: parseCmpOp always
-- consumes exactly one token on success.
tryCmpOp-shrinks : ∀ toks {op rest'}
                 → parseCmpOp toks ≡ just (op , rest')
                 → length rest' < length toks
tryCmpOp-shrinks (TLt    ∷ _) refl = s≤s ≤-refl
tryCmpOp-shrinks (TLe    ∷ _) refl = s≤s ≤-refl
tryCmpOp-shrinks (TGt    ∷ _) refl = s≤s ≤-refl
tryCmpOp-shrinks (TGe    ∷ _) refl = s≤s ≤-refl
tryCmpOp-shrinks (TEqEq  ∷ _) refl = s≤s ≤-refl
tryCmpOp-shrinks (TNeq   ∷ _) refl = s≤s ≤-refl

parseCmpWF toks (acc rec) with parseAddWF toks (acc rec)
... | nothing                   = nothing
... | just (left , rest , lt) = go (parseCmpOp rest) refl
  where
  go : (r : Maybe (BinOp × List Token))
     → parseCmpOp rest ≡ r
     → ParseEL< toks
  go nothing _ = just (left , rest , lt)
  go (just (op , rest')) eq with parseAddWF rest'
                                    (rec (<-trans (tryCmpOp-shrinks rest eq) lt))
  ... | nothing = nothing
  ... | just (right , rest'' , lt') =
        just (RBinOp op left right , rest'' ,
              <-trans lt' (<-trans (tryCmpOp-shrinks rest eq) lt))

------------------------------------------------------------------------
-- Composition: left-assoc f . g → compose f g
------------------------------------------------------------------------

parseCompTailWF left (TDot ∷ rest) (acc rec) with parseCmpWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , lt) with parseCompTailWF (RApp (RApp (RVar "compose") left) right) rest'
                                         (rec (m≤n⇒m≤1+n lt))
...   | nothing                    = nothing
...   | just (body , rest'' , le) =
        just (body , rest'' ,
              ≤-trans le (<⇒≤ (m≤n⇒m≤1+n lt)))
parseCompTailWF left []               _ = just (left , [] , ≤-refl)
parseCompTailWF left (TWord s    ∷ r) _ = just (left , TWord s    ∷ r , ≤-refl)
parseCompTailWF left (TInt n     ∷ r) _ = just (left , TInt n     ∷ r , ≤-refl)
parseCompTailWF left (TString s  ∷ r) _ = just (left , TString s  ∷ r , ≤-refl)
parseCompTailWF left (TLParen    ∷ r) _ = just (left , TLParen    ∷ r , ≤-refl)
parseCompTailWF left (TRParen    ∷ r) _ = just (left , TRParen    ∷ r , ≤-refl)
parseCompTailWF left (TLBrace    ∷ r) _ = just (left , TLBrace    ∷ r , ≤-refl)
parseCompTailWF left (TRBrace    ∷ r) _ = just (left , TRBrace    ∷ r , ≤-refl)
parseCompTailWF left (TColon     ∷ r) _ = just (left , TColon     ∷ r , ≤-refl)
parseCompTailWF left (TEquals    ∷ r) _ = just (left , TEquals    ∷ r , ≤-refl)
parseCompTailWF left (TArrow     ∷ r) _ = just (left , TArrow     ∷ r , ≤-refl)
parseCompTailWF left (TCaret1    ∷ r) _ = just (left , TCaret1    ∷ r , ≤-refl)
parseCompTailWF left (TCaret0    ∷ r) _ = just (left , TCaret0    ∷ r , ≤-refl)
parseCompTailWF left (TCaretW    ∷ r) _ = just (left , TCaretW    ∷ r , ≤-refl)
parseCompTailWF left (TLambda    ∷ r) _ = just (left , TLambda    ∷ r , ≤-refl)
parseCompTailWF left (TComma     ∷ r) _ = just (left , TComma     ∷ r , ≤-refl)
parseCompTailWF left (TSemicolon ∷ r) _ = just (left , TSemicolon ∷ r , ≤-refl)
parseCompTailWF left (TAt        ∷ r) _ = just (left , TAt        ∷ r , ≤-refl)
parseCompTailWF left (TPipe      ∷ r) _ = just (left , TPipe      ∷ r , ≤-refl)
parseCompTailWF left (TPlus      ∷ r) _ = just (left , TPlus      ∷ r , ≤-refl)
parseCompTailWF left (TMinus     ∷ r) _ = just (left , TMinus     ∷ r , ≤-refl)
parseCompTailWF left (TStar      ∷ r) _ = just (left , TStar      ∷ r , ≤-refl)
parseCompTailWF left (TSlash     ∷ r) _ = just (left , TSlash     ∷ r , ≤-refl)
parseCompTailWF left (TPercent   ∷ r) _ = just (left , TPercent   ∷ r , ≤-refl)
parseCompTailWF left (TAmpersand ∷ r) _ = just (left , TAmpersand ∷ r , ≤-refl)
parseCompTailWF left (TLt        ∷ r) _ = just (left , TLt        ∷ r , ≤-refl)
parseCompTailWF left (TLe        ∷ r) _ = just (left , TLe        ∷ r , ≤-refl)
parseCompTailWF left (TGt        ∷ r) _ = just (left , TGt        ∷ r , ≤-refl)
parseCompTailWF left (TGe        ∷ r) _ = just (left , TGe        ∷ r , ≤-refl)
parseCompTailWF left (TEqEq      ∷ r) _ = just (left , TEqEq      ∷ r , ≤-refl)
parseCompTailWF left (TNeq       ∷ r) _ = just (left , TNeq       ∷ r , ≤-refl)
parseCompTailWF left (TNewline   ∷ r) _ = just (left , TNewline   ∷ r , ≤-refl)
parseCompTailWF left (TEOF       ∷ r) _ = just (left , TEOF       ∷ r , ≤-refl)

parseCompWF toks (acc rec) with parseCmpWF toks (acc rec)
... | nothing                   = nothing
... | just (first , rest , lt) with parseCompTailWF first rest (rec lt)
...   | nothing                    = nothing
...   | just (body , rest' , le) = just (body , rest' , ≤-<-trans le lt)

------------------------------------------------------------------------
-- Top-level entry: parseExpr = parseComp.
------------------------------------------------------------------------

parseExprWF toks a = parseCompWF toks a

------------------------------------------------------------------------
-- Plain-Parser wrapper for external callers.
------------------------------------------------------------------------

parseExpr : Parser RawExpr
parseExpr toks with parseExprWF toks (<-wellFounded (length toks))
... | nothing                = nothing
... | just (e , rest , _)    = just (e , rest)
