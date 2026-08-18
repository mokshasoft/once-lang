-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
-- Σ-packaged result that includes a parsing-relation derivation
-- witness (see `Once.Parser.ExprRelation`). Acc inputs for recursive
-- sub-calls are derived from sub-derivations via `ParsesX-shrinks`.
-- Per plan 0.3 task #38 (Phase 3b).
--
-- External callers use `parseExpr : Parser RawExpr` (the top-level
-- wrapper at the end of this file) which forgets the derivation.
------------------------------------------------------------------------

module Once.Parser.Expr where

open import Data.List using (List; []; _∷_; foldr; reverse; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Char using (Char)
open import Data.String using (String)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
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
                                       RPair; RDestruct; RUnit; RInt; RFloat;
                                       RStringLit; RAnnot; RBinOp; RUnaryOp;
                                       BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod;
                                       OpLt; OpLe; OpGt; OpGe; OpEq; OpNe;
                                       UnaryOp; OpNeg)
open import Once.Parser.Token
open import Once.Parser.Core
open import Once.Parser.Type using (parseTypeWF)
open import Once.Parser.TypeRelation using (ParsesType; ParsesType-shrinks)

------------------------------------------------------------------------
-- `isReserved` lives in `Once.Parser.ExprRelation` (to avoid an import
-- cycle between this module and the relations module). Re-export it
-- so downstream callers (e.g. Once.Grammar.ExprPrinter) keep importing
-- it from Once.Parser.Expr.
------------------------------------------------------------------------

open import Once.Parser.ExprRelation public using (isReserved)
open import Once.Parser.ExprRelation

------------------------------------------------------------------------
-- Dec-valued return types: success carries a *derivation* in the
-- corresponding parsing relation, not just a length bound. The bound
-- is recovered on demand via the relation's `ParsesX-shrinks` lemma.
--
-- Plan 0.3 task #38 Phase 3b.
------------------------------------------------------------------------

ParseExprD : List Token → Set
ParseExprD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesExpr toks e rest)

ParseCompD : List Token → Set
ParseCompD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesComp toks e rest)

ParseCmpD : List Token → Set
ParseCmpD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesCmp toks e rest)

ParseAddD : List Token → Set
ParseAddD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesAdd toks e rest)

ParseMulD : List Token → Set
ParseMulD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesMul toks e rest)

ParseUnaryD : List Token → Set
ParseUnaryD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesUnary toks e rest)

ParseAppD : List Token → Set
ParseAppD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesApp toks e rest)

ParseAtomExprD : List Token → Set
ParseAtomExprD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesAtomExpr toks e rest)

ParseAppTailD : RawExpr → List Token → Set
ParseAppTailD left toks =
  Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesAppTail left toks e rest)

ParseMulTailD : RawExpr → List Token → Set
ParseMulTailD left toks =
  Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesMulTail left toks e rest)

ParseAddTailD : RawExpr → List Token → Set
ParseAddTailD left toks =
  Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesAddTail left toks e rest)

ParseCompTailD : RawExpr → List Token → Set
ParseCompTailD left toks =
  Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesCompTail left toks e rest)

ParseLamParamsD : List Token → Set
ParseLamParamsD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesLamParams toks e rest)

ParseLetD : List Token → Set
ParseLetD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesLet toks e rest)

ParseLetInD : String → RawExpr → List Token → Set
ParseLetInD name val toks =
  Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesLetIn name val toks e rest)

ParseDestructD : List Token → Set
ParseDestructD toks = Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesDestruct toks e rest)

ParseDestructOfD : RawExpr → List Token → Set
ParseDestructOfD scrut toks =
  Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesDestructOf scrut toks e rest)

ParseDestructBranchesD : RawExpr → List Token → Set
ParseDestructBranchesD scrut toks =
  Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesDestructBranches scrut toks e rest)

ParseRightBranchD : RawExpr → String → RawExpr → List Token → Set
ParseRightBranchD scrut x left toks =
  Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesRightBranch scrut x left toks e rest)

ParseParenContD : RawExpr → List Token → Set
ParseParenContD e toks =
  Maybe (Σ[ eOut ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesParenCont e toks eOut rest)

ParseParenTripleD : RawExpr → RawExpr → List Token → Set
ParseParenTripleD e1 e2 toks =
  Maybe (Σ[ rest ∈ List Token ] ParsesParenTriple e1 e2 toks rest)

ParseOpExprD : List Char → List Token → Set
ParseOpExprD chars toks =
  Maybe (Σ[ e ∈ RawExpr ] Σ[ rest ∈ List Token ] ParsesOpExpr chars toks e rest)

------------------------------------------------------------------------
-- Operator-as-expression parser: (&), (.), (|>), etc.
--
-- Structurally recursive on the token list (each clause consumes at
-- least one token before recursing). The result carries a
-- `ParsesOpExpr` derivation.
------------------------------------------------------------------------

parseOpExprWF : (toks : List Token) (a : List Char) → ParseOpExprD a toks
parseOpExprWF (TDot       ∷ rest) a with parseOpExprWF rest ('.' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-dot d)
parseOpExprWF (TPlus      ∷ rest) a with parseOpExprWF rest ('+' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-plus d)
parseOpExprWF (TMinus     ∷ rest) a with parseOpExprWF rest ('-' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-minus d)
parseOpExprWF (TStar      ∷ rest) a with parseOpExprWF rest ('*' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-star d)
parseOpExprWF (TSlash     ∷ rest) a with parseOpExprWF rest ('/' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-slash d)
parseOpExprWF (TPercent   ∷ rest) a with parseOpExprWF rest ('%' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-percent d)
parseOpExprWF (TLt        ∷ rest) a with parseOpExprWF rest ('<' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-lt d)
parseOpExprWF (TGt        ∷ rest) a with parseOpExprWF rest ('>' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-gt d)
parseOpExprWF (TPipe      ∷ rest) a with parseOpExprWF rest ('|' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-pipe d)
parseOpExprWF (TAmpersand ∷ rest) a with parseOpExprWF rest ('&' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-amp d)
parseOpExprWF (TAt        ∷ rest) a with parseOpExprWF rest ('@' ∷ a)
... | nothing               = nothing
... | just (e , rest' , d) = just (e , rest' , poe-at d)
-- Closing paren: finish.  Empty operator name → nothing.
parseOpExprWF (TRParen ∷ rest) []      = nothing
parseOpExprWF (TRParen ∷ rest) (c ∷ a) =
  just (RVar (Data.String.fromList (reverse (c ∷ a))) , rest , poe-close)
-- Any other token kills the operator parse.
parseOpExprWF []               _ = nothing
parseOpExprWF (TWord _    ∷ _) _ = nothing
parseOpExprWF (TInt _     ∷ _) _ = nothing
parseOpExprWF (TFloat _ _ _ ∷ _) _ = nothing
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
parseOpExprWF (TBang      ∷ _) _ = nothing
parseOpExprWF (TNewline   ∷ _) _ = nothing
parseOpExprWF (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- Mutual WF parser declarations
------------------------------------------------------------------------

parseExprWF        : (toks : List Token) → Acc _<_ (length toks) → ParseExprD toks
parseCompWF        : (toks : List Token) → Acc _<_ (length toks) → ParseCompD toks
parseCmpWF         : (toks : List Token) → Acc _<_ (length toks) → ParseCmpD toks
parseAddWF         : (toks : List Token) → Acc _<_ (length toks) → ParseAddD toks
parseMulWF         : (toks : List Token) → Acc _<_ (length toks) → ParseMulD toks
parseUnaryWF       : (toks : List Token) → Acc _<_ (length toks) → ParseUnaryD toks
parseAppWF         : (toks : List Token) → Acc _<_ (length toks) → ParseAppD toks
parseAtomExprWF    : (toks : List Token) → Acc _<_ (length toks) → ParseAtomExprD toks

parseLamParamsWF   : (toks : List Token) → Acc _<_ (length toks) → ParseLamParamsD toks
parseLetWF         : (toks : List Token) → Acc _<_ (length toks) → ParseLetD toks
parseDestructWF    : (toks : List Token) → Acc _<_ (length toks) → ParseDestructD toks

parseLetContWF     : (name : String) (val : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseLetInD name val toks
parseDestructBranchesWF :
                     (scrut : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseDestructBranchesD scrut toks
parseDestructOfWF  : (scrut : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseDestructOfD scrut toks
parseRightBranchWF : (scrut : RawExpr) (x : String) (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseRightBranchD scrut x left toks
parseParenTripleWF : (e e2 : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseParenTripleD e e2 toks
parseParenContWF   : (e : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseParenContD e toks

-- Tail parsers (may no-op, non-strict decrease)
parseAppTailWF     : (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseAppTailD left toks
parseMulTailWF     : (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseMulTailD left toks
parseAddTailWF     : (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseAddTailD left toks
parseCompTailWF    : (left : RawExpr)
                   → (toks : List Token) → Acc _<_ (length toks) → ParseCompTailD left toks

------------------------------------------------------------------------
-- Named helpers for `parseAtomExprWF` consume-and-recurse cases.
-- Each takes the POST-Acc-destructured sub-Acc, keeping the nested
-- `with` tree out of parseAtomExprWF's body (termination-checker
-- hygiene — same trick Parser/Type.agda uses).
------------------------------------------------------------------------

parseAtomExprWF-TLParen :
    (rest : List Token) → Acc _<_ (length rest)
  → ParseAtomExprD (TLParen ∷ rest)
parseAtomExprWF-TLambda :
    (rest : List Token) → Acc _<_ (length rest)
  → ParseAtomExprD (TLambda ∷ rest)
parseAtomExprWF-TLet :
    (rest : List Token) → Acc _<_ (length rest)
  → ParseAtomExprD (TWord "let" ∷ rest)
parseAtomExprWF-TDestruct :
    (rest : List Token) → Acc _<_ (length rest)
  → ParseAtomExprD (TWord "destruct" ∷ rest)

-- | Paren-continuation helper: after `(`, parse inner expr +
-- `parseParenContWF` continuation. Separated from the operator-first
-- dispatch so termination-checks cleanly: this helper takes `a` and
-- passes it straight to `parseExprWF`, which matches the same pattern
-- as Parser/Type.agda's `parseTypeAtomWF-TLParen`.
parseAtomExprWF-TLParen-paren :
    (rest : List Token) → Acc _<_ (length rest)
  → ParseAtomExprD (TLParen ∷ rest)

------------------------------------------------------------------------
-- parseLamParamsWF : \x y z -> body
------------------------------------------------------------------------

parseLamParamsWF (TArrow ∷ rest) (acc rec) with parseExprWF rest (rec (s≤s ≤-refl))
... | nothing                = nothing
... | just (body , rest' , d) = just (body , rest' , plp-body d)
parseLamParamsWF (TWord name ∷ rest) (acc rec) with parseLamParamsWF rest (rec (s≤s ≤-refl))
... | nothing                  = nothing
... | just (body , rest' , d) = just (RLam name body , rest' , plp-arg d)
parseLamParamsWF []               _ = nothing
parseLamParamsWF (TInt _     ∷ _) _ = nothing
parseLamParamsWF (TFloat _ _ _ ∷ _) _ = nothing
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
parseLamParamsWF (TBang      ∷ _) _ = nothing
parseLamParamsWF (TNewline   ∷ _) _ = nothing
parseLamParamsWF (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseLetContWF : the `in body` continuation of a let binding.
-- Only single-binding is supported by the relation (ConcreteExpr's
-- c-e-let1). Multi-binding `; more-lets in body` is rejected.
------------------------------------------------------------------------

parseLetContWF name val (TWord w ∷ rest) (acc rec) with wordEq-view w "in"
... | we-match refl with parseExprWF rest (rec (s≤s ≤-refl))
...   | nothing                  = nothing
...   | just (body , rest' , d) = just (RLet name val body , rest' , plin d)
parseLetContWF name val (TWord w ∷ rest) _ | we-nomatch _ = nothing
parseLetContWF _ _ []               _ = nothing
parseLetContWF _ _ (TInt _     ∷ _) _ = nothing
parseLetContWF _ _ (TFloat _ _ _ ∷ _) _ = nothing
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
parseLetContWF _ _ (TSemicolon ∷ _) _ = nothing
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
parseLetContWF _ _ (TBang      ∷ _) _ = nothing
parseLetContWF _ _ (TNewline   ∷ _) _ = nothing
parseLetContWF _ _ (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseLetWF : let x = e1 in e2
--
-- Single-binding only (the relation doesn't model `let x = e1 ; y = e2
-- in body`). Multi-binding is rejected here too (previously accepted
-- by the bound-only parser; kept consistent with the relation's scope).
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
... | let-head name rest
    with parseExprWF rest (rec (s≤s (n≤1+n _)))
...   | nothing = nothing
...   | just (val , rest' , dV)
      with parseLetContWF name val rest'
             (rec (<-trans (ParsesExpr-shrinks dV) (s≤s (n≤1+n _))))
...     | nothing                       = nothing
...     | just (body , rest'' , dIn) =
          just (body , rest'' , plet-single dV dIn)

------------------------------------------------------------------------
-- parseRightBranchWF : Right y -> e2 }
------------------------------------------------------------------------

-- | Shape view on a 4-token prefix `TSemicolon ∷ TWord w ∷ TWord y ∷ TArrow ∷ rest`.
data RBShape : List Token → Set where
  rb-head  : (w y : String) (rest : List Token)
           → RBShape (TSemicolon ∷ TWord w ∷ TWord y ∷ TArrow ∷ rest)
  rb-other : (toks : List Token) → RBShape toks

rbView : (toks : List Token) → RBShape toks
rbView (TSemicolon ∷ TWord w ∷ TWord y ∷ TArrow ∷ rest) = rb-head w y rest
rbView toks = rb-other toks

parseRightBranchWF scrut x left toks (acc rec) with rbView toks
... | rb-other _ = nothing
... | rb-head w y rest with wordEq-view w "Right"
...   | we-nomatch _ = nothing
...   | we-match refl
      with parseExprWF rest (rec (s≤s (m≤n⇒m≤1+n (m≤n⇒m≤1+n (n≤1+n _)))))
...     | nothing                              = nothing
...     | just (right , TRBrace ∷ final , dR) =
          just (RDestruct scrut x left y right , final , prb dR)
...     | just (_ , [] , _)              = nothing
...     | just (_ , TWord _    ∷ _ , _)  = nothing
...     | just (_ , TInt _     ∷ _ , _)  = nothing
...     | just (_ , TFloat _ _ _ ∷ _ , _)  = nothing
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
...     | just (_ , TBang      ∷ _ , _)  = nothing
...     | just (_ , TNewline   ∷ _ , _)  = nothing
...     | just (_ , TEOF       ∷ _ , _)  = nothing

------------------------------------------------------------------------
-- parseDestructBranchesWF : Left x -> e1 ; Right y -> e2 }
------------------------------------------------------------------------

-- | Shape view on `TWord w ∷ TWord x ∷ TArrow ∷ rest`.
data DBShape : List Token → Set where
  db-head  : (w x : String) (rest : List Token)
           → DBShape (TWord w ∷ TWord x ∷ TArrow ∷ rest)
  db-other : (toks : List Token) → DBShape toks

dbView : (toks : List Token) → DBShape toks
dbView (TWord w ∷ TWord x ∷ TArrow ∷ rest) = db-head w x rest
dbView toks                                 = db-other toks

parseDestructBranchesWF scrut toks (acc rec) with dbView toks
... | db-other _ = nothing
... | db-head w x rest with wordEq-view w "Left"
...   | we-nomatch _ = nothing
...   | we-match refl
      with parseExprWF rest (rec (s≤s (m≤n⇒m≤1+n (n≤1+n _))))
...     | nothing                  = nothing
...     | just (left , rest' , dL)
        with parseRightBranchWF scrut x left rest'
              (rec (<-trans (ParsesExpr-shrinks dL) (s≤s (m≤n⇒m≤1+n (n≤1+n _)))))
...       | nothing                   = nothing
...       | just (body , rest'' , dR) = just (body , rest'' , pdb dL dR)

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
... | do-head w rest with wordEq-view w "of"
...   | we-nomatch _ = nothing
...   | we-match refl
      with parseDestructBranchesWF scrut rest (rec (s≤s (n≤1+n _)))
...     | nothing                  = nothing
...     | just (body , rest' , dB) = just (body , rest' , pdof dB)

------------------------------------------------------------------------
-- parseDestructWF : `destruct e of { ... }`
------------------------------------------------------------------------

parseDestructWF toks (acc rec) with parseExprWF toks (acc rec)
... | nothing                   = nothing
... | just (scrut , rest , dS)
    with parseDestructOfWF scrut rest (rec (ParsesExpr-shrinks dS))
...   | nothing                   = nothing
...   | just (body , rest' , dOf) = just (body , rest' , pd-mk dS dOf)

------------------------------------------------------------------------
-- parseParenTripleWF : continuation after 2nd tuple element.
-- The relation only supports `TRParen ∷ rest` (closing immediately
-- after two elements). A triple via `, e3 )` is NOT represented in
-- `ParsesParenTriple` — reject it here.
------------------------------------------------------------------------

parseParenTripleWF e e2 (TRParen ∷ final) _ =
  just (final , ppt-close)
parseParenTripleWF _ _ []               _ = nothing
parseParenTripleWF _ _ (TWord _    ∷ _) _ = nothing
parseParenTripleWF _ _ (TInt _     ∷ _) _ = nothing
parseParenTripleWF _ _ (TFloat _ _ _ ∷ _) _ = nothing
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
parseParenTripleWF _ _ (TComma     ∷ _) _ = nothing
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
parseParenTripleWF _ _ (TBang      ∷ _) _ = nothing
parseParenTripleWF _ _ (TNewline   ∷ _) _ = nothing
parseParenTripleWF _ _ (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseParenContWF : continuation after first `(` + expr
------------------------------------------------------------------------

parseParenContWF e (TRParen ∷ final) _ = just (e , final , ppc-close)
parseParenContWF e (TComma ∷ rest) (acc rec)
  with parseExprWF rest (rec (s≤s ≤-refl))
... | nothing                = nothing
... | just (e2 , rest' , dE)
    with parseParenTripleWF e e2 rest'
          (rec (<-trans (ParsesExpr-shrinks dE) (s≤s ≤-refl)))
...   | nothing                   = nothing
...   | just (final , dT) =
        just (RPair e e2 , final , ppc-pair dE dT)
parseParenContWF e (TColon ∷ rest) (acc rec)
  with parseTypeWF rest (<-wellFounded (length rest))
... | just (ty , TRParen ∷ final , dT) =
      just (RAnnot e ty , final , ppc-annot dT)
... | just (_ , []               , _)  = nothing
... | just (_ , TWord _    ∷ _   , _)  = nothing
... | just (_ , TInt _     ∷ _   , _)  = nothing
... | just (_ , TFloat _ _ _ ∷ _   , _)  = nothing
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
... | just (_ , TBang      ∷ _   , _)  = nothing
... | just (_ , TNewline   ∷ _   , _)  = nothing
... | just (_ , TEOF       ∷ _   , _)  = nothing
... | nothing                            = nothing
parseParenContWF _ []               _ = nothing
parseParenContWF _ (TWord _    ∷ _) _ = nothing
parseParenContWF _ (TInt _     ∷ _) _ = nothing
parseParenContWF _ (TFloat _ _ _ ∷ _) _ = nothing
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
parseParenContWF _ (TBang      ∷ _) _ = nothing
parseParenContWF _ (TNewline   ∷ _) _ = nothing
parseParenContWF _ (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- parseAtomExprWF-TLParen : `( ... )` — unit, operator-as-expr, or
-- ordinary paren/pair/triple/annot.
--
-- When the first post-`(` token is an operator-shape, try operator-
-- parser first; on its failure, fall through to the general paren
-- continuation. Each operator-shape case has its own clause so both
-- poe constructors for that token kind and the fallback paren paths
-- are visible to Agda's termination checker.
------------------------------------------------------------------------

-- | `( )` → RUnit.
parseAtomExprWF-TLParen (TRParen ∷ rest) _ =
  just (RUnit , rest , pae-unit)
-- Operator-shaped leads: try parseOpExprWF first, fall through to
-- parseAtomExprWF-TLParen-paren on failure.
parseAtomExprWF-TLParen rest@(TDot ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TPlus ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TMinus ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TStar ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TSlash ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TPercent ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TLt ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TGt ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TPipe ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TAmpersand ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TAt ∷ _) a with parseOpExprWF rest []
... | just (e , rest' , dOp) = just (e , rest' , pae-paren-op dOp)
... | nothing                = parseAtomExprWF-TLParen-paren rest a
-- Non-operator leads: delegate directly.
parseAtomExprWF-TLParen []                 a = parseAtomExprWF-TLParen-paren [] a
parseAtomExprWF-TLParen rest@(TWord _   ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TInt _    ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TFloat _ _ _ ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TString _ ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TLParen   ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TLBrace   ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TRBrace   ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TColon    ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TEquals   ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TArrow    ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TCaret1   ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TCaret0   ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TCaretW   ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TLambda   ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TComma    ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TSemicolon ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TLe       ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TGe       ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TEqEq     ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TNeq      ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TBang     ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TNewline  ∷ _) a = parseAtomExprWF-TLParen-paren rest a
parseAtomExprWF-TLParen rest@(TEOF      ∷ _) a = parseAtomExprWF-TLParen-paren rest a

-- Paren-continuation helper. Mirrors Type.agda's parseTypeAtomWF-TLParen:
-- keep Acc opaque for the `parseExprWF` call, destructure only in
-- the nested success branch to get a sub-Acc for parseParenContWF.
parseAtomExprWF-TLParen-paren rest a with parseExprWF rest a
... | nothing = nothing
parseAtomExprWF-TLParen-paren rest (acc rec) | just (e , rest' , dE)
    with parseParenContWF e rest' (rec (ParsesExpr-shrinks dE))
...   | nothing = nothing
...   | just (eOut , restO , dC) = just (eOut , restO , pae-paren dE dC)

-- Lambda body.
parseAtomExprWF-TLambda rest a with parseLamParamsWF rest a
... | nothing                = nothing
... | just (e , rest' , d)   = just (e , rest' , pae-lambda d)

-- let-body.
parseAtomExprWF-TLet rest a with parseLetWF rest a
... | nothing                = nothing
... | just (e , rest' , d)   = just (e , rest' , pae-let d)

-- destruct-body.
parseAtomExprWF-TDestruct rest a with parseDestructWF rest a
... | nothing                = nothing
... | just (e , rest' , d)   = just (e , rest' , pae-destruct d)

------------------------------------------------------------------------
-- parseAtomExprWF
------------------------------------------------------------------------

-- | Variable-case guard: refl-evidence that `isReserved name ≡ false`.
-- The pae-var / pae-qual constructors require this evidence.
atomExprVarWF :
    (name : String) (eq : isReserved name ≡ false) (rest : List Token)
  → ParseAtomExprD (TWord name ∷ rest)
atomExprVarWF name eq (TAt ∷ TWord alias ∷ rest) =
  just (RQualified name alias , rest , pae-qual eq)
atomExprVarWF name eq []                = just (RVar name , [] , pae-var eq nqp-[])
atomExprVarWF name eq (TWord _    ∷ r)  = just (RVar name , TWord _    ∷ r , pae-var eq nqp-TWord)
atomExprVarWF name eq (TInt _     ∷ r)  = just (RVar name , TInt _     ∷ r , pae-var eq nqp-TInt)
atomExprVarWF name eq (TFloat _ _ _ ∷ r) = just (RVar name , TFloat _ _ _ ∷ r , pae-var eq nqp-TFloat)
atomExprVarWF name eq (TString _  ∷ r)  = just (RVar name , TString _  ∷ r , pae-var eq nqp-TString)
atomExprVarWF name eq (TLParen    ∷ r)  = just (RVar name , TLParen    ∷ r , pae-var eq nqp-TLParen)
atomExprVarWF name eq (TRParen    ∷ r)  = just (RVar name , TRParen    ∷ r , pae-var eq nqp-TRParen)
atomExprVarWF name eq (TLBrace    ∷ r)  = just (RVar name , TLBrace    ∷ r , pae-var eq nqp-TLBrace)
atomExprVarWF name eq (TRBrace    ∷ r)  = just (RVar name , TRBrace    ∷ r , pae-var eq nqp-TRBrace)
atomExprVarWF name eq (TColon     ∷ r)  = just (RVar name , TColon     ∷ r , pae-var eq nqp-TColon)
atomExprVarWF name eq (TEquals    ∷ r)  = just (RVar name , TEquals    ∷ r , pae-var eq nqp-TEquals)
atomExprVarWF name eq (TArrow     ∷ r)  = just (RVar name , TArrow     ∷ r , pae-var eq nqp-TArrow)
atomExprVarWF name eq (TCaret1    ∷ r)  = just (RVar name , TCaret1    ∷ r , pae-var eq nqp-TCaret1)
atomExprVarWF name eq (TCaret0    ∷ r)  = just (RVar name , TCaret0    ∷ r , pae-var eq nqp-TCaret0)
atomExprVarWF name eq (TCaretW    ∷ r)  = just (RVar name , TCaretW    ∷ r , pae-var eq nqp-TCaretW)
atomExprVarWF name eq (TLambda    ∷ r)  = just (RVar name , TLambda    ∷ r , pae-var eq nqp-TLambda)
atomExprVarWF name eq (TComma     ∷ r)  = just (RVar name , TComma     ∷ r , pae-var eq nqp-TComma)
atomExprVarWF name eq (TSemicolon ∷ r)  = just (RVar name , TSemicolon ∷ r , pae-var eq nqp-TSemicolon)
-- TAt without a following TWord: just a variable.
atomExprVarWF name eq (TAt        ∷ []) = just (RVar name , TAt ∷ [] , pae-var eq nqp-TAt-[])
atomExprVarWF name eq (TAt        ∷ TInt _     ∷ r) = just (RVar name , TAt ∷ TInt _     ∷ r , pae-var eq (nqp-TAt-cons ntw-TInt))
atomExprVarWF name eq (TAt        ∷ TFloat _ _ _ ∷ r) = just (RVar name , TAt ∷ TFloat _ _ _ ∷ r , pae-var eq (nqp-TAt-cons ntw-TFloat))
atomExprVarWF name eq (TAt        ∷ TString _  ∷ r) = just (RVar name , TAt ∷ TString _  ∷ r , pae-var eq (nqp-TAt-cons ntw-TString))
atomExprVarWF name eq (TAt        ∷ TLParen    ∷ r) = just (RVar name , TAt ∷ TLParen    ∷ r , pae-var eq (nqp-TAt-cons ntw-TLParen))
atomExprVarWF name eq (TAt        ∷ TRParen    ∷ r) = just (RVar name , TAt ∷ TRParen    ∷ r , pae-var eq (nqp-TAt-cons ntw-TRParen))
atomExprVarWF name eq (TAt        ∷ TLBrace    ∷ r) = just (RVar name , TAt ∷ TLBrace    ∷ r , pae-var eq (nqp-TAt-cons ntw-TLBrace))
atomExprVarWF name eq (TAt        ∷ TRBrace    ∷ r) = just (RVar name , TAt ∷ TRBrace    ∷ r , pae-var eq (nqp-TAt-cons ntw-TRBrace))
atomExprVarWF name eq (TAt        ∷ TColon     ∷ r) = just (RVar name , TAt ∷ TColon     ∷ r , pae-var eq (nqp-TAt-cons ntw-TColon))
atomExprVarWF name eq (TAt        ∷ TEquals    ∷ r) = just (RVar name , TAt ∷ TEquals    ∷ r , pae-var eq (nqp-TAt-cons ntw-TEquals))
atomExprVarWF name eq (TAt        ∷ TArrow     ∷ r) = just (RVar name , TAt ∷ TArrow     ∷ r , pae-var eq (nqp-TAt-cons ntw-TArrow))
atomExprVarWF name eq (TAt        ∷ TCaret1    ∷ r) = just (RVar name , TAt ∷ TCaret1    ∷ r , pae-var eq (nqp-TAt-cons ntw-TCaret1))
atomExprVarWF name eq (TAt        ∷ TCaret0    ∷ r) = just (RVar name , TAt ∷ TCaret0    ∷ r , pae-var eq (nqp-TAt-cons ntw-TCaret0))
atomExprVarWF name eq (TAt        ∷ TCaretW    ∷ r) = just (RVar name , TAt ∷ TCaretW    ∷ r , pae-var eq (nqp-TAt-cons ntw-TCaretW))
atomExprVarWF name eq (TAt        ∷ TLambda    ∷ r) = just (RVar name , TAt ∷ TLambda    ∷ r , pae-var eq (nqp-TAt-cons ntw-TLambda))
atomExprVarWF name eq (TAt        ∷ TComma     ∷ r) = just (RVar name , TAt ∷ TComma     ∷ r , pae-var eq (nqp-TAt-cons ntw-TComma))
atomExprVarWF name eq (TAt        ∷ TSemicolon ∷ r) = just (RVar name , TAt ∷ TSemicolon ∷ r , pae-var eq (nqp-TAt-cons ntw-TSemicolon))
atomExprVarWF name eq (TAt        ∷ TAt        ∷ r) = just (RVar name , TAt ∷ TAt        ∷ r , pae-var eq (nqp-TAt-cons ntw-TAt))
atomExprVarWF name eq (TAt        ∷ TPipe      ∷ r) = just (RVar name , TAt ∷ TPipe      ∷ r , pae-var eq (nqp-TAt-cons ntw-TPipe))
atomExprVarWF name eq (TAt        ∷ TDot       ∷ r) = just (RVar name , TAt ∷ TDot       ∷ r , pae-var eq (nqp-TAt-cons ntw-TDot))
atomExprVarWF name eq (TAt        ∷ TPlus      ∷ r) = just (RVar name , TAt ∷ TPlus      ∷ r , pae-var eq (nqp-TAt-cons ntw-TPlus))
atomExprVarWF name eq (TAt        ∷ TMinus     ∷ r) = just (RVar name , TAt ∷ TMinus     ∷ r , pae-var eq (nqp-TAt-cons ntw-TMinus))
atomExprVarWF name eq (TAt        ∷ TStar      ∷ r) = just (RVar name , TAt ∷ TStar      ∷ r , pae-var eq (nqp-TAt-cons ntw-TStar))
atomExprVarWF name eq (TAt        ∷ TSlash     ∷ r) = just (RVar name , TAt ∷ TSlash     ∷ r , pae-var eq (nqp-TAt-cons ntw-TSlash))
atomExprVarWF name eq (TAt        ∷ TPercent   ∷ r) = just (RVar name , TAt ∷ TPercent   ∷ r , pae-var eq (nqp-TAt-cons ntw-TPercent))
atomExprVarWF name eq (TAt        ∷ TAmpersand ∷ r) = just (RVar name , TAt ∷ TAmpersand ∷ r , pae-var eq (nqp-TAt-cons ntw-TAmpersand))
atomExprVarWF name eq (TAt        ∷ TLt        ∷ r) = just (RVar name , TAt ∷ TLt        ∷ r , pae-var eq (nqp-TAt-cons ntw-TLt))
atomExprVarWF name eq (TAt        ∷ TLe        ∷ r) = just (RVar name , TAt ∷ TLe        ∷ r , pae-var eq (nqp-TAt-cons ntw-TLe))
atomExprVarWF name eq (TAt        ∷ TGt        ∷ r) = just (RVar name , TAt ∷ TGt        ∷ r , pae-var eq (nqp-TAt-cons ntw-TGt))
atomExprVarWF name eq (TAt        ∷ TGe        ∷ r) = just (RVar name , TAt ∷ TGe        ∷ r , pae-var eq (nqp-TAt-cons ntw-TGe))
atomExprVarWF name eq (TAt        ∷ TEqEq      ∷ r) = just (RVar name , TAt ∷ TEqEq      ∷ r , pae-var eq (nqp-TAt-cons ntw-TEqEq))
atomExprVarWF name eq (TAt        ∷ TNeq       ∷ r) = just (RVar name , TAt ∷ TNeq       ∷ r , pae-var eq (nqp-TAt-cons ntw-TNeq))
atomExprVarWF name eq (TAt        ∷ TBang      ∷ r) = just (RVar name , TAt ∷ TBang      ∷ r , pae-var eq (nqp-TAt-cons ntw-TBang))
atomExprVarWF name eq (TAt        ∷ TNewline   ∷ r) = just (RVar name , TAt ∷ TNewline   ∷ r , pae-var eq (nqp-TAt-cons ntw-TNewline))
atomExprVarWF name eq (TAt        ∷ TEOF       ∷ r) = just (RVar name , TAt ∷ TEOF       ∷ r , pae-var eq (nqp-TAt-cons ntw-TEOF))
atomExprVarWF name eq (TPipe      ∷ r)  = just (RVar name , TPipe      ∷ r , pae-var eq nqp-TPipe)
atomExprVarWF name eq (TDot       ∷ r)  = just (RVar name , TDot       ∷ r , pae-var eq nqp-TDot)
atomExprVarWF name eq (TPlus      ∷ r)  = just (RVar name , TPlus      ∷ r , pae-var eq nqp-TPlus)
atomExprVarWF name eq (TMinus     ∷ r)  = just (RVar name , TMinus     ∷ r , pae-var eq nqp-TMinus)
atomExprVarWF name eq (TStar      ∷ r)  = just (RVar name , TStar      ∷ r , pae-var eq nqp-TStar)
atomExprVarWF name eq (TSlash     ∷ r)  = just (RVar name , TSlash     ∷ r , pae-var eq nqp-TSlash)
atomExprVarWF name eq (TPercent   ∷ r)  = just (RVar name , TPercent   ∷ r , pae-var eq nqp-TPercent)
atomExprVarWF name eq (TAmpersand ∷ r)  = just (RVar name , TAmpersand ∷ r , pae-var eq nqp-TAmpersand)
atomExprVarWF name eq (TLt        ∷ r)  = just (RVar name , TLt        ∷ r , pae-var eq nqp-TLt)
atomExprVarWF name eq (TLe        ∷ r)  = just (RVar name , TLe        ∷ r , pae-var eq nqp-TLe)
atomExprVarWF name eq (TGt        ∷ r)  = just (RVar name , TGt        ∷ r , pae-var eq nqp-TGt)
atomExprVarWF name eq (TGe        ∷ r)  = just (RVar name , TGe        ∷ r , pae-var eq nqp-TGe)
atomExprVarWF name eq (TEqEq      ∷ r)  = just (RVar name , TEqEq      ∷ r , pae-var eq nqp-TEqEq)
atomExprVarWF name eq (TNeq       ∷ r)  = just (RVar name , TNeq       ∷ r , pae-var eq nqp-TNeq)
atomExprVarWF name eq (TBang      ∷ r)  = just (RVar name , TBang      ∷ r , pae-var eq nqp-TBang)
atomExprVarWF name eq (TNewline   ∷ r)  = just (RVar name , TNewline   ∷ r , pae-var eq nqp-TNewline)
atomExprVarWF name eq (TEOF       ∷ r)  = just (RVar name , TEOF       ∷ r , pae-var eq nqp-TEOF)

-- | Word-case dispatch: "let" / "destruct" keywords or variable.
atomExprWordWF :
    (name : String) (rest : List Token)
  → Acc _<_ (length rest)
  → ParseAtomExprD (TWord name ∷ rest)
atomExprWordWF name rest a with wordEq-view name "let"
... | we-match refl = parseAtomExprWF-TLet rest a
... | we-nomatch _ with wordEq-view name "destruct"
...   | we-match refl = parseAtomExprWF-TDestruct rest a
...   | we-nomatch _ with reserved-view name
...     | rv-reserved _      = nothing
...     | rv-not-reserved eq = atomExprVarWF name eq rest

parseAtomExprWF [] _ = nothing
parseAtomExprWF (TLParen  ∷ rest) (acc rec) = parseAtomExprWF-TLParen rest (rec (s≤s ≤-refl))
parseAtomExprWF (TLambda  ∷ rest) (acc rec) = parseAtomExprWF-TLambda rest (rec (s≤s ≤-refl))
parseAtomExprWF (TWord name ∷ rest) (acc rec) = atomExprWordWF name rest (rec (s≤s ≤-refl))
parseAtomExprWF (TInt n    ∷ rest) _ = just (RInt n , rest , pae-int)
-- Plan 0.71 F3a: the AST has its node now, so the rejection F1 left here
-- becomes the real rule.
parseAtomExprWF (TFloat i f l ∷ rest) _ = just (RFloat i f l , rest , pae-float)
parseAtomExprWF (TString s ∷ rest) _ = just (RStringLit s , rest , pae-str)
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
parseAtomExprWF (TBang      ∷ _) _ = nothing
parseAtomExprWF (TNewline   ∷ _) _ = nothing
parseAtomExprWF (TEOF       ∷ _) _ = nothing

------------------------------------------------------------------------
-- Application tail: left-assoc juxtaposition.
--
-- parseAtomExprWF succeeds only on an atom-start token; otherwise
-- the tail no-ops. For the no-op case we need a `NotAtomStart toks`
-- witness. We supply it by case-splitting on the first token.
------------------------------------------------------------------------

parseAppTailWF f []               _ = just (f , [] , papp-done nas-[])
parseAppTailWF f (TLParen   ∷ rest) (acc rec)
  with parseAtomExprWF (TLParen ∷ rest) (acc rec)
... | nothing = nothing
... | just (arg , rest' , dA)
    with parseAppTailWF (RApp f arg) rest' (rec (ParsesAtomExpr-shrinks dA))
...   | nothing                   = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , papp-arg aao-TLParen dA dT)
parseAppTailWF f (TLambda   ∷ rest) (acc rec)
  with parseAtomExprWF (TLambda ∷ rest) (acc rec)
... | nothing = nothing
... | just (arg , rest' , dA)
    with parseAppTailWF (RApp f arg) rest' (rec (ParsesAtomExpr-shrinks dA))
...   | nothing                   = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , papp-arg aao-TLambda dA dT)
-- TWord: reserved words stop the tail; non-reserved proceed into
-- parseAtomExprWF. We case on isReserved WITH `in`-binding so the
-- NotAtomStart / AppArgOk witness can be built from the same dispatch.
parseAppTailWF f (TWord s ∷ rest) (acc rec) with reserved-view s
... | rv-reserved isR = just (f , TWord s ∷ rest , papp-done (nas-word-res isR))
... | rv-not-reserved notR
    with parseAtomExprWF (TWord s ∷ rest) (acc rec)
...   | nothing = nothing
...   | just (arg , rest' , dA)
      with parseAppTailWF (RApp f arg) rest' (rec (ParsesAtomExpr-shrinks dA))
...     | nothing                   = nothing
...     | just (body , rest'' , dT) = just (body , rest'' , papp-arg (aao-word notR) dA dT)
parseAppTailWF f (TInt n    ∷ rest) (acc rec)
  with parseAtomExprWF (TInt n ∷ rest) (acc rec)
... | nothing = nothing
... | just (arg , rest' , dA)
    with parseAppTailWF (RApp f arg) rest' (rec (ParsesAtomExpr-shrinks dA))
...   | nothing                   = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , papp-arg aao-TInt dA dT)
parseAppTailWF f (TString s ∷ rest) (acc rec)
  with parseAtomExprWF (TString s ∷ rest) (acc rec)
... | nothing = nothing
... | just (arg , rest' , dA)
    with parseAppTailWF (RApp f arg) rest' (rec (ParsesAtomExpr-shrinks dA))
...   | nothing                   = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , papp-arg aao-TString dA dT)
-- Non-atom-start tokens: tail no-ops.
parseAppTailWF f (TRParen   ∷ r) _ = just (f , TRParen   ∷ r , papp-done nas-TRParen)
parseAppTailWF f (TFloat i fr l ∷ rest) (acc rec)
  with parseAtomExprWF (TFloat i fr l ∷ rest) (acc rec)
... | nothing = nothing
... | just (arg , rest' , dA)
    with parseAppTailWF (RApp f arg) rest' (rec (ParsesAtomExpr-shrinks dA))
...   | nothing                   = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , papp-arg aao-TFloat dA dT)
parseAppTailWF f (TLBrace   ∷ r) _ = just (f , TLBrace   ∷ r , papp-done nas-TLBrace)
parseAppTailWF f (TRBrace   ∷ r) _ = just (f , TRBrace   ∷ r , papp-done nas-TRBrace)
parseAppTailWF f (TColon    ∷ r) _ = just (f , TColon    ∷ r , papp-done nas-TColon)
parseAppTailWF f (TEquals   ∷ r) _ = just (f , TEquals   ∷ r , papp-done nas-TEquals)
parseAppTailWF f (TArrow    ∷ r) _ = just (f , TArrow    ∷ r , papp-done nas-TArrow)
parseAppTailWF f (TCaret1   ∷ r) _ = just (f , TCaret1   ∷ r , papp-done nas-TCaret1)
parseAppTailWF f (TCaret0   ∷ r) _ = just (f , TCaret0   ∷ r , papp-done nas-TCaret0)
parseAppTailWF f (TCaretW   ∷ r) _ = just (f , TCaretW   ∷ r , papp-done nas-TCaretW)
parseAppTailWF f (TComma    ∷ r) _ = just (f , TComma    ∷ r , papp-done nas-TComma)
parseAppTailWF f (TSemicolon ∷ r) _ = just (f , TSemicolon ∷ r , papp-done nas-TSemicolon)
parseAppTailWF f (TAt       ∷ r) _ = just (f , TAt       ∷ r , papp-done nas-TAt)
parseAppTailWF f (TPipe     ∷ r) _ = just (f , TPipe     ∷ r , papp-done nas-TPipe)
parseAppTailWF f (TDot      ∷ r) _ = just (f , TDot      ∷ r , papp-done nas-TDot)
parseAppTailWF f (TPlus     ∷ r) _ = just (f , TPlus     ∷ r , papp-done nas-TPlus)
parseAppTailWF f (TMinus    ∷ r) _ = just (f , TMinus    ∷ r , papp-done nas-TMinus)
parseAppTailWF f (TStar     ∷ r) _ = just (f , TStar     ∷ r , papp-done nas-TStar)
parseAppTailWF f (TSlash    ∷ r) _ = just (f , TSlash    ∷ r , papp-done nas-TSlash)
parseAppTailWF f (TPercent  ∷ r) _ = just (f , TPercent  ∷ r , papp-done nas-TPercent)
parseAppTailWF f (TAmpersand ∷ r) _ = just (f , TAmpersand ∷ r , papp-done nas-TAmpersand)
parseAppTailWF f (TLt       ∷ r) _ = just (f , TLt       ∷ r , papp-done nas-TLt)
parseAppTailWF f (TLe       ∷ r) _ = just (f , TLe       ∷ r , papp-done nas-TLe)
parseAppTailWF f (TGt       ∷ r) _ = just (f , TGt       ∷ r , papp-done nas-TGt)
parseAppTailWF f (TGe       ∷ r) _ = just (f , TGe       ∷ r , papp-done nas-TGe)
parseAppTailWF f (TEqEq     ∷ r) _ = just (f , TEqEq     ∷ r , papp-done nas-TEqEq)
parseAppTailWF f (TNeq      ∷ r) _ = just (f , TNeq      ∷ r , papp-done nas-TNeq)
parseAppTailWF f (TBang     ∷ r) _ = just (f , TBang     ∷ r , papp-done nas-TBang)
parseAppTailWF f (TNewline  ∷ r) _ = just (f , TNewline  ∷ r , papp-done nas-TNewline)
parseAppTailWF f (TEOF      ∷ r) _ = just (f , TEOF      ∷ r , papp-done nas-TEOF)

parseAppWF toks (acc rec) with parseAtomExprWF toks (acc rec)
... | nothing                  = nothing
... | just (f , rest , dAE)
    with parseAppTailWF f rest (rec (ParsesAtomExpr-shrinks dAE))
...   | nothing                   = nothing
...   | just (body , rest' , dT)  = just (body , rest' , papp-mk dAE dT)

------------------------------------------------------------------------
-- Unary: negation prefix.
--
-- `- e` → pu-neg dE; anything else → pu-app dApp.
------------------------------------------------------------------------

parseUnaryWF (TMinus ∷ rest) (acc rec) with parseUnaryWF rest (rec (s≤s ≤-refl))
... | nothing                  = nothing
... | just (e , rest' , dU)   = just (RUnaryOp OpNeg e , rest' , pu-neg dU)
parseUnaryWF []               a with parseAppWF [] a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TWord s    ∷ r) a with parseAppWF (TWord s    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TInt n     ∷ r) a with parseAppWF (TInt n     ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TString s  ∷ r) a with parseAppWF (TString s  ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TLParen    ∷ r) a with parseAppWF (TLParen    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TRParen    ∷ r) a with parseAppWF (TRParen    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TFloat i f l ∷ r) a with parseAppWF (TFloat i f l ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TLBrace    ∷ r) a with parseAppWF (TLBrace    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TRBrace    ∷ r) a with parseAppWF (TRBrace    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TColon     ∷ r) a with parseAppWF (TColon     ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TEquals    ∷ r) a with parseAppWF (TEquals    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TArrow     ∷ r) a with parseAppWF (TArrow     ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TCaret1    ∷ r) a with parseAppWF (TCaret1    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TCaret0    ∷ r) a with parseAppWF (TCaret0    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TCaretW    ∷ r) a with parseAppWF (TCaretW    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TLambda    ∷ r) a with parseAppWF (TLambda    ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TComma     ∷ r) a with parseAppWF (TComma     ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TSemicolon ∷ r) a with parseAppWF (TSemicolon ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TAt        ∷ r) a with parseAppWF (TAt        ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TPipe      ∷ r) a with parseAppWF (TPipe      ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TDot       ∷ r) a with parseAppWF (TDot       ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TPlus      ∷ r) a with parseAppWF (TPlus      ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TStar      ∷ r) a with parseAppWF (TStar      ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TSlash     ∷ r) a with parseAppWF (TSlash     ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TPercent   ∷ r) a with parseAppWF (TPercent   ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TAmpersand ∷ r) a with parseAppWF (TAmpersand ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TLt        ∷ r) a with parseAppWF (TLt        ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TLe        ∷ r) a with parseAppWF (TLe        ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TGt        ∷ r) a with parseAppWF (TGt        ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TGe        ∷ r) a with parseAppWF (TGe        ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TEqEq      ∷ r) a with parseAppWF (TEqEq      ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TNeq       ∷ r) a with parseAppWF (TNeq       ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TBang      ∷ r) a with parseAppWF (TBang      ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TNewline   ∷ r) a with parseAppWF (TNewline   ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)
parseUnaryWF (TEOF       ∷ r) a with parseAppWF (TEOF       ∷ r) a
... | nothing                 = nothing
... | just (e , rest' , d)   = just (e , rest' , pu-app d)

------------------------------------------------------------------------
-- Multiplicative * / %.
------------------------------------------------------------------------

-- | `NotMul toks` for each non-mul first token.
notMul-[] : NotMul []
notMul-[] = tt

parseMulTailWF left (TStar ∷ rest) (acc rec) with parseUnaryWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , dU)
    with parseMulTailWF (RBinOp OpMul left right) rest'
          (rec (<-trans (ParsesUnary-shrinks dU) (s≤s ≤-refl)))
...   | nothing                    = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , pmt-star dU dT)
parseMulTailWF left (TSlash ∷ rest) (acc rec) with parseUnaryWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , dU)
    with parseMulTailWF (RBinOp OpDiv left right) rest'
          (rec (<-trans (ParsesUnary-shrinks dU) (s≤s ≤-refl)))
...   | nothing                    = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , pmt-slash dU dT)
parseMulTailWF left (TPercent ∷ rest) (acc rec) with parseUnaryWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , dU)
    with parseMulTailWF (RBinOp OpMod left right) rest'
          (rec (<-trans (ParsesUnary-shrinks dU) (s≤s ≤-refl)))
...   | nothing                    = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , pmt-percent dU dT)
parseMulTailWF left []               _ = just (left , [] , pmt-done notMul-[])
parseMulTailWF left (TWord s    ∷ r) _ = just (left , TWord s    ∷ r , pmt-done tt)
parseMulTailWF left (TInt n     ∷ r) _ = just (left , TInt n     ∷ r , pmt-done tt)
parseMulTailWF left (TFloat i f l ∷ r) _ = just (left , TFloat i f l ∷ r , pmt-done tt)
parseMulTailWF left (TString s  ∷ r) _ = just (left , TString s  ∷ r , pmt-done tt)
parseMulTailWF left (TLParen    ∷ r) _ = just (left , TLParen    ∷ r , pmt-done tt)
parseMulTailWF left (TRParen    ∷ r) _ = just (left , TRParen    ∷ r , pmt-done tt)
parseMulTailWF left (TLBrace    ∷ r) _ = just (left , TLBrace    ∷ r , pmt-done tt)
parseMulTailWF left (TRBrace    ∷ r) _ = just (left , TRBrace    ∷ r , pmt-done tt)
parseMulTailWF left (TColon     ∷ r) _ = just (left , TColon     ∷ r , pmt-done tt)
parseMulTailWF left (TEquals    ∷ r) _ = just (left , TEquals    ∷ r , pmt-done tt)
parseMulTailWF left (TArrow     ∷ r) _ = just (left , TArrow     ∷ r , pmt-done tt)
parseMulTailWF left (TCaret1    ∷ r) _ = just (left , TCaret1    ∷ r , pmt-done tt)
parseMulTailWF left (TCaret0    ∷ r) _ = just (left , TCaret0    ∷ r , pmt-done tt)
parseMulTailWF left (TCaretW    ∷ r) _ = just (left , TCaretW    ∷ r , pmt-done tt)
parseMulTailWF left (TLambda    ∷ r) _ = just (left , TLambda    ∷ r , pmt-done tt)
parseMulTailWF left (TComma     ∷ r) _ = just (left , TComma     ∷ r , pmt-done tt)
parseMulTailWF left (TSemicolon ∷ r) _ = just (left , TSemicolon ∷ r , pmt-done tt)
parseMulTailWF left (TAt        ∷ r) _ = just (left , TAt        ∷ r , pmt-done tt)
parseMulTailWF left (TPipe      ∷ r) _ = just (left , TPipe      ∷ r , pmt-done tt)
parseMulTailWF left (TDot       ∷ r) _ = just (left , TDot       ∷ r , pmt-done tt)
parseMulTailWF left (TPlus      ∷ r) _ = just (left , TPlus      ∷ r , pmt-done tt)
parseMulTailWF left (TMinus     ∷ r) _ = just (left , TMinus     ∷ r , pmt-done tt)
parseMulTailWF left (TAmpersand ∷ r) _ = just (left , TAmpersand ∷ r , pmt-done tt)
parseMulTailWF left (TLt        ∷ r) _ = just (left , TLt        ∷ r , pmt-done tt)
parseMulTailWF left (TLe        ∷ r) _ = just (left , TLe        ∷ r , pmt-done tt)
parseMulTailWF left (TGt        ∷ r) _ = just (left , TGt        ∷ r , pmt-done tt)
parseMulTailWF left (TGe        ∷ r) _ = just (left , TGe        ∷ r , pmt-done tt)
parseMulTailWF left (TEqEq      ∷ r) _ = just (left , TEqEq      ∷ r , pmt-done tt)
parseMulTailWF left (TNeq       ∷ r) _ = just (left , TNeq       ∷ r , pmt-done tt)
parseMulTailWF left (TBang      ∷ r) _ = just (left , TBang      ∷ r , pmt-done tt)
parseMulTailWF left (TNewline   ∷ r) _ = just (left , TNewline   ∷ r , pmt-done tt)
parseMulTailWF left (TEOF       ∷ r) _ = just (left , TEOF       ∷ r , pmt-done tt)

parseMulWF toks (acc rec) with parseUnaryWF toks (acc rec)
... | nothing                   = nothing
... | just (first , rest , dU)
    with parseMulTailWF first rest (rec (ParsesUnary-shrinks dU))
...   | nothing                    = nothing
...   | just (body , rest' , dT)   = just (body , rest' , pm-mk dU dT)

------------------------------------------------------------------------
-- Additive + -
------------------------------------------------------------------------

parseAddTailWF left (TPlus ∷ rest) (acc rec) with parseMulWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , dM)
    with parseAddTailWF (RBinOp OpAdd left right) rest'
          (rec (<-trans (ParsesMul-shrinks dM) (s≤s ≤-refl)))
...   | nothing                    = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , pat-plus dM dT)
parseAddTailWF left (TMinus ∷ rest) (acc rec) with parseMulWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , dM)
    with parseAddTailWF (RBinOp OpSub left right) rest'
          (rec (<-trans (ParsesMul-shrinks dM) (s≤s ≤-refl)))
...   | nothing                    = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , pat-minus dM dT)
parseAddTailWF left []               _ = just (left , [] , pat-done tt)
parseAddTailWF left (TWord s    ∷ r) _ = just (left , TWord s    ∷ r , pat-done tt)
parseAddTailWF left (TInt n     ∷ r) _ = just (left , TInt n     ∷ r , pat-done tt)
parseAddTailWF left (TFloat i f l ∷ r) _ = just (left , TFloat i f l ∷ r , pat-done tt)
parseAddTailWF left (TString s  ∷ r) _ = just (left , TString s  ∷ r , pat-done tt)
parseAddTailWF left (TLParen    ∷ r) _ = just (left , TLParen    ∷ r , pat-done tt)
parseAddTailWF left (TRParen    ∷ r) _ = just (left , TRParen    ∷ r , pat-done tt)
parseAddTailWF left (TLBrace    ∷ r) _ = just (left , TLBrace    ∷ r , pat-done tt)
parseAddTailWF left (TRBrace    ∷ r) _ = just (left , TRBrace    ∷ r , pat-done tt)
parseAddTailWF left (TColon     ∷ r) _ = just (left , TColon     ∷ r , pat-done tt)
parseAddTailWF left (TEquals    ∷ r) _ = just (left , TEquals    ∷ r , pat-done tt)
parseAddTailWF left (TArrow     ∷ r) _ = just (left , TArrow     ∷ r , pat-done tt)
parseAddTailWF left (TCaret1    ∷ r) _ = just (left , TCaret1    ∷ r , pat-done tt)
parseAddTailWF left (TCaret0    ∷ r) _ = just (left , TCaret0    ∷ r , pat-done tt)
parseAddTailWF left (TCaretW    ∷ r) _ = just (left , TCaretW    ∷ r , pat-done tt)
parseAddTailWF left (TLambda    ∷ r) _ = just (left , TLambda    ∷ r , pat-done tt)
parseAddTailWF left (TComma     ∷ r) _ = just (left , TComma     ∷ r , pat-done tt)
parseAddTailWF left (TSemicolon ∷ r) _ = just (left , TSemicolon ∷ r , pat-done tt)
parseAddTailWF left (TAt        ∷ r) _ = just (left , TAt        ∷ r , pat-done tt)
parseAddTailWF left (TPipe      ∷ r) _ = just (left , TPipe      ∷ r , pat-done tt)
parseAddTailWF left (TDot       ∷ r) _ = just (left , TDot       ∷ r , pat-done tt)
parseAddTailWF left (TStar      ∷ r) _ = just (left , TStar      ∷ r , pat-done tt)
parseAddTailWF left (TSlash     ∷ r) _ = just (left , TSlash     ∷ r , pat-done tt)
parseAddTailWF left (TPercent   ∷ r) _ = just (left , TPercent   ∷ r , pat-done tt)
parseAddTailWF left (TAmpersand ∷ r) _ = just (left , TAmpersand ∷ r , pat-done tt)
parseAddTailWF left (TLt        ∷ r) _ = just (left , TLt        ∷ r , pat-done tt)
parseAddTailWF left (TLe        ∷ r) _ = just (left , TLe        ∷ r , pat-done tt)
parseAddTailWF left (TGt        ∷ r) _ = just (left , TGt        ∷ r , pat-done tt)
parseAddTailWF left (TGe        ∷ r) _ = just (left , TGe        ∷ r , pat-done tt)
parseAddTailWF left (TEqEq      ∷ r) _ = just (left , TEqEq      ∷ r , pat-done tt)
parseAddTailWF left (TNeq       ∷ r) _ = just (left , TNeq       ∷ r , pat-done tt)
parseAddTailWF left (TBang      ∷ r) _ = just (left , TBang      ∷ r , pat-done tt)
parseAddTailWF left (TNewline   ∷ r) _ = just (left , TNewline   ∷ r , pat-done tt)
parseAddTailWF left (TEOF       ∷ r) _ = just (left , TEOF       ∷ r , pat-done tt)

parseAddWF toks (acc rec) with parseMulWF toks (acc rec)
... | nothing                   = nothing
... | just (first , rest , dM)
    with parseAddTailWF first rest (rec (ParsesMul-shrinks dM))
...   | nothing                    = nothing
...   | just (body , rest' , dT)   = just (body , rest' , pa-mk dM dT)

------------------------------------------------------------------------
-- Comparison: non-associative.
--
-- ParsesCmp only models the no-op case (`pcm-noop`). Compound
-- comparisons (x < y) aren't currently in the relation (ConcreteExpr
-- wraps them in parens so they reach atomExpr). We therefore DON'T
-- accept `a < b` at the cmp level; it reduces to parseAddWF.
------------------------------------------------------------------------

parseCmpWF toks (acc rec) with parseAddWF toks (acc rec)
... | nothing                   = nothing
... | just (left , []               , dA) = just (left , []               , pcm-noop dA tt)
... | just (left , TWord s    ∷ r , dA) = just (left , TWord s    ∷ r , pcm-noop dA tt)
... | just (left , TInt n     ∷ r , dA) = just (left , TInt n     ∷ r , pcm-noop dA tt)
... | just (left , TFloat i f l ∷ r , dA) = just (left , TFloat i f l ∷ r , pcm-noop dA tt)
... | just (left , TString s  ∷ r , dA) = just (left , TString s  ∷ r , pcm-noop dA tt)
... | just (left , TLParen    ∷ r , dA) = just (left , TLParen    ∷ r , pcm-noop dA tt)
... | just (left , TRParen    ∷ r , dA) = just (left , TRParen    ∷ r , pcm-noop dA tt)
... | just (left , TLBrace    ∷ r , dA) = just (left , TLBrace    ∷ r , pcm-noop dA tt)
... | just (left , TRBrace    ∷ r , dA) = just (left , TRBrace    ∷ r , pcm-noop dA tt)
... | just (left , TColon     ∷ r , dA) = just (left , TColon     ∷ r , pcm-noop dA tt)
... | just (left , TEquals    ∷ r , dA) = just (left , TEquals    ∷ r , pcm-noop dA tt)
... | just (left , TArrow     ∷ r , dA) = just (left , TArrow     ∷ r , pcm-noop dA tt)
... | just (left , TCaret1    ∷ r , dA) = just (left , TCaret1    ∷ r , pcm-noop dA tt)
... | just (left , TCaret0    ∷ r , dA) = just (left , TCaret0    ∷ r , pcm-noop dA tt)
... | just (left , TCaretW    ∷ r , dA) = just (left , TCaretW    ∷ r , pcm-noop dA tt)
... | just (left , TLambda    ∷ r , dA) = just (left , TLambda    ∷ r , pcm-noop dA tt)
... | just (left , TComma     ∷ r , dA) = just (left , TComma     ∷ r , pcm-noop dA tt)
... | just (left , TSemicolon ∷ r , dA) = just (left , TSemicolon ∷ r , pcm-noop dA tt)
... | just (left , TAt        ∷ r , dA) = just (left , TAt        ∷ r , pcm-noop dA tt)
... | just (left , TPipe      ∷ r , dA) = just (left , TPipe      ∷ r , pcm-noop dA tt)
... | just (left , TDot       ∷ r , dA) = just (left , TDot       ∷ r , pcm-noop dA tt)
... | just (left , TPlus      ∷ r , dA) = just (left , TPlus      ∷ r , pcm-noop dA tt)
... | just (left , TMinus     ∷ r , dA) = just (left , TMinus     ∷ r , pcm-noop dA tt)
... | just (left , TStar      ∷ r , dA) = just (left , TStar      ∷ r , pcm-noop dA tt)
... | just (left , TSlash     ∷ r , dA) = just (left , TSlash     ∷ r , pcm-noop dA tt)
... | just (left , TPercent   ∷ r , dA) = just (left , TPercent   ∷ r , pcm-noop dA tt)
... | just (left , TAmpersand ∷ r , dA) = just (left , TAmpersand ∷ r , pcm-noop dA tt)
... | just (left , TNewline   ∷ r , dA) = just (left , TNewline   ∷ r , pcm-noop dA tt)
... | just (left , TBang      ∷ r , dA) = just (left , TBang      ∷ r , pcm-noop dA tt)
... | just (left , TEOF       ∷ r , dA) = just (left , TEOF       ∷ r , pcm-noop dA tt)
-- Compound comparison: parse a second `add`, build `RBinOp`.
... | just (left , TLt   ∷ r , dL)
    with parseAddWF r (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL)))
...   | nothing = nothing
...   | just (right , rest' , dR) = just (RBinOp OpLt left right , rest' , pcm-lt dL dR)
parseCmpWF toks (acc rec) | just (left , TLe ∷ r , dL)
    with parseAddWF r (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL)))
...   | nothing = nothing
...   | just (right , rest' , dR) = just (RBinOp OpLe left right , rest' , pcm-le dL dR)
parseCmpWF toks (acc rec) | just (left , TGt ∷ r , dL)
    with parseAddWF r (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL)))
...   | nothing = nothing
...   | just (right , rest' , dR) = just (RBinOp OpGt left right , rest' , pcm-gt dL dR)
parseCmpWF toks (acc rec) | just (left , TGe ∷ r , dL)
    with parseAddWF r (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL)))
...   | nothing = nothing
...   | just (right , rest' , dR) = just (RBinOp OpGe left right , rest' , pcm-ge dL dR)
parseCmpWF toks (acc rec) | just (left , TEqEq ∷ r , dL)
    with parseAddWF r (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL)))
...   | nothing = nothing
...   | just (right , rest' , dR) = just (RBinOp OpEq left right , rest' , pcm-eq dL dR)
parseCmpWF toks (acc rec) | just (left , TNeq ∷ r , dL)
    with parseAddWF r (rec (<-trans (s≤s ≤-refl) (ParsesAdd-shrinks dL)))
...   | nothing = nothing
...   | just (right , rest' , dR) = just (RBinOp OpNe left right , rest' , pcm-ne dL dR)

------------------------------------------------------------------------
-- Composition: left-assoc f . g → compose f g
------------------------------------------------------------------------

parseCompTailWF left (TDot ∷ rest) (acc rec) with parseCmpWF rest (rec (s≤s ≤-refl))
... | nothing                       = nothing
... | just (right , rest' , dC)
    with parseCompTailWF (RApp (RApp (RVar "compose") left) right) rest'
          (rec (<-trans (ParsesCmp-shrinks dC) (s≤s ≤-refl)))
...   | nothing                    = nothing
...   | just (body , rest'' , dT) = just (body , rest'' , pct-dot dC dT)
parseCompTailWF left []               _ = just (left , [] , pct-done tt)
parseCompTailWF left (TWord s    ∷ r) _ = just (left , TWord s    ∷ r , pct-done tt)
parseCompTailWF left (TInt n     ∷ r) _ = just (left , TInt n     ∷ r , pct-done tt)
parseCompTailWF left (TFloat i f l ∷ r) _ = just (left , TFloat i f l ∷ r , pct-done tt)
parseCompTailWF left (TString s  ∷ r) _ = just (left , TString s  ∷ r , pct-done tt)
parseCompTailWF left (TLParen    ∷ r) _ = just (left , TLParen    ∷ r , pct-done tt)
parseCompTailWF left (TRParen    ∷ r) _ = just (left , TRParen    ∷ r , pct-done tt)
parseCompTailWF left (TLBrace    ∷ r) _ = just (left , TLBrace    ∷ r , pct-done tt)
parseCompTailWF left (TRBrace    ∷ r) _ = just (left , TRBrace    ∷ r , pct-done tt)
parseCompTailWF left (TColon     ∷ r) _ = just (left , TColon     ∷ r , pct-done tt)
parseCompTailWF left (TEquals    ∷ r) _ = just (left , TEquals    ∷ r , pct-done tt)
parseCompTailWF left (TArrow     ∷ r) _ = just (left , TArrow     ∷ r , pct-done tt)
parseCompTailWF left (TCaret1    ∷ r) _ = just (left , TCaret1    ∷ r , pct-done tt)
parseCompTailWF left (TCaret0    ∷ r) _ = just (left , TCaret0    ∷ r , pct-done tt)
parseCompTailWF left (TCaretW    ∷ r) _ = just (left , TCaretW    ∷ r , pct-done tt)
parseCompTailWF left (TLambda    ∷ r) _ = just (left , TLambda    ∷ r , pct-done tt)
parseCompTailWF left (TComma     ∷ r) _ = just (left , TComma     ∷ r , pct-done tt)
parseCompTailWF left (TSemicolon ∷ r) _ = just (left , TSemicolon ∷ r , pct-done tt)
parseCompTailWF left (TAt        ∷ r) _ = just (left , TAt        ∷ r , pct-done tt)
parseCompTailWF left (TPipe      ∷ r) _ = just (left , TPipe      ∷ r , pct-done tt)
parseCompTailWF left (TPlus      ∷ r) _ = just (left , TPlus      ∷ r , pct-done tt)
parseCompTailWF left (TMinus     ∷ r) _ = just (left , TMinus     ∷ r , pct-done tt)
parseCompTailWF left (TStar      ∷ r) _ = just (left , TStar      ∷ r , pct-done tt)
parseCompTailWF left (TSlash     ∷ r) _ = just (left , TSlash     ∷ r , pct-done tt)
parseCompTailWF left (TPercent   ∷ r) _ = just (left , TPercent   ∷ r , pct-done tt)
parseCompTailWF left (TAmpersand ∷ r) _ = just (left , TAmpersand ∷ r , pct-done tt)
parseCompTailWF left (TLt        ∷ r) _ = just (left , TLt        ∷ r , pct-done tt)
parseCompTailWF left (TLe        ∷ r) _ = just (left , TLe        ∷ r , pct-done tt)
parseCompTailWF left (TGt        ∷ r) _ = just (left , TGt        ∷ r , pct-done tt)
parseCompTailWF left (TGe        ∷ r) _ = just (left , TGe        ∷ r , pct-done tt)
parseCompTailWF left (TEqEq      ∷ r) _ = just (left , TEqEq      ∷ r , pct-done tt)
parseCompTailWF left (TNeq       ∷ r) _ = just (left , TNeq       ∷ r , pct-done tt)
parseCompTailWF left (TBang      ∷ r) _ = just (left , TBang      ∷ r , pct-done tt)
parseCompTailWF left (TNewline   ∷ r) _ = just (left , TNewline   ∷ r , pct-done tt)
parseCompTailWF left (TEOF       ∷ r) _ = just (left , TEOF       ∷ r , pct-done tt)

parseCompWF toks (acc rec) with parseCmpWF toks (acc rec)
... | nothing                   = nothing
... | just (first , rest , dC)
    with parseCompTailWF first rest (rec (ParsesCmp-shrinks dC))
...   | nothing                    = nothing
...   | just (body , rest' , dT)   = just (body , rest' , pc-mk dC dT)

------------------------------------------------------------------------
-- Top-level entry: parseExpr = parseComp (wrapped via pe-mk).
------------------------------------------------------------------------

parseExprWF toks a with parseCompWF toks a
... | nothing              = nothing
... | just (e , rest , d) = just (e , rest , pe-mk d)

------------------------------------------------------------------------
-- Plain-Parser wrapper for external callers.
------------------------------------------------------------------------

-- | Strip derivation from a Dec-valued parse result. Mirrors `stripType`
-- in `Once.Parser.Type`. Used by `Once.Grammar.ExprBridge` to state
-- parser success directly in terms of a raw `(e, rest)` pair, where
-- the derivation then follows from an inversion lemma.
stripExpr : (toks : List Token) → ParseExprD toks → Maybe (RawExpr × List Token)
stripExpr _ nothing = nothing
stripExpr _ (just (e , rest , _)) = just (e , rest)

parseExpr : Parser RawExpr
parseExpr toks = stripExpr toks (parseExprWF toks (<-wellFounded (length toks)))
