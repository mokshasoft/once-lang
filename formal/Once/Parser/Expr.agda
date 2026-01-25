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
------------------------------------------------------------------------

module Once.Parser.Expr where

open import Data.List using (List; []; _∷_; foldr; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char)
open import Data.String using (String)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr; RVar; RQualified; RApp; RLam; RLet;
                                       RPair; RDestruct; RUnit; RInt;
                                       RStringLit; RAnnot; RBinOp; RUnaryOp;
                                       BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod;
                                       OpLt; OpLe; OpGt; OpGe; OpEq; OpNe;
                                       UnaryOp; OpNeg)
open import Once.Parser.Token
open import Once.Parser.Core
open import Once.Parser.Type using (parseType)

------------------------------------------------------------------------
-- Expression Parser (mutual recursion via TERMINATING)
------------------------------------------------------------------------

{-# TERMINATING #-}

-- | Full expression (lowest precedence)
parseExpr : Parser RawExpr

-- | Composition level (f . g)
parseComp : Parser RawExpr

-- | Comparison level (non-associative)
parseCmp : Parser RawExpr

-- | Additive level (left-assoc + -)
parseAdd : Parser RawExpr

-- | Multiplicative level (left-assoc * / %)
parseMul : Parser RawExpr

-- | Unary level (- prefix)
parseUnary : Parser RawExpr

-- | Application level (left-assoc juxtaposition)
parseApp : Parser RawExpr

-- | Atomic expression (highest precedence)
parseAtomExpr : Parser RawExpr

------------------------------------------------------------------------
-- Atom: variables, literals, parens, lambda, let, destruct
------------------------------------------------------------------------

-- | Parse lambda parameters and body: \x y z -> body
parseLamParams : Parser RawExpr
parseLamParams (TArrow ∷ rest) = parseExpr rest
parseLamParams (TWord name ∷ rest) with parseLamParams rest
... | just (body , rest') = just (RLam name body , rest')
... | nothing = nothing
parseLamParams _ = nothing

-- | Parse let bindings: let x = e1 in e2
-- Also: let x = e1 ; y = e2 in body
parseLet : Parser RawExpr

-- | Parse the continuation after 'let name = val': either 'in body' or '; more-lets in body'
parseLetCont : String → RawExpr → Parser RawExpr
parseLetCont name val (TWord "in" ∷ rest) with parseExpr rest
... | just (body , rest') = just (RLet name val body , rest')
... | nothing = nothing
parseLetCont name val (TSemicolon ∷ rest) with parseLet rest
... | just (body , rest') = just (RLet name val body , rest')
... | nothing = nothing
parseLetCont _ _ _ = nothing

parseLet toks with anyWord toks
... | nothing = nothing
... | just (name , rest) with (expect TEquals >>= λ _ → parseExpr) rest
...   | nothing = nothing
...   | just (val , rest') = parseLetCont name val rest'

-- | Parse the right branch after semicolon: Right y -> e2 }
parseRightBranch : RawExpr → String → RawExpr → Parser RawExpr
parseRightBranch scrut x left (TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ rest) with parseExpr rest
... | just (right , TRBrace ∷ final) = just (RDestruct scrut x left y right , final)
... | _ = nothing
parseRightBranch _ _ _ _ = nothing

-- | Parse destruct branches: Left x -> e1 ; Right y -> e2 }
parseDestructBranches : RawExpr → Parser RawExpr
parseDestructBranches scrut (TWord "Left" ∷ TWord x ∷ TArrow ∷ rest) with parseExpr rest
... | just (left , rest') = parseRightBranch scrut x left rest'
... | nothing = nothing
parseDestructBranches _ _ = nothing

-- | Parse destruct continuation after the scrutinee
parseDestructOf : RawExpr → Parser RawExpr
parseDestructOf scrut (TWord "of" ∷ TLBrace ∷ rest) = parseDestructBranches scrut rest
parseDestructOf _ _ = nothing

-- | Parse destruct: destruct e of { Left x -> e1 ; Right y -> e2 }
parseDestruct : Parser RawExpr
parseDestruct toks with parseExpr toks
... | nothing = nothing
... | just (scrut , rest) = parseDestructOf scrut rest

-- | Parse continuation after a tuple element: , more or )
parseParenTriple : RawExpr → RawExpr → Parser RawExpr
parseParenTriple e e2 (TRParen ∷ final) = just (RPair e e2 , final)
parseParenTriple e e2 (TComma ∷ rest) with parseExpr rest
... | just (e3 , TRParen ∷ final) = just (RPair (RPair e e2) e3 , final)
... | _ = nothing
parseParenTriple _ _ _ = nothing

-- | Parse continuation after first expr in parens: comma, colon, or close
parseParenCont : RawExpr → Parser RawExpr
parseParenCont e (TComma ∷ rest) with parseExpr rest
... | just (e2 , rest') = parseParenTriple e e2 rest'
... | nothing = nothing
parseParenCont e (TColon ∷ rest) with parseType rest
... | just (ty , TRParen ∷ final) = just (RAnnot e ty , final)
... | _ = nothing
parseParenCont e (TRParen ∷ final) = just (e , final)
parseParenCont _ _ = nothing

-- | Parse content inside parentheses (after opening paren)
parseParen : Parser RawExpr
parseParen toks with parseExpr toks
... | nothing = nothing
... | just (e , rest) = parseParenCont e rest

-- | Parse operator chars inside parens: (&), (.), (|>), etc.
-- Returns RVar with the operator name.
parseOpExpr : List Token → List Char → Maybe (RawExpr × List Token)
parseOpExpr (TDot ∷ rest) acc = parseOpExpr rest ('.' ∷ acc)
parseOpExpr (TPlus ∷ rest) acc = parseOpExpr rest ('+' ∷ acc)
parseOpExpr (TMinus ∷ rest) acc = parseOpExpr rest ('-' ∷ acc)
parseOpExpr (TStar ∷ rest) acc = parseOpExpr rest ('*' ∷ acc)
parseOpExpr (TSlash ∷ rest) acc = parseOpExpr rest ('/' ∷ acc)
parseOpExpr (TPercent ∷ rest) acc = parseOpExpr rest ('%' ∷ acc)
parseOpExpr (TLt ∷ rest) acc = parseOpExpr rest ('<' ∷ acc)
parseOpExpr (TGt ∷ rest) acc = parseOpExpr rest ('>' ∷ acc)
parseOpExpr (TPipe ∷ rest) acc = parseOpExpr rest ('|' ∷ acc)
parseOpExpr (TAmpersand ∷ rest) acc = parseOpExpr rest ('&' ∷ acc)
parseOpExpr (TAt ∷ rest) acc = parseOpExpr rest ('@' ∷ acc)
parseOpExpr (TRParen ∷ rest) [] = nothing  -- empty operator
parseOpExpr (TRParen ∷ rest) acc = just (RVar (Data.String.fromList (reverse acc)) , rest)
parseOpExpr _ _ = nothing

parseAtomExpr [] = nothing
-- Unit literal
parseAtomExpr (TLParen ∷ TRParen ∷ rest) = just (RUnit , rest)
-- Operator as expression: (&), (.), (|>), etc.
parseAtomExpr (TLParen ∷ rest) with parseOpExpr rest []
... | just result = just result
... | nothing = parseParen rest
-- Lambda
parseAtomExpr (TLambda ∷ rest) = parseLamParams rest
-- Let
parseAtomExpr (TWord "let" ∷ rest) = parseLet rest
-- Destruct
parseAtomExpr (TWord "destruct" ∷ rest) = parseDestruct rest
-- Integer literal
parseAtomExpr (TInt n ∷ rest) = just (RInt n , rest)
-- String literal
parseAtomExpr (TString s ∷ rest) = just (RStringLit s , rest)
-- Variable with optional qualified reference: name or name@alias
parseAtomExpr (TWord name ∷ TAt ∷ TWord alias ∷ rest) = just (RQualified name alias , rest)
parseAtomExpr (TWord name ∷ rest) = just (RVar name , rest)
-- Not an atom
parseAtomExpr (_ ∷ _) = nothing

------------------------------------------------------------------------
-- Application: left-associative juxtaposition
------------------------------------------------------------------------

-- | Greedily apply arguments
parseAppTail : RawExpr → Parser RawExpr
parseAppTail f toks with parseAtomExpr toks
... | just (arg , rest) = parseAppTail (RApp f arg) rest
... | nothing = just (f , toks)

parseApp toks with parseAtomExpr toks
... | nothing = nothing
... | just (f , rest) = parseAppTail f rest

------------------------------------------------------------------------
-- Unary: negation prefix
------------------------------------------------------------------------

parseUnary (TMinus ∷ rest) with parseUnary rest
... | just (e , rest') = just (RUnaryOp OpNeg e , rest')
... | nothing = nothing
parseUnary toks = parseApp toks

------------------------------------------------------------------------
-- Multiplicative: left-assoc * / %
------------------------------------------------------------------------

-- | Try to parse a multiplicative operator
tryMulOp : List Token → Maybe (BinOp × List Token)
tryMulOp (TStar ∷ rest) = just (OpMul , rest)
tryMulOp (TSlash ∷ rest) = just (OpDiv , rest)
tryMulOp (TPercent ∷ rest) = just (OpMod , rest)
tryMulOp _ = nothing

parseMulTail : RawExpr → Parser RawExpr
parseMulTail left toks with tryMulOp toks
parseMulTail left toks | just (op , rest) with parseUnary rest
parseMulTail left toks | just (op , rest) | just (right , rest') = parseMulTail (RBinOp op left right) rest'
parseMulTail left toks | just (op , rest) | nothing = nothing
parseMulTail left toks | nothing = just (left , toks)

parseMul toks with parseUnary toks
... | nothing = nothing
... | just (first , rest) = parseMulTail first rest

------------------------------------------------------------------------
-- Additive: left-assoc + -
------------------------------------------------------------------------

-- | Try to parse an additive operator
tryAddOp : List Token → Maybe (BinOp × List Token)
tryAddOp (TPlus ∷ rest) = just (OpAdd , rest)
tryAddOp (TMinus ∷ rest) = just (OpSub , rest)
tryAddOp _ = nothing

parseAddTail : RawExpr → Parser RawExpr
parseAddTail left toks with tryAddOp toks
parseAddTail left toks | just (op , rest) with parseMul rest
parseAddTail left toks | just (op , rest) | just (right , rest') = parseAddTail (RBinOp op left right) rest'
parseAddTail left toks | just (op , rest) | nothing = nothing
parseAddTail left toks | nothing = just (left , toks)

parseAdd toks with parseMul toks
... | nothing = nothing
... | just (first , rest) = parseAddTail first rest

------------------------------------------------------------------------
-- Comparison: non-associative
------------------------------------------------------------------------

parseCmpOp : List Token → Maybe (BinOp × List Token)
parseCmpOp (TLt ∷ rest) = just (OpLt , rest)
parseCmpOp (TLe ∷ rest) = just (OpLe , rest)
parseCmpOp (TGt ∷ rest) = just (OpGt , rest)
parseCmpOp (TGe ∷ rest) = just (OpGe , rest)
parseCmpOp (TEqEq ∷ rest) = just (OpEq , rest)
parseCmpOp (TNeq ∷ rest) = just (OpNe , rest)
parseCmpOp _ = nothing

parseCmp toks with parseAdd toks
... | nothing = nothing
... | just (left , rest) with parseCmpOp rest
...   | nothing = just (left , rest)
...   | just (op , rest') with parseAdd rest'
...     | just (right , rest'') = just (RBinOp op left right , rest'')
...     | nothing = nothing

------------------------------------------------------------------------
-- Composition: left-assoc f . g → compose f g
------------------------------------------------------------------------

-- | Try to parse a composition operator
tryCompOp : List Token → Maybe (List Token)
tryCompOp (TDot ∷ rest) = just rest
tryCompOp _ = nothing

parseCompTail : RawExpr → Parser RawExpr
parseCompTail left toks with tryCompOp toks
parseCompTail left toks | just rest with parseCmp rest
parseCompTail left toks | just rest | just (right , rest') =
      parseCompTail (RApp (RApp (RVar "compose") left) right) rest'
parseCompTail left toks | just rest | nothing = nothing
parseCompTail left toks | nothing = just (left , toks)

parseComp toks with parseCmp toks
... | nothing = nothing
... | just (first , rest) = parseCompTail first rest

------------------------------------------------------------------------
-- Full Expression (with type annotation)
------------------------------------------------------------------------

parseExpr toks = parseComp toks
