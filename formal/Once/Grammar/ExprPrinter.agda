-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.ExprPrinter
--
-- Plan 0.3 task #38: a pretty-printer from `GExpr` to a token stream,
-- and a `ConcreteExpr` predicate that carves out the subset of GExpr
-- values for which round-trip is well-defined.
--
-- Canonical form: always emit explicit parentheses around compound
-- expressions (binop applications, pairs, lambdas, annotations, etc.),
-- in the same spirit as `Once.Grammar.Printer.printGType`. This avoids
-- precedence-reconstruction ambiguity at the cost of verbose output.
--
-- Goal: `parseExpr (printGExpr g) ≡ just (gexprToRaw g, [])` for every
-- `g : GExpr` with a `ConcreteExpr g` witness. The round-trip theorem
-- itself lives in `Once.Grammar.ExprRoundtrip` (future work — see
-- that module for the status).
------------------------------------------------------------------------

module Once.Grammar.ExprPrinter where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)

import Once.Grammar as G
open G using (GExpr; GType; LowerIdent)
open import Once.Parser.Token
open import Once.Grammar.Printer using (printGType)

------------------------------------------------------------------------
-- Token-level helpers
------------------------------------------------------------------------

binOpToken : G.BinOp → Token
binOpToken G.OpAdd = TPlus
binOpToken G.OpSub = TMinus
binOpToken G.OpMul = TStar
binOpToken G.OpDiv = TSlash
binOpToken G.OpMod = TPercent
binOpToken G.OpLt  = TLt
binOpToken G.OpLe  = TLe
binOpToken G.OpGt  = TGt
binOpToken G.OpGe  = TGe
binOpToken G.OpEq  = TEqEq
binOpToken G.OpNe  = TNeq

------------------------------------------------------------------------
-- GExpr printer
------------------------------------------------------------------------

-- | Print a GExpr as a canonical token stream with explicit parens
-- around every compound expression. Leaves print as single tokens
-- (or a 3-token sequence for `EQualified`).
--
-- The parser's precedence chain (comp → cmp → add → mul → unary →
-- app → atom) is collapsed by always parenthesising, so the printed
-- form can be parsed back at the atom level in every compound case.
printGExpr : GExpr → List Token

printLetBindings : List (LowerIdent × GExpr) → List Token

-- Leaves
printGExpr G.EUnit       = TLParen ∷ TRParen ∷ []
-- Offset 0: the printer synthesises tokens from a `GExpr`, so there is no
-- source they came from. The roundtrip below is what pins that this is
-- consistent rather than arbitrary.
printGExpr (G.EInt n)    = TInt (+ n) 0 ∷ []
printGExpr (G.EString s) = TString s ∷ []
printGExpr (G.EVar name) = TWord name ∷ []
printGExpr (G.EQualified name alias) =
  TWord name ∷ TAt ∷ TWord alias ∷ []

-- Lambda: (\x -> body)
printGExpr (G.ELam x body) =
  TLParen ∷ TLambda ∷ TWord x ∷ TArrow ∷ printGExpr body ++ TRParen ∷ []

-- Application: (f x) — parenthesised to force atom-level parse.
printGExpr (G.EApp f x) =
  TLParen ∷ printGExpr f ++ printGExpr x ++ TRParen ∷ []

-- Pair: (a, b)
printGExpr (G.EPair a b) =
  TLParen ∷ printGExpr a ++ TComma ∷ printGExpr b ++ TRParen ∷ []

-- Annotation: (e : T)
printGExpr (G.EAnnot e t) =
  TLParen ∷ printGExpr e ++ TColon ∷ printGType t ++ TRParen ∷ []

-- Let
printGExpr (G.ELet [] body) =
  -- Degenerate: no bindings. Print body in parens for symmetry.
  TLParen ∷ printGExpr body ++ TRParen ∷ []
printGExpr (G.ELet (b ∷ bs) body) =
  TLParen ∷ TWord "let" ∷ printLetBindings (b ∷ bs)
    ++ TWord "in" ∷ printGExpr body ++ TRParen ∷ []

-- Destruct: (destruct e of { Left x -> e1 ; Right y -> e2 })
printGExpr (G.EDestruct scrut x l y r) =
  TLParen ∷ TWord "destruct" ∷ printGExpr scrut
    ++ TWord "of" ∷ TLBrace
    ∷ TWord "Left"  ∷ TWord x ∷ TArrow ∷ printGExpr l
    ++ TSemicolon ∷ TWord "Right" ∷ TWord y ∷ TArrow ∷ printGExpr r
    ++ TRBrace ∷ TRParen ∷ []

-- Binary operator: (a + b), (a * b), etc.
printGExpr (G.EBinOp op a b) =
  TLParen ∷ printGExpr a ++ binOpToken op ∷ printGExpr b ++ TRParen ∷ []

-- Unary negation: (-e)
printGExpr (G.EUnaryOp G.OpNeg e) =
  TLParen ∷ TMinus ∷ printGExpr e ++ TRParen ∷ []

-- Composition: (f . g)
printGExpr (G.ECompose f g) =
  TLParen ∷ printGExpr f ++ TDot ∷ printGExpr g ++ TRParen ∷ []

printLetBindings [] = []
printLetBindings ((n , e) ∷ []) =
  TWord n ∷ TEquals ∷ printGExpr e
printLetBindings ((n , e) ∷ more@(_ ∷ _)) =
  TWord n ∷ TEquals ∷ printGExpr e ++ TSemicolon ∷ printLetBindings more

------------------------------------------------------------------------
-- ConcreteExpr predicate
--
-- Carves out the subset of GExpr values that the round-trip theorem
-- is intended to cover. One constructor per GExpr shape.
--
-- Notes:
--  * `c-e-var`: requires `isReserved name ≡ false`. The parser's
--    `isReserved` check rejects keyword-shadowing identifiers as
--    variables; the round-trip domain must therefore exclude them.
--
--  * `c-e-let1` restricts to the single-binding form for the initial
--    theorem scope. Multi-binding cases have a different print shape
--    (semicolon-separated bindings) and require a distinct proof.
------------------------------------------------------------------------

open import Data.Bool using (Bool; false)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Re-export reserved-word check from the parser for the var case.
open import Once.Parser.Expr using (isReserved)

data ConcreteExpr : GExpr → Set where
  c-e-unit   : ConcreteExpr G.EUnit
  c-e-int    : ∀ {n} → ConcreteExpr (G.EInt n)
  c-e-string : ∀ {s} → ConcreteExpr (G.EString s)
  c-e-var    : ∀ {name} → isReserved name ≡ false
             → ConcreteExpr (G.EVar name)
  c-e-qual   : ∀ {name alias} → isReserved name ≡ false
             → ConcreteExpr (G.EQualified name alias)
  c-e-lam    : ∀ {x body} → ConcreteExpr body
             → ConcreteExpr (G.ELam x body)
  c-e-app    : ∀ {f x} → ConcreteExpr f → ConcreteExpr x
             → ConcreteExpr (G.EApp f x)
  c-e-pair   : ∀ {a b} → ConcreteExpr a → ConcreteExpr b
             → ConcreteExpr (G.EPair a b)
  c-e-annot  : ∀ {e t} → ConcreteExpr e
             → Once.Grammar.Printer.Concrete t
             → ConcreteExpr (G.EAnnot e t)
  c-e-binop  : ∀ {op a b} → ConcreteExpr a → ConcreteExpr b
             → ConcreteExpr (G.EBinOp op a b)
  c-e-unary  : ∀ {op e} → ConcreteExpr e
             → ConcreteExpr (G.EUnaryOp op e)
  c-e-comp   : ∀ {f g} → ConcreteExpr f → ConcreteExpr g
             → ConcreteExpr (G.ECompose f g)
  c-e-let1   : ∀ {x v body} → ConcreteExpr v → ConcreteExpr body
             → ConcreteExpr (G.ELet ((x , v) ∷ []) body)
  c-e-destr  : ∀ {scrut x l y r}
             → ConcreteExpr scrut → ConcreteExpr l → ConcreteExpr r
             → ConcreteExpr (G.EDestruct scrut x l y r)

------------------------------------------------------------------------
-- Smoke tests: the printer produces syntactically well-formed token
-- streams for canonical inputs.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (refl)

_ : printGExpr G.EUnit ≡ TLParen ∷ TRParen ∷ []
_ = refl

_ : printGExpr (G.EInt 42) ≡ TInt (+ 42) 0 ∷ []
_ = refl

_ : printGExpr (G.EVar "x") ≡ TWord "x" ∷ []
_ = refl

_ : printGExpr (G.EQualified "foo" "M") ≡ TWord "foo" ∷ TAt ∷ TWord "M" ∷ []
_ = refl
