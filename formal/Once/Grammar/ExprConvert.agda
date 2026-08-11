-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.ExprConvert
--
-- Plan 0.3 task #38: conversion from `GExpr` (with a `ConcreteExpr`
-- witness) to `RawExpr`, the parser's output type.
--
-- Parallel to `Once.Grammar.Convert.gtypeToType` / `toType`, but for
-- expressions. Only defined on `ConcreteExpr` witnesses because the
-- predicate carries the reserved-word side condition on EVar/EQualified
-- that the parser enforces, and because concrete types are required
-- for EAnnot.
--
-- Key design choice: `ECompose f g` converts to
-- `RApp (RApp (RVar "compose") (gexprToRaw f)) (gexprToRaw g)`,
-- matching the parser's desugaring of `f . g` in `parseCompTailWF`.
------------------------------------------------------------------------

module Once.Grammar.ExprConvert where

open import Data.List using (List; []; _∷_)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)

import Once.Grammar as G
open G using (GExpr)
open import Once.TypeCheck.Raw
open import Once.Type using (Type)
open import Once.Grammar.Printer using (Concrete)
open import Once.Grammar.Convert using (gtypeToType)
open import Once.Grammar.ExprPrinter using
  (ConcreteExpr; c-e-unit; c-e-int; c-e-string; c-e-var; c-e-qual;
   c-e-lam; c-e-app; c-e-pair; c-e-annot; c-e-binop; c-e-unary; c-e-comp;
   c-e-let1; c-e-destr)

------------------------------------------------------------------------
-- Binary / unary operator conversion
------------------------------------------------------------------------

gBinOpToRaw : G.BinOp → BinOp
gBinOpToRaw G.OpAdd = OpAdd
gBinOpToRaw G.OpSub = OpSub
gBinOpToRaw G.OpMul = OpMul
gBinOpToRaw G.OpDiv = OpDiv
gBinOpToRaw G.OpMod = OpMod
gBinOpToRaw G.OpLt  = OpLt
gBinOpToRaw G.OpLe  = OpLe
gBinOpToRaw G.OpGt  = OpGt
gBinOpToRaw G.OpGe  = OpGe
gBinOpToRaw G.OpEq  = OpEq
gBinOpToRaw G.OpNe  = OpNe

gUnaryOpToRaw : G.UnaryOp → UnaryOp
gUnaryOpToRaw G.OpNeg = OpNeg

------------------------------------------------------------------------
-- Type conversion: trust the `Concrete` predicate to guarantee
-- `gtypeToType t` returns `just _`. We extract that internal Type via
-- a structural witness-based conversion.
------------------------------------------------------------------------

open import Once.Grammar.Printer using
  (c-unit; c-void; c-int; c-float; c-buffer; c-string;
   c-prod; c-sum; c-fun; c-eff)
open import Once.Grammar.ParserRelation using (toType)

------------------------------------------------------------------------
-- Main converter
------------------------------------------------------------------------

-- | Convert a ConcreteExpr witness to a RawExpr.
--
-- Direct structural recursion. Used by the round-trip theorem to
-- express the expected parser output.
gexprToRaw : ∀ {g : GExpr} → ConcreteExpr g → RawExpr
gexprToRaw c-e-unit                   = RUnit
gexprToRaw (c-e-int {n})              = RInt (+ n)
gexprToRaw (c-e-string {s})           = RStringLit s
gexprToRaw (c-e-var {name} _)         = RVar name
gexprToRaw (c-e-qual {name} {alias} _) = RQualified name alias
gexprToRaw (c-e-lam {x} c)            = RLam x (gexprToRaw c)
gexprToRaw (c-e-app cF cX)            = RApp (gexprToRaw cF) (gexprToRaw cX)
gexprToRaw (c-e-pair cA cB)           = RPair (gexprToRaw cA) (gexprToRaw cB)
gexprToRaw (c-e-annot cE cT)          = RAnnot (gexprToRaw cE) (toType cT)
gexprToRaw (c-e-binop {op} cA cB)     =
  RBinOp (gBinOpToRaw op) (gexprToRaw cA) (gexprToRaw cB)
gexprToRaw (c-e-unary {op} cE)        = RUnaryOp (gUnaryOpToRaw op) (gexprToRaw cE)
gexprToRaw (c-e-comp cF cG)           =
  -- f . g desugars to compose f g.
  RApp (RApp (RVar "compose") (gexprToRaw cF)) (gexprToRaw cG)
gexprToRaw (c-e-let1 {x} cV cBody)    =
  RLet x (gexprToRaw cV) (gexprToRaw cBody)
gexprToRaw (c-e-destr {x = x} {y = y} cS cL cR) =
  RDestruct (gexprToRaw cS) x (gexprToRaw cL) y (gexprToRaw cR)
