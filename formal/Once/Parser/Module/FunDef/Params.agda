-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module.FunDef.Params
--
-- Function-parameter scanner (before `=`). Structurally recursive on
-- the token list; always succeeds and is weakly shrinking.
------------------------------------------------------------------------

module Once.Parser.Module.FunDef.Params where

open import Once.Parser.Module.Core

-- | Wrap body in lambdas for each parameter.
wrapLams : List String → RawExpr → RawExpr
wrapLams [] body = body
wrapLams (p ∷ ps) body = RLam p (wrapLams ps body)

-- | Bounded parse of function parameters before `=`. Always succeeds
-- (returns the empty list for no params) and is weakly shrinking: the
-- residual is ≤ the input. Structurally recursive on the token list,
-- with the `(TWord _ ∷ TWord _ ∷ _)` case recursing on a strictly
-- smaller tail.
parseParamsB : (toks : List Token) →
               Σ[ ps ∈ List String ] Σ[ rest ∈ List Token ]
                 length rest ≤ length toks
parseParamsB [] = [] , [] , ≤-refl
parseParamsB (TWord name ∷ TEquals ∷ rest) = name ∷ [] , TEquals ∷ rest , n≤1+n _
parseParamsB (TWord name ∷ TWord m ∷ rest)
  with parseParamsB (TWord m ∷ rest)
... | params , rest' , bnd =
      name ∷ params , rest' , ≤-trans bnd (n≤1+n _)
parseParamsB toks = [] , toks , ≤-refl

parseParams : List Token → List String × List Token
parseParams toks = let (ps , rest , _) = parseParamsB toks in (ps , rest)
