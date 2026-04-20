-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module.FunDef.Def
--
-- Combined function-definition parser: threads `tryAllocB`,
-- `parseParamsB`, and `parseFunBodyB` together. Split out from `Body`
-- because the nested `with` chain produces a large case tree that
-- OOM-kills MAlonzo if kept co-located.
------------------------------------------------------------------------

module Once.Parser.Module.FunDef.Def where

open import Once.Parser.Module.Core
open import Once.Parser.Module.Alloc
open import Once.Parser.Module.FunDef.Params
open import Once.Parser.Module.FunDef.Body

-- | Bounded parse of a function definition: `name [@alloc] [params] = body`.
-- The total shrink is (parseFunBody strict) × (parseParams weak) ×
-- (tryAlloc weak), giving an overall strict decrease.
parseFunDefB : String → (toks : List Token) → ParseAtB {Decl} toks
parseFunDefB name toks with tryAllocB toks
... | alloc , toks' , allocBnd with parseParamsB toks'
...   | params , toks'' , paramsBnd
      with parseFunBodyB name alloc params toks''
...     | just (d , rest , bodyBnd) =
          just (d , rest , <-≤-trans (<-≤-trans bodyBnd paramsBnd) allocBnd)
...     | nothing = nothing

parseFunDef : String → Parser Decl
parseFunDef name toks with parseFunDefB name toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
