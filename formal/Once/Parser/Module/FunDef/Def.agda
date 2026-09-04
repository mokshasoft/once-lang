-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.FunDef.Def
--
-- Combined function-definition parser: threads `parseParamsB` and
-- `parseFunBodyB` together. (D142: the `tryAllocB` stage is GONE — allocation
-- is mechanical, so there is no `@alloc` to parse.) Split out from `Body`
-- because the nested `with` chain produces a large case tree that
-- OOM-kills MAlonzo if kept co-located.
------------------------------------------------------------------------

module Once.Parser.Module.FunDef.Def where

open import Once.Parser.Module.Core
open import Once.Parser.Module.FunDef.Params
open import Once.Parser.Module.FunDef.Body

-- | Bounded parse of a function definition: `name [params] = body`.
-- The total shrink is (parseFunBody strict) × (parseParams weak), giving an
-- overall strict decrease. De-`with`'d through `pfd-params`/`pfd-body` for the
-- adequacy bridge.
parseFunDefB : String → (toks : List Token) → ParseAtB {Decl} toks
pfd-params : (name : String) (toks : List Token) →
             Σ[ ps ∈ List String ] Σ[ rest ∈ List Token ] length rest ≤ length toks →
             ParseAtB {Decl} toks
pfd-body : (name : String) (toks : List Token)
           (params : List String) (toks'' : List Token) (bnd'' : length toks'' ≤ length toks)
           (fb : ParseAtB {Decl} toks'') → ParseAtB {Decl} toks

parseFunDefB name toks = pfd-params name toks (parseParamsB toks)
pfd-params name toks (params , toks'' , paramsBnd) =
  pfd-body name toks params toks'' paramsBnd (parseFunBodyB name params toks'')
pfd-body name toks params toks'' bnd'' (just (d , rest , bodyBnd)) =
  just (d , rest , <-≤-trans bodyBnd bnd'')
pfd-body name toks params toks'' bnd'' nothing = nothing

parseFunDef : String → Parser Decl
parseFunDef name toks with parseFunDefB name toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
