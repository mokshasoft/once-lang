-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module.FunDef.Body
--
-- Function body parser (after `=`). Isolated from `parseFunDefB` so
-- MAlonzo extraction stays within memory budget.
------------------------------------------------------------------------

module Once.Parser.Module.FunDef.Body where

open import Once.Parser.Module.Core
open import Once.Parser.Module.Alloc
open import Once.Parser.Module.FunDef.Params

-- | Bounded parse of function body after `=`: consumes `=` plus a
-- non-empty expression, so the residual is strictly shorter.
parseFunBodyB : String → Maybe AllocStrategy → List String →
                (toks : List Token) → ParseAtB {Decl} toks
parseFunBodyB name alloc params (TEquals ∷ rest) with parseExprB rest
... | just (body , rest' , bnd) =
      just (DFunDef name alloc (wrapLams params body) , rest' ,
            <-trans bnd (s≤s ≤-refl))
... | nothing = nothing
parseFunBodyB _ _ _ _ = nothing

parseFunBody : String → Maybe AllocStrategy → List String → Parser Decl
parseFunBody name alloc params toks with parseFunBodyB name alloc params toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
