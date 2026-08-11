-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.FunDef.Body
--
-- Function body parser (after `=`). Isolated from `parseFunDefB` so
-- MAlonzo extraction stays within memory budget.
------------------------------------------------------------------------

module Once.Parser.Module.FunDef.Body where

open import Data.Bool using (Bool; true; false)
open import Once.Parser.Module.Core
open import Once.Parser.Module.Alloc
open import Once.Parser.Module.FunDef.Params

-- | Bounded parse of function body after `=`: consumes `=` plus a non-empty
-- expression, so the residual is strictly shorter. CLASSIFIER-ROUTED (Plan 0.52
-- bridge-readiness): the `TEquals∷` dispatch goes through `eqHead` + `drop1`, so
-- the adequacy bridge steps it for a variable tail.
eqHead : List Token → Bool
eqHead (TEquals ∷ _) = true
eqHead _             = false

drop1 : List Token → List Token
drop1 []       = []
drop1 (_ ∷ xs) = xs

drop1-≤ : (xs : List Token) → length (drop1 xs) ≤ length xs
drop1-≤ []       = ≤-refl
drop1-≤ (_ ∷ xs) = m≤n⇒m≤1+n ≤-refl

parseFunBodyB : String → Maybe AllocStrategy → List String →
                (toks : List Token) → ParseAtB {Decl} toks
pfb-eq : (name : String) (alloc : Maybe AllocStrategy) (params : List String)
         (toks : List Token) → Bool → ParseAtB {Decl} toks
pfb-body : (name : String) (alloc : Maybe AllocStrategy) (params : List String)
           (toks : List Token) → ParseAtB {RawExpr} (drop1 toks) → ParseAtB {Decl} toks

parseFunBodyB name alloc params toks = pfb-eq name alloc params toks (eqHead toks)

pfb-eq name alloc params toks true  = pfb-body name alloc params toks (parseExprB (drop1 toks))
pfb-eq name alloc params toks false = nothing

pfb-body name alloc params toks (just (body , rest' , bnd)) =
  just (DFunDef name alloc (wrapLams params body) , rest' , <-≤-trans bnd (drop1-≤ toks))
pfb-body name alloc params toks nothing = nothing

parseFunBody : String → Maybe AllocStrategy → List String → Parser Decl
parseFunBody name alloc params toks with parseFunBodyB name alloc params toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
