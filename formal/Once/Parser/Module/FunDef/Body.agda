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

parseFunBodyB : String → List String →
                (toks : List Token) → ParseAtB {Decl} toks
pfb-eq : (name : String) (params : List String)
         (toks : List Token) → Bool → ParseAtB {Decl} toks
pfb-body : (name : String) (params : List String)
           (toks : List Token) → ParseAtB {RawExpr} (drop1 toks) → ParseAtB {Decl} toks

parseFunBodyB name params toks = pfb-eq name params toks (eqHead toks)

pfb-eq name params toks true  = pfb-body name params toks (parseExprB (drop1 toks))
pfb-eq name params toks false = nothing

pfb-body name params toks (just (body , rest' , bnd)) =
  just (DFunDef name (wrapLams params body) , rest' , <-≤-trans bnd (drop1-≤ toks))
pfb-body name params toks nothing = nothing

parseFunBody : String → List String → Parser Decl
parseFunBody name params toks with parseFunBodyB name params toks
... | just (d , rest , _) = just (d , rest)
... | nothing = nothing
