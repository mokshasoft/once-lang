-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Grammar.FunDef — the RELATIONS for a function definition
-- `[@alloc] name param* = expr`, and nothing else (Plan 0.84).
--
-- Reachable from `correct` via `ParsesDecl`, so a spec reviewer must read it.
-- `sound-fundef`/`complete-fundef` and the WF param-scanner proofs stay in
-- `Once.Grammar.FunDefBridge`.
--
-- `ParsesExpr` is NOT moved: `Once.Parser.ExprRelation` is already proof-free
-- and lives in the parser hierarchy by design (plan 0.84 §3a).
------------------------------------------------------------------------

module Once.Spec.Grammar.FunDef where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Parser.Token
open import Once.Parser.Module.Core using (Decl; DFunDef; wordHead)
open import Once.Parser.Module.FunDef.Params using (skEq; skWord; skStop; sepClass; wrapLams)
open import Once.Parser.Module.FunDef.Body using (eqHead; drop1)
open import Once.Parser.ExprRelation using (ParsesExpr)

------------------------------------------------------------------------
-- Parameter list, terminated by `=`.
------------------------------------------------------------------------

data ParsesParams : List Token → List String → List Token → Set where
  pp-eq     : ∀ {name tail} → sepClass tail ≡ skEq →
              ParsesParams (TWord name ∷ tail) (name ∷ []) tail
  pp-cons   : ∀ {name tail ps rest'} → sepClass tail ≡ skWord → ParsesParams tail ps rest' →
              ParsesParams (TWord name ∷ tail) (name ∷ ps) rest'
  pp-stop   : ∀ {name tail} → sepClass tail ≡ skStop →
              ParsesParams (TWord name ∷ tail) [] (TWord name ∷ tail)
  pp-noword : ∀ {toks} → wordHead toks ≡ false → ParsesParams toks [] toks

------------------------------------------------------------------------
-- The body, `= expr`, with the parameters wrapped back into lambdas.
------------------------------------------------------------------------

data ParsesFunBody (name : String) (params : List String)
                   : List Token → Decl → List Token → Set where
  pfb-mk : ∀ {toks body rest'} → eqHead toks ≡ true → ParsesExpr (drop1 toks) body rest' →
           ParsesFunBody name params toks (DFunDef name (wrapLams params body)) rest'

------------------------------------------------------------------------
-- Function definition = params then body. (D142: no alloc stage.)
------------------------------------------------------------------------

data ParsesFunDef (name : String) : List Token → Decl → List Token → Set where
  pfd-mk : ∀ {toks params toks'' d rest} →
           ParsesParams toks params toks'' →
           ParsesFunBody name params toks'' d rest →
           ParsesFunDef name toks d rest
