-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

-- | Separator class of the token AFTER a parameter name: `=` ends the params,
-- another word continues, anything else stops (the word is NOT a param).
-- CLASSIFIER-ROUTED (Plan 0.52 bridge-readiness): the 2-token lookahead becomes
-- `anyWordB` (consume the name) + this 1-token `sepClass` on the tail, so the
-- adequacy bridge steps the parser for a variable tail. Reuses `_≤_`/`anyWordB`.
data SepK : Set where skEq skWord skStop : SepK

sepClass : List Token → SepK
sepClass (TEquals ∷ _) = skEq
sepClass (TWord _ ∷ _)  = skWord
sepClass _              = skStop

-- | Bounded parse of function parameters before `=`. Always succeeds (empty list
-- for no params), weakly shrinking. WF on token-list length (the `skWord`
-- recursion is on the `anyWordB`-tail, not a structural sub-term).
parseParamsB : (toks : List Token) →
               Σ[ ps ∈ List String ] Σ[ rest ∈ List Token ] length rest ≤ length toks
parseParamsWF : (toks : List Token) → Acc _<_ (length toks) →
                Σ[ ps ∈ List String ] Σ[ rest ∈ List Token ] length rest ≤ length toks
pp-aw : (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
        (aw : ParseAtB {String} toks) →
        Σ[ ps ∈ List String ] Σ[ rest ∈ List Token ] length rest ≤ length toks
pp-sep : (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
         (name : String) (tail : List Token) (bnd : length tail < length toks) (sk : SepK) →
         Σ[ ps ∈ List String ] Σ[ rest ∈ List Token ] length rest ≤ length toks

parseParamsB toks = parseParamsWF toks (<-wellFounded (length toks))
parseParamsWF toks (acc rec) = pp-aw toks rec (anyWordB toks)

pp-aw toks rec nothing                  = [] , toks , ≤-refl
pp-aw toks rec (just (name , tail , bnd)) = pp-sep toks rec name tail bnd (sepClass tail)

pp-sep toks rec name tail bnd skEq   = name ∷ [] , tail , <⇒≤ bnd
pp-sep toks rec name tail bnd skWord =
  let (ps , rest' , bnd') = parseParamsWF tail (rec bnd)
  in  name ∷ ps , rest' , ≤-trans bnd' (<⇒≤ bnd)
pp-sep toks rec name tail bnd skStop = [] , toks , ≤-refl

parseParams : List Token → List String × List Token
parseParams toks = let (ps , rest , _) = parseParamsB toks in (ps , rest)
