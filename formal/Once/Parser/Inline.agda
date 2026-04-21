-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Inline
--
-- Inline user-defined function references at the RawExpr level.
-- Replaces RVar "name" with the body when "name" is a previously
-- defined function (not a generator/builtin).
------------------------------------------------------------------------

module Once.Parser.Inline where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no; ¬_)

open import Once.TypeCheck.Raw using (RawExpr; RVar; RQualified; RApp; RLam; RLet;
                                       RPair; RDestruct; RUnit; RInt;
                                       RStringLit; RAnnot; RBinOp; RUnaryOp)

------------------------------------------------------------------------
-- Definition Environment
------------------------------------------------------------------------

-- | A list of (name, body) pairs for previously-defined functions
Defs : Set
Defs = List (String × RawExpr)

-- | Look up a name in the definitions
lookupDef : String → Defs → Maybe RawExpr
lookupDef _ [] = nothing
lookupDef name ((n , body) ∷ rest) with name ≟ n
... | yes _ = just body
... | no _  = lookupDef name rest

-- | Remove a name from the definitions (for shadowing)
removeDef : String → Defs → Defs
removeDef _ [] = []
removeDef name ((n , body) ∷ rest) with name ≟ n
... | yes _ = removeDef name rest
... | no _  = (n , body) ∷ removeDef name rest

------------------------------------------------------------------------
-- Inline References
------------------------------------------------------------------------

-- | Inline all references to user-defined functions.
-- Uses fuel parameter for termination (inlining may expand definitions
-- that contain further references).
inlineReferences : ℕ → Defs → RawExpr → RawExpr
inlineReferences zero _ expr = expr  -- fuel exhausted
inlineReferences (suc fuel) defs (RVar name) with lookupDef name defs
... | just body = inlineReferences fuel defs body  -- substitute and continue
... | nothing   = RVar name  -- generator or unbound, leave as-is
-- Qualified names refer to imported functions, don't inline them
inlineReferences _ _ (RQualified name alias) = RQualified name alias
inlineReferences (suc fuel) defs (RApp f x) =
  RApp (inlineReferences (suc fuel) defs f)
       (inlineReferences (suc fuel) defs x)
inlineReferences (suc fuel) defs (RLam x body) =
  RLam x (inlineReferences (suc fuel) (removeDef x defs) body)
inlineReferences (suc fuel) defs (RLet x e₁ e₂) =
  RLet x (inlineReferences (suc fuel) defs e₁)
         (inlineReferences (suc fuel) (removeDef x defs) e₂)
inlineReferences (suc fuel) defs (RPair a b) =
  RPair (inlineReferences (suc fuel) defs a)
        (inlineReferences (suc fuel) defs b)
inlineReferences (suc fuel) defs (RDestruct s x l y r) =
  RDestruct (inlineReferences (suc fuel) defs s)
            x (inlineReferences (suc fuel) (removeDef x defs) l)
            y (inlineReferences (suc fuel) (removeDef y defs) r)
inlineReferences _ _ RUnit = RUnit
inlineReferences _ _ (RInt n) = RInt n
inlineReferences _ _ (RStringLit s) = RStringLit s
inlineReferences (suc fuel) defs (RAnnot e ty) =
  RAnnot (inlineReferences (suc fuel) defs e) ty
inlineReferences (suc fuel) defs (RBinOp op a b) =
  RBinOp op (inlineReferences (suc fuel) defs a)
            (inlineReferences (suc fuel) defs b)
inlineReferences (suc fuel) defs (RUnaryOp op e) =
  RUnaryOp op (inlineReferences (suc fuel) defs e)

------------------------------------------------------------------------
-- Applied-builtin desugaring
------------------------------------------------------------------------

-- | Fresh variable name for the `pair` desugaring. Contains `$`,
-- which is not a legal identifier character in user source (see
-- `Once.Parser.Lexer.isIdentStart` / `isIdentContinue`), so this
-- name is guaranteed not to clash with any user-declared variable.
pairDesugarVar : String
pairDesugarVar = "$pair_x"

-- | Desugar applied-pair forms to explicit lambda+pair shapes.
--
-- The 2-arg curried application `pair f g` is rewritten to
-- `λ x → (f x, g x)` where `x = pairDesugarVar`. This lets the
-- existing bidirectional typechecker handle `pair`'s specialization
-- against the call site's expected type via the RLam + RPair + RApp
-- paths, without a dedicated applied-form classifier and without
-- corresponding judgment / soundness / completeness extensions.
--
-- Semantics: `pair f g ≡ λ x → (f x, g x)` is the universal property
-- of the categorical pair morphism in a CCC — the two forms are
-- beta-equivalent by construction. The optimizer's beta/eta laws
-- fuse the lambda+pair+app form back into `IR.pair` so there is no
-- runtime cost versus a direct classifier route.
--
-- Plan 0.6 Phase C.2.
expandPairs : RawExpr → RawExpr
expandPairs (RApp (RApp (RVar "pair") f) g) =
  RLam pairDesugarVar (RPair (RApp (expandPairs f) (RVar pairDesugarVar))
                              (RApp (expandPairs g) (RVar pairDesugarVar)))
expandPairs (RVar name) = RVar name
expandPairs (RQualified name alias) = RQualified name alias
expandPairs (RApp f x) = RApp (expandPairs f) (expandPairs x)
expandPairs (RLam x body) = RLam x (expandPairs body)
expandPairs (RLet x e₁ e₂) = RLet x (expandPairs e₁) (expandPairs e₂)
expandPairs (RPair a b) = RPair (expandPairs a) (expandPairs b)
expandPairs (RDestruct s x l y r) =
  RDestruct (expandPairs s) x (expandPairs l) y (expandPairs r)
expandPairs RUnit = RUnit
expandPairs (RInt n) = RInt n
expandPairs (RStringLit s) = RStringLit s
expandPairs (RAnnot e ty) = RAnnot (expandPairs e) ty
expandPairs (RBinOp op a b) = RBinOp op (expandPairs a) (expandPairs b)
expandPairs (RUnaryOp op e) = RUnaryOp op (expandPairs e)