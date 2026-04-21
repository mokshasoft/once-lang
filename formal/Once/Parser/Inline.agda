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

-- | Fresh variable names for builtin desugarings. `$` is illegal in
-- user identifier syntax (see `Once.Parser.Lexer.isIdentStart` /
-- `isIdentContinue`), so any name containing `$` cannot clash with a
-- user-declared variable.
pairDesugarVar : String
pairDesugarVar = "$pair_x"

composeDesugarVar : String
composeDesugarVar = "$compose_x"

-- | Desugar applied-builtin forms to explicit lambda / pair / app
-- shapes, so the existing bidirectional typechecker (RLam + RPair +
-- RApp paths) handles their specialization against the call site's
-- expected type — no dedicated applied-form classifier, no judgment
-- rule, no Soundness / Completeness / ErrorProofs delta.
--
-- Each rewrite is the *universal property* of the corresponding
-- categorical morphism; the original and desugared forms are
-- beta-equivalent by construction, and the optimizer's beta/eta
-- laws fuse the lambda form back into the direct IR combinator so
-- runtime output matches the classifier route.
--
-- Covered (plan 0.6 Phase C.2 + C.3):
--   * `pair f g       ↦  λ x → (f x, g x)`        (2-arg form)
--   * `pair f g arg   ↦  (f arg, g arg)`          (beta-reduced)
--   * `compose f g    ↦  λ x → f (g x)`           (2-arg form)
--   * `compose f g x  ↦  f (g x)`                 (beta-reduced)
--
-- Beta-reduced clauses come first so they win pattern matching when
-- the full application is visible; the 2-arg lambda form is the
-- fallback for cases where the call site is partially applied or
-- passes the NT as a higher-order argument.
expandBuiltins : RawExpr → RawExpr
expandBuiltins (RApp (RApp (RApp (RVar "pair") f) g) arg) =
  RPair (RApp (expandBuiltins f) (expandBuiltins arg))
        (RApp (expandBuiltins g) (expandBuiltins arg))
expandBuiltins (RApp (RApp (RApp (RVar "compose") f) g) arg) =
  RApp (expandBuiltins f) (RApp (expandBuiltins g) (expandBuiltins arg))
expandBuiltins (RApp (RApp (RVar "pair") f) g) =
  RLam pairDesugarVar (RPair (RApp (expandBuiltins f) (RVar pairDesugarVar))
                              (RApp (expandBuiltins g) (RVar pairDesugarVar)))
expandBuiltins (RApp (RApp (RVar "compose") f) g) =
  RLam composeDesugarVar
    (RApp (expandBuiltins f)
          (RApp (expandBuiltins g) (RVar composeDesugarVar)))
expandBuiltins (RVar name) = RVar name
expandBuiltins (RQualified name alias) = RQualified name alias
expandBuiltins (RApp f x) = RApp (expandBuiltins f) (expandBuiltins x)
expandBuiltins (RLam x body) = RLam x (expandBuiltins body)
expandBuiltins (RLet x e₁ e₂) = RLet x (expandBuiltins e₁) (expandBuiltins e₂)
expandBuiltins (RPair a b) = RPair (expandBuiltins a) (expandBuiltins b)
expandBuiltins (RDestruct s x l y r) =
  RDestruct (expandBuiltins s) x (expandBuiltins l) y (expandBuiltins r)
expandBuiltins RUnit = RUnit
expandBuiltins (RInt n) = RInt n
expandBuiltins (RStringLit s) = RStringLit s
expandBuiltins (RAnnot e ty) = RAnnot (expandBuiltins e) ty
expandBuiltins (RBinOp op a b) = RBinOp op (expandBuiltins a) (expandBuiltins b)
expandBuiltins (RUnaryOp op e) = RUnaryOp op (expandBuiltins e)

-- | Back-compat alias. Code calling `expandPairs` gets both `pair`
-- and `compose` desugaring now.
expandPairs : RawExpr → RawExpr
expandPairs = expandBuiltins

------------------------------------------------------------------------
-- Beta reduction pass
------------------------------------------------------------------------
--
-- `expandBuiltins` introduces lambdas for partially-applied NTs
-- (`pair f g`, `compose f g`). When such a lambda then appears as the
-- head of an outer RApp (e.g. `compose f (pair h k)` expands such
-- that the pair-lambda is applied to the compose-lambda's bound
-- variable), the existing typechecker cannot infer the lambda's
-- type — "Lambda without type annotation not supported in inference
-- mode." Beta-reducing `RApp (RLam x body) arg ↦ body[arg/x]` at the
-- RawExpr level eliminates the applied lambda and exposes the
-- underlying structure to the classifier.
--
-- The desugar-fresh names (`$pair_x`, `$compose_x`) are guaranteed
-- capture-free vs. user code (see identifier-char rules); capture
-- between desugar-fresh names is avoided by subst's shadowing check.

-- | Substitute `arg` for free occurrences of variable `x` in `body`.
-- Honours shadowing: a binder introducing the same name stops the
-- substitution inside its body.
subst : String → RawExpr → RawExpr → RawExpr
subst x arg (RVar y) with x ≟ y
... | yes _ = arg
... | no  _ = RVar y
subst _ _ (RQualified name alias) = RQualified name alias
subst x arg (RApp f y) = RApp (subst x arg f) (subst x arg y)
subst x arg (RLam y body) with x ≟ y
... | yes _ = RLam y body
... | no  _ = RLam y (subst x arg body)
subst x arg (RLet y e₁ e₂) with x ≟ y
... | yes _ = RLet y (subst x arg e₁) e₂
... | no  _ = RLet y (subst x arg e₁) (subst x arg e₂)
subst x arg (RPair a b) = RPair (subst x arg a) (subst x arg b)
subst x arg (RDestruct s yl l yr r) with x ≟ yl | x ≟ yr
... | yes _ | yes _ = RDestruct (subst x arg s) yl l yr r
... | yes _ | no  _ = RDestruct (subst x arg s) yl l yr (subst x arg r)
... | no  _ | yes _ = RDestruct (subst x arg s) yl (subst x arg l) yr r
... | no  _ | no  _ = RDestruct (subst x arg s) yl (subst x arg l) yr (subst x arg r)
subst _ _ RUnit = RUnit
subst _ _ (RInt n) = RInt n
subst _ _ (RStringLit s) = RStringLit s
subst x arg (RAnnot e ty) = RAnnot (subst x arg e) ty
subst x arg (RBinOp op a b) = RBinOp op (subst x arg a) (subst x arg b)
subst x arg (RUnaryOp op e) = RUnaryOp op (subst x arg e)

-- | Repeated beta reduction with a fuel cap. Each recursive call
-- either descends into a strictly-smaller subterm or reduces an
-- `RApp (RLam x body) arg` to `body[arg/x]`. Fuel guards against
-- pathological inputs (none expected from our desugarings, but
-- defence-in-depth costs nothing).
betaReduceApps : ℕ → RawExpr → RawExpr
betaReduceApps zero e = e
betaReduceApps (suc fuel) (RApp f arg) with betaReduceApps fuel f
... | RLam x body = betaReduceApps fuel (subst x (betaReduceApps fuel arg) body)
... | f'          = RApp f' (betaReduceApps fuel arg)
betaReduceApps _         (RVar name) = RVar name
betaReduceApps _         (RQualified name alias) = RQualified name alias
betaReduceApps (suc fuel) (RLam x body) = RLam x (betaReduceApps fuel body)
betaReduceApps (suc fuel) (RLet x e₁ e₂) =
  RLet x (betaReduceApps fuel e₁) (betaReduceApps fuel e₂)
betaReduceApps (suc fuel) (RPair a b) =
  RPair (betaReduceApps fuel a) (betaReduceApps fuel b)
betaReduceApps (suc fuel) (RDestruct s x l y r) =
  RDestruct (betaReduceApps fuel s) x (betaReduceApps fuel l) y (betaReduceApps fuel r)
betaReduceApps _         RUnit = RUnit
betaReduceApps _         (RInt n) = RInt n
betaReduceApps _         (RStringLit s) = RStringLit s
betaReduceApps (suc fuel) (RAnnot e ty) = RAnnot (betaReduceApps fuel e) ty
betaReduceApps (suc fuel) (RBinOp op a b) =
  RBinOp op (betaReduceApps fuel a) (betaReduceApps fuel b)
betaReduceApps (suc fuel) (RUnaryOp op e) =
  RUnaryOp op (betaReduceApps fuel e)