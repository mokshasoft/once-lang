-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.Soundness
--
-- Plan 0.3, gap G2 (partial): soundness of the operational type
-- checker against the declarative judgment.
--
-- The soundness theorem says: whenever `inferElab` returns a success
-- with type `A` and usage `Ψ`, the declarative judgment
-- `ctx ⊢ e ∶ A ⨾ Ψ` holds. This strengthens the intrinsic-typing
-- guarantee (which gives "the returned SExpr is well-formed at that
-- type") with "and the assignment of type+usage is derivable from the
-- spec rules".
--
-- This module covers soundness for the rules currently stated in
-- `Once.TypeCheck.Judgment`: literals, the `unit` builtin, local
-- variable lookup, annotations, pair introduction, and unary
-- negation. The remaining RawExpr forms (application, let, case,
-- lambdas, binary operators, qualified/import lookups) are deferred
-- until their rules are added to the judgment.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G2.
------------------------------------------------------------------------

module Once.TypeCheck.Soundness where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.String using (String; _++_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; inspect; [_])

open import Once.Type as T using (Type; Unit; Int; Str; Void; Float; Buffer;
                                  _*_; _+_; _⇒[_]_)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RInt; RStringLit; RUnit; RAnnot; RPair;
         RLet; RUnaryOp; OpNeg)
open import Data.String using (_++_)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport; extendNamedCtx)
open import Once.TypeCheck.Judgment

open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_)
  renaming (Expr to SExpr)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)

------------------------------------------------------------------------
-- Soundness of `inferElab` (partial coverage)
------------------------------------------------------------------------

-- | If `inferElab` succeeds, the declarative judgment holds.
-- Covers the rules stated in `Once.TypeCheck.Judgment` so far.
--
-- The proof is one case per RawExpr constructor. For cases not yet in
-- the judgment, we do not claim soundness — the theorem's statement
-- is restricted via pattern matching to the covered forms.

-- Soundness for integer literals.
sound-RInt : ∀ (ctx : NamedCtx) (n : ℤ)
             {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
             {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
           → inferElab ctx (RInt n) ≡ success A Ψ eE d f
           → ctx ⊢ RInt n ∶ A ⨾ Ψ
sound-RInt ctx n refl = t-int n

-- Soundness for string literals.
sound-RStringLit : ∀ (ctx : NamedCtx) (s : String)
                   {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
                   {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
                 → inferElab ctx (RStringLit s) ≡ success A Ψ eE d f
                 → ctx ⊢ RStringLit s ∶ A ⨾ Ψ
sound-RStringLit ctx s refl = t-str s

-- Soundness for unit literal.
sound-RUnit : ∀ (ctx : NamedCtx)
              {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
              {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
            → inferElab ctx RUnit ≡ success A Ψ eE d f
            → ctx ⊢ RUnit ∶ A ⨾ Ψ
sound-RUnit ctx refl = t-unit

-- Soundness for the `unit` variable builtin (monomorphic Unit).
sound-RVar-unit : ∀ (ctx : NamedCtx)
                  {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
                  {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
                → inferElab ctx (RVar "unit") ≡ success A Ψ eE d f
                → ctx ⊢ RVar "unit" ∶ A ⨾ Ψ
sound-RVar-unit ctx refl = t-unit-var

------------------------------------------------------------------------
-- Recursive cases (RUnaryOp, RAnnot, RPair)
--
-- These cases require the soundness induction hypothesis applied to
-- a sub-expression. Naïve `with inferElab ctx e in eqSub` collapses
-- `eqSub` to reflexivity because Agda's `with` machinery abstracts the
-- scrutinee throughout the clause, including in the type of `eqSub`
-- itself. The stdlib `inspect` idiom has the same problem when the
-- scrutinee appears in the IH's type.
--
-- The workaround: bundle each sub-call with a proof-of-equality into
-- a fresh scrutinee value, then match on that. The bundle's type is
-- a view-like Σ: `(r : InferElabResult _) × inferElab ctx e ≡ r`.
-- Because the `with` now dispatches on the bundle (not on the bare
-- `inferElab ctx e`), the equation survives the substitution.
------------------------------------------------------------------------

-- A view bundling an inference result with its defining equation.
InferBundle : (ctx : NamedCtx) → RawExpr → Set
InferBundle ctx e =
  ∃[ r ] inferElab ctx e ≡ r

inferBundle : (ctx : NamedCtx) (e : RawExpr) → InferBundle ctx e
inferBundle ctx e = inferElab ctx e , refl

CheckBundle : (ctx : NamedCtx) → RawExpr → Type → Set
CheckBundle ctx e T =
  ∃[ r ] checkElab ctx e T ≡ r

checkBundle : (ctx : NamedCtx) (e : RawExpr) (T : Type) → CheckBundle ctx e T
checkBundle ctx e T = checkElab ctx e T , refl

-- Soundness for RUnaryOp OpNeg: the sub-expression must be inferable
-- at type Int, and the result inherits that type and its usage
-- vector unchanged.
--
-- Strategy: bundle the sub-call with its equation, then `rewrite`
-- with the equation inside each branch. The rewrite causes the outer
-- `inferElab` to reduce according to the sub-result's shape — either
-- to `success Int …` (the Int branch) or to `failure …`. In the
-- Int branch, we apply `t-neg` with `IH refl` (the IH is also
-- rewritten, so `refl` now gives us the judgment for the sub). In
-- every other branch, the outer `eq` is `failure ≡ success`, absurd.
sound-RUnaryOp-neg :
  ∀ (ctx : NamedCtx) (e : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {A' Ψ' eE' d' f'}
        → inferElab ctx e ≡ success A' Ψ' eE' d' f'
        → ctx ⊢ e ∶ A' ⨾ Ψ')
  → inferElab ctx (RUnaryOp OpNeg e) ≡ success A Ψ eE d f
  → ctx ⊢ RUnaryOp OpNeg e ∶ A ⨾ Ψ
sound-RUnaryOp-neg ctx e IH eq with inferBundle ctx e
sound-RUnaryOp-neg ctx e IH eq | success Int _ _ _ _ , eqSub
  rewrite eqSub with eq
... | refl = t-neg (IH refl)
sound-RUnaryOp-neg ctx e IH eq | success Unit _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success Void _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success Float _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success Str _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success Buffer _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (_ * _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (_ + _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (_ ⇒[ _ ] _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (T.Eff _ _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (T.μ-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | success (T.ν-type _) _ _ _ _ , eqSub
  rewrite eqSub with eq
... | ()
sound-RUnaryOp-neg ctx e IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

-- Soundness for RAnnot: the sub-expression must successfully check
-- at the annotated type, and the result's type equals that annotation.
sound-RAnnot :
  ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH : ∀ {Ψ' eE' d' f'}
        → checkElab ctx e T ≡ success Ψ' eE' d' f'
        → ctx ⊢ e ∶ T ⨾ Ψ')
  → inferElab ctx (RAnnot e T) ≡ success A Ψ eE d f
  → ctx ⊢ RAnnot e T ∶ A ⨾ Ψ
sound-RAnnot ctx e T IH eq with checkBundle ctx e T
sound-RAnnot ctx e T IH eq | success _ _ _ _ , eqSub
  rewrite eqSub with eq
... | refl = t-annot (IH refl)
sound-RAnnot ctx e T IH eq | failure _ , eqSub
  rewrite eqSub with eq
... | ()

-- Soundness for RPair: both sub-expressions infer; the pair's type
-- is the product, and its usage is the per-position sum.
sound-RPair :
  ∀ (ctx : NamedCtx) (a b : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IHa : ∀ {A' Ψ' eE' d' f'}
         → inferElab ctx a ≡ success A' Ψ' eE' d' f'
         → ctx ⊢ a ∶ A' ⨾ Ψ')
  → (IHb : ∀ {B' Ψ' eE' d' f'}
         → inferElab ctx b ≡ success B' Ψ' eE' d' f'
         → ctx ⊢ b ∶ B' ⨾ Ψ')
  → inferElab ctx (RPair a b) ≡ success A Ψ eE d f
  → ctx ⊢ RPair a b ∶ A ⨾ Ψ
sound-RPair ctx a b IHa IHb eq with inferBundle ctx a
sound-RPair ctx a b IHa IHb eq | success _ _ _ _ _ , eqA
  with inferBundle ctx b
sound-RPair ctx a b IHa IHb eq
  | success _ _ _ _ _ , eqA | success _ _ _ _ _ , eqB
  rewrite eqA | eqB with eq
... | refl = t-pair (IHa refl) (IHb refl)
sound-RPair ctx a b IHa IHb eq
  | success _ _ _ _ _ , eqA | failure _ , eqB
  rewrite eqA | eqB with eq
... | ()
sound-RPair ctx a b IHa IHb eq | failure _ , eqA
  rewrite eqA with eq
... | ()

------------------------------------------------------------------------
-- Soundness for RQualified
--
-- No recursion — a `RQualified` either resolves in the imports table
-- or fails. We case-split on the lookup result and either apply
-- `t-var-qualified` (success) or close with an absurd pattern (failure).
------------------------------------------------------------------------

-- Bundle wrapping `lookupImport` calls (single-shot, no IH involved).
LookupBundle : (xs : _) → (q : _) → Set
LookupBundle xs q = ∃[ r ] lookupImport xs q ≡ r

lookupBundle : ∀ xs q → LookupBundle xs q
lookupBundle xs q = lookupImport xs q , refl

sound-RQualified :
  ∀ (ctx : NamedCtx) (name alias : _)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → inferElab ctx (RQualified name alias) ≡ success A Ψ eE d f
  → ctx ⊢ RQualified name alias ∶ A ⨾ Ψ
sound-RQualified ctx name alias eq
  with lookupBundle (NamedCtx.imports ctx) (alias ++ "." ++ name)
sound-RQualified ctx name alias eq | just T , eqLookup
  rewrite eqLookup with eq
... | refl = t-var-qualified eqLookup
sound-RQualified ctx name alias eq | nothing , eqLookup
  rewrite eqLookup with eq
... | ()

------------------------------------------------------------------------
-- Soundness for RLet
--
-- Two-stage recursion, but the second IH lives in the *extended*
-- context `extendNamedCtx ctx x A` — where `A` is the type inferred
-- for `e₁` in stage one. The second IH is therefore parameterised by
-- `A`: before we've inspected e₁'s result, we don't know which
-- extended context applies. Using the standard bundle + rewrite
-- technique, we inspect e₁ first, pin `A`, then apply IH₂ at that A.
------------------------------------------------------------------------

-- Sub-bundle for the body of a let: the body's inferElab call is
-- parameterised by the let-bound variable's type.
LetBodyBundle : (ctx : NamedCtx) (x : _) (A : Type) (e₂ : RawExpr) → Set
LetBodyBundle ctx x A e₂ =
  ∃[ r ] inferElab (extendNamedCtx ctx x A) e₂ ≡ r

letBodyBundle : ∀ (ctx : NamedCtx) (x : _) (A : Type) (e₂ : RawExpr)
              → LetBodyBundle ctx x A e₂
letBodyBundle ctx x A e₂ = inferElab (extendNamedCtx ctx x A) e₂ , refl

sound-RLet :
  ∀ (ctx : NamedCtx) (x : _) (e₁ e₂ : RawExpr)
    {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  → (IH₁ : ∀ {A' Ψ' eE' d' f'}
         → inferElab ctx e₁ ≡ success A' Ψ' eE' d' f'
         → ctx ⊢ e₁ ∶ A' ⨾ Ψ')
  → (IH₂ : ∀ {Aty B' Ψ' eE' d' f'}
         → inferElab (extendNamedCtx ctx x Aty) e₂ ≡ success B' Ψ' eE' d' f'
         → (extendNamedCtx ctx x Aty) ⊢ e₂ ∶ B' ⨾ Ψ')
  → inferElab ctx (RLet x e₁ e₂) ≡ success A Ψ eE d f
  → ctx ⊢ RLet x e₁ e₂ ∶ A ⨾ Ψ
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq with inferBundle ctx e₁
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq | success A' Ψ₁ e₁E d₁ f₁ , eq₁
  with letBodyBundle ctx x A' e₂
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq
  | success A' Ψ₁ e₁E d₁ f₁ , eq₁
  | success B' (q ∷ᵘ Ψ₂) e₂E d₂ f₂ , eq₂
  -- Feed the raw equations to the IHs *before* any rewrite, so Agda
  -- can solve implicits from the equation's type. Then rewrite the
  -- outer elaborator step to line up the final `eq`.
  with IH₁ eq₁ | IH₂ {Aty = A'} eq₂
... | sub1 | sub2 rewrite eq₁ | eq₂ with eq
... | refl = t-let sub1 sub2
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq
  | success A' Ψ₁ e₁E d₁ f₁ , eq₁
  | failure _ , eq₂
  rewrite eq₁ | eq₂ with eq
... | ()
sound-RLet ctx x e₁ e₂ IH₁ IH₂ eq | failure _ , eq₁
  rewrite eq₁ with eq
... | ()
