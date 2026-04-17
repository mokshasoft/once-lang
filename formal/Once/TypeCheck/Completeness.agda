-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.Completeness
--
-- Plan 0.3, gap G2 (completeness direction): if the declarative
-- judgment derives `ctx ⊢ e ∶ A ⨾ Ψ`, the operational type-checker
-- succeeds with the matching type + usage.
--
-- Soundness (in `Once.TypeCheck.Soundness`) goes the other way:
-- if the elaborator succeeds, the judgment holds. Together they
-- give `inferElab-succeeds ⟺ judgment-derivable`.
--
-- Structure:
--   * `infer-complete`: for judgments whose outermost rule matches
--     an infer-mode clause (all rules except `t-lam`), show
--     `inferElab` succeeds. `t-lam`'s derivation has shape
--     `ctx ⊢ RLam x body ∶ (A ⇒[ q ] B) ⨾ Ψ`, and `inferElab`
--     rejects `RLam` regardless of its sub-derivation — so the
--     single `t-lam` case has to be excluded.
--   * `check-complete-lam`: for the `t-lam` rule, show `checkElab`
--     at the function type succeeds.
--
-- Reference: plans/0.3-frontend-verification-gaps.md, gap G2.
------------------------------------------------------------------------

module Once.TypeCheck.Completeness where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.String using (String; _++_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type as T using (Type; Unit; Int; Str; Void; Float; Buffer;
                                  _*_; _+_; _⇒[_]_; Quantity)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RInt; RStringLit; RUnit; RAnnot; RPair)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport)
open import Once.TypeCheck.Judgment

open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_)
  renaming (Expr to SExpr)

------------------------------------------------------------------------
-- Leaf-case completeness
--
-- For the base rules (t-int, t-str, t-unit, t-unit-var), the
-- inferElab clause is a direct success with hard-coded type and
-- zeroUsage. Completeness reduces to constructing the existential
-- witnesses (eE, depth, fresh) from the elaborator's computation.
------------------------------------------------------------------------

infer-complete-RInt :
  ∀ {ctx : NamedCtx} (n : ℤ)
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RInt n) ≡ success Int zeroUsage eE d f
infer-complete-RInt {ctx} n =
  Surface.int n , 0 , NamedCtx.freshCounter ctx , refl

infer-complete-RStringLit :
  ∀ {ctx : NamedCtx} (s : String)
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RStringLit s) ≡ success Str zeroUsage eE d f
infer-complete-RStringLit {ctx} s =
  Surface.str s , 0 , NamedCtx.freshCounter ctx , refl

infer-complete-RUnit :
  ∀ {ctx : NamedCtx}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx RUnit ≡ success Unit zeroUsage eE d f
infer-complete-RUnit {ctx} =
  Surface.unit , 0 , NamedCtx.freshCounter ctx , refl

infer-complete-RVar-unit :
  ∀ {ctx : NamedCtx}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar "unit") ≡ success Unit zeroUsage eE d f
infer-complete-RVar-unit {ctx} =
  Surface.unit , 0 , NamedCtx.freshCounter ctx , refl

------------------------------------------------------------------------
-- Single-lookup completeness: qualified imports, local vars, imports.
------------------------------------------------------------------------

infer-complete-RQualified :
  ∀ {ctx : NamedCtx} {name alias : String} {T : Type}
  → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RQualified name alias) ≡ success T zeroUsage eE d f
infer-complete-RQualified {ctx} {name} {alias} eqLookup
  rewrite eqLookup =
  Surface.prim (alias ++ "." ++ name) , 0 , NamedCtx.freshCounter ctx , refl

------------------------------------------------------------------------
-- Sub-expression composition completeness.
--
-- The pattern: given IHs witnessing sub-elaborator successes, show
-- the outer elaborator succeeds. Proof: rewrite with the sub-equations,
-- elaborator body reduces, conclude with `refl`.
--
-- These theorems don't take a derivation premise — the IH shape
-- carries enough structure. For a top-level
-- `full-complete : derivation → elaborator-success` proof, the
-- derivation's structure would drive which IH chain to use; each
-- case invokes the corresponding single-rule theorem below.
------------------------------------------------------------------------

infer-complete-RPair :
  ∀ {ctx : NamedCtx} (a b : RawExpr) {A B : Type}
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {aE : SExpr (NamedCtx.debruijn ctx) Ψ₁ A}
    {bE : SExpr (NamedCtx.debruijn ctx) Ψ₂ B}
    {dA dB fA fB : ℕ}
  → inferElab ctx a ≡ success A Ψ₁ aE dA fA
  → inferElab ctx b ≡ success B Ψ₂ bE dB fB
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RPair a b) ≡ success (A * B) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RPair a b eqA eqB rewrite eqA | eqB =
  _ , _ , _ , refl

infer-complete-RUnaryOp-neg :
  ∀ {ctx : NamedCtx} (e : RawExpr)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn ctx) Ψ Int}
    {d' f' : ℕ}
  → inferElab ctx e ≡ success Int Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ success Int Ψ eE d f
infer-complete-RUnaryOp-neg e eqSub rewrite eqSub =
  _ , _ , _ , refl

infer-complete-RAnnot :
  ∀ {ctx : NamedCtx} (e : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → checkElab ctx e T ≡ success Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RAnnot e T) ≡ success T Ψ eE d f
infer-complete-RAnnot e T eqSub rewrite eqSub =
  _ , _ , _ , refl

------------------------------------------------------------------------
-- Completeness notes
--
-- The full theorem `∀ (d : ctx ⊢ e ∶ A ⨾ Ψ) → e-is-not-RLam e →
-- ∃ eE d' f'. inferElab ctx e ≡ success A Ψ eE d' f'` walks the
-- derivation structurally, invoking the per-rule completeness
-- lemmas above. Each rule becomes one case of the pattern match.
-- Remaining work (mechanical, mirrors the soundness file):
--
--   * t-let, t-case, t-app, t-binop-*, t-var-local, t-var-import,
--     t-id-app, t-fst-app, t-snd-app, t-terminal-app.
--   * `check-complete-lam` for the `t-lam` rule specifically, showing
--     `checkElab ctx (RLam x body) (A ⇒[ q ] B)` succeeds.
------------------------------------------------------------------------

infer-complete-RLet :
  ∀ {ctx : NamedCtx} (x : String) (e₁ e₂ : RawExpr)
    {A B : Type} {q : Quantity}
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ A}
    {e₂E : SExpr (NamedCtx.debruijn (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A))
                 (q Surface.Usage.∷ Ψ₂) B}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success A Ψ₁ e₁E d₁ f₁
  → inferElab (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A) e₂
      ≡ success B (q Surface.Usage.∷ Ψ₂) e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RLet x e₁ e₂) ≡ success B (Ψ₂ +ᵘ (q *ᵘ Ψ₁)) eE d f
infer-complete-RLet x e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ =
  _ , _ , _ , refl

infer-complete-RApp-id :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {T : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "id") arg)
        ≡ success T (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-id arg eqSub rewrite eqSub =
  _ , _ , _ , refl

infer-complete-RApp-terminal :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {T : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "terminal") arg)
        ≡ success Unit (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-terminal arg eqSub rewrite eqSub =
  _ , _ , _ , refl

infer-complete-RApp-fst :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {A B : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "fst") arg)
        ≡ success A (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-fst arg eqSub rewrite eqSub =
  _ , _ , _ , refl

infer-complete-RApp-snd :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {A B : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "snd") arg)
        ≡ success B (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-snd arg eqSub rewrite eqSub =
  _ , _ , _ , refl
