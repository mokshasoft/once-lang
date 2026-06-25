-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.RealizeAgrees — the proof behind `RealizeBridge.realize-agrees`
-- (Plan 0.49 piece 3). `checkElab`'s emitted term `se` denotes the same as the
-- canonical `realize` term read off its typing witness `w` (which `realize`
-- consumes, INDEPENDENT of `checkElab`'s term). A wrong elaboration breaks the apex.
--
-- Stated over the ELABORATOR EQUATION (`inferElabV`/`checkElabV ≡ (success … , w)`),
-- NOT an arbitrary derivation: the witness `w` is then exactly the elaborator's
-- own output, so `se` is well-defined (an arbitrary `⊢ᶜ` derivation over-generates
-- — `t-embed (t-pair …)` vs the `t-pair-lit-check` the checker actually emits).
-- Induct on `e`, fold the elaborator via `with inferElabV ctx a in eqa` (now clean
-- because the multi-`with` `inferElabV` clauses were refactored to aux helpers).
-- `faithful`-style agreements: `_>>=T_` threads each sub at the same depth `k`.
--
-- WIP: leaves + `RPair` (infer) validate the equation-form technique end to end;
-- the rest route through `infer-agreeV-todo`/`check-agreeV-todo`
-- ([[feedback_scaffold_then_discharge]] — to be emptied).
------------------------------------------------------------------------

module Once.Adequacy.RealizeAgrees where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

import Once.Type
open import Once.Type using (Type; Int)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Elaborate using (success; failure; VerifiedInferResult)
import Once.TypeCheck.Elaborate as E
open import Once.TypeCheck.Judgment using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; t-int; t-str; t-unit; t-pair; t-neg)
open import Once.Denotation.Realize using (realize; realize-infer)
open import Once.Surface.Syntax using (Expr; Usage; ⟦_⟧ᶜ; pair; neg)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
import Once.Denotation.SourceDenote as SD

private
  Env : NamedCtx → Set
  Env ctx = ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜ ⟧ᴰ

-- Agreement of the elaborator's emitted term `se` with `realize`(its witness),
-- over the elaborator equation. (Forward sigs for the mutual block + scaffolds.)
InferAgreeV : (ctx : NamedCtx) (e : RawExpr) {A : Type} {Ψ : Usage (NamedCtx.size ctx)}
              {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ} {w : ctx ⊢ᵢ e ∶ A ⨾ Ψ}
            → E.inferElabV ctx e ≡ (success A Ψ se d f , w) → Set
InferAgreeV ctx e {se = se} {w = w} _ =
  ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k

CheckAgreeV : (ctx : NamedCtx) (e : RawExpr) (T : Type) {Ψ : Usage (NamedCtx.size ctx)}
              {se : Expr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ} {w : ctx ⊢ᶜ e ∶ T ⨾ Ψ}
            → E.checkElabV ctx e T ≡ (success Ψ se d f , w) → Set
CheckAgreeV ctx e T {se = se} {w = w} _ =
  ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize w ⟧ˢ dγ k

postulate
  infer-agreeV-todo : ∀ (ctx : NamedCtx) (e : RawExpr) {A Ψ se d f w}
    (eq : E.inferElabV ctx e ≡ (success A Ψ se d f , w)) → InferAgreeV ctx e eq
  check-agreeV-todo : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type) {Ψ se d f w}
    (eq : E.checkElabV ctx e T ≡ (success Ψ se d f , w)) → CheckAgreeV ctx e T eq

-- RUnaryOp(neg) folded top-level (avoids mutual-block `...|` ambiguity,
-- [[feedback_mutual_block_syntax]]): takes the sub-result explicitly + the
-- sub-IH as a function (applied only in the Int branch). Non-Int/failure subs
-- make `inferElabV-RUnaryOp-aux` a `failure`, so the success equation is absurd.
agree-RUnaryOp : ∀ {ctx : NamedCtx} {e : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RUnaryOp Raw.OpNeg e ∶ A ⨾ Ψ}
  (rE : VerifiedInferResult ctx e)
  → E.inferElabV-RUnaryOp-aux ctx e rE ≡ (success A Ψ se d f , w)
  → (∀ {Ψ' eE' d' fr'} {wE' : ctx ⊢ᵢ e ∶ Int ⨾ Ψ'}
       → rE ≡ (success Int Ψ' eE' d' fr' , wE')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ dγ k ≡ SD.⟦ realize-infer wE' ⟧ˢ dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
agree-RUnaryOp (success Int Ψ eE d fr , wE) refl subAg dγ k rewrite subAg refl dγ k = refl
agree-RUnaryOp (failure _ , _) () subAg
agree-RUnaryOp (success Once.Type.Unit _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Void _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Float _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Str _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Buffer _ _ _ _ , _) () subAg
agree-RUnaryOp (success (_ Once.Type.* _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (_ Once.Type.+ _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (_ Once.Type.⇒[ _ ] _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (Once.Type.μ-type _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (Once.Type.ν-type _) _ _ _ _ , _) () subAg

mutual
  infer-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) {A Ψ se d f w}
    (eq : E.inferElabV ctx e ≡ (success A Ψ se d f , w)) → InferAgreeV ctx e eq
  infer-agreeV ctx (Raw.RInt n)       refl dγ k = refl
  infer-agreeV ctx (Raw.RStringLit s) refl dγ k = refl
  infer-agreeV ctx Raw.RUnit          refl dγ k = refl
  -- RPair: the de-withed `inferElabV-RPair-aux` reduces once the two sub-results
  -- are exposed, so `with inferElabV … in eq` folds with no opaque with-helper.
  infer-agreeV ctx (Raw.RPair a b) eq dγ k
    with E.inferElabV ctx a in eqa | E.inferElabV ctx b in eqb
  ... | success A Ψ₁ aE da fa , wA | success B Ψ₂ bE db fb , wB with eq
  ...   | refl rewrite infer-agreeV ctx a eqa dγ k | infer-agreeV ctx b eqb dγ k = refl
  infer-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) eq dγ k =
    agree-RUnaryOp (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e p) dγ k
  infer-agreeV ctx e eq = infer-agreeV-todo ctx e eq

  check-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type) {Ψ se d f w}
    (eq : E.checkElabV ctx e T ≡ (success Ψ se d f , w)) → CheckAgreeV ctx e T eq
  check-agreeV ctx e T eq = check-agreeV-todo ctx e T eq
