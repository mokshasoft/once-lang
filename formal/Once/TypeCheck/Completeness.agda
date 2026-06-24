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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Data.String.Properties as StrProp using (_≟_)

open import Once.Type as T using (Type; Unit; Int; Str; Void; Float; Buffer;
                                  _*_; _+_; _⇒[_]_; Quantity; _≤q_;
                                  Zero; One; Many)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RInt; RStringLit; RUnit; RAnnot; RPair)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport;
         inferElabV; checkElabV; _≟T_;
         classifyAppHead; classifyAppHeadView; ahv-other;
         classifyAppHead-nothing⇒view-other; AppHeadView;
         classifyBareBuiltin; checkG; inspectWellFormedF; wfv-yes; wfv-no;
         inspectCheckG; cgv-just; cgv-nothing;
         bbc-id; bbc-fst; bbc-snd; bbc-terminal; bbc-initial;
         bbc-inl; bbc-inr; bbc-arr; bbc-other)
open import Once.TypeCheck.Judgment
open import Once.Functor.Translate using (WellFormedF)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys; composeArgB; composeMid;
  inspectLookupLocal; inspectLookupImport; llv-found; llv-not-found; liv-found; liv-not-found)

open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_)
  renaming (Expr to SExpr)
-- Plan 0.49 / D063: morphism-completeness, proven by induction on ⊢ᵐ
-- (12/15 cases; m-const/m-cata/m-named are scoped postulates there).
open import Once.TypeCheck.MorphComplete using (morph-complete)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
import Data.String.Properties

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
infer-complete-RInt n = _ , _ , _ , refl

infer-complete-RStringLit :
  ∀ {ctx : NamedCtx} (s : String)
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RStringLit s) ≡ success Str zeroUsage eE d f
infer-complete-RStringLit s = _ , _ , _ , refl

infer-complete-RUnit :
  ∀ {ctx : NamedCtx}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx RUnit ≡ success Unit zeroUsage eE d f
infer-complete-RUnit = _ , _ , _ , refl

infer-complete-RVar-unit :
  ∀ {ctx : NamedCtx}
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar "unit") ≡ success Unit zeroUsage eE d f
infer-complete-RVar-unit = _ , _ , _ , refl

------------------------------------------------------------------------
-- Single-lookup completeness: qualified imports, local vars, imports.
------------------------------------------------------------------------

infer-complete-RQualified :
  ∀ {ctx : NamedCtx} {name alias : String} {T : Type}
  → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RQualified name alias) ≡ success T zeroUsage eE d f
-- Plan 0.36: `inferElabV-RQualified-aux` splits on the looked-up type (a
-- `Many`-arrow → `lift-morphism (SigOp …)`, else `sigOp`), so the aux no
-- longer reduces for an abstract `T`. `go` mirrors the split over `T`'s
-- shape so the reduction is determined in each branch; the proof term is
-- uniform (`cong proj₁ (helper _ eq')`) — only the elaborated surface expr
-- differs, and it is existentially bound.
infer-complete-RQualified {ctx} {name} {alias} {T} eq = go T eq
  where
    open Once.TypeCheck.Elaborate using (inferElabV-RQualified-aux)
    helper : ∀ (lhs : Maybe Type)
           → (eq' : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ lhs)
           → inferElabV-RQualified-aux ctx name alias
               (lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)) refl
             ≡ inferElabV-RQualified-aux ctx name alias lhs eq'
    helper _ refl = refl
    go : ∀ (T' : Type)
       → (eq' : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just T')
       → ∃[ eE ] ∃[ d ] ∃[ f ]
           inferElab ctx (RQualified name alias) ≡ success T' zeroUsage eE d f
    go (A ⇒[ T.mk-kind Many π ] B) eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go (A ⇒[ T.mk-kind One  π ] B) eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go (A ⇒[ T.mk-kind Zero π ] B) eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Unit          eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Void          eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Int           eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Float         eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Str           eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go Buffer        eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go (A * B)       eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go (A + B)       eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go (T.μ-type F)  eq' = _ , _ , _ , cong proj₁ (helper _ eq')
    go (T.ν-type F)  eq' = _ , _ , _ , cong proj₁ (helper _ eq')

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
infer-complete-RPair {ctx} a b eqA eqB
  with inferElabV ctx a | eqA
... | success _ _ _ _ _ , _ | refl
    with inferElabV ctx b | eqB
...   | success _ _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RUnaryOp-neg :
  ∀ {ctx : NamedCtx} (e : RawExpr)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn ctx) Ψ Int}
    {d' f' : ℕ}
  → inferElab ctx e ≡ success Int Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RUnaryOp Raw.OpNeg e) ≡ success Int Ψ eE d f
infer-complete-RUnaryOp-neg {ctx} e eqE
  with inferElabV ctx e | eqE
... | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RAnnot :
  ∀ {ctx : NamedCtx} (e : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → checkElab ctx e T ≡ success Ψ eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RAnnot e T) ≡ success T Ψ eE d f
infer-complete-RAnnot {ctx} e T eqC
  with checkElabV ctx e T | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

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
infer-complete-RLet {ctx} x e₁ e₂ {A = A} eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success _ _ _ _ _ , _ | refl
    with inferElabV (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A) e₂ | eq₂
...   | success _ (_ Surface.Usage.∷ _) _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-id :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {T : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "id") arg)
        ≡ success T (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-id {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success _ _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-terminal :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {T : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ T}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success T Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "terminal") arg)
        ≡ success Unit (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-terminal {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success _ _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-fst :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {A B : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "fst") arg)
        ≡ success A (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-fst {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success (_ * _) _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-snd :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {A B : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (A * B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A * B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "snd") arg)
        ≡ success B (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-snd {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success (_ * _) _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-arr :
  ∀ {ctx : NamedCtx} (arg : RawExpr) {A B : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ (A T.⇒[ T.mk-kind T.Many T.pure ] B)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success (A T.⇒[ T.mk-kind T.Many T.pure ] B) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "arr") arg)
        ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψ eE d f
infer-complete-RApp-arr {ctx} arg eqArg
  with inferElabV ctx arg | eqArg
... | success (_ T.⇒[ T.mk-kind T.Many T.pure ] _) _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-apply :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A : Type) {B : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {argE : SExpr (NamedCtx.debruijn ctx) Ψ ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A)}
    {d' f' : ℕ}
  → inferElab ctx arg ≡ success ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A) Ψ argE d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RApp (RVar "apply") arg)
        ≡ success B (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
infer-complete-RApp-apply {ctx} arg A eqArg
  with inferElabV ctx arg | eqArg
... | success ((_ T.⇒[ T.mk-kind T.Many T.pure ] _) T.* A') _ _ _ _ , _ | refl
    with A ≟T A'
...   | yes refl = _ , _ , _ , refl
...   | no  ¬eq  = ⊥-elim (¬eq refl)

------------------------------------------------------------------------
-- Variable lookup (local / import)
------------------------------------------------------------------------

infer-complete-RVar-local :
  ∀ {ctx : NamedCtx} (x : String) {A : Type}
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn ctx) Ψ A}
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ just (A , Ψ , eE')
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar x) ≡ success A Ψ eE d f
infer-complete-RVar-local {ctx} x {A} {Ψ} {eE'} ¬unit eqLoc
  with StrProp._≟_ x "unit"
... | yes refl = ⊥-elim (¬unit refl)
... | no _     = _ , _ , _ , cong proj₁ (helper _ eqLoc)
  where
    open Once.TypeCheck.Elaborate using (inferElabV-RVar-lookup-aux)
    helper : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (SExpr (NamedCtx.debruijn ctx) Ψ' A')))
           → (eq' : lookupLocal ctx x ≡ lhs)
           → inferElabV-RVar-lookup-aux ctx x ¬unit (lookupLocal ctx x) refl _ refl
             ≡ inferElabV-RVar-lookup-aux ctx x ¬unit lhs eq' _ refl
    helper _ refl = refl

infer-complete-RVar-import :
  ∀ {ctx : NamedCtx} (x : String) {T : Type}
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ just T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar x) ≡ success T zeroUsage eE d f
infer-complete-RVar-import {ctx} x {T} ¬unit eqLoc eqImp
  with StrProp._≟_ x "unit"
... | yes refl = ⊥-elim (¬unit refl)
... | no _     = _ , _ , _ , cong proj₁ (trans (helperLoc _ eqLoc) (helperImp _ eqImp))
  where
    open Once.TypeCheck.Elaborate using (inferElabV-RVar-lookup-aux)
    helperLoc : ∀ (lhs : Maybe (∃[ A' ] ∃[ Ψ' ] (SExpr (NamedCtx.debruijn ctx) Ψ' A')))
              → (eq' : lookupLocal ctx x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x ¬unit (lookupLocal ctx x) refl _ refl
                ≡ inferElabV-RVar-lookup-aux ctx x ¬unit lhs eq' _ refl
    helperLoc _ refl = refl
    helperImp : ∀ (lhs : Maybe Type)
              → (eq' : lookupImport (NamedCtx.imports ctx) x ≡ lhs)
              → inferElabV-RVar-lookup-aux ctx x ¬unit nothing eqLoc (lookupImport (NamedCtx.imports ctx) x) refl
                ≡ inferElabV-RVar-lookup-aux ctx x ¬unit nothing eqLoc lhs eq'
    helperImp _ refl = refl

------------------------------------------------------------------------
-- RBinOp (arithmetic and comparison)
--
-- Each of the 10 operators has its own completeness theorem since
-- `isArithmeticOp op` / `isComparisonOp op` only reduces when `op`
-- is concrete. The outer elaborator's `if Raw.isArithmeticOp op`
-- dispatches per-operator.
------------------------------------------------------------------------

infer-complete-RBinOp-arith :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (arithEq : Raw.isArithmeticOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success Int (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-arith {ctx} Raw.OpAdd refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith {ctx} Raw.OpSub refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith {ctx} Raw.OpMul refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith {ctx} Raw.OpDiv refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-arith {ctx} Raw.OpMod refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RBinOp-cmp :
  ∀ {ctx : NamedCtx} (op : Raw.BinOp) (cmpEq : Raw.isComparisonOp op ≡ true)
    (e₁ e₂ : RawExpr)
    {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    {e₁E : SExpr (NamedCtx.debruijn ctx) Ψ₁ Int}
    {e₂E : SExpr (NamedCtx.debruijn ctx) Ψ₂ Int}
    {d₁ d₂ f₁ f₂ : ℕ}
  → inferElab ctx e₁ ≡ success Int Ψ₁ e₁E d₁ f₁
  → inferElab ctx e₂ ≡ success Int Ψ₂ e₂E d₂ f₂
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RBinOp op e₁ e₂) ≡ success (Unit + Unit) (Ψ₁ +ᵘ Ψ₂) eE d f
infer-complete-RBinOp-cmp {ctx} Raw.OpLt refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpLe refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpGt refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpGe refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpEq refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl
infer-complete-RBinOp-cmp {ctx} Raw.OpNe refl e₁ e₂ eq₁ eq₂
  with inferElabV ctx e₁ | eq₁
... | success Int _ _ _ _ , _ | refl
    with inferElabV ctx e₂ | eq₂
...   | success Int _ _ _ _ , _ | refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- RLam check mode
------------------------------------------------------------------------

private
  decideLeq-just : ∀ q' q → (q' ≤q q) ≡ true
                 → ∃ λ (eq : (q' ≤q q) ≡ true)
                 → Once.TypeCheck.Elaborate.decideLeq q' q ≡ just eq
  decideLeq-just Zero Zero refl = refl , refl
  decideLeq-just Zero One  refl = refl , refl
  decideLeq-just Zero Many refl = refl , refl
  decideLeq-just One  One  refl = refl , refl
  decideLeq-just One  Many refl = refl , refl
  decideLeq-just Many Many refl = refl , refl

check-complete-RLam :
  ∀ (ctx : NamedCtx) (x : String) (body : RawExpr)
    (A : Type) (q q' : Quantity) (B : Type)
    {Ψ' : Surface.Usage (NamedCtx.size ctx)}
    {eE' : SExpr (NamedCtx.debruijn (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A))
                 (q' Surface.Usage.∷ Ψ') B}
    {d' f' : ℕ}
  → (q' T.≤q q) ≡ true
  → checkElab (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A) body B
      ≡ success (q' Surface.Usage.∷ Ψ') eE' d' f'
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      checkElab ctx (Raw.RLam x body) (A T.⇒[ T.mk-kind q T.pure ] B) ≡ success Ψ' eE d f
check-complete-RLam ctx x body A q q' B leqEq eqC
  with checkElabV (Once.TypeCheck.Elaborate.extendNamedCtx ctx x A) body B | eqC
... | success (_ Surface.Usage.∷ _) _ _ _ , _ | refl
    with Once.TypeCheck.Elaborate.decideLeq q' q | decideLeq-just q' q leqEq
...   | just _ | _ , refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- RDestruct (case / sum elimination)
------------------------------------------------------------------------

infer-complete-RDestruct :
  ∀ {ctx : NamedCtx} (scrut : RawExpr) (xL : String) (eL : RawExpr)
    (xR : String) (eR : RawExpr) {A B : Type}
    {Ψs : Surface.Usage (NamedCtx.size ctx)}
    {scrutE : SExpr (NamedCtx.debruijn ctx) Ψs (A + B)}
    {ds fs : ℕ}
    (C : Type) {qℓ qr : Quantity}
    {Ψₗ : Surface.Usage (NamedCtx.size ctx)}
    {eLE : SExpr (NamedCtx.debruijn
                    (Once.TypeCheck.Elaborate.extendNamedCtx ctx xL A))
                 (qℓ Surface.Usage.∷ Ψₗ) C}
    {dL fL : ℕ}
    {Ψᵣ : Surface.Usage (NamedCtx.size ctx)}
    {eRE : SExpr (NamedCtx.debruijn
                    (Once.TypeCheck.Elaborate.extendNamedCtx ctx xR B))
                 (qr Surface.Usage.∷ Ψᵣ) C}
    {dR fR : ℕ}
  → inferElab ctx scrut ≡ success (A + B) Ψs scrutE ds fs
  → inferElab (Once.TypeCheck.Elaborate.extendNamedCtx ctx xL A) eL
      ≡ success C (qℓ Surface.Usage.∷ Ψₗ) eLE dL fL
  → inferElab (Once.TypeCheck.Elaborate.extendNamedCtx ctx xR B) eR
      ≡ success C (qr Surface.Usage.∷ Ψᵣ) eRE dR fR
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (Raw.RDestruct scrut xL eL xR eR)
        ≡ success C (Ψs +ᵘ (Ψₗ Surface.⊔ᵘ Ψᵣ)) eE d f
infer-complete-RDestruct {ctx} scrut xL eL xR eR {A = A} {B = B} C eqS eqL eqR
  with inferElabV ctx scrut | eqS
... | success (_ + _) _ _ _ _ , _ | refl
    with inferElabV (Once.TypeCheck.Elaborate.extendNamedCtx ctx xL A) eL | eqL
...   | success _ (_ Surface.Usage.∷ _) _ _ _ , _ | refl
      with inferElabV (Once.TypeCheck.Elaborate.extendNamedCtx ctx xR B) eR | eqR
...     | success _ (_ Surface.Usage.∷ _) _ _ _ , _ | refl
        with C ≟T C
...       | yes refl = _ , _ , _ , refl
...       | no  ¬eq  = ⊥-elim (¬eq refl)

------------------------------------------------------------------------
-- Generic RApp
------------------------------------------------------------------------

-- Plan 0.4 T1, change 1 (2026-04-30): premise on `x` is now a
-- `checkElab` success, matching the new bidirectional rule in
-- `inferElab` (it CHECKs the arg at the synthesized domain rather
-- than inferring it). Call sites that have a `t-app`-style
-- derivation already provide ⊢ᶜ for x; those that have an
-- inferElab witness convert via `check-complete (t-embed dX)`.
infer-complete-RApp-generic :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (A : Type) {B : Type} {q : Quantity}
    {Ψf : Surface.Usage (NamedCtx.size ctx)}
    {fE : SExpr (NamedCtx.debruijn ctx) Ψf (A T.⇒[ T.mk-kind q T.pure ] B)}
    {df ff : ℕ}
    {Ψx : Surface.Usage (NamedCtx.size ctx)}
    {xE : SExpr (NamedCtx.debruijn ctx) Ψx A}
    {dx fx : ℕ}
  → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (A T.⇒[ T.mk-kind q T.pure ] B) Ψf fE df ff
  → checkElab ctx x A ≡ success Ψx xE dx fx
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x)
        ≡ success B (Ψf +ᵘ (q *ᵘ Ψx)) eE d f'
private
  open Once.TypeCheck.Elaborate
    using (inferElabV-RApp-dispatch; inferElabV-RApp-other-aux)
  viewBridge : ∀ {ctx f x} (vw : AppHeadView f) (eq : classifyAppHeadView f ≡ vw)
             → inferElabV-RApp-dispatch ctx f x (classifyAppHeadView f) refl
               ≡ inferElabV-RApp-dispatch ctx f x vw eq
  viewBridge _ refl = refl
  otherBridge : ∀ {ctx f x} (lhs : Maybe Once.TypeCheck.Elaborate.PolyBuiltinApp)
                (eq : classifyAppHead f ≡ lhs)
              → inferElabV-RApp-other-aux ctx f x (classifyAppHead f) refl
                ≡ inferElabV-RApp-other-aux ctx f x lhs eq
  otherBridge _ refl = refl

infer-complete-RApp-generic {ctx} f x A {B} {q} eqAH eqF eqX
  rewrite cong proj₁ (viewBridge {ctx} {f} {x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | cong proj₁ (otherBridge {ctx} {f} {x} nothing eqAH)
  with inferElabV ctx f | eqF
... | success _ _ _ _ _ , _ | refl
    with checkElabV ctx x A | eqX
...   | success _ _ _ _ , _ | refl = _ , _ , _ , refl

infer-complete-RApp-eff :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (A : Type) {B : Type}
    {Ψf : Surface.Usage (NamedCtx.size ctx)}
    {fE : SExpr (NamedCtx.debruijn ctx) Ψf (A T.⇒[ T.mk-kind T.Many T.eff ] B)}
    {df ff : ℕ}
    {Ψx : Surface.Usage (NamedCtx.size ctx)}
    {xE : SExpr (NamedCtx.debruijn ctx) Ψx A}
    {dx fx : ℕ}
  → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) Ψf fE df ff
  → checkElab ctx x A ≡ success Ψx xE dx fx
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x)
        ≡ success (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] B) (Ψf +ᵘ Ψx) eE d f'
infer-complete-RApp-eff {ctx} f x A {B} eqAH eqF eqX
  rewrite cong proj₁ (viewBridge {ctx} {f} {x} ahv-other (classifyAppHead-nothing⇒view-other eqAH))
        | cong proj₁ (otherBridge {ctx} {f} {x} nothing eqAH)
  with inferElabV ctx f | eqF
... | success _ _ _ _ _ , _ | refl
    with checkElabV ctx x A | eqX
...   | success _ _ _ _ , _ | refl = _ , _ , _ , refl

------------------------------------------------------------------------
-- Effectful RApp completeness
--
-- Same structure as `infer-complete-RApp-generic` but for the case
-- where `f : Eff A B`. After `classifyAppHead-nothing⇒view-other`
-- exposes the `ahv-other` branch, `asFun` sees `success (A ⇒[ mk-kind Many eff ] B) ...`
-- and takes the `isEff` case; the body mirrors `isFun` but emits
-- `Surface.effApp`. The check-mode fallback is
-- `checkElab-fallback-RApp-generic`, reusable as-is because its
-- statement only mentions the outer `inferElab (RApp f x)`, not the
-- inner function-vs-effect dispatch.
------------------------------------------------------------------------

-- (defined above with infer-complete-RApp-generic)

------------------------------------------------------------------------
-- Full-walk completeness — enabled by the G2(a) judgment split
--
-- With mutual ⊢ᵢ / ⊢ᶜ judgments and the `classifyAppHead f ≡ nothing`
-- premise on `t-app`, the two mismatches that previously blocked a
-- full walk are now structural invariants:
--   * t-lam lives only in ⊢ᶜ, so infer-mode sub-derivations can't
--     use it.
--   * t-app doesn't shadow the polymorphic-builtin specialisations.
--
-- The walk is a direct mutual structural recursion on derivations.
------------------------------------------------------------------------

-- (Judgment is already fully opened at the top of this file; the morphism realm
-- `_⊢ᵐ_∶_⇨_`, `t-morph-lift`, and the `m-*` constructors are in scope from there.
-- The former redundant `using`-list re-open was removed in the D063 collapse.)


------------------------------------------------------------------------
-- Mutual full walk (G2 completeness — both directions)
--
-- With the `AppHeadView` refactor unblocking `checkElab-fallback-RApp-
-- generic` and the removal of the specialised bare-builtin check-mode
-- clauses (G2 decision) eliminating the RVar-shadow impedance, the
-- walk now closes.
------------------------------------------------------------------------

open Once.TypeCheck.Elaborate
  using (checkElab-fallback-RInt; checkElab-fallback-RStringLit;
         checkElab-fallback-RUnit; checkElab-fallback-RVar-unit;
         checkElab-fallback-RVar-id; checkElab-fallback-RVar-fst;
         checkElab-fallback-RVar-snd; checkElab-fallback-RVar-terminal;
         checkElab-fallback-RVar-initial; checkElab-fallback-RVar-inl;
         checkElab-fallback-RVar-inr;
         checkElab-fallback-RApp-In; checkElab-fallback-RApp-apply;
         checkElab-fallback-RApp-arr;
         checkElab-fallback-RVar-poly;
         checkElab-fallback-RQualified; checkElab-fallback-RAnnot;
         checkElab-fallback-RLet;
         checkElab-fallback-RDestruct; checkElab-fallback-RUnaryOp;
         checkElab-fallback-RBinOp;
         checkElab-fallback-RApp-id; checkElab-fallback-RApp-fst;
         checkElab-fallback-RApp-snd; checkElab-fallback-RApp-terminal;
         checkElab-fallback-RApp-generic)

-- RVar case: covers both local and import lookups (and "unit"). The
-- fallback lemma takes the inferElab-success equation uniformly.
--
-- Plan 0.6 Phase C.7: `checkElab-RVar` dispatches via
-- `classifyBareBuiltin x` to specialised clauses for each bare
-- polymorphic builtin. The proof mirrors this dispatch — each
-- specialised case rewrites by `eqInf` (pushing lookup-success
-- through), then discharges the `T ≟T T` guard. The proof is
-- uniform across all specialised names because each specialised
-- clause's lookup-success branch is identical in shape.
checkElab-fallback-RVar :
  ∀ {ctx : NamedCtx} (x : String) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : _} {d f : ℕ}
  → inferElab ctx (Raw.RVar x) ≡ success T Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RVar x) T ≡ success Ψ eE' d' f'
checkElab-fallback-RVar {ctx} x T eqInf
  with classifyBareBuiltin x
... | bbc-id with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-fst with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-snd with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-terminal with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-initial with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-inl with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-inr with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-arr with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)
checkElab-fallback-RVar {ctx} x T eqInf
    | bbc-other with inferElabV ctx (Raw.RVar x) | eqInf
...   | success _ _ _ _ _ , _ | refl with T ≟T T
...     | yes refl = _ , _ , _ , refl
...     | no ¬eq   = ⊥-elim (¬eq refl)

-- Plan 0.4 T0 (2026-04-30): completeness gaps for t-embed of
-- t-arr-app-infer / t-apply-app-infer. The elaborator's check-mode
-- for these uses specialised dispatches that don't transport via
-- inferElab → checkElab catchall. The natural fix is recursion on
-- check-complete (t-embed d), which is structurally smaller — but
-- Agda's mutual termination checker rejects it. Soundness is fully
-- proven (sound-RApp-arr, sound-RApp-apply); this gap is on the
-- completeness side only.
-- Completeness-gap-* helpers (formerly postulates) — given a checkElab/
-- inferElab equation on the sub-expression(s), produce the outer
-- checkElab equation. The proofs walk checkElabV-RApp-dispatch at the
-- corresponding ahv-X branch.
completeness-gap-inl-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ A}
    {d f : ℕ}
  → checkElab ctx arg A ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (RVar "inl") arg) (A T.+ B)
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-inl-app-check-eq {ctx} arg A B eqC
  with checkElabV ctx arg A | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

completeness-gap-inr-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ B}
    {d f : ℕ}
  → checkElab ctx arg B ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (RVar "inr") arg) (A T.+ B)
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-inr-app-check-eq {ctx} arg A B eqC
  with checkElabV ctx arg B | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

completeness-gap-initial-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ T.Void}
    {d f : ℕ}
  → checkElab ctx arg T.Void ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (RVar "initial") arg) T
        ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE' d' f'
completeness-gap-initial-app-check-eq {ctx} arg T eqC
  with checkElabV ctx arg T.Void | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

completeness-gap-arr-app-check-eq :
  ∀ {ctx : NamedCtx} (arg : RawExpr) (A B : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : SExpr (NamedCtx.debruijn ctx) Ψ (A T.⇒[ T.mk-kind T.Many T.pure ] B)}
    {d f : ℕ}
  → checkElab ctx arg (A T.⇒[ T.mk-kind T.Many T.pure ] B) ≡ success Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RApp (RVar "arr") arg)
                    (A T.⇒[ T.mk-kind T.Many T.eff ] B)
        ≡ success Ψ eE' d' f'
completeness-gap-arr-app-check-eq {ctx} arg A B eqC
  with checkElabV ctx arg (A T.⇒[ T.mk-kind T.Many T.pure ] B) | eqC
... | success _ _ _ _ , _ | refl = _ , _ , _ , refl

postulate
  completeness-gap-arr-check :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ (A T.⇒[ T.mk-kind T.Many T.pure ] B) ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RApp (RVar "arr") e)
                      (A T.⇒[ T.mk-kind T.Many T.eff ] B)
          ≡ success Ψ eE d f
  completeness-gap-apply-check :
    ∀ {ctx : NamedCtx} {p : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ p ∶ ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A) ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RApp (RVar "apply") p) B
          ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
  completeness-gap-arg-driven-app-check :
    ∀ {ctx : NamedCtx} {f arg : RawExpr} {X T : Type}
      {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
    → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
    → ctx ⊢ᵢ arg ∶ X ⨾ Ψ₂
    → ctx ⊢ᶜ f ∶ (X T.⇒[ T.mk-kind T.Many T.pure ] T) ⨾ Ψ₁
    → ∃[ eE ] ∃[ d ] ∃[ fr ]
        checkElab ctx (Raw.RApp f arg) T
          ≡ success (Ψ₁ +ᵘ (T.Many *ᵘ Ψ₂)) eE d fr

mutual
  infer-complete :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        inferElab ctx e ≡ success A Ψ eE d f

  infer-complete {ctx} (t-int n)   = infer-complete-RInt {ctx} n
  infer-complete {ctx} (t-str s)   = infer-complete-RStringLit {ctx} s
  infer-complete {ctx} t-unit      = infer-complete-RUnit {ctx}
  infer-complete {ctx} t-unit-var  = infer-complete-RVar-unit {ctx}
  infer-complete (t-var-local {x = x} x≢unit eqLocal) =
    infer-complete-RVar-local x x≢unit eqLocal
  infer-complete {ctx} (t-var-qualified {name = name} {alias = alias} eqImp) =
    infer-complete-RQualified {ctx} {name} {alias} eqImp
  infer-complete (t-var-import {x = x} x≢unit eqLoc eqImp) =
    infer-complete-RVar-import x x≢unit eqLoc eqImp
  infer-complete (t-annot {e = e} {T = T} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in infer-complete-RAnnot e T eqC
  infer-complete (t-pair {a = a} {b = b} d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RPair a b eq₁ eq₂
  infer-complete (t-neg {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RUnaryOp-neg e eqSub
  infer-complete (t-let {x = x} {e₁ = e₁} {e₂ = e₂} d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RLet x e₁ e₂ eq₁ eq₂
  infer-complete
    (t-case {scrut = scrut} {eL = eL} {eR = eR} {xL = xL} {xR = xR} {C = C}
            dS dL dR) =
    let (_ , _ , _ , eqS) = infer-complete dS
        (_ , _ , _ , eqL) = infer-complete dL
        (_ , _ , _ , eqR) = infer-complete dR
    in infer-complete-RDestruct scrut xL eL xR eR C eqS eqL eqR
  infer-complete
    (t-binop-arith {op = op} {e₁ = e₁} {e₂ = e₂} arithEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-arith op arithEq e₁ e₂ eq₁ eq₂
  infer-complete
    (t-binop-cmp {op = op} {e₁ = e₁} {e₂ = e₂} cmpEq d₁ d₂) =
    let (_ , _ , _ , eq₁) = infer-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in infer-complete-RBinOp-cmp op cmpEq e₁ e₂ eq₁ eq₂
  infer-complete (t-id-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-id e eqSub
  infer-complete (t-fst-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-fst e eqSub
  infer-complete (t-snd-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-snd e eqSub
  infer-complete (t-terminal-app {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-terminal e eqSub
  infer-complete (t-arr-app-infer {e = e} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-arr e eqSub
  infer-complete (t-apply-app-infer {p = p} {A = A} d) =
    let (_ , _ , _ , eqSub) = infer-complete d
    in infer-complete-RApp-apply p A eqSub
  -- Plan 0.4 T1, change 1: dX is now a check-mode derivation
  -- (per the t-app/t-effApp signature changes in Judgment).
  -- check-complete gives us the checkElab evidence directly.
  infer-complete (t-app {f = f} {x = x} {A = A} notPoly dF dX) =
    let (_ , _ , _ , eqF) = infer-complete dF
        (_ , _ , _ , eqX) = check-complete dX
    in infer-complete-RApp-generic f x A notPoly eqF eqX
  infer-complete (t-effApp {f = f} {x = x} {A = A} notPoly dF dX) =
    let (_ , _ , _ , eqF) = infer-complete dF
        (_ , _ , _ , eqX) = check-complete dX
    in infer-complete-RApp-eff f x A notPoly eqF eqX

  -- Plan 0.49 / D063: the MORPHISM-COMPLETENESS theorem. A `⊢ᵐ` morphism
  -- check-elaborates at its arrow type (any grade π). TRUE — provable by
  -- induction on `⊢ᵐ` (bare builtins → `checkElab-fallback-RVar-*`; compose/
  -- case/pair/curry → the new fused `checkX` succeed on morphism arms; cata →
  -- `checkCataGo`; leaves m-const/m-named/m-lam → value/import/lambda paths).
  -- This SINGLE postulate REPLACES the three former false/dead postulates
  -- (`cata-check-complete`, `case-copair-eff-complete`, `compose-eff-complete`) —
  -- restoring consistency (the old eff ones were FALSE). Discharge = C3 follow-up.
  -- `morph-complete` (Plan 0.49 / D063) is now PROVEN in Once.TypeCheck.MorphComplete
  -- (imported above): induction on ⊢ᵐ, 12/15 cases discharged; m-const/m-cata/m-named
  -- remain scoped postulates there (the latter pending plan 0.50).
  postulate
    -- Plan 0.36 Phase 2a follow-up — TRANSIENT, PROVABLE: pair-literal
    -- check-mode completeness. `checkElabV (RPair a b) (A * B)` reduces
    -- via `checkPairLit` to `success (Surface.pair …)` given the two
    -- component check-mode derivations.
    pair-lit-check-complete : ∀ {ctx : NamedCtx} {a b : RawExpr} {A B : Type}
      {Ψ₁ Ψ₂ : Surface.Usage (NamedCtx.size ctx)}
      → ctx ⊢ᶜ a ∶ A ⨾ Ψ₁
      → ctx ⊢ᶜ b ∶ B ⨾ Ψ₂
      → ∃[ eE ] ∃[ d ] ∃[ f ]
          checkElab ctx (Raw.RPair a b) (A * B)
            ≡ success (Ψ₁ +ᵘ Ψ₂) eE d f

  -- `nothing ≡ just _` is absurd — returns any goal type (no `⊥` import needed).
  nothing≢just : ∀ {ℓ} {A : Set ℓ} {x : A} {C : Set} → nothing ≡ just x → C
  nothing≢just ()

  -- Plan 0.42: `checkG` succeeds on any closed global-element value. By
  -- induction on the `⊢ᵍ` derivation: leaves reduce directly; structural cases
  -- `rewrite` the recursive equations so `checkG`'s `with checkG …` reduces to
  -- `just`. The extractable family is total under `checkG` — load-bearing for
  -- `gd-complete`.
  checkG-just : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type} (X : Type)
              → (gd : ctx ⊢ᵍ e ∶ A)
              → ∃[ m ] ∃[ gd' ] checkG ctx X e A ≡ just (m , gd')
  checkG-just X (g-int n) = _ , _ , refl
  checkG-just {ctx = ctx} X (g-terminal eqL eqI)
    with inspectLookupLocal ctx "terminal" | inspectLookupImport ctx "terminal"
  ... | llv-not-found _ | liv-not-found _ = _ , _ , refl
  ... | llv-found eqL2  | _               = nothing≢just (trans (sym eqL) eqL2)
  ... | llv-not-found _ | liv-found eqI2  = nothing≢just (trans (sym eqI) eqI2)
  checkG-just X (g-pair ga gb) with checkG-just X ga | checkG-just X gb
  ... | _ , _ , eqa | _ , _ , eqb rewrite eqa | eqb = _ , _ , refl
  checkG-just X (g-inl ga) with checkG-just X ga
  ... | _ , _ , eqa rewrite eqa = _ , _ , refl
  checkG-just X (g-inr gb) with checkG-just X gb
  ... | _ , _ , eqb rewrite eqb = _ , _ , refl
  checkG-just X (g-In {F = F} eqWF garg) with inspectWellFormedF F | checkG-just X garg
  ... | wfv-yes _   | _ , _ , eqarg rewrite eqarg = _ , _ , refl
  ... | wfv-no eqNo | _                           = nothing≢just (trans (sym eqNo) eqWF)

  -- Plan 0.42: the `⊢ᵍ` completeness — a closed global-element value elaborates
  -- at a pure arrow. POSTULATE-FREE. `g-int` is the direct `RInt` clause;
  -- `g-terminal` routes through the existing bare-`terminal` fallback; the
  -- structural shapes (`g-pair`/`g-inl`/`g-inr`/`g-In`) scrutinise the SAME
  -- `inspectCheckG` view as their value-lift `checkElabV` clauses, so the
  -- elaborator reduces (no `with checkG` opacity). `checkG-just` rules out the
  -- `cgv-nothing` branch (the value IS a `checkG`-success).
  gd-complete : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type} (X : Type)
              → ctx ⊢ᵍ e ∶ A
              → ∃[ eE ] ∃[ d ] ∃[ f' ]
                  checkElab ctx e (X T.⇒[ T.mk-kind T.Many T.pure ] A)
                    ≡ success Surface.zeroUsage eE d f'
  gd-complete X (g-int n) = _ , _ , _ , refl
  gd-complete {ctx = ctx} X (g-terminal eqL eqI) =
    checkElab-fallback-RVar-terminal {ctx} X eqL eqI
  gd-complete {ctx = ctx} X (g-pair {a = a} {b = b} {A = A} {B = B} ga gb)
    with inspectCheckG ctx X (Raw.RPair a b) (A T.* B) | checkG-just X (g-pair ga gb)
  ... | cgv-just _      | _              = _ , _ , _ , refl
  ... | cgv-nothing eqN | _ , _ , eqJ    = nothing≢just (trans (sym eqN) eqJ)
  gd-complete {ctx = ctx} X (g-inl {arg = arg} {A = A} {B = B} ga)
    with inspectCheckG ctx X (Raw.RApp (Raw.RVar "inl") arg) (A T.+ B) | checkG-just X (g-inl ga)
  ... | cgv-just _      | _              = _ , _ , _ , refl
  ... | cgv-nothing eqN | _ , _ , eqJ    = nothing≢just (trans (sym eqN) eqJ)
  gd-complete {ctx = ctx} X (g-inr {arg = arg} {A = A} {B = B} gb)
    with inspectCheckG ctx X (Raw.RApp (Raw.RVar "inr") arg) (A T.+ B) | checkG-just X (g-inr gb)
  ... | cgv-just _      | _              = _ , _ , _ , refl
  ... | cgv-nothing eqN | _ , _ , eqJ    = nothing≢just (trans (sym eqN) eqJ)
  gd-complete {ctx = ctx} X (g-In {arg = arg} {F = F} eqWF garg)
    with inspectCheckG ctx X (Raw.RApp (Raw.RVar "In") arg) (T.μ-type F) | checkG-just X (g-In eqWF garg)
  ... | cgv-just _      | _              = _ , _ , _ , refl
  ... | cgv-nothing eqN | _ , _ , eqJ    = nothing≢just (trans (sym eqN) eqJ)

  -- Full ⊢ᶜ walk: handles t-lam recursively and delegates t-embed
  -- to the per-shape fallback lemma.
  check-complete :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ e ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx e A ≡ success Ψ eE d f

  check-complete {ctx}
    (t-lam {x = x} {body = body} {A = A} {B = B} {q = q} {q' = q'}
           leq-eq bodyD) =
    let (_ , _ , _ , eqBody) = check-complete bodyD
    in check-complete-RLam ctx x body A q q' B leq-eq eqBody

  -- t-embed: case-split on the inner ⊢ᵢ derivation to recover e's
  -- shape, then invoke the matching fallback lemma.
  check-complete {ctx} (t-embed (t-int n))   = checkElab-fallback-RInt {ctx} n
  check-complete {ctx} (t-embed (t-str s))   = checkElab-fallback-RStringLit {ctx} s
  check-complete {ctx} (t-embed t-unit)      = checkElab-fallback-RUnit {ctx}
  check-complete {ctx} (t-embed t-unit-var)  = checkElab-fallback-RVar-unit {ctx}
  check-complete (t-embed (t-var-local {x = x} {A = T} x≢unit eqLocal)) =
    let (_ , _ , _ , eqI) = infer-complete (t-var-local x≢unit eqLocal)
    in checkElab-fallback-RVar x T eqI
  check-complete {ctx}
    (t-embed (t-var-qualified {name = n} {alias = a} {T = T} eqImp)) =
    let (_ , _ , _ , eqI) = infer-complete {ctx} (t-var-qualified eqImp)
    in checkElab-fallback-RQualified {ctx} n a T eqI
  check-complete (t-embed (t-var-import {x = x} {T = T} x≢unit eqLoc eqImp)) =
    let (_ , _ , _ , eqI) = infer-complete (t-var-import x≢unit eqLoc eqImp)
    in checkElab-fallback-RVar x T eqI
  check-complete (t-embed (t-annot {e = e} {T = T} d)) =
    let (_ , _ , _ , eqI) = infer-complete (t-annot d)
    in checkElab-fallback-RAnnot e T eqI
  -- Plan 0.36 Phase 2a: RPair check-mode now goes through `checkPairLit`
  -- (bidirectional). Route the embedded-infer pair through the same
  -- pair-literal bridge by re-embedding the component infer derivations.
  check-complete (t-embed (t-pair {a = a} {b = b} {A = A} {B = B} d₁ d₂)) =
    pair-lit-check-complete (t-embed d₁) (t-embed d₂)
  check-complete (t-embed (t-neg {e = e} d)) =
    let (_ , _ , _ , eqI) = infer-complete (t-neg d)
    in checkElab-fallback-RUnaryOp Raw.OpNeg e T.Int eqI
  check-complete (t-embed (t-let {x = x} {e₁ = e₁} {e₂ = e₂} {B = B} d₁ d₂)) =
    let (_ , _ , _ , eqI) = infer-complete (t-let d₁ d₂)
    in checkElab-fallback-RLet x e₁ e₂ B eqI
  check-complete (t-embed (t-case {scrut = scrut} {eL = eL} {eR = eR}
                                   {xL = xL} {xR = xR} {C = C} dS dL dR)) =
    let (_ , _ , _ , eqI) = infer-complete (t-case dS dL dR)
    in checkElab-fallback-RDestruct scrut xL eL xR eR C eqI
  check-complete (t-embed (t-binop-arith {op = op} {e₁ = e₁} {e₂ = e₂}
                                          arithEq d₁ d₂)) =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-arith arithEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ T.Int eqI
  check-complete (t-embed (t-binop-cmp {op = op} {e₁ = e₁} {e₂ = e₂}
                                        cmpEq d₁ d₂)) =
    let (_ , _ , _ , eqI) = infer-complete (t-binop-cmp cmpEq d₁ d₂)
    in checkElab-fallback-RBinOp op e₁ e₂ (Unit T.+ Unit) eqI
  check-complete (t-embed (t-id-app {e = e} {T = T} d)) =
    let (_ , _ , _ , eqI) = infer-complete (t-id-app d)
    in checkElab-fallback-RApp-id e T eqI
  check-complete (t-embed (t-fst-app {e = e} {A = A} d)) =
    let (_ , _ , _ , eqI) = infer-complete (t-fst-app d)
    in checkElab-fallback-RApp-fst e A eqI
  check-complete (t-embed (t-snd-app {e = e} {B = B} d)) =
    let (_ , _ , _ , eqI) = infer-complete (t-snd-app d)
    in checkElab-fallback-RApp-snd e B eqI
  check-complete (t-embed (t-terminal-app {e = e} d)) =
    let (_ , _ , _ , eqI) = infer-complete (t-terminal-app d)
    in checkElab-fallback-RApp-terminal e Unit eqI
  -- Plan 0.4 T0 (2026-04-30): t-embed of t-arr-app-infer.
  -- The elaborator's check-mode for `arr e` uses ahv-arr-check (a
  -- specialised path) which calls checkElab on `e` rather than
  -- transporting via inferElab. So the existing
  -- checkElab-fallback-RApp-generic (which assumes catchall transport)
  -- doesn't apply. The natural recursion `check-complete (t-embed d)`
  -- to obtain checkElab evidence on `e` triggers a termination-checker
  -- false-negative (the recursive arg is structurally smaller, but
  -- the lex measure is confused by the mutual block + projection
  -- pattern). Postulated as a completeness gap; soundness for
  -- t-arr-app-infer / t-apply-app-infer is fully proven via
  -- sound-RApp-arr / sound-RApp-apply.
  check-complete (t-embed (t-arr-app-infer d)) =
    completeness-gap-arr-check d
  check-complete (t-embed (t-apply-app-infer d)) =
    completeness-gap-apply-check d
  check-complete (t-embed (t-app {f = f} {x = x} {B = B} notPoly dF dX)) =
    let (_ , _ , _ , eqI) = infer-complete (t-app notPoly dF dX)
    in checkElab-fallback-RApp-generic f x B notPoly eqI
  check-complete (t-embed (t-effApp {f = f} {x = x} {B = B} notPoly dF dX)) =
    let (_ , _ , _ , eqI) = infer-complete (t-effApp notPoly dF dX)
    in checkElab-fallback-RApp-generic f x (T.Unit T.⇒[ T.mk-kind T.Many T.eff ] B) notPoly eqI
  -- Plan 0.6 Phase C.7 POC-1: bare `id` check-mode. The derivation's
  -- Plan 0.41: the value-lift bridge. A closed global-element value (`⊢ᵍ`)
  -- elaborates at the pure arrow — recurses on the `⊢ᵍ` derivation via
  -- `gd-complete` (the extractable family always elaborates).
  check-complete {ctx} (t-value-lift {X = X} gd) = gd-complete X gd
  -- Plan 0.49 / D063: the morphism bridge. A `⊢ᵐ` morphism check-elaborates at
  -- its arrow type — by `morph-complete` (induction on `⊢ᵐ`). This ONE clause
  -- subsumes the 13 deleted combinator clauses and REPLACES the two false
  -- `*-eff-complete` postulates with a single TRUE one.
  check-complete (t-morph-lift d) = morph-complete d
  check-complete (t-In-app-check {arg = arg} {F = F} eqWF dArg) =
    let (_ , _ , _ , eqA) = check-complete dArg
    in checkElab-fallback-RApp-In arg F eqWF eqA
  check-complete (t-pair-lit-check {a = a} {b = b} {A = A} {B = B} dA dB) =
    pair-lit-check-complete dA dB
  check-complete (t-apply-check {p = p} {A = A} {B = B} d) =
    let (_ , _ , _ , eq) = infer-complete d
    in checkElab-fallback-RApp-apply p A B eq
  -- Plan 0.4 T0 Phase F new check-mode rules — discharged by
  -- completeness-gap-*-eq helpers above (recursive check-complete on
  -- the sub-derivation produces the bridging checkElab equation).
  check-complete (t-inl-app-check {arg = arg} {A = A} {B = B} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-inl-app-check-eq arg A B eqC
  check-complete (t-inr-app-check {arg = arg} {A = A} {B = B} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-inr-app-check-eq arg A B eqC
  check-complete (t-initial-app-check {arg = arg} {T = T} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-initial-app-check-eq arg T eqC
  check-complete (t-arr-app-check {arg = arg} {A = A} {B = B} d) =
    let (_ , _ , _ , eqC) = check-complete d
    in completeness-gap-arr-app-check-eq arg A B eqC
  check-complete (t-arg-driven-app-check notPoly dArg dF) =
    completeness-gap-arg-driven-app-check notPoly dArg dF

  -- Plan 0.6.2 Phase 4: polymorphic schema-instantiation. Threads
  -- the body's check-mode derivation through `check-complete`,
  -- then composes with the lookup premises via the helper.
  check-complete {ctx}
    (t-var-poly-instantiate {x = x} {T = T} bbcOther x≢unit localN importN polyE bodyD) =
    let (_ , _ , _ , eqBody) = check-complete bodyD
    in checkElab-fallback-RVar-poly {ctx} x T bbcOther x≢unit localN importN polyE eqBody
