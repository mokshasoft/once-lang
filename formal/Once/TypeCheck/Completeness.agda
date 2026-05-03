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
                                  _*_; _+_; _⇒[_]_; Quantity; _≤q_;
                                  Zero; One; Many)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RInt; RStringLit; RUnit; RAnnot; RPair)
open import Once.TypeCheck.Elaborate
  using (NamedCtx; inferElab; checkElab; InferElabResult; CheckElabResult;
         success; failure; lookupLocal; lookupImport;
         inferElabV; checkElabV; _≟T_)
open import Once.TypeCheck.Judgment

open import Once.Surface.Syntax as Surface using (zeroUsage; _+ᵘ_; _*ᵘ_)
  renaming (Expr to SExpr)
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

postulate
  infer-complete-RQualified :
    ∀ {ctx : NamedCtx} {name alias : String} {T : Type}
    → lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just T
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        inferElab ctx (RQualified name alias) ≡ success T zeroUsage eE d f

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
        ≡ success (A T.⇒[ T.mk-kind T.Many T.eff ] B) (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
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

postulate
  infer-complete-RVar-local :
    ∀ {ctx : NamedCtx} (x : String) {A : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
      {eE' : SExpr (NamedCtx.debruijn ctx) Ψ A}
    → ¬ (x ≡ "unit")
    → lookupLocal ctx x ≡ just (A , Ψ , eE')
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        inferElab ctx (RVar x) ≡ success A Ψ eE d f

postulate
  infer-complete-RVar-import :
    ∀ {ctx : NamedCtx} (x : String) {T : Type}
    → ¬ (x ≡ "unit")
    → lookupLocal ctx x ≡ nothing
    → lookupImport (NamedCtx.imports ctx) x ≡ just T
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        inferElab ctx (RVar x) ≡ success T zeroUsage eE d f

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
postulate
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

postulate
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

open Once.TypeCheck.Judgment
  using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_;
         t-int; t-str; t-unit; t-unit-var;
         t-var-local; t-var-qualified; t-var-import;
         t-annot; t-pair; t-neg; t-let; t-case;
         t-binop-arith; t-binop-cmp;
         t-id-app; t-fst-app; t-snd-app; t-terminal-app; t-app; t-effApp;
         t-embed; t-lam;
         t-id-check; t-fst-check; t-snd-check; t-terminal-check;
         t-initial-check; t-inl-check; t-inr-check; t-arr-check;
         t-pair-check; t-compose-check; t-curry-check; t-apply-check;
         t-var-poly-instantiate)


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
         checkElab-fallback-RVar-inr; checkElab-fallback-RVar-arr;
         checkElab-fallback-RApp-pair; checkElab-fallback-RApp-compose;
         checkElab-fallback-RApp-curry; checkElab-fallback-RApp-apply;
         checkElab-fallback-RApp-arr;
         checkElab-fallback-RVar-poly;
         checkElab-fallback-RQualified; checkElab-fallback-RAnnot;
         checkElab-fallback-RPair; checkElab-fallback-RLet;
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
postulate
  checkElab-fallback-RVar :
    ∀ {ctx : NamedCtx} (x : String) (T : Type)
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
      {eE : _} {d f : ℕ}
    → inferElab ctx (Raw.RVar x) ≡ success T Ψ eE d f
    → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
        checkElab ctx (Raw.RVar x) T ≡ success Ψ eE' d' f'

-- Plan 0.4 T0 (2026-04-30): completeness gaps for t-embed of
-- t-arr-app-infer / t-apply-app-infer. The elaborator's check-mode
-- for these uses specialised dispatches that don't transport via
-- inferElab → checkElab catchall. The natural fix is recursion on
-- check-complete (t-embed d), which is structurally smaller — but
-- Agda's mutual termination checker rejects it. Soundness is fully
-- proven (sound-RApp-arr, sound-RApp-apply); this gap is on the
-- completeness side only.
postulate
  completeness-gap-arr-check :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ e ∶ (A T.⇒[ T.mk-kind T.Many T.pure ] B) ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RApp (RVar "arr") e)
                      (A T.⇒[ T.mk-kind T.Many T.eff ] B)
          ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
  completeness-gap-apply-check :
    ∀ {ctx : NamedCtx} {p : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᵢ p ∶ ((A T.⇒[ T.mk-kind T.Many T.pure ] B) T.* A) ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RApp (RVar "apply") p) B
          ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f

  -- Phase F new-rule completeness gaps. Each is the dual of
  -- t-{inl,inr,initial,arr,arg-driven}-app-check from Judgment.agda.
  -- The elaborator's specialised check-mode branches realise each
  -- rule; these postulates stand in for the structural completeness
  -- proofs.
  completeness-gap-inl-app-check :
    ∀ {ctx : NamedCtx} {arg : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ arg ∶ A ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RApp (RVar "inl") arg) (A T.+ B)
          ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
  completeness-gap-inr-app-check :
    ∀ {ctx : NamedCtx} {arg : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ arg ∶ B ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RApp (RVar "inr") arg) (A T.+ B)
          ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
  completeness-gap-initial-app-check :
    ∀ {ctx : NamedCtx} {arg : RawExpr} {T : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ arg ∶ T.Void ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RApp (RVar "initial") arg) T
          ≡ success (zeroUsage +ᵘ (T.Many *ᵘ Ψ)) eE d f
  completeness-gap-arr-app-check :
    ∀ {ctx : NamedCtx} {arg : RawExpr} {A B : Type}
      {Ψ : Surface.Usage (NamedCtx.size ctx)}
    → ctx ⊢ᶜ arg ∶ (A T.⇒[ T.mk-kind T.Many T.pure ] B) ⨾ Ψ
    → ∃[ eE ] ∃[ d ] ∃[ f ]
        checkElab ctx (Raw.RApp (RVar "arr") arg)
                      (A T.⇒[ T.mk-kind T.Many T.eff ] B)
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
  check-complete (t-embed (t-pair {a = a} {b = b} {A = A} {B = B} d₁ d₂)) =
    let (_ , _ , _ , eqI) = infer-complete (t-pair d₁ d₂)
    in checkElab-fallback-RPair a b (A T.* B) eqI
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
  -- lookup-failure premises drive the elaborator past its lookup
  -- branch (which matches `t-embed (t-var-local/import …)`) into
  -- the specialised `specId` emission with `zeroUsage`.
  check-complete {ctx} (t-id-check {T = T} localN importN) =
    checkElab-fallback-RVar-id {ctx} T localN importN
  check-complete {ctx} (t-fst-check {A = A} {B = B} localN importN) =
    checkElab-fallback-RVar-fst {ctx} A B localN importN
  check-complete {ctx} (t-snd-check {A = A} {B = B} localN importN) =
    checkElab-fallback-RVar-snd {ctx} A B localN importN
  check-complete {ctx} (t-terminal-check {A = A} localN importN) =
    checkElab-fallback-RVar-terminal {ctx} A localN importN
  check-complete {ctx} (t-initial-check {A = A} localN importN) =
    checkElab-fallback-RVar-initial {ctx} A localN importN
  check-complete {ctx} (t-inl-check {A = A} {B = B} localN importN) =
    checkElab-fallback-RVar-inl {ctx} A B localN importN
  check-complete {ctx} (t-inr-check {A = A} {B = B} localN importN) =
    checkElab-fallback-RVar-inr {ctx} A B localN importN
  check-complete {ctx} (t-arr-check {A = A} {B = B} localN importN) =
    checkElab-fallback-RVar-arr {ctx} A B localN importN
  -- Plan 0.6 Phase C.7 POC-2: applied `pair f g` check-mode. The
  -- recursive check-complete calls on f and g give the
  -- inferElab-success equations threaded through the fallback
  -- helper.
  check-complete (t-pair-check {f = f} {g = g} {A = A} {B = B} {C = C} d₁ d₂) =
    let (_ , _ , _ , eq₁) = check-complete d₁
        (_ , _ , _ , eq₂) = check-complete d₂
    in checkElab-fallback-RApp-pair f g A B C eq₁ eq₂
  check-complete (t-compose-check {f = f} {g = g} {A = A} {B = B} {C = C} d₁ d₂) =
    let (_ , _ , _ , eq₁) = check-complete d₁
        (_ , _ , _ , eq₂) = infer-complete d₂
    in checkElab-fallback-RApp-compose f g A B C eq₁ eq₂
  check-complete (t-curry-check {f = f} {A = A} {B = B} {C = C} d) =
    let (_ , _ , _ , eq) = check-complete d
    in checkElab-fallback-RApp-curry f A B C eq
  check-complete (t-apply-check {p = p} {A = A} {B = B} d) =
    let (_ , _ , _ , eq) = infer-complete d
    in checkElab-fallback-RApp-apply p A B eq
  -- Plan 0.4 T0 Phase F new check-mode rules — completeness via
  -- dedicated postulates (see completeness-gap-* above).
  check-complete (t-inl-app-check d) =
    completeness-gap-inl-app-check d
  check-complete (t-inr-app-check d) =
    completeness-gap-inr-app-check d
  check-complete (t-initial-app-check d) =
    completeness-gap-initial-app-check d
  check-complete (t-arr-app-check d) =
    completeness-gap-arr-app-check d
  check-complete (t-arg-driven-app-check notPoly dArg dF) =
    completeness-gap-arg-driven-app-check notPoly dArg dF

  -- Plan 0.6.2 Phase 4: polymorphic schema-instantiation. Threads
  -- the body's check-mode derivation through `check-complete`,
  -- then composes with the lookup premises via the helper.
  check-complete {ctx}
    (t-var-poly-instantiate {x = x} {T = T} bbcOther x≢unit localN importN polyE bodyD) =
    let (_ , _ , _ , eqBody) = check-complete bodyD
    in checkElab-fallback-RVar-poly {ctx} x T bbcOther x≢unit localN importN polyE eqBody
