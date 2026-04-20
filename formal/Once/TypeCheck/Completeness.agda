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
infer-complete-RVar-local {ctx} x x≢unit eqLocal
  with x Data.String.Properties.≟ "unit"
... | yes p = ⊥-elim (x≢unit p)
... | no  _ rewrite eqLocal =
  _ , 0 , NamedCtx.freshCounter ctx , refl

infer-complete-RVar-import :
  ∀ {ctx : NamedCtx} (x : String) {T : Type}
  → ¬ (x ≡ "unit")
  → lookupLocal ctx x ≡ nothing
  → lookupImport (NamedCtx.imports ctx) x ≡ just T
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      inferElab ctx (RVar x) ≡ success T zeroUsage eE d f
infer-complete-RVar-import {ctx} x x≢unit eqLoc eqImp
  with x Data.String.Properties.≟ "unit"
... | yes p = ⊥-elim (x≢unit p)
... | no  _ rewrite eqLoc | eqImp =
  Surface.prim x , 0 , NamedCtx.freshCounter ctx , refl

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
-- Proof: case-split on `op` and each concrete arith op reduces the
-- outer elaborator's `if` to the `then` (success Int ...) branch.
infer-complete-RBinOp-arith Raw.OpAdd _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-arith Raw.OpSub _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-arith Raw.OpMul _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-arith Raw.OpDiv _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-arith Raw.OpMod _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
-- Comparison ops are excluded by `arithEq`: the premise says
-- `isArithmeticOp op ≡ true`, which is `false` for cmp ops,
-- so those cases are unreachable via the absurd pattern on arithEq.
infer-complete-RBinOp-arith Raw.OpLt ()
infer-complete-RBinOp-arith Raw.OpLe ()
infer-complete-RBinOp-arith Raw.OpGt ()
infer-complete-RBinOp-arith Raw.OpGe ()
infer-complete-RBinOp-arith Raw.OpEq ()
infer-complete-RBinOp-arith Raw.OpNe ()

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
infer-complete-RBinOp-cmp Raw.OpLt _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-cmp Raw.OpLe _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-cmp Raw.OpGt _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-cmp Raw.OpGe _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-cmp Raw.OpEq _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-cmp Raw.OpNe _ e₁ e₂ eq₁ eq₂ rewrite eq₁ | eq₂ = _ , _ , _ , refl
infer-complete-RBinOp-cmp Raw.OpAdd ()
infer-complete-RBinOp-cmp Raw.OpSub ()
infer-complete-RBinOp-cmp Raw.OpMul ()
infer-complete-RBinOp-cmp Raw.OpDiv ()
infer-complete-RBinOp-cmp Raw.OpMod ()

------------------------------------------------------------------------
-- RLam check mode
------------------------------------------------------------------------

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
      checkElab ctx (Raw.RLam x body) (A T.⇒[ q ] B) ≡ success Ψ' eE d f
-- Enumerate the 9 (q, q') pairs; 6 have `q' ≤q q = true` and
-- admit the success; 3 have `q' ≤q q = false` and are ruled out
-- by the `leq-eq : q' ≤q q ≡ true` premise (absurd pattern `()`).
-- Arg order: ctx x body A (q : arrow grade) (q' : body-usage qty) B.
check-complete-RLam ctx x body A T.Zero T.Zero B leq-eq eqBody rewrite eqBody = _ , _ , _ , refl
check-complete-RLam ctx x body A T.One  T.Zero B leq-eq eqBody rewrite eqBody = _ , _ , _ , refl
check-complete-RLam ctx x body A T.One  T.One  B leq-eq eqBody rewrite eqBody = _ , _ , _ , refl
check-complete-RLam ctx x body A T.Many T.Zero B leq-eq eqBody rewrite eqBody = _ , _ , _ , refl
check-complete-RLam ctx x body A T.Many T.One  B leq-eq eqBody rewrite eqBody = _ , _ , _ , refl
check-complete-RLam ctx x body A T.Many T.Many B leq-eq eqBody rewrite eqBody = _ , _ , _ , refl
-- Absurd: q' ≤q q = false makes leq-eq uninhabited.
check-complete-RLam ctx x body A T.Zero T.One  B ()     eqBody
check-complete-RLam ctx x body A T.Zero T.Many B ()     eqBody
check-complete-RLam ctx x body A T.One  T.Many B ()     eqBody

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
infer-complete-RDestruct scrut xL eL xR eR C eqS eqL eqR
  rewrite eqS | eqL | eqR with Once.TypeCheck.Elaborate._≟T_ C C
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

------------------------------------------------------------------------
-- Generic RApp
------------------------------------------------------------------------

infer-complete-RApp-generic :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (A : Type) {B : Type} {q : Quantity}
    {Ψf : Surface.Usage (NamedCtx.size ctx)}
    {fE : SExpr (NamedCtx.debruijn ctx) Ψf (A T.⇒[ q ] B)}
    {df ff : ℕ}
    {Ψx : Surface.Usage (NamedCtx.size ctx)}
    {xE : SExpr (NamedCtx.debruijn ctx) Ψx A}
    {dx fx : ℕ}
  → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (A T.⇒[ q ] B) Ψf fE df ff
  → inferElab ctx x ≡ success A Ψx xE dx fx
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x)
        ≡ success B (Ψf +ᵘ (q *ᵘ Ψx)) eE d f'
infer-complete-RApp-generic f x A notPoly eqF eqX
  rewrite Once.TypeCheck.Elaborate.classifyAppHead-nothing⇒view-other {f} notPoly
        | eqF | eqX with Once.TypeCheck.Elaborate._≟T_ A A
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

------------------------------------------------------------------------
-- Effectful RApp completeness
--
-- Same structure as `infer-complete-RApp-generic` but for the case
-- where `f : Eff A B`. After `classifyAppHead-nothing⇒view-other`
-- exposes the `ahv-other` branch, `asFun` sees `success (Eff A B) ...`
-- and takes the `isEff` case; the body mirrors `isFun` but emits
-- `Surface.effApp`. The check-mode fallback is
-- `checkElab-fallback-RApp-generic`, reusable as-is because its
-- statement only mentions the outer `inferElab (RApp f x)`, not the
-- inner function-vs-effect dispatch.
------------------------------------------------------------------------

infer-complete-RApp-eff :
  ∀ {ctx : NamedCtx} (f x : RawExpr) (A : Type) {B : Type}
    {Ψf : Surface.Usage (NamedCtx.size ctx)}
    {fE : SExpr (NamedCtx.debruijn ctx) Ψf (T.Eff A B)}
    {df ff : ℕ}
    {Ψx : Surface.Usage (NamedCtx.size ctx)}
    {xE : SExpr (NamedCtx.debruijn ctx) Ψx A}
    {dx fx : ℕ}
  → Once.TypeCheck.Elaborate.classifyAppHead f ≡ nothing
  → inferElab ctx f ≡ success (T.Eff A B) Ψf fE df ff
  → inferElab ctx x ≡ success A Ψx xE dx fx
  → ∃[ eE ] ∃[ d ] ∃[ f' ]
      inferElab ctx (Raw.RApp f x)
        ≡ success (T.Eff T.Unit B) (Ψf +ᵘ Ψx) eE d f'
infer-complete-RApp-eff f x A notPoly eqF eqX
  rewrite Once.TypeCheck.Elaborate.classifyAppHead-nothing⇒view-other {f} notPoly
        | eqF | eqX with Once.TypeCheck.Elaborate._≟T_ A A
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

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
         t-embed; t-lam)


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
         checkElab-fallback-RQualified; checkElab-fallback-RAnnot;
         checkElab-fallback-RPair; checkElab-fallback-RLet;
         checkElab-fallback-RDestruct; checkElab-fallback-RUnaryOp;
         checkElab-fallback-RBinOp;
         checkElab-fallback-RApp-id; checkElab-fallback-RApp-fst;
         checkElab-fallback-RApp-snd; checkElab-fallback-RApp-terminal;
         checkElab-fallback-RApp-generic)

-- RVar case: covers both local and import lookups (and "unit"). The
-- fallback lemma takes the inferElab-success equation uniformly.
checkElab-fallback-RVar :
  ∀ {ctx : NamedCtx} (x : String) (T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    {eE : _} {d f : ℕ}
  → inferElab ctx (Raw.RVar x) ≡ success T Ψ eE d f
  → ∃[ eE' ] ∃[ d' ] ∃[ f' ]
      checkElab ctx (Raw.RVar x) T ≡ success Ψ eE' d' f'
checkElab-fallback-RVar x T eqInf
  rewrite eqInf with Once.TypeCheck.Elaborate._≟T_ T T
... | yes refl = _ , _ , _ , refl
... | no ¬eq   = ⊥-elim (¬eq refl)

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
  infer-complete (t-var-qualified eqImp) =
    infer-complete-RQualified eqImp
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
  infer-complete (t-app {f = f} {x = x} {A = A} notPoly dF dX) =
    let (_ , _ , _ , eqF) = infer-complete dF
        (_ , _ , _ , eqX) = infer-complete dX
    in infer-complete-RApp-generic f x A notPoly eqF eqX
  infer-complete (t-effApp {f = f} {x = x} {A = A} notPoly dF dX) =
    let (_ , _ , _ , eqF) = infer-complete dF
        (_ , _ , _ , eqX) = infer-complete dX
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
  check-complete (t-embed (t-app {f = f} {x = x} {B = B} notPoly dF dX)) =
    let (_ , _ , _ , eqI) = infer-complete (t-app notPoly dF dX)
    in checkElab-fallback-RApp-generic f x B notPoly eqI
  check-complete (t-embed (t-effApp {f = f} {x = x} {B = B} notPoly dF dX)) =
    let (_ , _ , _ , eqI) = infer-complete (t-effApp notPoly dF dX)
    in checkElab-fallback-RApp-generic f x (T.Eff T.Unit B) notPoly eqI
