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
         t-id-app; t-fst-app; t-snd-app; t-terminal-app; t-app;
         t-embed; t-lam)


------------------------------------------------------------------------
-- Summary of completeness status (G2)
--
-- Status: per-rule completeness theorems (the `infer-complete-*` and
-- `check-complete-RLam` lemmas above) are complete, and the
-- `checkElab-fallback-*` helpers in `Elaborate.agda` (including the
-- RApp-generic case, unblocked by the `AppHeadView` refactor) supply
-- the building blocks for the mutual full-walk.
--
-- Deferred (plan 0.3 G2 decision 2, reduced to ONE blocker):
--   * Full mutual `infer-complete` / `check-complete` walk.
--     Remaining blocker:
--     1. `t-embed (t-var-local …)` / `t-embed (t-var-import …)` for
--        `x ∈ {id, fst, snd, inl, inr, terminal, initial, arr, apply,
--         compose, pair, curry}`: the specialised check-mode bare-
--        builtin clauses in `checkElab` can reject at types the
--        fallback would accept. Needs either (a) a side-condition
--        `x ∉ specialised-builtin-set` on the lookup rules, or (b)
--        specialised lookup rules for each builtin name, or (c) the
--        specialised check-mode bare-builtin clauses removed from
--        `checkElab` in favour of inferElab-then-match.
--
--     Resolved: the t-app case was blocked by Agda's `with`-
--     abstraction over `classifyAppHead`'s internal dispatch. The
--     `AppHeadView` refactor in Elaborate.agda (mirroring the
--     lesson "eliminate opaque `with`-helpers by refactoring the
--     definition") exposes the classifier's result structurally, so
--     `rewrite` can substitute both checkElab's and inferElab's
--     dispatches in lockstep. See `checkElab-fallback-RApp-generic`
--     in Elaborate.agda for the unblocked proof.
--
-- All infrastructure for the walk exists; the remaining work is
-- restructuring, not proof discovery.
------------------------------------------------------------------------
