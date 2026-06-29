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

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; +-mono-<; m≤m+n; m≤n+m; +-suc)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

import Once.Type
open import Once.Type using (Type; Int; Unit; Void; Float; Str; Buffer; _*_; _+_; μ-type; ν-type;
                             Purity; pure; eff; mk-kind; Many; One; Zero; _⇒[_]_; isUnit?; ⟦_⟧T; Functor)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx; extendNamedCtx; lookupSigEffect; lookupImport; lookupLocal)
open import Once.TypeCheck.Elaborate using (success; failure; VerifiedInferResult; VerifiedCheckResult)
import Once.TypeCheck.Elaborate as E
open import Once.IR as IR using (IR)
open import Once.SigEffect using (SigEffect) renaming (halts to se-halts; emits to se-emits)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Once.Adequacy.ResolveFaithful using (bind2-faithful)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Once.TypeCheck.Judgment using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; _⊢ᵍ_∶_; t-int; t-str; t-unit; t-pair; t-neg; t-let; t-binop-arith; t-binop-cmp; g-int; g-terminal; g-pair; g-inl; g-inr; g-In)
open import Once.Denotation.Realize using (realize; realize-infer; realize-global)
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Surface.Syntax as Surface using (Expr; Usage; ⟦_⟧ᶜ; pair; neg; let'; sigOp; lift-morphism)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
import Once.Denotation.SourceDenote as SD
open import Once.CanonicalName using (CanonicalName; showCanonical; bare)

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

-- `infer-agreeV` is now TOTAL (every RawExpr constructor handled; the RApp
-- apply/other heads route through `agree-RApp-hard`). Only check-mode's
-- non-`t-embed` specials (RLam/RVar-bbc/RPair-product/RInt-vlift/literals)
-- remain as a postulate.
postulate
  check-agreeV-todo : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type) {Ψ se d f w}
    (eq : E.checkElabV ctx e T ≡ (success Ψ se d f , w)) → CheckAgreeV ctx e T eq

-- RPair folded top-level (no `with`): take both sub-results explicitly +
-- their sub-IHs as functions; the de-withed `inferElabV-RPair-aux` reduces by
-- pattern-matching them. success/success is the real case; a `failure` sub
-- makes the aux a `failure`, so the success equation is absurd.
agree-RPair : ∀ {ctx : NamedCtx} {a b : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RPair a b ∶ A ⨾ Ψ}
  (rA : VerifiedInferResult ctx a) (rB : VerifiedInferResult ctx b)
  → E.inferElabV-RPair-aux ctx a b rA rB ≡ (success A Ψ se d f , w)
  → (∀ {Aₐ Ψₐ aE dₐ fₐ} {wA : ctx ⊢ᵢ a ∶ Aₐ ⨾ Ψₐ}
       → rA ≡ (success Aₐ Ψₐ aE dₐ fₐ , wA) → ∀ dγ k → SD.⟦ aE ⟧ˢ dγ k ≡ SD.⟦ realize-infer wA ⟧ˢ dγ k)
  → (∀ {Bᵦ Ψᵦ bE dᵦ fᵦ} {wB : ctx ⊢ᵢ b ∶ Bᵦ ⨾ Ψᵦ}
       → rB ≡ (success Bᵦ Ψᵦ bE dᵦ fᵦ , wB) → ∀ dγ k → SD.⟦ bE ⟧ˢ dγ k ≡ SD.⟦ realize-infer wB ⟧ˢ dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
agree-RPair (success Aₐ Ψₐ aE dₐ fₐ , wA) (success Bᵦ Ψᵦ bE dᵦ fᵦ , wB) refl subA subB dγ k
  rewrite subA refl dγ k | subB refl dγ k = refl
agree-RPair (failure _ , _) _ () subA subB
agree-RPair (success _ _ _ _ _ , _) (failure _ , _) () subA subB

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

-- RBinOp folded top-level (mirrors `inferElabV-RBinOp-aux`'s left-type /
-- right-type / op dispatch). Both operands must elaborate to `Int`; any other
-- left/right shape makes the aux `failure`, so the success equation is absurd
-- (`()`). For the 11 success ops the witness is `t-binop-{arith,cmp} refl w₁ w₂`
-- and `se` is the matching arithmetic/comparison IR; `realize-infer` rebuilds
-- the SAME IR over `realize-infer w₁/w₂`, so rewriting both operand IHs at
-- `(dγ,k)` (the binary op denotation is fuel-`k`-pointwise, as for `agree-RPair`)
-- closes each case with `refl`.
agree-RBinOp : ∀ {ctx : NamedCtx} (op : Raw.BinOp) {e₁ e₂ : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RBinOp op e₁ e₂ ∶ A ⨾ Ψ}
  (r₁ : VerifiedInferResult ctx e₁) (r₂ : VerifiedInferResult ctx e₂)
  → E.inferElabV-RBinOp-aux ctx op e₁ e₂ r₁ r₂ ≡ (success A Ψ se d f , w)
  → (∀ {A₁ Ψ₁ e₁E d₁ f₁} {w₁ : ctx ⊢ᵢ e₁ ∶ A₁ ⨾ Ψ₁}
       → r₁ ≡ (success A₁ Ψ₁ e₁E d₁ f₁ , w₁) → ∀ dγ k → SD.⟦ e₁E ⟧ˢ dγ k ≡ SD.⟦ realize-infer w₁ ⟧ˢ dγ k)
  → (∀ {A₂ Ψ₂ e₂E d₂ f₂} {w₂ : ctx ⊢ᵢ e₂ ∶ A₂ ⨾ Ψ₂}
       → r₂ ≡ (success A₂ Ψ₂ e₂E d₂ f₂ , w₂) → ∀ dγ k → SD.⟦ e₂E ⟧ˢ dγ k ≡ SD.⟦ realize-infer w₂ ⟧ˢ dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
-- left operand fails to be Int → aux is `failure`
agree-RBinOp op (failure _ , _) _ () s₁ s₂
agree-RBinOp op (success Unit          _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Void          _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Float         _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Str           _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Buffer        _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (_ * _)       _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (_ + _)       _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (_ ⇒[ _ ] _)  _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (μ-type _)    _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (ν-type _)    _ _ _ _ , _) _ () s₁ s₂
-- left is Int, right fails to be Int → aux is `failure`
agree-RBinOp op (success Int _ _ _ _ , _) (failure _ , _)                  () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Unit          _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Void          _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Float         _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Str           _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Buffer        _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (_ * _)       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (_ + _)       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (_ ⇒[ _ ] _)  _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (μ-type _)    _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (ν-type _)    _ _ _ _ , _) () s₁ s₂
-- both Int → the op picks the IR; rewrite both operand IHs at (dγ,k)
agree-RBinOp Raw.OpAdd (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpSub (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpMul (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpDiv (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpMod (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpLt (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpLe (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpGt (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpGe (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpEq (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpNe (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl

-- RLet folded with-free via two levels (e₂'s context depends on e₁'s type A):
-- `agree-RLet` matches the e₁ result, `agree-RLet2` the e₂ result; the let'
-- agreement threads `v1` through `_>>=T_` by inline rewrite (rewrite the bound
-- IH at `(dγ,k)` — fixing `v1` — then the body IH at the now-fixed
-- `(dγ, proj₂ ⟦realize w₁⟧)`). The e₂ IH
-- is passed as a function of A (only knowable after matching e₁).
agree-RLet2 : ∀ {ctx : NamedCtx} {x e₁ e₂ A B} {Ψ₁ : Usage (NamedCtx.size ctx)}
  {Ψ : Usage (NamedCtx.size ctx)}
  {se : Expr (NamedCtx.debruijn ctx) Ψ B} {d f} {w : ctx ⊢ᵢ Raw.RLet x e₁ e₂ ∶ B ⨾ Ψ}
  (e₁E : Expr (NamedCtx.debruijn ctx) Ψ₁ A) (d₁ f₁ : ℕ) (w₁ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁)
  (rE2 : VerifiedInferResult (extendNamedCtx ctx x A) e₂)
  → E.inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ w₁ rE2 ≡ (success B Ψ se d f , w)
  → (∀ dγ k → SD.⟦ e₁E ⟧ˢ dγ k ≡ SD.⟦ realize-infer w₁ ⟧ˢ dγ k)
  → (∀ {B' q Ψ₂' e₂E d₂' f₂'} {w₂ : extendNamedCtx ctx x A ⊢ᵢ e₂ ∶ B' ⨾ (q ∷ᵘ Ψ₂')}
       → rE2 ≡ (success B' (q ∷ᵘ Ψ₂') e₂E d₂' f₂' , w₂)
       → ∀ dγ' k → SD.⟦ e₂E ⟧ˢ dγ' k ≡ SD.⟦ realize-infer w₂ ⟧ˢ dγ' k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
agree-RLet2 e₁E d₁ f₁ w₁ (success B (q ∷ᵘ Ψ₂) e₂E d₂ f₂ , w₂) refl e₁ag e₂IH dγ k
  rewrite e₁ag dγ k | e₂IH refl (dγ , proj₂ (SD.⟦ realize-infer w₁ ⟧ˢ dγ k)) k = refl
agree-RLet2 e₁E d₁ f₁ w₁ (failure _ , _) () e₁ag e₂IH

agree-RLet : ∀ {ctx : NamedCtx} {x e₁ e₂ B} {Ψ : Usage (NamedCtx.size ctx)}
  {se : Expr (NamedCtx.debruijn ctx) Ψ B} {d f} {w : ctx ⊢ᵢ Raw.RLet x e₁ e₂ ∶ B ⨾ Ψ}
  (rE1 : VerifiedInferResult ctx e₁)
  → E.inferElabV-RLet-aux ctx x e₁ e₂ rE1 ≡ (success B Ψ se d f , w)
  → (∀ {A Ψ₁ e₁E d₁ f₁} {w₁ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁}
       → rE1 ≡ (success A Ψ₁ e₁E d₁ f₁ , w₁) → ∀ dγ k → SD.⟦ e₁E ⟧ˢ dγ k ≡ SD.⟦ realize-infer w₁ ⟧ˢ dγ k)
  → (∀ {A} → (rE2 : VerifiedInferResult (extendNamedCtx ctx x A) e₂)
       → E.inferElabV (extendNamedCtx ctx x A) e₂ ≡ rE2
       → ∀ {B' q Ψ₂' e₂E d₂' f₂'} {w₂ : extendNamedCtx ctx x A ⊢ᵢ e₂ ∶ B' ⨾ (q ∷ᵘ Ψ₂')}
         → rE2 ≡ (success B' (q ∷ᵘ Ψ₂') e₂E d₂' f₂' , w₂)
         → ∀ dγ' k → SD.⟦ e₂E ⟧ˢ dγ' k ≡ SD.⟦ realize-infer w₂ ⟧ˢ dγ' k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
agree-RLet {ctx} {x} {e₁} {e₂} (success A Ψ₁ e₁E d₁ f₁ , w₁) eq e₁IH e₂IH dγ k =
  agree-RLet2 e₁E d₁ f₁ w₁ (E.inferElabV (extendNamedCtx ctx x A) e₂) eq
              (e₁IH refl) (λ p → e₂IH (E.inferElabV (extendNamedCtx ctx x A) e₂) refl p) dγ k
agree-RLet (failure _ , _) () e₁IH e₂IH

-- THE MASQUERADE (Plan 0.50): at a `Many`-arrow, the elaborator's effect-aware
-- `lift-morphism (IR.SigOp (ext-resolved-info cn π))` denotes the same as
-- `realize`'s `sigOp cn`. Now `refl` (after the effect-as-leaf-annotation fix):
-- both read the effect off the arrow's `Purity` via the SHARED `isUnit?`, and
-- `emit-D` collapses `Emits`/`Halts` (the event reads only the name = `cn`),
-- `semM` collapses to `tt`. `pure` → both `value-info`; `eff` → one `isUnit?`
-- case-split, the `Unit` branch one `lookupSigEffect` split, every leaf `refl`.
masq : ∀ {ctx : NamedCtx} {Dom Cod : Type} (cn : CanonicalName) (π : Purity)
       (dγ : Env ctx) (k : ℕ)
     → SD.⟦ lift-morphism {Γ = NamedCtx.debruijn ctx} {π = π} (IR.SigOp (E.ext-resolved-info {Dom} {Cod} ctx cn π)) ⟧ˢ dγ k
      ≡ SD.⟦ sigOp {Γ = NamedCtx.debruijn ctx} {A = Dom ⇒[ mk-kind Many π ] Cod} cn ⟧ˢ dγ k
-- `Cod ≡ Unit` branch: the arrow is an effect contract. `emit-D` collapses
-- `Emits`/`Halts` to the same event (it reads only `name = cn`), so every
-- `lookupSigEffect` outcome — `se-halts`, `se-emits`, `nothing` — denotes the
-- same thing as `realize`'s `sigOp cn` (whose `arrow-info-eff cn (isUnit? Unit)`
-- = `emitsV`). All three leaves are `refl`. No `with` (mse is an explicit arg).
masq-unit : ∀ {ctx : NamedCtx} {Dom : Type} (cn : CanonicalName) (mse : Maybe SigEffect)
            (dγ : Env ctx) (k : ℕ)
          → SD.⟦ lift-morphism {Γ = NamedCtx.debruijn ctx} {π = eff} (IR.SigOp (E.ext-resolved-info-aux {Dom} {Unit} cn eff (yes refl) mse)) ⟧ˢ dγ k
           ≡ SD.⟦ sigOp {Γ = NamedCtx.debruijn ctx} {A = Dom ⇒[ mk-kind Many eff ] Unit} cn ⟧ˢ dγ k
masq-unit cn (just se-halts) dγ k = refl
masq-unit cn (just se-emits) dγ k = refl
masq-unit cn nothing         dγ k = refl

-- The outer dispatch on `isUnit? Cod` is a `with` (NOT a Dec-arg helper): the
-- scrutinee appears in the GOAL via `⟦ sigOp … ⟧ˢ` (which computes `isUnit? Cod`
-- internally), and only the `yes refl` UNIFICATION (`Cod := Unit`) reduces that
-- hidden occurrence. A helper taking the `Dec` explicitly would leave the RHS's
-- `isUnit? Cod` stuck. `masq` is a leaf equality lemma — opaque downstream — so
-- the `with` blocks no later proof's reduction. The inner mse split lives in the
-- with-free `masq-unit`, keeping this a single, flat `with`.
masq {ctx} {Dom} {Cod} cn pure dγ k = refl
masq {ctx} {Dom} {Cod} cn eff dγ k with isUnit? Cod
... | no _ = refl
... | yes refl = masq-unit {ctx} {Dom} cn (lookupSigEffect (NamedCtx.sigEffects ctx) (showCanonical cn)) dγ k

-- The RQualified analogue of `masq`. `ext-arrow-info` decides its Unit-codomain
-- via `E._≟T_ Unit` (NOT the `isUnit?` realize's `sigOp` uses), so the bridge
-- cross-checks both deciders. `pure` is `refl` on both sides. For `eff`:
-- `Cod ≟T Unit = yes` ⇒ `Cod := Unit`, realize's `isUnit? Unit` also fires, and
-- the `lookupSigEffect` split is all `refl` (emit-D reads only the name, so
-- haltsV/emitsV collapse, exactly as in `masq-unit`); `Cod ≟T Unit = no ¬p` ⇒
-- both sides `pureV` once `isUnit? Cod` is forced to `no` (its `yes` corner
-- contradicts ¬p).
masq-arrow : ∀ {ctx : NamedCtx} {Dom Cod : Type} (alias name : String) (π : Purity)
       (dγ : Env ctx) (k : ℕ)
     → SD.⟦ lift-morphism {Γ = NamedCtx.debruijn ctx} {π = π} (IR.SigOp (E.ext-arrow-info {Dom} {Cod} ctx alias name π)) ⟧ˢ dγ k
      ≡ SD.⟦ sigOp {Γ = NamedCtx.debruijn ctx} {A = Dom ⇒[ mk-kind Many π ] Cod} (bare (alias ++ "." ++ name)) ⟧ˢ dγ k
masq-arrow {ctx} {Dom} {Cod} alias name pure dγ k = refl
masq-arrow {ctx} {Dom} {Cod} alias name eff dγ k with Cod E.≟T Unit
... | yes refl with lookupSigEffect (NamedCtx.sigEffects ctx) (alias ++ "." ++ name)
...   | just se-halts = refl
...   | just se-emits = refl
...   | nothing       = refl
masq-arrow {ctx} {Dom} {Cod} alias name eff dγ k | no ¬p with isUnit? Cod
... | no _     = refl
... | yes refl = ⊥-elim (¬p refl)

-- RResolved agreement, dispatched on the import-lookup result exactly as the
-- elaborator's `inferElabV-RResolved-aux` does. A `Many`-arrow type resolves to
-- the effect-aware `lift-morphism (SigOp (ext-resolved-info …))` whose
-- agreement with realize's `sigOp cn` IS the `masq`-erade; every other type
-- resolves to `sigOp cn` directly (= realize) so agreement is `refl`. The type
-- shapes are ENUMERATED (not a catch-all): the aux's `just ty` clause sits
-- behind the `just (Many-arrow)` clause, so on an abstract type it would not
-- reduce — mirroring `Completeness`'s `go`. `nothing` ⇒ the aux fails, so the
-- success-eq is absurd.
-- `failure` and `success` are distinct constructors of `InferElabResult`, so a
-- proof identifying them is absurd (used to discharge the `nothing`-lookup case,
-- where the elaborator fails but the agreement obligation assumes success).
fail≢succ : ∀ {n} {Δ : Surface.Ctx n} {te} {A} {Ψ} {se : Surface.Expr Δ Ψ A} {d f}
          → failure {Δ = Δ} te ≡ success A Ψ se d f → ⊥
fail≢succ ()

agree-RResolved : ∀ (ctx : NamedCtx) (cn : CanonicalName) (lhs : Maybe Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ lhs)
  {A Ψ se d f w}
  → E.inferElabV-RResolved-aux ctx cn lhs lkup ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
agree-RResolved ctx cn (just (A ⇒[ mk-kind Many π ] B)) lkup refl dγ k = masq {ctx} {A} {B} cn π dγ k
agree-RResolved ctx cn (just (A ⇒[ mk-kind One  π ] B)) lkup refl dγ k = refl
agree-RResolved ctx cn (just (A ⇒[ mk-kind Zero π ] B)) lkup refl dγ k = refl
agree-RResolved ctx cn (just Unit)        lkup refl dγ k = refl
agree-RResolved ctx cn (just Void)        lkup refl dγ k = refl
agree-RResolved ctx cn (just Int)         lkup refl dγ k = refl
agree-RResolved ctx cn (just Float)       lkup refl dγ k = refl
agree-RResolved ctx cn (just Str)         lkup refl dγ k = refl
agree-RResolved ctx cn (just Buffer)      lkup refl dγ k = refl
agree-RResolved ctx cn (just (A * B))     lkup refl dγ k = refl
agree-RResolved ctx cn (just (A + B))     lkup refl dγ k = refl
agree-RResolved ctx cn (just (μ-type F))  lkup refl dγ k = refl
agree-RResolved ctx cn (just (ν-type F))  lkup refl dγ k = refl
agree-RResolved ctx cn nothing lkup eq dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))

-- RVar (non-unit): cases the lookup-aux. Local → the bound SExpr IS realize's
-- `eE`; import → both elaborator and `realize-infer` emit `sigOp (bare x)`;
-- neither-found → the success equation is absurd. No `masq` (unlike RResolved,
-- whose aux emits a `lift-morphism` for arrows).
agree-RVar : ∀ (ctx : NamedCtx) (x : String) (¬u : ¬ (x ≡ "unit"))
  (locLhs : Maybe (∃[ A ] ∃[ Ψ ] (Expr (NamedCtx.debruijn ctx) Ψ A)))
  (eq-loc : lookupLocal ctx x ≡ locLhs)
  (impLhs : Maybe Type) (eq-imp : lookupImport (NamedCtx.imports ctx) x ≡ impLhs)
  {A Ψ se d f w}
  → E.inferElabV-RVar-lookup-aux ctx x ¬u locLhs eq-loc impLhs eq-imp ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
agree-RVar ctx x ¬u (just (A , Ψ , se)) eq-loc impLhs eq-imp refl dγ k = refl
agree-RVar ctx x ¬u nothing eq-loc (just ty) eq-imp refl dγ k = refl
agree-RVar ctx x ¬u nothing eq-loc nothing eq-imp eq dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))

-- RQualified agreement, dispatched on the import-lookup of the dotted path,
-- exactly as `inferElabV-RQualified-aux` does. A `Many`-arrow resolves to the
-- effect-aware `lift-morphism (SigOp (ext-arrow-info …))` whose agreement with
-- realize's `sigOp (bare (alias.name))` is `masq-arrow`; every other type
-- resolves to that same `sigOp` directly (= realize) so agreement is `refl`.
-- `nothing` ⇒ the aux fails, so the success-eq is absurd.
agree-RQualified : ∀ (ctx : NamedCtx) (name alias : String) (lhs : Maybe Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ lhs)
  {A Ψ se d f w}
  → E.inferElabV-RQualified-aux ctx name alias lhs lkup ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
agree-RQualified ctx name alias (just (A ⇒[ mk-kind Many π ] B)) lkup refl dγ k = masq-arrow {ctx} {A} {B} alias name π dγ k
agree-RQualified ctx name alias (just (A ⇒[ mk-kind One  π ] B)) lkup refl dγ k = refl
agree-RQualified ctx name alias (just (A ⇒[ mk-kind Zero π ] B)) lkup refl dγ k = refl
agree-RQualified ctx name alias (just Unit)        lkup refl dγ k = refl
agree-RQualified ctx name alias (just Void)        lkup refl dγ k = refl
agree-RQualified ctx name alias (just Int)         lkup refl dγ k = refl
agree-RQualified ctx name alias (just Float)       lkup refl dγ k = refl
agree-RQualified ctx name alias (just Str)         lkup refl dγ k = refl
agree-RQualified ctx name alias (just Buffer)      lkup refl dγ k = refl
agree-RQualified ctx name alias (just (A * B))     lkup refl dγ k = refl
agree-RQualified ctx name alias (just (A + B))     lkup refl dγ k = refl
agree-RQualified ctx name alias (just (μ-type F))  lkup refl dγ k = refl
agree-RQualified ctx name alias (just (ν-type F))  lkup refl dγ k = refl
agree-RQualified ctx name alias nothing lkup eq dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))

-- RApp agreement, dispatched on the app-head VIEW (a parameter of
-- `inferElabV-RApp-dispatch`, so we case it directly — no `with` on
-- `classifyAppHeadView`). 9 check-only/initial heads FAIL in infer mode, so the
-- success-eq is absurd. The 5 builtin-combinator heads emit `morph-app IR.X arg`
-- (unary `>>=T`, same morphism both sides ⇒ `rewrite` the arg IH) or `arr' arg`
-- (denotational identity ⇒ the arg IH directly); their `realize-infer (t-X-app)`
-- is the same shape over the witness. `ahv-apply` (app of `specApply` vs
-- `morph-app apply`) and `ahv-other` (generic app/effApp; needs the FUNCTION-
-- position agreement too) carry semantic content → `agree-RApp-hard`.
postulate
  agree-RApp-hard : ∀ {ctx : NamedCtx} (f arg : RawExpr) {A Ψ se d fr w}
    (vw : E.AppHeadView f) (veq : E.classifyAppHeadView f ≡ vw)
    → E.inferElabV-RApp-dispatch ctx f arg vw veq ≡ (success A Ψ se d fr , w)
    → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k

agree-RApp : ∀ (ctx : NamedCtx) (f arg : RawExpr) {A Ψ se d fr w}
  (vw : E.AppHeadView f) (veq : E.classifyAppHeadView f ≡ vw)
  → E.inferElabV-RApp-dispatch ctx f arg vw veq ≡ (success A Ψ se d fr , w)
  → (argIH : ∀ {A' Ψ' argE d' fr'} {w' : ctx ⊢ᵢ arg ∶ A' ⨾ Ψ'}
       → E.inferElabV ctx arg ≡ (success A' Ψ' argE d' fr' , w')
       → ∀ dγ k → SD.⟦ argE ⟧ˢ dγ k ≡ SD.⟦ realize-infer w' ⟧ˢ dγ k)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
-- check-only / infer-failing heads: the dispatch is `failure`, so success-eq absurd.
agree-RApp ctx f arg E.ahv-inl            veq eq argIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-inr            veq eq argIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-initial        veq eq argIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-pair-applied   veq eq argIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-compose-applied veq eq argIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-case-applied   veq eq argIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-In             veq eq argIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-cata           veq eq argIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-curry          veq eq argIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
-- ahv-id : any-typed arg, result morph-app id.
agree-RApp ctx f arg E.ahv-id veq eq argIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success T Ψ argE d fr , w | refl rewrite argIH refl dγ k = refl
-- ahv-terminal : any-typed arg, result morph-app terminal.
agree-RApp ctx f arg E.ahv-terminal veq eq argIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success T Ψ argE d fr , w | refl rewrite argIH refl dγ k = refl
-- ahv-fst : arg must be a product; other shapes fail.
agree-RApp ctx f arg E.ahv-fst veq eq argIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success (A * B) Ψ argE d fr , w | refl rewrite argIH refl dγ k = refl
... | success Unit _ _ _ _ , _ | ()
... | success Void _ _ _ _ , _ | ()
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
-- ahv-snd : arg must be a product; other shapes fail.
agree-RApp ctx f arg E.ahv-snd veq eq argIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success (A * B) Ψ argE d fr , w | refl rewrite argIH refl dγ k = refl
... | success Unit _ _ _ _ , _ | ()
... | success Void _ _ _ _ , _ | ()
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
-- ahv-arr : arg must be a pure Many-arrow; `arr'` is the identity denotation.
agree-RApp ctx f arg E.ahv-arr veq eq argIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success (A ⇒[ mk-kind Many pure ] B) Ψ argE d fr , w | refl = argIH refl dγ k
... | success Unit _ _ _ _ , _ | ()
... | success Void _ _ _ _ , _ | ()
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ * _) _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (_ ⇒[ mk-kind Many eff ] _) _ _ _ _ , _ | ()
... | success (_ ⇒[ mk-kind One  eff ] _) _ _ _ _ , _ | ()
... | success (_ ⇒[ mk-kind Zero eff ] _) _ _ _ _ , _ | ()
... | success (_ ⇒[ mk-kind Zero pure ] _) _ _ _ _ , _ | ()
... | success (_ ⇒[ mk-kind One pure ] _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
-- ahv-apply / ahv-other : genuine semantic content (deferred).
agree-RApp ctx f arg E.ahv-apply veq eq argIH dγ k = agree-RApp-hard f arg E.ahv-apply veq eq dγ k
agree-RApp ctx f arg E.ahv-other veq eq argIH dγ k = agree-RApp-hard f arg E.ahv-other veq eq dγ k

-- RAnnot infers by CHECKING `e` against the annotation `T₀`; witness is
-- `t-annot witness`, se is the check-elaborated `eE`, and
-- `realize-infer (t-annot witness) = realize witness`, so agreement IS the
-- supplied `check-agreeV ctx e T₀` IH. A check failure makes the eq absurd.
agree-RAnnot : ∀ {ctx : NamedCtx} {e : RawExpr} {T₀ : Type} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RAnnot e T₀ ∶ A ⨾ Ψ}
  (r : VerifiedCheckResult ctx e T₀)
  → E.inferElabV-RAnnot-aux ctx e T₀ r ≡ (success A Ψ se d f , w)
  → (∀ {Ψ' eE' d' fr' w'} → r ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ dγ k ≡ SD.⟦ realize w' ⟧ˢ dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k
agree-RAnnot (success Ψ' eE' d' fr' , witness) refl IH dγ k = IH refl dγ k
agree-RAnnot (failure _ , _) () IH

------------------------------------------------------------------------
-- `checkG` builds EXACTLY the global-element IR that `realize-global` reads off
-- the ⊢ᵍ witness it returns: `m ≡ realize-global gd`. By induction on `gd`
-- (each constructor fixes `e`,`A` so `checkG` reduces); leaves (`g-int`,
-- `g-terminal`) are `refl`, the recursive cases re-run `checkG`'s sub-`with` and
-- `cong` the IH. Unblocks every check-mode value-lift case (RPair-vlift etc.).
checkG-realize : ∀ {ctx : NamedCtx} {X : Type} {e : RawExpr} {A : Type} {m : IR X A}
  (gd : ctx ⊢ᵍ e ∶ A)
  → E.checkG ctx X e A ≡ just (m , gd) → m ≡ realize-global gd
checkG-realize (g-int n) refl = refl
checkG-realize {ctx} {X} (g-terminal eqL eqI) eq
  with E.inspectLookupLocal ctx "terminal" | E.inspectLookupImport ctx "terminal" | eq
... | E.llv-not-found _ | E.liv-not-found _ | refl = refl
... | E.llv-not-found _ | E.liv-found _     | ()
... | E.llv-found _     | _                 | ()
checkG-realize {ctx} {X} (g-pair {a = a} {b = b} {A = A} {B = B} ga gb) eq
  with E.checkG ctx X a A in eqa | E.checkG ctx X b B in eqb | eq
... | just (ma , _) | just (mb , _) | refl =
      cong₂ (λ x y → IR.⟨ x , y ⟩ IR.Heap) (checkG-realize ga eqa) (checkG-realize gb eqb)
... | nothing       | _            | ()
... | just _        | nothing      | ()
checkG-realize {ctx} {X} (g-inl {arg = arg} {A = A} ga) eq
  with E.checkG ctx X arg A in eqa | eq
... | just (ma , _) | refl = cong (λ z → IR.inl IR.Heap IR.∘ z) (checkG-realize ga eqa)
... | nothing       | ()
checkG-realize {ctx} {X} (g-inr {arg = arg} {B = B} gb) eq
  with E.checkG ctx X arg B in eqb | eq
... | just (mb , _) | refl = cong (λ z → IR.inr IR.Heap IR.∘ z) (checkG-realize gb eqb)
... | nothing       | ()
checkG-realize {ctx} {X} (g-In {arg = arg} {F = F} {wfF = wfF} eqWF garg) eq
  with E.inspectWellFormedF F | eq
... | E.wfv-no _  | ()
... | E.wfv-yes _ | eq'
      with E.checkG ctx X arg (⟦ F ⟧T (μ-type F)) in eqarg | eq'
...     | just (marg , _) | refl = cong (λ z → IR.In wfF IR.Heap IR.∘ z) (checkG-realize garg eqarg)
...     | nothing         | ()

------------------------------------------------------------------------
-- Well-founded measure for the infer/check mutual recursion. The same-size
-- `check-agreeV e → infer-agreeV e` (the t-embed fallback) together with the
-- strictly-smaller `infer-agreeV (RAnnot e T) → check-agreeV e` make the SCC
-- mutual, and foetus cannot see termination through the `with`-auxes. We make
-- it explicit via `Acc` on a lexicographic measure `(size, phase)` flattened to
-- `μe+μe` (infer, phase 0) / `suc (μe+μe)` (check, phase 1): check→infer at the
-- same `e` drops the phase (strictly <), infer→check is on a strictly smaller
-- subterm, and every other recursive call shrinks the subterm.
μ : RawExpr → ℕ
μ (Raw.RVar _)            = 1
μ (Raw.RQualified _ _)    = 1
μ (Raw.RResolved _)       = 1
μ (Raw.RApp f x)          = suc (μ f +ℕ μ x)
μ (Raw.RLam _ b)          = suc (μ b)
μ (Raw.RLet _ e₁ e₂)      = suc (μ e₁ +ℕ μ e₂)
μ (Raw.RPair a b)         = suc (μ a +ℕ μ b)
μ (Raw.RDestruct s _ l _ r) = suc (μ s +ℕ (μ l +ℕ μ r))
μ Raw.RUnit               = 1
μ (Raw.RInt _)            = 1
μ (Raw.RStringLit _)      = 1
μ (Raw.RAnnot e _)        = suc (μ e)
μ (Raw.RBinOp _ a b)      = suc (μ a +ℕ μ b)
μ (Raw.RUnaryOp _ e)      = suc (μ e)
μ (Raw.RAna _ e)          = suc (μ e)

mInfer mCheck : RawExpr → ℕ
mInfer e = μ e +ℕ μ e
mCheck e = suc (μ e +ℕ μ e)

-- doubling is strictly monotone
dbl-< : ∀ {m n} → m < n → m +ℕ m < n +ℕ n
dbl-< h = +-mono-< h h

-- check-mode strictly dominates infer-mode at the same expression (phase drop)
infer<check : ∀ e → mInfer e < mCheck e
infer<check e = ≤-refl

-- `RAnnot e T` (infer) strictly dominates its checked body `e` (check)
check<infer-annot : ∀ e T → mCheck e < mInfer (Raw.RAnnot e T)
check<infer-annot e T = s≤s (≤-reflexive (sym (+-suc (μ e) (μ e))))

-- check→check on a strictly-smaller subterm: `μ sub < μ par` ⇒
-- `mCheck sub < mCheck par`. Stated over the ℕ measures (NOT the exprs — `μ` is
-- not injective, so expr indices wouldn't infer).
mC-sub : ∀ {m n : ℕ} → m < n → suc (m +ℕ m) < suc (n +ℕ n)
mC-sub h = s≤s (dbl-< h)

-- generic subterm size bounds (raw ℕ; instantiate with the μ of children)
μ<-l : ∀ a b → a < suc (a +ℕ b)
μ<-l a b = s≤s (m≤m+n a b)
μ<-r : ∀ a b → b < suc (a +ℕ b)
μ<-r a b = s≤s (m≤n+m b a)
μ<-d-s : ∀ s l r → s < suc (s +ℕ (l +ℕ r))
μ<-d-s s l r = s≤s (m≤m+n s (l +ℕ r))
μ<-d-l : ∀ s l r → l < suc (s +ℕ (l +ℕ r))
μ<-d-l s l r = s≤s (≤-trans (m≤m+n l r) (m≤n+m (l +ℕ r) s))
μ<-d-r : ∀ s l r → r < suc (s +ℕ (l +ℕ r))
μ<-d-r s l r = s≤s (≤-trans (m≤n+m r l) (m≤n+m (l +ℕ r) s))

mutual
  infer-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (ac : Acc _<_ (mInfer e)) {A Ψ se d f w}
    (eq : E.inferElabV ctx e ≡ (success A Ψ se d f , w)) → InferAgreeV ctx e eq
  infer-agreeV ctx (Raw.RInt n)       _ refl dγ k = refl
  infer-agreeV ctx (Raw.RStringLit s) _ refl dγ k = refl
  infer-agreeV ctx Raw.RUnit          _ refl dγ k = refl
  -- RPair: with-free — delegate to the top-level `agree-RPair`, passing both
  -- sub-results + sub-IHs (each with a strictly-smaller `Acc` from `rec`).
  infer-agreeV ctx (Raw.RPair a b) (acc rec) eq dγ k =
    agree-RPair (E.inferElabV ctx a) (E.inferElabV ctx b) eq
      (λ p → infer-agreeV ctx a (rec (dbl-< (μ<-l (μ a) (μ b)))) p)
      (λ p → infer-agreeV ctx b (rec (dbl-< (μ<-r (μ a) (μ b)))) p) dγ k
  infer-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) (acc rec) eq dγ k =
    agree-RUnaryOp (E.inferElabV ctx e) eq
      (λ p → infer-agreeV ctx e (rec (dbl-< ≤-refl)) p) dγ k
  infer-agreeV ctx (Raw.RLet x e₁ e₂) (acc rec) eq dγ k =
    agree-RLet (E.inferElabV ctx e₁) eq
      (λ p → infer-agreeV ctx e₁ (rec (dbl-< (μ<-l (μ e₁) (μ e₂)))) p)
      (λ {A} rE2 eqRE2 p → infer-agreeV (extendNamedCtx ctx x A) e₂ (rec (dbl-< (μ<-r (μ e₁) (μ e₂)))) (trans eqRE2 p)) dγ k
  infer-agreeV ctx (Raw.RResolved cn) _ eq dγ k =
    agree-RResolved ctx cn (lookupImport (NamedCtx.imports ctx) (showCanonical cn)) refl eq dγ k
  -- RVar: mirror inferElabV's `x ≟ "unit"` dispatch (bring `eq` into the `with`
  -- so it specialises); unit → `unit`, else the lookup-aux via `agree-RVar`.
  infer-agreeV ctx (Raw.RVar x) _ eq dγ k with StrProp._≟_ x "unit" | eq
  ... | yes refl | refl = refl
  ... | no ¬unit | eq' =
        agree-RVar ctx x ¬unit (lookupLocal ctx x) refl
                   (lookupImport (NamedCtx.imports ctx) x) refl eq' dγ k
  -- RLam / RAna: `inferElabV` always fails (no infer rule), so the success
  -- equation is absurd.
  infer-agreeV ctx (Raw.RLam _ _) _ ()
  infer-agreeV ctx (Raw.RAna _ _) _ ()
  -- RBinOp: with-free — delegate to top-level `agree-RBinOp`, passing both
  -- operand results explicitly + their sub-IHs (mirrors RPair).
  infer-agreeV ctx (Raw.RBinOp op e₁ e₂) (acc rec) eq dγ k =
    agree-RBinOp op (E.inferElabV ctx e₁) (E.inferElabV ctx e₂) eq
      (λ p → infer-agreeV ctx e₁ (rec (dbl-< (μ<-l (μ e₁) (μ e₂)))) p)
      (λ p → infer-agreeV ctx e₂ (rec (dbl-< (μ<-r (μ e₁) (μ e₂)))) p) dγ k
  -- RQualified: dispatch on the dotted-path import-lookup (with-free top-level).
  infer-agreeV ctx (Raw.RQualified name alias) _ eq dγ k =
    agree-RQualified ctx name alias
      (lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)) refl eq dγ k
  -- RApp: dispatch on the app-head view (delegates clean heads, defers
  -- apply/other to agree-RApp-hard). Argument IH carries a smaller `Acc`.
  infer-agreeV ctx (Raw.RApp f arg) (acc rec) eq dγ k =
    agree-RApp ctx f arg (E.classifyAppHeadView f) refl eq
      (λ p → infer-agreeV ctx arg (rec (dbl-< (μ<-r (μ f) (μ arg)))) p) dγ k
  -- RAnnot: infers by CHECKING the body against the annotation; delegate to
  -- `check-agreeV` (phase drops to check, which is strictly < this infer node).
  infer-agreeV ctx (Raw.RAnnot e T₀) (acc rec) eq dγ k =
    agree-RAnnot (E.checkElabV ctx e T₀) eq
      (λ p → check-agreeV ctx e T₀ (rec (check<infer-annot e T₀)) p) dγ k
  -- RDestruct (case): mirror the de-withed elaborator auxes (scrutinee type;
  -- left branch in ctx,xL:A; right branch in ctx,xR:B; branch-type match). The
  -- emitted `case' scrutE eLE eRE` denotes `⟦scrutE⟧ >>=T copair-of-branches`;
  -- `realize-infer (t-case …)` is the SAME shape; close by `bind2-faithful`
  -- with each sub-IH carrying a strictly-smaller `Acc`.
  infer-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) (acc rec) eq dγ k
    with E.inferElabV ctx scrut in seq | eq
  ... | failure _ , _ | ()
  ... | success Unit   _ _ _ _ , _ | ()
  ... | success Void   _ _ _ _ , _ | ()
  ... | success Int    _ _ _ _ , _ | ()
  ... | success Float  _ _ _ _ , _ | ()
  ... | success Str    _ _ _ _ , _ | ()
  ... | success Buffer _ _ _ _ , _ | ()
  ... | success (_ * _)      _ _ _ _ , _ | ()
  ... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
  ... | success (μ-type _)   _ _ _ _ , _ | ()
  ... | success (ν-type _)   _ _ _ _ , _ | ()
  ... | success (A + B) Ψs scrutE ds fs , wS | eq₁
        with E.inferElabV (extendNamedCtx ctx xL A) eL in leq | eq₁
  ...     | failure _ , _ | ()
  ...     | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , wL | eq₂
            with E.inferElabV (extendNamedCtx ctx xR B) eR in req | eq₂
  ...       | failure _ , _ | ()
  ...       | success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR , wR | eq₃
              with C₁ E.≟T C₂ | eq₃
  ...         | no _     | ()
  ...         | yes refl | refl =
                bind2-faithful (SD.⟦ scrutE ⟧ˢ dγ) (SD.⟦ realize-infer wS ⟧ˢ dγ)
                  (λ v → [ (λ a → SD.⟦ eLE ⟧ˢ (dγ , a)) , (λ b → SD.⟦ eRE ⟧ˢ (dγ , b)) ]′ v)
                  (λ v → [ (λ a → SD.⟦ realize-infer wL ⟧ˢ (dγ , a)) , (λ b → SD.⟦ realize-infer wR ⟧ˢ (dγ , b)) ]′ v)
                  (λ j → infer-agreeV ctx scrut (rec (dbl-< (μ<-d-s (μ scrut) (μ eL) (μ eR)))) seq dγ j)
                  (λ { (inj₁ a) j → infer-agreeV (extendNamedCtx ctx xL A) eL (rec (dbl-< (μ<-d-l (μ scrut) (μ eL) (μ eR)))) leq (dγ , a) j
                     ; (inj₂ b) j → infer-agreeV (extendNamedCtx ctx xR B) eR (rec (dbl-< (μ<-d-r (μ scrut) (μ eL) (μ eR)))) req (dγ , b) j })
                  k

  check-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type) (ac : Acc _<_ (mCheck e)) {Ψ se d f w}
    (eq : E.checkElabV ctx e T ≡ (success Ψ se d f , w)) → CheckAgreeV ctx e T eq
  -- Generic infer-and-match fallback (checkElabV's catch-all): the check
  -- witness is `t-embed w` over the infer witness `w`, `se` is the infer-
  -- elaborated `eE`, and `realize (t-embed w) = realize-infer w`, so agreement
  -- is EXACTLY `infer-agreeV` of the same expr (the phase drops, so the `Acc`
  -- is strictly smaller via `infer<check`). Mirror the fallback's two `with`s
  -- (inferElabV result; `T ≟T T'`), threading `eq` so it reduces.
  check-agreeV ctx (Raw.RBinOp op a b) T (acc rec) eq dγ k
    with E.inferElabV ctx (Raw.RBinOp op a b) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RBinOp op a b) (rec (infer<check (Raw.RBinOp op a b))) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) T (acc rec) eq dγ k
    with E.inferElabV ctx (Raw.RUnaryOp Raw.OpNeg e) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) (rec (infer<check (Raw.RUnaryOp Raw.OpNeg e))) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RLet x e₁ e₂) T (acc rec) eq dγ k
    with E.inferElabV ctx (Raw.RLet x e₁ e₂) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RLet x e₁ e₂) (rec (infer<check (Raw.RLet x e₁ e₂))) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) T (acc rec) eq dγ k
    with E.inferElabV ctx (Raw.RDestruct scrut xL eL xR eR) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) (rec (infer<check (Raw.RDestruct scrut xL eL xR eR))) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RAnnot e T₀) T (acc rec) eq dγ k
    with E.inferElabV ctx (Raw.RAnnot e T₀) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RAnnot e T₀) (rec (infer<check (Raw.RAnnot e T₀))) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RQualified name alias) T (acc rec) eq dγ k
    with E.inferElabV ctx (Raw.RQualified name alias) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RQualified name alias) (rec (infer<check (Raw.RQualified name alias))) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RResolved cn) T (acc rec) eq dγ k
    with E.inferElabV ctx (Raw.RResolved cn) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RResolved cn) (rec (infer<check (Raw.RResolved cn))) ieq dγ k
  ...     | no _     | ()
  -- RUnit / RStringLit: generic fallback over a literal whose inferred type is
  -- fixed (Unit / Str); case `T ≟T <that>` (the fallback's `T ≟T T'`), so `eq`
  -- reduces. `yes refl` delegates to `infer-agreeV` of the literal.
  check-agreeV ctx Raw.RUnit T (acc rec) eq dγ k with T E.≟T Unit | eq
  ... | yes refl | refl = infer-agreeV ctx Raw.RUnit (rec (infer<check Raw.RUnit)) refl dγ k
  ... | no _     | ()
  check-agreeV ctx (Raw.RStringLit s) T (acc rec) eq dγ k with T E.≟T Str | eq
  ... | yes refl | refl = infer-agreeV ctx (Raw.RStringLit s) (rec (infer<check (Raw.RStringLit s))) refl dγ k
  ... | no _     | ()
  -- RInt: vlift target (X ⇒[Many,pure] Int) emits `lift-morphism (intLit n)`,
  -- witness `t-value-lift (g-int n)`; `realize-global (g-int n) = intLit n`, so
  -- the two `lift-morphism`s coincide ⇒ `refl`. Otherwise the generic fallback
  -- (inferred type Int) delegates to `infer-agreeV`.
  check-agreeV ctx (Raw.RInt n) T (acc rec) eq dγ k with E.isRIntVliftTarget? T | eq
  ... | just (X , refl) | refl = refl
  ... | nothing | eq' with T E.≟T Int | eq'
  ...   | yes refl | refl = infer-agreeV ctx (Raw.RInt n) (rec (infer<check (Raw.RInt n))) refl dγ k
  ...   | no _     | ()
  -- RPair: product target → bidirectional component check (pair denotation is
  -- fuel-`k`-pointwise, rewrite both component agreements); pure-arrow→product
  -- vlift → `lift-morphism m` vs `realize-global gd`, bridged by `checkG-realize`;
  -- else the generic infer-and-match fallback.
  check-agreeV ctx (Raw.RPair a b) T (acc rec) eq dγ k with E.classifyRPairTarget T | eq
  ... | E.rpt-prod A B | eq'
        with E.checkElabV ctx a A in eqa | eq'
  ...     | failure _ , _ | ()
  ...     | success Ψ₁ aE da fa , wA | eq''
            with E.checkElabV ctx b B in eqb | eq''
  ...         | failure _ , _ | ()
  ...         | success Ψ₂ bE db fb , wB | refl
                rewrite check-agreeV ctx a A (rec (mC-sub (μ<-l (μ a) (μ b)))) eqa dγ k
                      | check-agreeV ctx b B (rec (mC-sub (μ<-r (μ a) (μ b)))) eqb dγ k = refl
  check-agreeV ctx (Raw.RPair a b) T (acc rec) eq dγ k | E.rpt-vlift X A B | eq'
        with E.inspectCheckG ctx X (Raw.RPair a b) (A * B) | eq'
  ...     | E.cgv-nothing _ | ()
  ...     | E.cgv-just {m} {gd} cgeq | refl rewrite checkG-realize gd cgeq = refl
  check-agreeV ctx (Raw.RPair a b) T (acc rec) eq dγ k | E.rpt-other T' | eq'
        with E.inferElabV ctx (Raw.RPair a b) in ieq | eq'
  ...     | failure _ , _ | ()
  ...     | success T'' Ψ eE d fr , w | eq₂ with T' E.≟T T'' | eq₂
  ...       | yes refl | refl = infer-agreeV ctx (Raw.RPair a b) (rec (infer<check (Raw.RPair a b))) ieq dγ k
  ...       | no _     | ()
  check-agreeV ctx e T _ eq = check-agreeV-todo ctx e T eq

------------------------------------------------------------------------
-- THE BRIDGE (Plan 0.50: de-island). `realize-agrees` of the EXACT type
-- `RealizeBridge`/`Compile.main-realize-agrees` consume. Mirrors `check-sound`'s
-- own case-split (`checkElab = proj₁ ∘ checkElabV`): casing `checkElabV` reduces
-- `cc` to a `success`/`failure` equation; `success` ⇒ the goal is `check-agreeV`'s
-- conclusion; `failure` is absurd. RealizeBridge re-exports this.
------------------------------------------------------------------------
realize-agrees : ∀ (ctx : NamedCtx) (e : RawExpr) (A : Type)
  {Ψ : Usage (NamedCtx.size ctx)}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  (cc : E.checkElab ctx e A ≡ success Ψ se d f)
  (dγ : ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜ ⟧ᴰ) (k : ℕ) →
  SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize (check-sound ctx e A cc) ⟧ˢ dγ k
realize-agrees ctx e A cc dγ k with E.checkElabV ctx e A in eqV
... | success Ψ' eE' d' fr' , w' with cc
...   | refl = check-agreeV ctx e A (<-wellFounded (mCheck e)) eqV dγ k
realize-agrees ctx e A cc dγ k | failure _ , _ with cc
... | ()
