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
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

import Once.Type
open import Once.Type using (Type; Int; Unit; Void; Float; Str; Buffer; _*_; _+_; μ-type; ν-type;
                             Purity; pure; eff; mk-kind; Many; One; Zero; _⇒[_]_; isUnit?)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx; extendNamedCtx; lookupSigEffect; lookupImport; lookupLocal)
open import Once.TypeCheck.Elaborate using (success; failure; VerifiedInferResult)
import Once.TypeCheck.Elaborate as E
open import Once.IR as IR using (IR)
open import Once.SigEffect using (SigEffect) renaming (halts to se-halts; emits to se-emits)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Once.Adequacy.ResolveFaithful using (bind2-faithful)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Once.TypeCheck.Judgment using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; t-int; t-str; t-unit; t-pair; t-neg; t-let; t-binop-arith; t-binop-cmp)
open import Once.Denotation.Realize using (realize; realize-infer)
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

postulate
  infer-agreeV-todo : ∀ (ctx : NamedCtx) (e : RawExpr) {A Ψ se d f w}
    (eq : E.inferElabV ctx e ≡ (success A Ψ se d f , w)) → InferAgreeV ctx e eq
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

mutual
  infer-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) {A Ψ se d f w}
    (eq : E.inferElabV ctx e ≡ (success A Ψ se d f , w)) → InferAgreeV ctx e eq
  infer-agreeV ctx (Raw.RInt n)       refl dγ k = refl
  infer-agreeV ctx (Raw.RStringLit s) refl dγ k = refl
  infer-agreeV ctx Raw.RUnit          refl dγ k = refl
  -- RPair: with-free — delegate to the top-level `agree-RPair`, passing both
  -- sub-results + sub-IHs as functions (mirrors RUnaryOp; the de-withed aux
  -- reduces by pattern-matching the sub-results).
  infer-agreeV ctx (Raw.RPair a b) eq dγ k =
    agree-RPair (E.inferElabV ctx a) (E.inferElabV ctx b) eq
      (λ p → infer-agreeV ctx a p) (λ p → infer-agreeV ctx b p) dγ k
  infer-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) eq dγ k =
    agree-RUnaryOp (E.inferElabV ctx e) eq (λ p → infer-agreeV ctx e p) dγ k
  infer-agreeV ctx (Raw.RLet x e₁ e₂) eq dγ k =
    agree-RLet (E.inferElabV ctx e₁) eq
      (λ p → infer-agreeV ctx e₁ p)
      (λ {A} rE2 eqRE2 p → infer-agreeV (extendNamedCtx ctx x A) e₂ (trans eqRE2 p)) dγ k
  infer-agreeV ctx (Raw.RResolved cn) eq dγ k =
    agree-RResolved ctx cn (lookupImport (NamedCtx.imports ctx) (showCanonical cn)) refl eq dγ k
  -- RVar: mirror inferElabV's `x ≟ "unit"` dispatch (bring `eq` into the `with`
  -- so it specialises); unit → `unit`, else the lookup-aux via `agree-RVar`.
  infer-agreeV ctx (Raw.RVar x) eq dγ k with StrProp._≟_ x "unit" | eq
  ... | yes refl | refl = refl
  ... | no ¬unit | eq' =
        agree-RVar ctx x ¬unit (lookupLocal ctx x) refl
                   (lookupImport (NamedCtx.imports ctx) x) refl eq' dγ k
  -- RLam / RAna: `inferElabV` always fails (no infer rule), so the success
  -- equation is absurd.
  infer-agreeV ctx (Raw.RLam _ _) ()
  infer-agreeV ctx (Raw.RAna _ _) ()
  -- RBinOp: with-free — delegate to top-level `agree-RBinOp`, passing both
  -- operand results explicitly + their sub-IHs (mirrors RPair).
  infer-agreeV ctx (Raw.RBinOp op e₁ e₂) eq dγ k =
    agree-RBinOp op (E.inferElabV ctx e₁) (E.inferElabV ctx e₂) eq
      (λ p → infer-agreeV ctx e₁ p) (λ p → infer-agreeV ctx e₂ p) dγ k
  -- RQualified: dispatch on the dotted-path import-lookup (with-free top-level).
  infer-agreeV ctx (Raw.RQualified name alias) eq dγ k =
    agree-RQualified ctx name alias
      (lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)) refl eq dγ k
  -- RDestruct (case): mirror the de-withed elaborator auxes (scrutinee type;
  -- left branch in ctx,xL:A; right branch in ctx,xR:B; branch-type match). The
  -- emitted `case' scrutE eLE eRE` denotes `⟦scrutE⟧ >>=T copair-of-branches`;
  -- `realize-infer (t-case …)` is the SAME shape over the witnesses. Close by
  -- `bind2-faithful`: scrutinee agreement = `infer-agreeV scrut`, branch
  -- agreement = `infer-agreeV eL/eR` at the injected env `(dγ , a)/(dγ , b)`.
  infer-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) eq dγ k
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
                  (λ j → infer-agreeV ctx scrut seq dγ j)
                  (λ { (inj₁ a) j → infer-agreeV (extendNamedCtx ctx xL A) eL leq (dγ , a) j
                     ; (inj₂ b) j → infer-agreeV (extendNamedCtx ctx xR B) eR req (dγ , b) j })
                  k
  infer-agreeV ctx e eq = infer-agreeV-todo ctx e eq

  check-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type) {Ψ se d f w}
    (eq : E.checkElabV ctx e T ≡ (success Ψ se d f , w)) → CheckAgreeV ctx e T eq
  -- Generic infer-and-match fallback (checkElabV's catch-all): the check
  -- witness is `t-embed w` over the infer witness `w`, `se` is the infer-
  -- elaborated `eE`, and `realize (t-embed w) = realize-infer w`, so agreement
  -- is EXACTLY `infer-agreeV` of the same expr. We mirror the fallback's two
  -- `with`s (inferElabV result; `T ≟T T'`), threading `eq` through each level
  -- so it reduces: `failure`/type-mismatch make it absurd, `yes refl` delegates.
  check-agreeV ctx (Raw.RBinOp op a b) T eq dγ k
    with E.inferElabV ctx (Raw.RBinOp op a b) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RBinOp op a b) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) T eq dγ k
    with E.inferElabV ctx (Raw.RUnaryOp Raw.OpNeg e) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RLet x e₁ e₂) T eq dγ k
    with E.inferElabV ctx (Raw.RLet x e₁ e₂) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RLet x e₁ e₂) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) T eq dγ k
    with E.inferElabV ctx (Raw.RDestruct scrut xL eL xR eR) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RAnnot e T₀) T eq dγ k
    with E.inferElabV ctx (Raw.RAnnot e T₀) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RAnnot e T₀) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RQualified name alias) T eq dγ k
    with E.inferElabV ctx (Raw.RQualified name alias) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RQualified name alias) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx (Raw.RResolved cn) T eq dγ k
    with E.inferElabV ctx (Raw.RResolved cn) in ieq | eq
  ... | failure _ , _ | ()
  ... | success T' Ψ eE d fr , w | eq₁
        with T E.≟T T' | eq₁
  ...     | yes refl | refl = infer-agreeV ctx (Raw.RResolved cn) ieq dγ k
  ...     | no _     | ()
  check-agreeV ctx e T eq = check-agreeV-todo ctx e T eq

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
...   | refl = check-agreeV ctx e A eqV dγ k
realize-agrees ctx e A cc dγ k | failure _ , _ with cc
... | ()
