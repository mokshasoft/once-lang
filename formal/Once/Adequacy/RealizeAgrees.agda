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
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

import Once.Type
open import Once.Type using (Type; Int; Unit; Void; Float; Str; Buffer; _*_; _+_; μ-type; ν-type;
                             Purity; pure; eff; mk-kind; Many; One; Zero; _⇒[_]_; isUnit?)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx; extendNamedCtx; lookupSigEffect; lookupImport)
open import Once.TypeCheck.Elaborate using (success; failure; VerifiedInferResult)
import Once.TypeCheck.Elaborate as E
open import Once.IR as IR using (IR)
open import Once.SigEffect using (SigEffect) renaming (halts to se-halts; emits to se-emits)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Once.TypeCheck.Judgment using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; t-int; t-str; t-unit; t-pair; t-neg; t-let)
open import Once.Denotation.Realize using (realize; realize-infer)
open import Once.Surface.Syntax as Surface using (Expr; Usage; ⟦_⟧ᶜ; pair; neg; let'; sigOp; lift-morphism)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
import Once.Denotation.SourceDenote as SD
open import Once.CanonicalName using (CanonicalName; showCanonical)

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
  infer-agreeV ctx e eq = infer-agreeV-todo ctx e eq

  check-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type) {Ψ se d f w}
    (eq : E.checkElabV ctx e T ≡ (success Ψ se d f , w)) → CheckAgreeV ctx e T eq
  check-agreeV ctx e T eq = check-agreeV-todo ctx e T eq
