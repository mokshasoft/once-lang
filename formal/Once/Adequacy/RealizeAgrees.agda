-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.RealizeAgrees — the proof behind `RealizeBridge.realize-agrees`
-- (Plan 0.49 piece 3). `checkElab`'s emitted term `se` denotes the same as the
-- canonical `realize` term read off the (term-free) typing derivation, which is
-- INDEPENDENT of `checkElab`. So a wrong elaboration breaks the apex.
--
-- Structure (mirrors `Completeness.infer-complete`/`check-complete`): induct on
-- the typing DERIVATION. Each node recurses for its sub-derivations' success
-- equations + denotational agreements, then folds the elaborator's internal
-- `with` via the `with inferElabV ctx a | eqA` technique (matching the
-- equation `refl` — the same trick `infer-complete-RPair` uses to sidestep the
-- opaque `with`-helper). We return BOTH the success equation (so the emitted
-- term is pinned) and the agreement (`faithful`-style: leaves `refl`,
-- structural nodes `rewrite` the sub-IHs — `_>>=T_` threads each at depth `k`).
--
-- WIP: leaves + `t-pair` validate the full technique (derivation induction +
-- equation-folding helper + `>>=T` agreement).
------------------------------------------------------------------------

module Once.Adequacy.RealizeAgrees where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Type using (Type; _*_)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Elaborate using (inferElab; success; failure)
import Once.TypeCheck.Elaborate as E
open import Once.TypeCheck.Judgment
  using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_;
         t-int; t-str; t-unit; t-unit-var; t-pair)
open import Once.Denotation.Realize using (realize; realize-infer)
open import Once.Surface.Syntax as Surf using (Expr; Usage; ⟦_⟧ᶜ; pair; _+ᵘ_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
import Once.Denotation.SourceDenote as SD

private
  Env : NamedCtx → Set
  Env ctx = ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜ ⟧ᴰ

-- The packaged result of `infer-agree`: the emitted term `eE` (pinned by the
-- success equation) denotes the same as `realize-infer w`.
InferAgree : (ctx : NamedCtx) (e : RawExpr) {A : Type} {Ψ : Usage (NamedCtx.size ctx)}
           → ctx ⊢ᵢ e ∶ A ⨾ Ψ → Set
InferAgree ctx e {A} {Ψ} w =
  ∃[ eE ] ∃[ d ] ∃[ f ]
    (inferElab ctx e ≡ success A Ψ eE d f)
    × (∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ eE ⟧ˢ dγ k ≡ SD.⟦ realize-infer w ⟧ˢ dγ k)

-- RPair node: fold the elaborator's two inner `with`s via the sub-equations,
-- then the pair agreement reduces to the two sub-agreements at depth `k`.
agree-RPair : ∀ {ctx : NamedCtx} (a b : RawExpr)
  {A B : Type} {Ψ₁ Ψ₂ : Usage (NamedCtx.size ctx)}
  {aE : Expr (NamedCtx.debruijn ctx) Ψ₁ A} {bE : Expr (NamedCtx.debruijn ctx) Ψ₂ B}
  {dA dB fA fB : ℕ}
  {rA : Expr (NamedCtx.debruijn ctx) Ψ₁ A} {rB : Expr (NamedCtx.debruijn ctx) Ψ₂ B}
  → inferElab ctx a ≡ success A Ψ₁ aE dA fA
  → inferElab ctx b ≡ success B Ψ₂ bE dB fB
  → (∀ dγ k → SD.⟦ aE ⟧ˢ dγ k ≡ SD.⟦ rA ⟧ˢ dγ k)
  → (∀ dγ k → SD.⟦ bE ⟧ˢ dγ k ≡ SD.⟦ rB ⟧ˢ dγ k)
  → ∃[ eE ] ∃[ d ] ∃[ f ]
      (inferElab ctx (Raw.RPair a b) ≡ success (A * B) (Ψ₁ +ᵘ Ψ₂) eE d f)
      × (∀ dγ k → SD.⟦ eE ⟧ˢ dγ k ≡ SD.⟦ pair rA rB ⟧ˢ dγ k)
agree-RPair {ctx} a b {rA = rA} {rB = rB} eqA eqB agA agB
  with E.inferElabV ctx a | eqA
... | success _ _ aE _ _ , _ | refl
    with E.inferElabV ctx b | eqB
...   | success _ _ bE _ _ , _ | refl = _ , _ , _ , refl , pairAgree
  where
    pairAgree : ∀ dγ k → SD.⟦ pair aE bE ⟧ˢ dγ k ≡ SD.⟦ pair rA rB ⟧ˢ dγ k
    pairAgree dγ k rewrite agA dγ k | agB dγ k = refl

-- SCAFFOLD (Plan 0.49, [[feedback_scaffold_then_discharge]]): the not-yet-
-- discharged derivation cases route through this ONE placeholder. Every clause
-- ABOVE the catch-all is genuinely proven; this is the explicit remaining-work
-- marker (to be emptied — end state has zero obligations). It is true
-- (`InferAgree` holds for every derivation); standalone WIP, off the apex.
postulate
  infer-agree-todo : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
                       {Ψ : Usage (NamedCtx.size ctx)}
                     (w : ctx ⊢ᵢ e ∶ A ⨾ Ψ) → InferAgree ctx e w

infer-agree : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
                {Ψ : Usage (NamedCtx.size ctx)}
              (w : ctx ⊢ᵢ e ∶ A ⨾ Ψ) → InferAgree ctx e w
infer-agree (t-int n)   = _ , _ , _ , refl , λ dγ k → refl
infer-agree (t-str s)   = _ , _ , _ , refl , λ dγ k → refl
infer-agree t-unit      = _ , _ , _ , refl , λ dγ k → refl
infer-agree t-unit-var  = _ , _ , _ , refl , λ dγ k → refl
infer-agree (t-pair {a = a} {b = b} wA wB) =
  let (aE , _ , _ , eqA , agA) = infer-agree wA
      (bE , _ , _ , eqB , agB) = infer-agree wB
  in agree-RPair a b {rA = realize-infer wA} {rB = realize-infer wB} eqA eqB agA agB
infer-agree w = infer-agree-todo w
