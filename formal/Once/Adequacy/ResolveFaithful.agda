-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ResolveFaithful — Plan 0.51 / 3b: discharge of
-- `MainRealizeAgrees.resolveExpr-faithful` (the resolver preserves SD denotation).
--
-- Induction on the elaborated `Expr`. The ~30 STRUCTURAL constructors need only
-- the IHs: `resolveExpr-C` is `refl` (resolution commutes structurally, same
-- `Acc`), so `resolveExpr (C …)` reduces DEFINITIONALLY to `C (resolveExpr …)`;
-- and `>>=T` at fuel `k` consumes only the sub-trace `m k`, so the pointwise-`k`
-- IH `rewrite`s cleanly. Binders (`lam`/`case'`) close over the bound var → use
-- `Once.Postulates.extensionality` (funext).
--
-- SCAFFOLD (feedback_scaffold_then_discharge): the genuinely-hard constructors
-- (`sigOp` name-resolution, `morph-app`, `cata`/`ana` closure-bridges, `poly`
-- inlining via `resolveExpr-poly-match`) route to the single named residual
-- `resolveExpr-faithful-hard`, to be discharged next.
------------------------------------------------------------------------

module Once.Adequacy.ResolveFaithful where

open import Data.Nat using (ℕ)
open import Data.List using ([])
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.Type using (Type; Int)
open import Once.Surface.Syntax as Srf using (Expr; Usage; ⟦_⟧ᶜ)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; _>>=T_)
import Once.Denotation.SourceDenote as SD
open import Once.TypeCheck.Elaborate using (resolveExpr; PolyCtx; Imports)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- The hard-constructor residual (sigOp / morph-app / cata / ana / poly).
------------------------------------------------------------------------

postulate
  resolveExpr-faithful-hard :
    ∀ {n} {Γ : Srf.Ctx n} {Ψ : Usage n} {A : Type}
      (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
      (e : Expr Γ Ψ A) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
    → SD.⟦ resolveExpr polys imps userFns fresh e ⟧ˢ dγ k ≡ SD.⟦ e ⟧ˢ dγ k

-- Two-sided bind congruence at each fuel: `>>=T` at `j` consumes only `m j`
-- (and the continuation at `proj₂ (m j)`), so pointwise equalities of BOTH the
-- monad value and the continuation transfer.
bind2-faithful : ∀ {X Y} (mR mU : T X) (gR gU : X → T Y)
  → (∀ j → mR j ≡ mU j) → (∀ v j → gR v j ≡ gU v j)
  → ∀ j → (mR >>=T gR) j ≡ (mU >>=T gU) j
bind2-faithful mR mU gR gU me ge j rewrite me j | ge (proj₂ (mU j)) j = refl

------------------------------------------------------------------------
-- The faithfulness theorem.
------------------------------------------------------------------------

resolveExpr-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ : Usage n} {A : Type}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Expr Γ Ψ A) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → SD.⟦ resolveExpr polys imps userFns fresh e ⟧ˢ dγ k ≡ SD.⟦ e ⟧ˢ dγ k
-- Leaves (resolveExpr unchanged ⇒ definitionally equal).
resolveExpr-faithful polys imps userFns fresh (Srf.var i) dγ k = refl
resolveExpr-faithful polys imps userFns fresh Srf.unit dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.int z) dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.str s) dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.closure s) dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.lift-morphism m) dγ k = refl
-- Unary / binary (structural ⇒ rewrite the IHs).
resolveExpr-faithful polys imps userFns fresh (Srf.fst' p) dγ k rewrite resolveExpr-faithful polys imps userFns fresh p dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.snd' p) dγ k rewrite resolveExpr-faithful polys imps userFns fresh p dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.inl' e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.inr' e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.neg e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.absurd e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.arr' e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.morph-app m a) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.app f a) dγ k rewrite resolveExpr-faithful polys imps userFns fresh f dγ k | resolveExpr-faithful polys imps userFns fresh a dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.pair a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.add a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.sub a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.mul a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.div a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.mod' a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.lt a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.le a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.gt a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.ge a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.eq a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.ne a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
-- Binders.
resolveExpr-faithful polys imps userFns fresh (Srf.lam q prf b) dγ k =
  cong ([] ,_)
    (extensionality (λ a → extensionality (λ j →
      resolveExpr-faithful polys imps userFns fresh b (dγ , a) j)))
resolveExpr-faithful polys imps userFns fresh (Srf.let' e₁ e₂) dγ k
  rewrite resolveExpr-faithful polys imps userFns fresh e₁ dγ k
        | resolveExpr-faithful polys imps userFns fresh e₂ (dγ , proj₂ (SD.⟦ e₁ ⟧ˢ dγ k)) k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.case' s l r) dγ k
  rewrite resolveExpr-faithful polys imps userFns fresh s dγ k
        | extensionality (λ a → extensionality (λ j → resolveExpr-faithful polys imps userFns fresh l (dγ , a) j))
        | extensionality (λ b → extensionality (λ j → resolveExpr-faithful polys imps userFns fresh r (dγ , b) j)) = refl
-- effApp: D018 closure `returnT (λ _ → ⟦f⟧ >>=T λ vf → ⟦x⟧ >>=T λ vx → vf vx)`.
-- Funext over the Unit arg + fuel; the body is a nested bind closed by bind2.
resolveExpr-faithful polys imps userFns fresh (Srf.effApp f x) dγ k =
  cong ([] ,_) (extensionality (λ _ → extensionality
    (bind2-faithful (SD.⟦ resolveExpr polys imps userFns fresh f ⟧ˢ dγ) (SD.⟦ f ⟧ˢ dγ) _ _
      (λ j → resolveExpr-faithful polys imps userFns fresh f dγ j)
      (λ vf → bind2-faithful (SD.⟦ resolveExpr polys imps userFns fresh x ⟧ˢ dγ) (SD.⟦ x ⟧ˢ dγ)
                (λ vx → vf vx) (λ vx → vf vx)
                (λ j → resolveExpr-faithful polys imps userFns fresh x dγ j)
                (λ vx j → refl)))))
-- Hard constructors (sigOp / cata / ana / poly) → the named residual.
resolveExpr-faithful polys imps userFns fresh e dγ k = resolveExpr-faithful-hard polys imps userFns fresh e dγ k
