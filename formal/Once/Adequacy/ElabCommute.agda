-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ElabCommute — plan 0.104 E.2 (ii): ELABORATION COMMUTES WITH
-- THE RIGID SUBSTITUTION.
--
-- Elaborating the surface substitution instance of a derivation
-- (`RigidSubst.subst-c′`) gives the core substitution of its elaboration
-- (`CoreInst.ρ̂ᶜ`): the same term up to `ρ̂ₜ`, the same derivation up to index
-- transports. By induction on the surface derivation, clause by clause with
-- the elaboration; each combinator's case is its commutation lemma
-- (`CoreInst.c-*`), and a reference's is the view's naturality.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig; KCtx; GSub; Respects)
import Once.Spec.Core.Abstract as Abs
import Once.Spec.Elaboration as El
import Once.TypeCheck.RigidSubst as RSm
import Once.Adequacy.ViewNatural as VN
open import Once.TypeCheck.Classify using (Imports; PolyCtx)

module Once.Adequacy.ElabCommute {s : ℕ} (S : Sig s) {m : ℕ} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ)
  (sg : Abs.SigGround S) {imps : Imports} {polys : PolyCtx} (V : El.View S imps polys)
  (nat : VN.Natural S Δ τ r V) (ir : RSm.ImportsRF Δ τ r imps) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

import Once.Type as T
open T using (Type; mk-kind; Many; pure; eff; μ-type; ν-type; ⟦_⟧T)
open import Once.Type.Sub using (<:-unique; sub-arr; <:-refl)
open import Once.Functor.Translate using (IsBaseType-irrelevant)
open import Once.Type.Rigid using (extractGround-rf)
open import Once.Postulates using (extensionality)
import Once.Surface.Context as C
open import Once.TypeCheck.Raw using (BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.TypeCheck.Classify using (mkCtx)
open import Once.TypeCheck.Judgment
import Once.Spec.Core.Syntax S as G
import Once.Spec.Core.Typing S as GT
open GT using (_⊢[_]_∷_!_)
open import Once.Spec.Core.PolyTy using (_!!_; arity; kinds; type; _⟪_⟫)
import Once.Spec.Core.Rename S as RN
import Once.Spec.Core.DerivedTyping S as DT
open El S using (View; elabᶜ; elabᵢ; elabᵈ; ImportAt; ffi; def; importE; refE; InstanceOf)
open RSm Δ τ r using (ρ̂; ρ̂S; ρ̂N; ρ̂-<:; ρ̂-wf; ρ̂-⟦⟧; ρ̂-rf; ρ̂-ki; lookup-ρ̂; lk-just;
  subst-c′; subst-i′; subst-d′; _⇝ᵢ_; _⇝ᶜ_)
import Once.Adequacy.CoreInst S Δ τ r as CI
open CI using (ρ̂ₜ; ρ̂ₜ-ren)
open CI.WithSG sg
open VN.Natural nat

open View V

------------------------------------------------------------------------
-- Transports, references, closing.
------------------------------------------------------------------------

private
  ⇝ᵢ-tm : ∀ {n Γ D fr e A B Ψ} (q : A ≡ B) (d : mkCtx n Γ D fr imps polys ⊢ᵢ e ∶ A ⨾ Ψ) → proj₁ (elabᵢ V (q ⇝ᵢ d)) ≡ proj₁ (elabᵢ V d)
  ⇝ᵢ-tm refl d = refl
  ⇝ᵢ-dr : ∀ {n Γ D fr e A B Ψ} (q : A ≡ B) (d : mkCtx n Γ D fr imps polys ⊢ᵢ e ∶ A ⨾ Ψ) → proj₂ (elabᵢ V (q ⇝ᵢ d)) ≅ proj₂ (elabᵢ V d)
  ⇝ᵢ-dr refl d = H.refl
  ⇝ᶜ-tm : ∀ {n Γ D fr e A B Ψ} (q : A ≡ B) (d : mkCtx n Γ D fr imps polys ⊢ᶜ e ∶ A ⨾ Ψ) → proj₁ (elabᶜ V (q ⇝ᶜ d)) ≡ proj₁ (elabᶜ V d)
  ⇝ᶜ-tm refl d = refl
  ⇝ᶜ-dr : ∀ {n Γ D fr e A B Ψ} (q : A ≡ B) (d : mkCtx n Γ D fr imps polys ⊢ᶜ e ∶ A ⨾ Ψ) → proj₂ (elabᶜ V (q ⇝ᶜ d)) ≅ proj₂ (elabᶜ V d)
  ⇝ᶜ-dr refl d = H.refl

  ≅ref : ∀ {n} {Γ : C.Ctx n} {d} {τ₁ τ₂ : GSub (arity (S !! d))} {r₁ r₂} → τ₁ ≡ τ₂
       → GT.⊢ref {Γ = Γ} d τ₁ r₁ ≅ GT.⊢ref {Γ = Γ} d τ₂ r₂
  ≅ref {r₁ = r₁} {r₂} refl
    rewrite extensionality (λ i → extensionality (λ e → IsBaseType-irrelevant (r₁ i e) (r₂ i e))) = H.refl

  -- A reference: the instance the substituted use finds is the substituted one.
  refE-tm : ∀ {n} {Γ : C.Ctx n} {A₁ A} (d : Fin s) (i₁ : InstanceOf d A₁) (i₀ : InstanceOf d A)
          → proj₁ i₁ ≡ (λ j → ρ̂ (proj₁ i₀ j))
          → proj₁ (refE {Γ = ρ̂S Γ} d i₁) ≡ ρ̂ₜ (proj₁ (refE {Γ = Γ} d i₀))
  refE-tm d i₁ i₀ h = cong (G.ref d) h

  refE-dr : ∀ {n} {Γ : C.Ctx n} {A₁ A} (d : Fin s) (i₁ : InstanceOf d A₁) (i₀ : InstanceOf d A)
          → proj₁ i₁ ≡ (λ j → ρ̂ (proj₁ i₀ j))
          → proj₂ (refE {Γ = ρ̂S Γ} d i₁) ≅ ρ̂ᶜ (proj₂ (refE {Γ = Γ} d i₀))
  refE-dr d (τ₁ , r₁ , e₁) (τ₀ , r₀ , e₀) h =
    H.trans (rmA (λ X → X) e₁)
      (H.trans (≅ref h) (H.sym (H.trans (ρ̂ᶜ-sA (λ X → X) e₀) (rmA (λ X → X) (sym (ρ̂-ref d τ₀))))))

  -- An import's reference: an FFI contract is ground; a definition at its
  -- ground instance is fixed.
  imp-tm : ∀ {n} {Γ : C.Ctx n} {T} cn k (ia : ImportAt T) → VN.NatImp S Δ τ r ia
         → proj₁ (importE {Γ = ρ̂S Γ} cn k ia) ≡ ρ̂ₜ (proj₁ (importE {Γ = Γ} cn k ia))
  imp-tm cn k (ffi h g) _  = refl
  imp-tm cn k (def d i) ni = cong (G.ref d) (sym ni)

  imp-dr : ∀ {n} {Γ : C.Ctx n} {T} cn k (ia : ImportAt T) → VN.NatImp S Δ τ r ia
         → proj₂ (importE {Γ = ρ̂S Γ} cn k ia) ≅ ρ̂ᶜ (proj₂ (importE {Γ = Γ} cn k ia))
  imp-dr cn k (ffi h g) _  = H.sym (rmA (λ X → X) (sym (ρ̂-rf g)))
  imp-dr {Γ = Γ} cn k (def d (τ′ , r′ , e′)) ni =
    H.trans (rmA (λ X → X) e′)
      (H.trans (≅ref (sym ni)) (H.sym (H.trans (ρ̂ᶜ-sA (λ X → X) e′) (rmA (λ X → X) (sym (ρ̂-ref d τ′))))))

  closeH : ∀ {n} {Γ : C.Ctx n} {t₁ t₂ A₁ A₂ π} {D₁ : C.∅ ⊢[ C.zeroUsage ] t₁ ∷ A₁ ! π} {D₂ : C.∅ ⊢[ C.zeroUsage ] t₂ ∷ A₂ ! π}
         → t₁ ≡ t₂ → A₁ ≡ A₂ → D₁ ≅ D₂ → RN.⊢close {Γ = Γ} D₁ ≅ RN.⊢close {Γ = Γ} D₂
  closeH refl refl H.refl = H.refl

  ≅app : ∀ {n} {Γ : C.Ctx n} {Ψ₁ Ψ₂ q π A₁ A₂ B₁ B₂ f₁ f₂ x₁ x₂}
           {df₁ : Γ ⊢[ Ψ₁ ] f₁ ∷ A₁ T.⇒[ mk-kind q π ] B₁ ! π} {df₂ : Γ ⊢[ Ψ₁ ] f₂ ∷ A₂ T.⇒[ mk-kind q π ] B₂ ! π}
           {dx₁ : Γ ⊢[ Ψ₂ ] x₁ ∷ A₁ ! π} {dx₂ : Γ ⊢[ Ψ₂ ] x₂ ∷ A₂ ! π}
       → A₁ ≡ A₂ → B₁ ≡ B₂ → f₁ ≡ f₂ → df₁ ≅ df₂ → x₁ ≡ x₂ → dx₁ ≅ dx₂ → GT.⊢app df₁ dx₁ ≅ GT.⊢app df₂ dx₂
  ≅app refl refl refl H.refl refl H.refl = H.refl

  -- The arm combinators' terms: `let′ f (let′ (wk g) B)`.
  arms : ∀ {n} {f₁ f g₁ g : G.Tm n} {B : G.Tm (suc (suc n))} → f₁ ≡ ρ̂ₜ f → g₁ ≡ ρ̂ₜ g
       → G.let′ f₁ (G.let′ (G.wk g₁) B) ≡ G.let′ (ρ̂ₜ f) (G.let′ (ρ̂ₜ (G.wk g)) B)
  arms ef eg = cong₂ (λ a b → G.let′ a (G.let′ b _)) ef (trans (cong G.wk eg) (sym (ρ̂ₜ-ren suc _)))

  closeT : ∀ {n} {t₁ t : G.Tm 0} → t₁ ≡ ρ̂ₜ t → RN.close {n} t₁ ≡ ρ̂ₜ (RN.close t)
  closeT et = trans (cong RN.close et) (sym (ρ̂ₜ-ren _ _))

  ≅coerce : ∀ {n} {Γ : C.Ctx n} {Ψ π A B t₁ t₂} {p₁ p₂ : A Once.Type.Sub.<: B}
              {d₁ : Γ ⊢[ Ψ ] t₁ ∷ A ! π} {d₂ : Γ ⊢[ Ψ ] t₂ ∷ A ! π}
          → t₁ ≡ t₂ → d₁ ≅ d₂ → GT.⊢coerce p₁ d₁ ≅ GT.⊢coerce p₂ d₂
  ≅coerce {p₁ = p₁} {p₂} refl H.refl rewrite <:-unique p₁ p₂ = H.refl

------------------------------------------------------------------------
-- THE INDUCTION.
------------------------------------------------------------------------

mutual
  tm-i : ∀ {n Γ D fr e A Ψ} (d : mkCtx n Γ D fr imps polys ⊢ᵢ e ∶ A ⨾ Ψ)
       → proj₁ (elabᵢ V (subst-i′ ir d)) ≡ ρ̂ₜ (proj₁ (elabᵢ V d))
  tm-i (t-int k)          = refl
  tm-i (t-float i f l p)  = refl
  tm-i (t-str x)          = refl
  tm-i t-unit             = refl
  tm-i t-unit-var         = refl
  tm-i {D = D} (t-var-local {eV = C.svar i} eq) = ⇝ᵢ-tm (lookup-ρ̂ D i) _
  tm-i (t-var-qualified li c) = trans (⇝ᵢ-tm (sym (ρ̂-rf (ir li))) _) (imp-tm _ c (imported li) (nat-imp li))
  tm-i (t-var-resolved ng li c) = trans (⇝ᵢ-tm (sym (ρ̂-rf (ir li))) _) (imp-tm _ c (imported li) (nat-imp li))
  tm-i (t-var-import gw ln li c) = trans (⇝ᵢ-tm (sym (ρ̂-rf (ir li))) _) (imp-tm _ c (imported li) (nat-imp li))
  tm-i (t-var-poly-instantiate-infer {schema = sc} {g = g} ln li lp gr refl) =
    trans (⇝ᵢ-tm (sym (ρ̂-rf (extractGround-rf sc g))) _) (cong (G.ref (entry lp)) (sym (nat-ground lp g)))
  tm-i (t-annot rf d)     = trans (⇝ᵢ-tm (sym (ρ̂-rf rf)) _) (trans (⇝ᶜ-tm (ρ̂-rf rf) _) (tm-c d))
  tm-i (t-pair a b)       = cong₂ G.pair (tm-i a) (tm-i b)
  tm-i (t-neg d)          = cong (G.prim G.p-neg) (tm-i d)
  tm-i (t-neg-float i f l p) = refl
  tm-i (t-let d₁ d₂)      = cong₂ G.let′ (tm-i d₁) (tm-i d₂)
  tm-i (t-case ds dl dr)  = trans (cong₂ (λ a b → G.case a b _) (tm-i ds) (tm-i dl)) (cong (G.case _ _) (tm-i dr))
  tm-i (t-binop-arith {op = OpAdd} o d₁ d₂) = cong (G.prim G.p-add) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-arith {op = OpSub} o d₁ d₂) = cong (G.prim G.p-sub) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-arith {op = OpMul} o d₁ d₂) = cong (G.prim G.p-mul) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-arith {op = OpDiv} o d₁ d₂) = cong (G.prim G.p-div) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-arith {op = OpMod} o d₁ d₂) = cong (G.prim G.p-mod) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-arith {op = OpLt} () _ _)
  tm-i (t-binop-arith {op = OpLe} () _ _)
  tm-i (t-binop-arith {op = OpGt} () _ _)
  tm-i (t-binop-arith {op = OpGe} () _ _)
  tm-i (t-binop-arith {op = OpEq} () _ _)
  tm-i (t-binop-arith {op = OpNe} () _ _)
  tm-i (t-binop-arith-float {op = OpAdd} o d₁ d₂) = cong (G.prim G.p-fadd) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-arith-float {op = OpSub} o d₁ d₂) = cong (G.prim G.p-fsub) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-arith-float {op = OpMul} o d₁ d₂) = cong (G.prim G.p-fmul) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-arith-float {op = OpDiv} o d₁ d₂) = cong (G.prim G.p-fdiv) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-arith-float {op = OpMod} () _ _)
  tm-i (t-binop-arith-float {op = OpLt} () _ _)
  tm-i (t-binop-arith-float {op = OpLe} () _ _)
  tm-i (t-binop-arith-float {op = OpGt} () _ _)
  tm-i (t-binop-arith-float {op = OpGe} () _ _)
  tm-i (t-binop-arith-float {op = OpEq} () _ _)
  tm-i (t-binop-arith-float {op = OpNe} () _ _)
  tm-i (t-binop-arith-float-il {op = OpAdd} o d₁ d₂) = cong (G.prim G.p-fadd) (cong₂ G.pair (cong (G.prim G.p-i2f) (tm-i d₁)) (tm-i d₂))
  tm-i (t-binop-arith-float-il {op = OpSub} o d₁ d₂) = cong (G.prim G.p-fsub) (cong₂ G.pair (cong (G.prim G.p-i2f) (tm-i d₁)) (tm-i d₂))
  tm-i (t-binop-arith-float-il {op = OpMul} o d₁ d₂) = cong (G.prim G.p-fmul) (cong₂ G.pair (cong (G.prim G.p-i2f) (tm-i d₁)) (tm-i d₂))
  tm-i (t-binop-arith-float-il {op = OpDiv} o d₁ d₂) = cong (G.prim G.p-fdiv) (cong₂ G.pair (cong (G.prim G.p-i2f) (tm-i d₁)) (tm-i d₂))
  tm-i (t-binop-arith-float-il {op = OpMod} () _ _)
  tm-i (t-binop-arith-float-il {op = OpLt} () _ _)
  tm-i (t-binop-arith-float-il {op = OpLe} () _ _)
  tm-i (t-binop-arith-float-il {op = OpGt} () _ _)
  tm-i (t-binop-arith-float-il {op = OpGe} () _ _)
  tm-i (t-binop-arith-float-il {op = OpEq} () _ _)
  tm-i (t-binop-arith-float-il {op = OpNe} () _ _)
  tm-i (t-binop-arith-float-ir {op = OpAdd} o d₁ d₂) = cong (G.prim G.p-fadd) (cong₂ G.pair (tm-i d₁) (cong (G.prim G.p-i2f) (tm-i d₂)))
  tm-i (t-binop-arith-float-ir {op = OpSub} o d₁ d₂) = cong (G.prim G.p-fsub) (cong₂ G.pair (tm-i d₁) (cong (G.prim G.p-i2f) (tm-i d₂)))
  tm-i (t-binop-arith-float-ir {op = OpMul} o d₁ d₂) = cong (G.prim G.p-fmul) (cong₂ G.pair (tm-i d₁) (cong (G.prim G.p-i2f) (tm-i d₂)))
  tm-i (t-binop-arith-float-ir {op = OpDiv} o d₁ d₂) = cong (G.prim G.p-fdiv) (cong₂ G.pair (tm-i d₁) (cong (G.prim G.p-i2f) (tm-i d₂)))
  tm-i (t-binop-arith-float-ir {op = OpMod} () _ _)
  tm-i (t-binop-arith-float-ir {op = OpLt} () _ _)
  tm-i (t-binop-arith-float-ir {op = OpLe} () _ _)
  tm-i (t-binop-arith-float-ir {op = OpGt} () _ _)
  tm-i (t-binop-arith-float-ir {op = OpGe} () _ _)
  tm-i (t-binop-arith-float-ir {op = OpEq} () _ _)
  tm-i (t-binop-arith-float-ir {op = OpNe} () _ _)
  tm-i (t-binop-cmp {op = OpLt} o d₁ d₂) = cong (G.prim G.p-lt) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-cmp {op = OpLe} o d₁ d₂) = cong (G.prim G.p-le) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-cmp {op = OpGt} o d₁ d₂) = cong (G.prim G.p-gt) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-cmp {op = OpGe} o d₁ d₂) = cong (G.prim G.p-ge) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-cmp {op = OpEq} o d₁ d₂) = cong (G.prim G.p-eq) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-cmp {op = OpNe} o d₁ d₂) = cong (G.prim G.p-ne) (cong₂ G.pair (tm-i d₁) (tm-i d₂))
  tm-i (t-binop-cmp {op = OpAdd} () _ _)
  tm-i (t-binop-cmp {op = OpSub} () _ _)
  tm-i (t-binop-cmp {op = OpMul} () _ _)
  tm-i (t-binop-cmp {op = OpDiv} () _ _)
  tm-i (t-binop-cmp {op = OpMod} () _ _)
  tm-i (t-id-app d)          = cong (G.app _) (tm-i d)
  tm-i (t-fst-app d)         = cong (G.app _) (tm-i d)
  tm-i (t-snd-app d)         = cong (G.app _) (tm-i d)
  tm-i (t-terminal-app d)    = cong (G.app _) (tm-i d)
  tm-i (t-apply-app-infer d) = cong (G.app _) (tm-i d)
  tm-i (t-apply-eff-app-infer d) = cong (G.app _) (tm-i d)
  tm-i (t-Out-app-infer {F = F} wf refl d) = trans (⇝ᵢ-tm (sym (ρ̂-⟦⟧ F (ν-type F pure))) _) (cong (G.app _) (tm-i d))
  tm-i (t-Out-eff-app-infer {F = F} wf refl d) =
    trans (⇝ᵢ-tm (cong (λ X → T.Unit T.⇒[ mk-kind Many eff ] X) (sym (ρ̂-⟦⟧ F (ν-type F eff)))) _) (cong (G.app _) (tm-i d))
  tm-i (t-app h df dx)       = cong₂ G.app (tm-i df) (tm-c dx)
  tm-i (t-effApp h df dx) =
    cong₂ (λ a b → G.lam (G.app a b)) (trans (cong G.wk (tm-i df)) (sym (ρ̂ₜ-ren suc _)))
                                      (trans (cong G.wk (tm-c dx)) (sym (ρ̂ₜ-ren suc _)))
  tm-i (t-app-spine h da df) = cong₂ G.app (tm-d df) (tm-i da)

  tm-c : ∀ {n Γ D fr e A Ψ} (d : mkCtx n Γ D fr imps polys ⊢ᶜ e ∶ A ⨾ Ψ)
       → proj₁ (elabᶜ V (subst-c′ ir d)) ≡ ρ̂ₜ (proj₁ (elabᶜ V d))
  tm-c t-id-check             = refl
  tm-c t-fst-check            = refl
  tm-c t-snd-check            = refl
  tm-c t-terminal-morph-check = refl
  tm-c t-initial-morph-check  = refl
  tm-c t-inl-morph-check      = refl
  tm-c t-inr-morph-check      = refl
  tm-c (t-compose-check-g dg df) = arms (tm-c df) (tm-d dg)
  tm-c (t-compose-check-f {B = B} {C = C′′} {C′ = C′} {π = π} {π′ = π′} wf p dg) =
    arms {f = G.coerce (B T.⇒[ mk-kind Many π′ ] C′) (B T.⇒[ mk-kind Many π ] C′′) _} (cong (G.coerce _ _) (tm-i wf)) (tm-c dg)
  tm-c (t-case-copair-check df dg) = arms (tm-c df) (tm-c dg)
  tm-c (t-pair-morph-check df dg)  = arms (tm-c df) (tm-c dg)
  tm-c (t-curry-check df)          = cong (λ u → G.let′ u _) (tm-c df)
  tm-c (t-cata-check {F = F} {A = A} {π = π} wf da) =
    cong (λ u → G.let′ u _) (closeT (trans (⇝ᶜ-tm (cong (λ X → X T.⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A)) _) (tm-c da)))
  tm-c (t-ana-check {F = F} {A = A} {π = π} wf dc) =
    cong (λ u → G.lam (G.unfold u (G.var zero)))
         (trans (cong G.wk (closeT (trans (⇝ᶜ-tm (cong (λ X → ρ̂ A T.⇒[ mk-kind Many π ] X) (ρ̂-⟦⟧ F A)) _) (tm-c dc))))
                (sym (ρ̂ₜ-ren suc _)))
  tm-c (t-sub d p)          = cong (G.coerce _ _) (tm-i d)
  tm-c (t-lam le d)         = cong G.lam (tm-c d)
  tm-c (t-pair-lit-check a b) = cong₂ G.pair (tm-c a) (tm-c b)
  tm-c (t-In-app-check {F = F} wf d) = cong (G.app _) (trans (⇝ᶜ-tm (ρ̂-⟦⟧ F (μ-type F)) _) (tm-c d))
  tm-c (t-apply-check d)      = cong (G.app _) (tm-i d)
  tm-c (t-inl-app-check d)    = cong (G.app _) (tm-c d)
  tm-c (t-inr-app-check d)    = cong (G.app _) (tm-c d)
  tm-c (t-initial-app-check d) = cong (G.app _) (tm-c d)
  tm-c (t-var-poly-instantiate {schema = sc} ln li lp ng ki) =
    cong (G.ref (entry lp)) (nat-inst lp ng ki)

  tm-d : ∀ {n Γ D fr e A π B Ψ} (d : mkCtx n Γ D fr imps polys ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ)
       → proj₁ (elabᵈ V (subst-d′ ir d)) ≡ ρ̂ₜ (proj₁ (elabᵈ V d))
  tm-d (d-infer w p g)     = cong (G.coerce _ _) (tm-i w)
  tm-d (d-poly {schema = sc} ln li lp ng as cv ki g) =
    cong (G.coerce _ _) (cong (G.ref (entry lp)) (nat-inst lp ng ki))
  tm-d (d-lam le d)        = cong G.lam (tm-i d)
  tm-d (d-compose dg df)   = arms (tm-d df) (tm-d dg)
  tm-d d-id                = refl
  tm-d d-fst               = refl
  tm-d d-snd               = refl
  tm-d d-terminal          = refl
  tm-d d-initial           = refl
  tm-d (d-case df dg)      = arms (tm-d df) (tm-d dg)
  tm-d (d-pair df dg)      = arms (tm-d df) (tm-d dg)
  tm-d (d-cata {F = F} {A = A} {π = π} wf da) =
    cong (λ u → G.let′ u _) (closeT (trans (⇝ᵢ-tm (cong (λ X → X T.⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A)) _) (tm-i da)))

  dr-i : ∀ {n Γ D fr e A Ψ} (d : mkCtx n Γ D fr imps polys ⊢ᵢ e ∶ A ⨾ Ψ)
       → proj₂ (elabᵢ V (subst-i′ ir d)) ≅ ρ̂ᶜ (proj₂ (elabᵢ V d))
  dr-i (t-int k)          = H.refl
  dr-i (t-float i f l p)  = H.refl
  dr-i (t-str x)          = H.refl
  dr-i t-unit             = H.refl
  dr-i t-unit-var         = H.refl
  dr-i {D = D} (t-var-local {eV = C.svar i} eq) =
    H.trans (⇝ᵢ-dr (lookup-ρ̂ D i) _) (H.sym (rmA (λ X → X) (lookup-ρ̂ D i)))
  dr-i (t-var-qualified li c) = H.trans (⇝ᵢ-dr (sym (ρ̂-rf (ir li))) _) (imp-dr _ c (imported li) (nat-imp li))
  dr-i (t-var-resolved ng li c) = H.trans (⇝ᵢ-dr (sym (ρ̂-rf (ir li))) _) (imp-dr _ c (imported li) (nat-imp li))
  dr-i (t-var-import gw ln li c) = H.trans (⇝ᵢ-dr (sym (ρ̂-rf (ir li))) _) (imp-dr _ c (imported li) (nat-imp li))
  dr-i (t-var-poly-instantiate-infer {schema = sc} {g = g} ln li lp gr refl) =
    H.trans (⇝ᵢ-dr (sym (ρ̂-rf (extractGround-rf sc g))) _)
            (refE-dr (entry lp) (ground lp g) (ground lp g) (sym (nat-ground lp g)))
  dr-i (t-annot rf d)     = H.trans (⇝ᵢ-dr (sym (ρ̂-rf rf)) _) (H.trans (⇝ᶜ-dr (ρ̂-rf rf) _) (dr-c d))
  dr-i (t-pair a b)       = ≅2 _ _ GT.⊢pair refl (tm-i a) (dr-i a) refl (tm-i b) (dr-i b)
  dr-i (t-neg d)          = ≅1 _ _ (GT.⊢prim G.p-neg) refl (tm-i d) (dr-i d)
  dr-i (t-neg-float i f l p) = H.refl
  dr-i (t-let d₁ d₂)      = ≅let refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂)
  dr-i (t-case ds dl dx)  = ≅case refl (tm-i ds) (dr-i ds) refl (tm-i dl) (dr-i dl) refl (tm-i dx) (dr-i dx)
  dr-i (t-binop-arith {op = OpAdd} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-add) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith {op = OpSub} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-sub) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith {op = OpMul} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-mul) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith {op = OpDiv} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-div) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith {op = OpMod} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-mod) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith {op = OpLt} () _ _)
  dr-i (t-binop-arith {op = OpLe} () _ _)
  dr-i (t-binop-arith {op = OpGt} () _ _)
  dr-i (t-binop-arith {op = OpGe} () _ _)
  dr-i (t-binop-arith {op = OpEq} () _ _)
  dr-i (t-binop-arith {op = OpNe} () _ _)
  dr-i (t-binop-arith-float {op = OpAdd} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fadd) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith-float {op = OpSub} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fsub) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith-float {op = OpMul} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fmul) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith-float {op = OpDiv} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fdiv) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith-float {op = OpMod} () _ _)
  dr-i (t-binop-arith-float {op = OpLt} () _ _)
  dr-i (t-binop-arith-float {op = OpLe} () _ _)
  dr-i (t-binop-arith-float {op = OpGt} () _ _)
  dr-i (t-binop-arith-float {op = OpGe} () _ _)
  dr-i (t-binop-arith-float {op = OpEq} () _ _)
  dr-i (t-binop-arith-float {op = OpNe} () _ _)
  dr-i (t-binop-arith-float-il {op = OpAdd} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fadd) refl (cong₂ G.pair (cong (G.prim G.p-i2f) (tm-i d₁)) (tm-i d₂))
      (≅2 _ _ GT.⊢pair refl (cong (G.prim G.p-i2f) (tm-i d₁)) (≅1 _ _ (GT.⊢prim G.p-i2f) refl (tm-i d₁) (dr-i d₁)) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith-float-il {op = OpSub} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fsub) refl (cong₂ G.pair (cong (G.prim G.p-i2f) (tm-i d₁)) (tm-i d₂))
      (≅2 _ _ GT.⊢pair refl (cong (G.prim G.p-i2f) (tm-i d₁)) (≅1 _ _ (GT.⊢prim G.p-i2f) refl (tm-i d₁) (dr-i d₁)) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith-float-il {op = OpMul} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fmul) refl (cong₂ G.pair (cong (G.prim G.p-i2f) (tm-i d₁)) (tm-i d₂))
      (≅2 _ _ GT.⊢pair refl (cong (G.prim G.p-i2f) (tm-i d₁)) (≅1 _ _ (GT.⊢prim G.p-i2f) refl (tm-i d₁) (dr-i d₁)) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith-float-il {op = OpDiv} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fdiv) refl (cong₂ G.pair (cong (G.prim G.p-i2f) (tm-i d₁)) (tm-i d₂))
      (≅2 _ _ GT.⊢pair refl (cong (G.prim G.p-i2f) (tm-i d₁)) (≅1 _ _ (GT.⊢prim G.p-i2f) refl (tm-i d₁) (dr-i d₁)) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-arith-float-il {op = OpMod} () _ _)
  dr-i (t-binop-arith-float-il {op = OpLt} () _ _)
  dr-i (t-binop-arith-float-il {op = OpLe} () _ _)
  dr-i (t-binop-arith-float-il {op = OpGt} () _ _)
  dr-i (t-binop-arith-float-il {op = OpGe} () _ _)
  dr-i (t-binop-arith-float-il {op = OpEq} () _ _)
  dr-i (t-binop-arith-float-il {op = OpNe} () _ _)
  dr-i (t-binop-arith-float-ir {op = OpAdd} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fadd) refl (cong₂ G.pair (tm-i d₁) (cong (G.prim G.p-i2f) (tm-i d₂)))
      (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (cong (G.prim G.p-i2f) (tm-i d₂)) (≅1 _ _ (GT.⊢prim G.p-i2f) refl (tm-i d₂) (dr-i d₂)))
  dr-i (t-binop-arith-float-ir {op = OpSub} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fsub) refl (cong₂ G.pair (tm-i d₁) (cong (G.prim G.p-i2f) (tm-i d₂)))
      (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (cong (G.prim G.p-i2f) (tm-i d₂)) (≅1 _ _ (GT.⊢prim G.p-i2f) refl (tm-i d₂) (dr-i d₂)))
  dr-i (t-binop-arith-float-ir {op = OpMul} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fmul) refl (cong₂ G.pair (tm-i d₁) (cong (G.prim G.p-i2f) (tm-i d₂)))
      (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (cong (G.prim G.p-i2f) (tm-i d₂)) (≅1 _ _ (GT.⊢prim G.p-i2f) refl (tm-i d₂) (dr-i d₂)))
  dr-i (t-binop-arith-float-ir {op = OpDiv} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-fdiv) refl (cong₂ G.pair (tm-i d₁) (cong (G.prim G.p-i2f) (tm-i d₂)))
      (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (cong (G.prim G.p-i2f) (tm-i d₂)) (≅1 _ _ (GT.⊢prim G.p-i2f) refl (tm-i d₂) (dr-i d₂)))
  dr-i (t-binop-arith-float-ir {op = OpMod} () _ _)
  dr-i (t-binop-arith-float-ir {op = OpLt} () _ _)
  dr-i (t-binop-arith-float-ir {op = OpLe} () _ _)
  dr-i (t-binop-arith-float-ir {op = OpGt} () _ _)
  dr-i (t-binop-arith-float-ir {op = OpGe} () _ _)
  dr-i (t-binop-arith-float-ir {op = OpEq} () _ _)
  dr-i (t-binop-arith-float-ir {op = OpNe} () _ _)
  dr-i (t-binop-cmp {op = OpLt} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-lt) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-cmp {op = OpLe} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-le) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-cmp {op = OpGt} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-gt) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-cmp {op = OpGe} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-ge) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-cmp {op = OpEq} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-eq) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-cmp {op = OpNe} o d₁ d₂) =
    ≅1 _ _ (GT.⊢prim G.p-ne) refl (cong₂ G.pair (tm-i d₁) (tm-i d₂)) (≅2 _ _ GT.⊢pair refl (tm-i d₁) (dr-i d₁) refl (tm-i d₂) (dr-i d₂))
  dr-i (t-binop-cmp {op = OpAdd} () _ _)
  dr-i (t-binop-cmp {op = OpSub} () _ _)
  dr-i (t-binop-cmp {op = OpMul} () _ _)
  dr-i (t-binop-cmp {op = OpDiv} () _ _)
  dr-i (t-binop-cmp {op = OpMod} () _ _)
  dr-i (t-id-app d)          = ≅2 _ _ GT.⊢app refl refl H.refl refl (tm-i d) (dr-i d)
  dr-i (t-fst-app d)         = ≅2 _ _ GT.⊢app refl refl H.refl refl (tm-i d) (dr-i d)
  dr-i (t-snd-app d)         = ≅2 _ _ GT.⊢app refl refl H.refl refl (tm-i d) (dr-i d)
  dr-i (t-terminal-app d)    = ≅2 _ _ GT.⊢app refl refl H.refl refl (tm-i d) (dr-i d)
  dr-i (t-apply-app-infer d) = ≅2 _ _ GT.⊢app refl refl (H.sym c-apply) refl (tm-i d) (dr-i d)
  dr-i (t-apply-eff-app-infer d) = ≅2 _ _ GT.⊢app refl refl (H.sym c-applyEff) refl (tm-i d) (dr-i d)
  dr-i (t-Out-app-infer {F = F} wf refl d) =
    H.trans (⇝ᵢ-dr (sym (ρ̂-⟦⟧ F (ν-type F pure))) _)
            (≅app refl (sym (ρ̂-⟦⟧ F (ν-type F pure))) refl (H.sym (c-out wf)) (tm-i d) (dr-i d))
  dr-i (t-Out-eff-app-infer {F = F} wf refl d) =
    H.trans (⇝ᵢ-dr (cong (λ X → T.Unit T.⇒[ mk-kind Many eff ] X) (sym (ρ̂-⟦⟧ F (ν-type F eff)))) _)
            (≅app refl (cong (λ X → T.Unit T.⇒[ mk-kind Many eff ] X) (sym (ρ̂-⟦⟧ F (ν-type F eff))))
                  refl (H.sym (c-outEff wf)) (tm-i d) (dr-i d))
  dr-i (t-app h df dx)       = ≅2 _ _ GT.⊢app refl (tm-i df) (dr-i df) refl (tm-c dx) (dr-c dx)
  dr-i (t-effApp h df dx)    =
    H.trans (≅2 _ _ DT.⊢effAppᶜ refl (tm-i df) (dr-i df) refl (tm-c dx) (dr-c dx)) (H.sym (c-effApp (proj₂ (elabᵢ V df)) (proj₂ (elabᶜ V dx))))
  dr-i (t-app-spine h da df) = ≅2 _ _ GT.⊢app refl (tm-d df) (dr-d df) refl (tm-i da) (dr-i da)

  dr-c : ∀ {n Γ D fr e A Ψ} (d : mkCtx n Γ D fr imps polys ⊢ᶜ e ∶ A ⨾ Ψ)
       → proj₂ (elabᶜ V (subst-c′ ir d)) ≅ ρ̂ᶜ (proj₂ (elabᶜ V d))
  dr-c t-id-check             = H.refl
  dr-c t-fst-check            = H.refl
  dr-c t-snd-check            = H.refl
  dr-c t-terminal-morph-check = H.refl
  dr-c t-initial-morph-check  = H.refl
  dr-c t-inl-morph-check      = H.refl
  dr-c t-inr-morph-check      = H.refl
  dr-c (t-compose-check-g dg df) =
    H.trans (≅2 _ _ DT.⊢composeᶜ refl (tm-c df) (dr-c df) refl (tm-d dg) (dr-d dg)) (H.sym (c-compose (proj₂ (elabᶜ V df)) (proj₂ (elabᵈ V dg))))
  dr-c (t-compose-check-f {B = B} {C = C′′} {C′ = C′} {π = π} {π′ = π′} wf p dg) =
    H.trans (≅2 _ _ DT.⊢composeᶜ refl
                 (cong (G.coerce (ρ̂ (B T.⇒[ mk-kind Many π′ ] C′)) (ρ̂ (B T.⇒[ mk-kind Many π ] C′′))) (tm-i wf))
                 (≅1 _ _ (GT.⊢coerce (ρ̂-<: p)) refl (tm-i wf) (dr-i wf))
                 refl (tm-c dg) (dr-c dg))
            (H.sym (c-compose (GT.⊢coerce p (proj₂ (elabᵢ V wf))) (proj₂ (elabᶜ V dg))))
  dr-c (t-case-copair-check df dg) =
    H.trans (≅2 _ _ DT.⊢caseᶜ refl (tm-c df) (dr-c df) refl (tm-c dg) (dr-c dg)) (H.sym (c-case (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg))))
  dr-c (t-pair-morph-check df dg) =
    H.trans (≅2 _ _ DT.⊢pairᶜ refl (tm-c df) (dr-c df) refl (tm-c dg) (dr-c dg)) (H.sym (c-pair (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg))))
  dr-c (t-curry-check {π₀ = π₀} df) =
    H.trans (≅1 _ _ (DT.⊢curryᶜ {π₀ = π₀}) refl (tm-c df) (dr-c df)) (H.sym (c-curry {π₀ = π₀} (proj₂ (elabᶜ V df))))
  dr-c (t-cata-check {F = F} {A = A} {π = π} wf da) =
    H.trans (≅1 _ _ (DT.⊢cataᶜ (ρ̂-wf wf)) refl (closeT TE)
                (H.trans (closeH TE (sym q) (H.trans (⇝ᶜ-dr q _) (dr-c da)))
                  (H.trans (H.sym (close≅ (proj₂ (elabᶜ V da))))
                           (H.sym (rmA (λ X → X T.⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A))))))
            (H.sym (c-cata wf (RN.⊢close (proj₂ (elabᶜ V da)))))
    where
      q  = cong (λ X → X T.⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A)
      TE = trans (⇝ᶜ-tm q _) (tm-c da)
  dr-c (t-ana-check {F = F} {A = A} {π₀ = π₀} {π = π} wf dc) =
    H.trans (≅1 _ _ (DT.⊢anaᶜ {π₀ = π₀} (ρ̂-wf wf)) refl (closeT TE)
                (H.trans (closeH TE (sym q) (H.trans (⇝ᶜ-dr q _) (dr-c dc)))
                  (H.trans (H.sym (close≅ (proj₂ (elabᶜ V dc))))
                           (H.sym (rmA (λ X → ρ̂ A T.⇒[ mk-kind Many π ] X) (ρ̂-⟦⟧ F A))))))
            (H.sym (c-ana {π₀ = π₀} wf (RN.⊢close (proj₂ (elabᶜ V dc)))))
    where
      q  = cong (λ X → ρ̂ A T.⇒[ mk-kind Many π ] X) (ρ̂-⟦⟧ F A)
      TE = trans (⇝ᶜ-tm q _) (tm-c dc)
  dr-c (t-sub d p)           = ≅1 _ _ (GT.⊢coerce (ρ̂-<: p)) refl (tm-i d) (dr-i d)
  dr-c (t-lam {π = π} le d)  =
    ≅lam refl (tm-c d) (≅1 _ _ (GT.⊢sub-eff (Once.Type.Sub.pure⊑ π)) refl (tm-c d) (dr-c d))
  dr-c (t-pair-lit-check a b) = ≅2 _ _ GT.⊢pair refl (tm-c a) (dr-c a) refl (tm-c b) (dr-c b)
  dr-c (t-In-app-check {F = F} wf d) =
    ≅app (sym (ρ̂-⟦⟧ F (μ-type F))) refl refl (H.sym (c-in wf))
         (trans (⇝ᶜ-tm (ρ̂-⟦⟧ F (μ-type F)) _) (tm-c d)) (H.trans (⇝ᶜ-dr (ρ̂-⟦⟧ F (μ-type F)) _) (dr-c d))
  dr-c (t-apply-check d)     = ≅2 _ _ GT.⊢app refl refl (H.sym c-apply) refl (tm-i d) (dr-i d)
  dr-c (t-inl-app-check d)   = ≅2 _ _ GT.⊢app refl refl H.refl refl (tm-c d) (dr-c d)
  dr-c (t-inr-app-check d)   = ≅2 _ _ GT.⊢app refl refl H.refl refl (tm-c d) (dr-c d)
  dr-c (t-initial-app-check d) = ≅2 _ _ GT.⊢app refl refl H.refl refl (tm-c d) (dr-c d)
  dr-c (t-var-poly-instantiate {schema = sc} ln li lp ng ki) =
    refE-dr (entry lp) (inst lp ng (ρ̂-ki {sc} ki)) (inst lp ng ki) (nat-inst lp ng ki)

  dr-d : ∀ {n Γ D fr e A π B Ψ} (d : mkCtx n Γ D fr imps polys ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ)
       → proj₂ (elabᵈ V (subst-d′ ir d)) ≅ ρ̂ᶜ (proj₂ (elabᵈ V d))
  dr-d (d-infer w p g)     = ≅coerce (tm-i w) (dr-i w)
  dr-d (d-poly {schema = sc} ln li lp ng as cv ki g) =
    ≅coerce (cong (G.ref (entry lp)) (nat-inst lp ng ki))
            (refE-dr (entry lp) (inst lp ng (ρ̂-ki {sc} ki)) (inst lp ng ki) (nat-inst lp ng ki))
  dr-d (d-lam {π = π} le d) =
    ≅lam refl (tm-i d) (≅1 _ _ (GT.⊢sub-eff (Once.Type.Sub.pure⊑ π)) refl (tm-i d) (dr-i d))
  dr-d (d-compose dg df)   =
    H.trans (≅2 _ _ DT.⊢composeᶜ refl (tm-d df) (dr-d df) refl (tm-d dg) (dr-d dg)) (H.sym (c-compose (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg))))
  dr-d d-id                = H.refl
  dr-d d-fst               = H.refl
  dr-d d-snd               = H.refl
  dr-d d-terminal          = H.refl
  dr-d d-initial           = H.refl
  dr-d (d-case df dg)      =
    H.trans (≅2 _ _ DT.⊢caseᶜ refl (tm-d df) (dr-d df) refl (tm-d dg) (dr-d dg)) (H.sym (c-case (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg))))
  dr-d (d-pair df dg)      =
    H.trans (≅2 _ _ DT.⊢pairᶜ refl (tm-d df) (dr-d df) refl (tm-d dg) (dr-d dg)) (H.sym (c-pair (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg))))
  dr-d (d-cata {F = F} {A = A} {π = π} wf da) =
    H.trans (≅1 _ _ (DT.⊢cataᶜ (ρ̂-wf wf)) refl (closeT TE)
                (H.trans (closeH TE (sym q) (H.trans (⇝ᵢ-dr q _) (dr-i da)))
                  (H.trans (H.sym (close≅ (proj₂ (elabᵢ V da))))
                           (H.sym (rmA (λ X → X T.⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A))))))
            (H.sym (c-cata wf (RN.⊢close (proj₂ (elabᵢ V da)))))
    where
      q  = cong (λ X → X T.⇒[ mk-kind Many π ] ρ̂ A) (ρ̂-⟦⟧ F A)
      TE = trans (⇝ᵢ-tm q _) (tm-i da)

------------------------------------------------------------------------
-- THE RESULT: the substituted derivation elaborates to the substituted
-- elaboration.
------------------------------------------------------------------------

private
  Σ≅ : ∀ {X : Set} {P : X → Set} {a₁ a₂ : X} {b₁ : P a₁} {b₂ : P a₂} → a₁ ≡ a₂ → b₁ ≅ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
  Σ≅ refl H.refl = refl

elab-ρ̂ᶜ : ∀ {n Γ D fr e A Ψ} (d : mkCtx n Γ D fr imps polys ⊢ᶜ e ∶ A ⨾ Ψ)
        → elabᶜ V (subst-c′ ir d) ≡ (ρ̂ₜ (proj₁ (elabᶜ V d)) , ρ̂ᶜ (proj₂ (elabᶜ V d)))
elab-ρ̂ᶜ d = Σ≅ (tm-c d) (dr-c d)
