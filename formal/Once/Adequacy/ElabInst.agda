-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ElabInst — plan 0.104 E.2, plan 0.122: ELABORATION COMMUTES
-- WITH INSTANTIATION (the semantic half of rank-1 polymorphism, D243).
--
-- A polymorphic entry is typed once over its parameters and elaborated there;
-- a use means it instantiated (`ty-subst-⊢`). The compiler instead
-- re-elaborates the body at the instance (the resolver's splice). The two
-- agree: the body's derivation at the instance is the surface substitution
-- instance of the polymorphic one (`TypeCheck.TySubst.subst-c`), and
-- elaborating THAT is the substitution of the elaboration (`ElabCommute`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (TySub)

module Once.Adequacy.ElabInst (Σ : Signature) (fmt : TargetNum) {s : ℕ} (S : Defs s) (σ₀ : TySub 0 0) where

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (Ty; Type; ∅ₖ; KCtx; _⟨_⟩)
open import Once.Spec.Context using (Ctx; [])
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Internal.Type.Instance using (KindedInstance; rigidOf; kindsOf)
open import Once.Internal.Type.Schema using (kinded-instance)
open import Once.Internal.Typing.Scope using (NamedCtx; PolyCtx)
open import Once.TypeCheck.Classify using (ctxAt; TopCtx)
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_)
open import Once.Denotation.SpecDomain Σ σ₀ using (⟦_⟧ᵛ)
import Once.Spec.Core.Meaning Σ fmt S as SM
open import Once.Adequacy.CoreMeaningBridge fmt Σ S σ₀ using (⟦_⟧ₛ)
open import Once.Spec.Core.Typing Σ S
import Once.Metatheory.TermModel.TySubst Σ S as TS
open import Once.Internal.Elaboration Σ S using (View; Views; elabᶜ)
import Once.TypeCheck.TySubst as RS
import Once.TypeCheck.Instance as Inst
import Once.Adequacy.ElabCommute as EC

inst-at = Inst.inst-at

-- A derivation's meaning does not depend on how its term is written.
⟦⟧-≅ : ∀ {n} {Δ : KCtx 0} {Γ : Ctx 0 n} {Ψ t t′ A π} {d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π} {d′ : Δ ⊩ Γ ⊢[ Ψ ] t′ ∷ A ! π}
     → t ≡ t′ → d ≅ d′ → ⟦ d ⟧ₛ ≡ ⟦ d′ ⟧ₛ
⟦⟧-≅ refl H.refl = refl

-- Elaborating a derivation moved along a type equation means the moved meaning.
elab-subst-sem : ∀ {A B : Type} {ctx : NamedCtx 0} {body Ψ} (V : Views ctx) (e : A ≡ B) (D : ctx ⊢ᶜ body ∶ A ⨾ Ψ)
                   (δ : SM.DefSem) (γ : SM.Env σ₀ (NamedCtx.debruijn ctx) Ψ)
               → ⟦ proj₂ (elabᶜ V (subst (λ X → ctx ⊢ᶜ body ∶ X ⨾ Ψ) e D)) ⟧ₛ δ γ
                 ≡ subst (λ X → ⟦ X ⟧ᵛ) e (⟦ proj₂ (elabᶜ V D) ⟧ₛ δ γ)
elab-subst-sem V refl D δ γ = refl

-- A body checked over its parameters, used at a kinded ground instance,
-- means its elaboration instantiated.
poly-instance-sem : ∀ {tc : TopCtx} {polys : PolyCtx} (V : View (TopCtx.tdefs tc) (TopCtx.tsig tc) polys)
                      (δ : SM.DefSem) {body} (sc : PolyType)
                      (D : ctxAt (kindsOf sc) tc polys ⊢ᶜ body ∶ rigidOf sc ⨾ []) {U : Type} (ki : KindedInstance ∅ₖ sc U)
                  → ⟦ proj₂ (elabᶜ V (inst-at sc D ki)) ⟧ₛ δ tt
                    ≡ subst (λ X → ⟦ X ⟧ᵛ) (proj₂ (proj₂ (kinded-instance sc ki)))
                        (⟦ TS.ty-subst-⊢ (proj₁ (kinded-instance sc ki)) (proj₁ (proj₂ (kinded-instance sc ki))) (proj₂ (elabᶜ V D)) ⟧ₛ δ tt)
poly-instance-sem {tc} {polys} V δ sc D ki =
  trans (elab-subst-sem V e (RS.subst-c (kindsOf sc) ∅ₖ τ r {ctx = ctxAt (kindsOf sc) tc polys} D) δ tt)
        (cong (subst (λ X → ⟦ X ⟧ᵛ) e)
              (cong (λ f → f δ tt) (⟦⟧-≅ (EC.Comm.tm C) (EC.Comm.dr C))))
  where
    τ = proj₁ (kinded-instance sc ki)
    r = proj₁ (proj₂ (kinded-instance sc ki))
    e = proj₂ (proj₂ (kinded-instance sc ki))
    C = EC.cm-c Σ S (kindsOf sc) ∅ₖ τ r V D
