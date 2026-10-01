-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ElabInst — plan 0.104 E.2: ELABORATION COMMUTES WITH
-- INSTANTIATION (the semantic half of rank-1 polymorphism, D243).
--
-- A polymorphic entry is typed once at its rigid schema, elaborated, and
-- stored abstracted (`abs-⊢`); a use reads it back instantiated
-- (`instantiate`). The compiler instead re-elaborates the body at the
-- instance (the resolver's splice). The two agree: the body's derivation at
-- the instance is the surface substitution instance of the rigid one
-- (`RigidSubst.subst-c`), and elaborating THAT gives the core instantiation of
-- the abstracted elaboration.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

module Once.Adequacy.ElabInst {s : ℕ} (S : Sig s) where

open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Target.Arch using (TargetNum)
open import Once.Type using (Type; PolyType; pure; Ground)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)
open import Once.Type.Rigid using (KindedInstance; rigidOf)
import Once.Surface.Context as C
open import Once.Spec.Core.PolyTy using (KCtx; GSub; Respects; _⟪_⟫)
open import Once.Spec.Core.AbsTy using (absTy)
open import Once.Spec.Core.Schema using (kindsOf; kinded-instance)
open import Once.TypeCheck.Classify using (Imports; PolyCtx; NamedCtx; ctxWithImportsAndPolys; lookupPolyPrefix)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ)
import Once.TypeCheck.RigidSubst as RS
import Once.Spec.Core.PolyTyping S as PT
open import Once.Spec.Core.Abstract S using (SigGround; abs-⊢)
import Once.Spec.Core.Meaning S as GM
open import Once.Spec.Elaboration S using (View; Views; elabᶜ; ImportAt; ffi; def)

------------------------------------------------------------------------
-- The view must agree with instantiation: a use at the substituted instance
-- finds the substituted instance of the entry. (`viewOf` does: its instance is
-- `τOf sc θ`, pointwise in `θ`.)
------------------------------------------------------------------------

module _ {m} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) where
  -- An imported definition is used at a ground instance, so it is fixed.
  NatImp : ∀ {T} → ImportAt T → Set
  NatImp (ffi _ _) = ⊤
  NatImp (def d i) = (λ j → RS.ρ̂ Δ τ r (proj₁ i j)) ≡ proj₁ i

  record Natural {imps : Imports} {polys : PolyCtx} (V : View imps polys) : Set where
    field
      nat-inst : ∀ {x sc body prefix T} (lp : lookupPolyPrefix polys x ≡ Data.Maybe.just (sc , body , prefix))
                   (ng : ¬ Ground sc) (ki : KindedInstance sc T)
               → proj₁ (View.inst V lp ng (RS.ρ̂-ki Δ τ r {sc} ki)) ≡ (λ i → RS.ρ̂ Δ τ r (proj₁ (View.inst V lp ng ki) i))
      nat-ground : ∀ {x sc body prefix} (lp : lookupPolyPrefix polys x ≡ Data.Maybe.just (sc , body , prefix)) (g : Ground sc)
                 → (λ i → RS.ρ̂ Δ τ r (proj₁ (View.ground V lp g) i)) ≡ proj₁ (View.ground V lp g)
      nat-imp : ∀ {x T} (lk : Once.TypeCheck.Classify.lookupImport imps x ≡ Data.Maybe.just T) → NatImp (View.imported V lk)

-- RESIDUAL (plan 0.104 E.2, deferred proof, to be discharged next): the
-- elaboration of the substituted derivation means what the instantiated
-- abstraction of the elaboration means.
postulate
  elab-inst-sem : ∀ {imps : Imports} {polys : PolyCtx} (V : View imps polys)
                    {m} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) (nat : Natural Δ τ r V) (sg : SigGround)
                    (ir : RS.ImportsRF Δ τ r imps)
                    {body : _} {A : Type} (D : ctxWithImportsAndPolys imps polys ⊢ᶜ body ∶ A ⨾ C.Usage.[])
                    (fmt : TargetNum) (δ : GM.DefSem)
                → GM.⟦ proj₂ (elabᶜ V (RS.subst-c Δ τ r ir D)) ⟧ fmt δ tt
                  ≡ GM.⟦ PT.instantiate τ r (abs-⊢ Δ sg (proj₂ (elabᶜ V D))) ⟧ fmt δ tt

-- A transport of the checked type moves the elaboration's meaning with it.
elab-subst-sem : ∀ {ctx body A B Ψ} (V : Views ctx) (e : A ≡ B) (D : ctx ⊢ᶜ body ∶ A ⨾ Ψ)
                   (fmt : TargetNum) (δ : GM.DefSem) (γ : GM.Env (NamedCtx.debruijn ctx) Ψ)
               → GM.⟦ proj₂ (elabᶜ V (subst (λ X → ctx ⊢ᶜ body ∶ X ⨾ Ψ) e D)) ⟧ fmt δ γ
                 ≡ subst (λ X → ⟦ X ⟧ᵛ) e (GM.⟦ proj₂ (elabᶜ V D) ⟧ fmt δ γ)
elab-subst-sem V refl D fmt δ γ = refl

------------------------------------------------------------------------
-- THE CONSUMER (TeleWalk's 6e step): the body at a kinded instance means the
-- entry's abstraction instantiated there.
------------------------------------------------------------------------

inst-at : ∀ {imps : Imports} {polys : PolyCtx} {body : _} (sc : PolyType)
        → (∀ {x T} → Once.TypeCheck.Classify.lookupImport imps x ≡ Data.Maybe.just T → Once.Type.Rigid.RigidFree T)
        → ctxWithImportsAndPolys imps polys ⊢ᶜ body ∶ rigidOf sc ⨾ C.Usage.[] → ∀ {U} → KindedInstance sc U
        → ctxWithImportsAndPolys imps polys ⊢ᶜ body ∶ U ⨾ C.Usage.[]
inst-at sc irf D ki =
  subst (λ X → _ ⊢ᶜ _ ∶ X ⨾ C.Usage.[]) (proj₂ (proj₂ (kinded-instance sc ki)))
        (RS.subst-c (kindsOf sc) (proj₁ (kinded-instance sc ki)) (proj₁ (proj₂ (kinded-instance sc ki))) irf D)

poly-instance-sem : ∀ {imps : Imports} {polys : PolyCtx} (V : View imps polys) (sg : SigGround)
                      (fmt : TargetNum) (δ : GM.DefSem) {body : _} (sc : PolyType)
                      (nat : ∀ {U} (ki : KindedInstance sc U)
                             → Natural (kindsOf sc) (proj₁ (kinded-instance sc ki)) (proj₁ (proj₂ (kinded-instance sc ki))) V)
                      (irf : ∀ {x T} → Once.TypeCheck.Classify.lookupImport imps x ≡ Data.Maybe.just T → Once.Type.Rigid.RigidFree T)
                      (D : ctxWithImportsAndPolys imps polys ⊢ᶜ body ∶ rigidOf sc ⨾ C.Usage.[]) {U : Type} (ki : KindedInstance sc U)
                  → GM.⟦ proj₂ (elabᶜ V (inst-at sc irf D ki)) ⟧ fmt δ tt
                    ≡ subst (λ X → ⟦ X ⟧ᵛ) (proj₂ (proj₂ (kinded-instance sc ki)))
                        (GM.⟦ PT.instantiate (proj₁ (kinded-instance sc ki)) (proj₁ (proj₂ (kinded-instance sc ki)))
                                (abs-⊢ (kindsOf sc) sg (proj₂ (elabᶜ V D))) ⟧ fmt δ tt)
poly-instance-sem V sg fmt δ sc nat irf D ki =
  trans (elab-subst-sem V e (RS.subst-c (kindsOf sc) τ rk irf D) fmt δ tt)
        (cong (subst (λ X → ⟦ X ⟧ᵛ) e) (elab-inst-sem V (kindsOf sc) τ rk (nat ki) sg irf D fmt δ))
  where
    τ  = proj₁ (kinded-instance sc ki)
    rk = proj₁ (proj₂ (kinded-instance sc ki))
    e  = proj₂ (proj₂ (kinded-instance sc ki))
