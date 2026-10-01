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
open import Data.List using (_∷_)
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
import Once.Adequacy.CoreInst as CI
import Once.Spec.Core.PolyTyping S as PT
open import Once.Spec.Core.Abstract S using (SigGround; abs-⊢)
import Once.Spec.Core.Meaning S as GM
open import Once.Spec.Elaboration S using (View; Views; elabᶜ; ImportAt; ffi; def)

------------------------------------------------------------------------
-- The view must agree with instantiation: a use at the substituted instance
-- finds the substituted instance of the entry. (`viewOf` does: its instance is
-- `τOf sc θ`, pointwise in `θ`.)
------------------------------------------------------------------------

open import Once.Adequacy.ViewNatural S using (NatImp; Natural; module Natural)

-- (ii) elaborating the substituted derivation is substituting the
-- elaboration (`ElabCommute`).
import Once.Adequacy.ElabCommute as EC
module _ {m} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) where
  elab-ρ̂ᶜ : ∀ {imps : Imports} {polys : PolyCtx} (V : View imps polys) (nat : Natural Δ τ r V) (sg : SigGround)
              (ir : RS.ImportsRF Δ τ r imps) {n Γ D fr e A Ψ}
              (d : Once.TypeCheck.Classify.mkCtx n Γ D fr imps polys ⊢ᶜ e ∶ A ⨾ Ψ)
          → elabᶜ V (RS.subst-c′ Δ τ r ir d) ≡ (CI.ρ̂ₜ S Δ τ r (proj₁ (elabᶜ V d)) , CI.WithSG.ρ̂ᶜ S Δ τ r sg (proj₂ (elabᶜ V d)))
  elab-ρ̂ᶜ V nat sg ir d = EC.elab-ρ̂ᶜ S Δ τ r sg V nat ir d

-- The elaboration of the substituted derivation means what the instantiated
-- abstraction of the elaboration means: (ii), then (i) at the empty context.
elab-inst-sem : ∀ {imps : Imports} {polys : PolyCtx} (V : View imps polys)
                  {m} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) (nat : Natural Δ τ r V) (sg : SigGround)
                  (ir : RS.ImportsRF Δ τ r imps)
                  {body : _} {A : Type} (D : ctxWithImportsAndPolys imps polys ⊢ᶜ body ∶ A ⨾ C.Usage.[])
                  (fmt : TargetNum) (δ : GM.DefSem)
              → GM.⟦ proj₂ (elabᶜ V (RS.subst-c Δ τ r ir D)) ⟧ fmt δ tt
                ≡ GM.⟦ PT.instantiate τ r (abs-⊢ Δ sg (proj₂ (elabᶜ V D))) ⟧ fmt δ tt
elab-inst-sem V Δ τ r nat sg ir D fmt δ =
  trans (cong (λ X → GM.⟦ proj₂ X ⟧ fmt δ tt) (elab-ρ̂ᶜ Δ τ r V nat sg ir D))
        (cong (λ E → GM.⟦ E ⟧ fmt δ tt) (sym (CI.WithSG.inst-abs S Δ τ r sg (proj₂ (elabᶜ V D)))))

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

------------------------------------------------------------------------
-- The module's view is natural (it builds every instance pointwise).
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.String using (String)
import Data.String.Properties as StrProp
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (yes; no)
open import Once.Postulates using (extensionality)
open import Once.Spec.Core.PolyTy using (Schema; arity; kinds; type; _!!_)
import Once.Compile as Cmp
open import Once.Spec.Core.Translate using (ImpSig; TeleSig; viewOf; telFind; poly-inst; mono-inst; i-ffi; i-def)
import Once.Spec.Core.Translate as TR

module _ {m} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) where
  private
    Inst : Type → Schema → Set
    Inst T sch = Σ-syntax (GSub (arity sch)) (λ τ′ → Respects (kinds sch) τ′ × (type sch ⟪ τ′ ⟫ ≡ T))

    -- Pointwise ρ̂ survives the transport along the schema equation.
    subst-pt : ∀ {sch sch′ : Schema} (e : sch′ ≡ sch) {T₁ T₂} (X : Inst T₁ sch) (Y : Inst T₂ sch)
             → proj₁ Y ≡ (λ i → RS.ρ̂ Δ τ r (proj₁ X i))
             → proj₁ (subst (Inst T₂) (sym e) Y) ≡ (λ i → RS.ρ̂ Δ τ r (proj₁ (subst (Inst T₁) (sym e) X) i))
    subst-pt refl X Y h = h

    subst-fix : ∀ {sch sch′ : Schema} (e : sch′ ≡ sch) {T} (X : Inst T sch)
              → (λ i → RS.ρ̂ Δ τ r (proj₁ X i)) ≡ proj₁ X
              → (λ i → RS.ρ̂ Δ τ r (proj₁ (subst (Inst T) (sym e) X) i)) ≡ proj₁ (subst (Inst T) (sym e) X)
    subst-fix refl X h = h

    nat-imp′ : ∀ {imps} (is : ImpSig S imps) {x T} (lk : Once.TypeCheck.Classify.lookupImport imps x ≡ Data.Maybe.just T)
             → NatImp Δ τ r (TR.impAt is lk)
    nat-imp′ TR.[] ()
    nat-imp′ {(n , T₀) ∷ rest} (i-ffi c h g is) {x} lk with StrProp._≟_ n x
    ... | yes _ with just-injective lk
    ...   | refl = tt
    nat-imp′ {(n , T₀) ∷ rest} (i-ffi c h g is) {x} lk | no _ = nat-imp′ is lk
    nat-imp′ {(n , T₀) ∷ rest} (i-def d e is) {x} lk with StrProp._≟_ n x
    ... | yes _ with just-injective lk
    ...   | refl = subst-fix e _ (extensionality (λ ()))
    nat-imp′ {(n , T₀) ∷ rest} (i-def d e is) {x} lk | no _ = nat-imp′ is lk

  viewOf-natural : ∀ {imps ps} (is : ImpSig S imps) (ts : TeleSig S ps) → Natural Δ τ r (viewOf {S = S} is ts)
  viewOf-natural is ts = record
    { nat-inst   = λ {x} {sc} lp ng ki →
        subst-pt (proj₂ (telFind ts lp)) (kinded-instance sc ki) (kinded-instance sc (RS.ρ̂-ki Δ τ r {sc} ki)) refl
    ; nat-ground = λ {x} {sc} lp g →
        subst-fix (proj₂ (telFind ts lp)) (kinded-instance sc (Once.Type.Rigid.ground-kinded sc g)) refl
    ; nat-imp    = nat-imp′ is
    }
