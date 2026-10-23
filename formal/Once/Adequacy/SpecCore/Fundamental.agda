{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Fundamental — the fundamental lemma of the meaning
-- relation (plan 0.121 §3.5; plan 0.122: over the one core).
--
-- A Spec core derivation `D` (over its type variables) means, in the
-- compiler, its instance `ty-subst-⊢ σ r D` read at no variable
-- (`Core.Telescope`), and in the Spec, `D` read at `σ` (`Spec.Core.Meaning`).
-- At related environments the two are related at the instance's type and
-- the derivation's grade (`Fund D`), given related definitions environments.
--
-- The instance's derivation is `D`'s rule by rule, but for a few rules whose
-- type the substitution moves along an equation (`retypeᵗ`), crossed by
-- `L-at`. The rules whose two meanings differ more than this — the recursion
-- formers, coercions, the loop, the signature's declarations, definitions
-- and arithmetic — are the cases record `Cases`, discharged in their own
-- module.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; _∶_)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Numerics using (TargetNum)

import Once.Spec.Grade
module Once.Adequacy.SpecCore.Fundamental (Σ : Signature) {s : ℕ} (S : Defs s) (fmt : TargetNum) where

open import Data.Unit using (⊤; tt)
import Data.Empty
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂) renaming ([_,_]′ to [_,_]′′)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; Finite; fin; mk-kind; _⊑π_; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; Type; Fun; KCtx; ∅ₖ; TySub; Respects; WFFun; _⟨_⟩; _⇒[_]_; _+_; μ; ν; ⟦_⟧F)
open import Once.Spec.Context using (Ctx; Usage; lookup; _⟨_⟩ᶜ; _*ᵘ_)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Signature using (DeclType)
open import Once.Spec.Core.Syntax using (Prim; primDom; primCod; Schema; _!!_)
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Program Σ using (noVars)
open import Once.Internal.Type using (noResp)
import Once.Spec.Core.Meaning Σ fmt S as SM
import Once.Spec.Domain Σ as SD
import Once.Spec.Effect Σ as SE
import Once.Metatheory.TermModel.TySubst Σ S as TS
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open import Once.Adequacy.SpecCore.Monad Σ
open import Once.Adequacy.SpecCore.Env Σ S fmt

------------------------------------------------------------------------
-- The statement
------------------------------------------------------------------------

module _ (ρ : SM.DefSem) (ρ′ : SM.DefSem) where

  -- The instance's meaning: at no variable.
  L⟦_⟧ : ∀ {n} {Γ : Ctx 0 n} {Ψ t A π} → ∅ₖ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → SM.Env noVars Γ Ψ → SE.M π SD.⟦ A ⟨ noVars ⟩ ⟧ᵛ
  L⟦ d ⟧ γ = SM.⟦ d ⟧ ρ noVars noResp γ

  -- `D` instantiated, and `D` read at the instance, mean related computations.
  Fund : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Set
  Fund {m} {Δ = Δ} {Γ} {Ψ} {A = A} {π} D =
    ∀ (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) (p : PR π π) {γ γ′}
    → EnvR σ Γ Ψ γ γ′
    → MR p (ValR (g⟨⟩ noVars (A ⟨ σ ⟩))) (L⟦ TS.ty-subst-⊢ σ r D ⟧ γ) (SM.⟦ D ⟧ ρ′ σ r γ′)

  ----------------------------------------------------------------------
  -- Crossing the equations
  ----------------------------------------------------------------------

  -- a grade's graph has one proof
  re-pr : ∀ {π π′} (p p′ : PR π π′) {X Y : Set} {R : X → Y → Set} {c c′} → MR p R c c′ → MR p′ R c c′
  re-pr p p′ {R = R} {c} {c′} h = subst (λ q → MR q R c c′) (PR-unique p p′) h

  -- the instance's side, along its retyping
  L-at : ∀ {m} (σ : TySub m 0) {Δ : KCtx m} (r : Respects Δ ∅ₖ σ) {n} {Γ : Ctx 0 n} {Ψ t X Y π B′}
         (e : X ≡ Y) (d : ∅ₖ ⊩ Γ ⊢[ Ψ ] t ∷ X ! π) (p : PR π π) (gX : GR (X ⟨ noVars ⟩) B′) (gY : GR (Y ⟨ noVars ⟩) B′) {γ y}
       → MR p (ValR gX) (L⟦ d ⟧ γ) y
       → MR p (ValR gY) (L⟦ TS.retypeᵗ σ r e d ⟧ γ) y
  L-at σ r refl d p gX gY {γ} {y} h = subst (λ g → MR p (ValR g) (L⟦ d ⟧ γ) y) (GR-unique gX gY) h

  ----------------------------------------------------------------------
  -- The rules discharged elsewhere
  ----------------------------------------------------------------------

  record Cases : Set where
    field
      c-roll   : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π F t} (wf : WFFun Δ F)
                 (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ ⟦ F ⟧F (μ F) ! π) → Fund d → Fund (⊢roll wf d)
      c-fold   : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψa Ψt π π₁ π₂ F A alg t} (wf : WFFun Δ F)
                 (da : Δ ⊩ Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ! π₁)
                 (dt : Δ ⊩ Γ ⊢[ Ψt ] t ∷ μ F ! π₂) → Fund da → Fund dt → Fund (⊢fold wf da dt)
      c-unfold : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψc Ψs} {φ : Finite} {π₁ π₂ F A c x} (wf : WFFun Δ F)
                 (dc : Δ ⊩ Γ ⊢[ Ψc ] c ∷ A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧F A ! π₁)
                 (dx : Δ ⊩ Γ ⊢[ Ψs ] x ∷ A ! π₂) → Fund dc → Fund dx → Fund (⊢unfold wf dc dx)
      c-out    : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ} {φ : Finite} {π₁ F t} (wf : WFFun Δ F)
                 (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ ν F φ ! π₁) → Fund d → Fund (⊢out wf d)
      c-iter   : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψf Ψs π₁ π₂ A B f x}
                 (df : Δ ⊩ Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind Many Once.Spec.Grade.act ] (B + A) ! π₁)
                 (dx : Δ ⊩ Γ ⊢[ Ψs ] x ∷ A ! π₂) → Fund df → Fund dx → Fund (⊢iter df dx)
      c-coerce : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π A B t} (p : A <: B)
                 (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Fund d → Fund (⊢coerce p d)
      c-lit-int   : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {i} → Fund (⊢lit-int {Δ = Δ} {Γ = Γ} {i = i})
      c-lit-float : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {d} → Fund (⊢lit-float {Δ = Δ} {Γ = Γ} {d = d})
      c-prim   : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π t} (p : Prim)
                 (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ primDom p ! π) → Fund d → Fund (⊢prim p d)
      c-sigop  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {c} {t : DeclType} (mem : (c ∶ t) ∈ Σ)
                 → Fund (⊢sigop {Δ = Δ} {Γ = Γ} mem)
      c-ref    : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} d τ rs → Fund (⊢ref {Δ = Δ} {Γ = Γ} d τ rs)

  ----------------------------------------------------------------------
  -- The fundamental lemma
  ----------------------------------------------------------------------

  -- (a pure value of a sum, taken apart on both sides)
  private
    case-R : ∀ {A A′ B B′} (a : GR A A′) (b : GR B B′) {X Y : Set} {π π′} (p : PR π π′) {R : X → Y → Set}
             {l : SD.⟦ A ⟧ᵛ → SE.M π X} {r : SD.⟦ B ⟧ᵛ → SE.M π X} {l′ r′}
           → (∀ {x x′} → ValR a x x′ → MR p R (l x) (l′ x′))
           → (∀ {x x′} → ValR b x x′ → MR p R (r x) (r′ x′))
           → ∀ v v′ → ValR (g-+ a b) v v′
           → MR p R ([ l , r ]′′ v) ([ l′ , r′ ]′′ v′)
    case-R a b p kl kr (inj₁ x) (inj₁ x′) h = kl h
    case-R a b p kl kr (inj₂ x) (inj₂ x′) h = kr h
    case-R a b p kl kr (inj₁ x) (inj₂ x′) ()
    case-R a b p kl kr (inj₂ x) (inj₁ x′) ()

  module _ (cases : Cases) where
    open Cases cases

    fund : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t A π} (D : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Fund D

    fund {Γ = Γ} (⊢var i) σ r pr-pure e =
      L-at σ r (TS.lookup-⟨⟩ σ Γ i) (⊢var i) pr-pure (GR-lookup σ Γ i) (g⟨⟩ noVars _) (lookup-R σ Γ i e)

    fund (⊢lam {q = Zero} 0≤q d) σ r pr-pure e = fund d σ r (pr _) e
    fund (⊢lam {q = One}  0≤q d) σ r pr-pure e = λ _ → fund d σ r (pr _) e
    fund (⊢lam {q = Many} 0≤q d) σ r pr-pure e = λ _ → fund d σ r (pr _) e
    fund (⊢lam 1≤1 d) σ r pr-pure e = λ v → fund d σ r (pr _) (e , v)
    fund (⊢lam 1≤ω d) σ r pr-pure e = λ v → fund d σ r (pr _) (e , v)
    fund (⊢lam ω≤ω d) σ r pr-pure e = λ v → fund d σ r (pr _) (e , v)

    fund ⊢unit σ r pr-pure e = tt

    fund (⊢sub-eff {π = π} {π′} x d) σ r p e = sub-R x x (pr π) p (fund d σ r (pr π) e)
    fund {Γ = Γ} (⊢sub-use x d) σ r p e = fund d σ r p (restrict-R σ {Γ = Γ} x e)

    fund (⊢fst {π = π} d) σ r p e = fmap-R p (fund d σ r p e) proj₁
    fund (⊢snd {π = π} d) σ r p e = fmap-R p (fund d σ r p e) proj₂
    fund (⊢inl {π = π} d) σ r p e = fmap-R p (fund d σ r p e) (λ h → h)
    fund (⊢inr {π = π} d) σ r p e = fmap-R p (fund d σ r p e) (λ h → h)
    fund (⊢absurd {π = π} d) σ r p e = bind-R p (fund d σ r p e) (λ {x} _ → ⊥-elim′ x)
      where ⊥-elim′ : ∀ {X : Set} → Data.Empty.⊥ → X
            ⊥-elim′ ()

    fund {Γ = Γ} (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = Zero} {π} {π₁} df dx) σ r p e =
      re-pr (pr-· (pr π₁) (pr π)) p (bindᵍ-R (pr π₁) (pr π) (fund df σ r (pr _) (envˡ-R σ {Γ = Γ} Ψ₁ (Zero *ᵘ Ψ₂) e)) (λ vf → vf))
    fund {Γ = Γ} (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = One} {π} {π₁} {π₂} df dx) σ r p e =
      re-pr (pr-· (pr π₁) (pr-· (pr π₂) (pr π))) p (bindᵍ-R (pr π₁) (pr-· (pr π₂) (pr π)) (fund df σ r (pr _) (envˡ-R σ {Γ = Γ} Ψ₁ (One *ᵘ Ψ₂) e))
               (λ vf → bindᵍ-R (pr π₂) (pr π) (fund dx σ r (pr _) (env*One-envʳ-R σ {Γ = Γ} Ψ₁ Ψ₂ e)) vf))
    fund {Γ = Γ} (⊢app {Ψ₁ = Ψ₁} {Ψ₂} {q = Many} {π} {π₁} {π₂} df dx) σ r p e =
      re-pr (pr-· (pr π₁) (pr-· (pr π₂) (pr π))) p (bindᵍ-R (pr π₁) (pr-· (pr π₂) (pr π)) (fund df σ r (pr _) (envˡ-R σ {Γ = Γ} Ψ₁ (Many *ᵘ Ψ₂) e))
               (λ vf → bindᵍ-R (pr π₂) (pr π) (fund dx σ r (pr _) (env*Many-envʳ-R σ {Γ = Γ} Ψ₁ Ψ₂ e)) vf))

    fund {Γ = Γ} (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = Zero} {π₁} {π₂} de db) σ r p e =
      re-pr (pr π₂) p (fund db σ r (pr _) (envˡ-R σ {Γ = Γ} Ψ₂ (Zero *ᵘ Ψ₁) e))
    fund {Γ = Γ} (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = One} {π₁} {π₂} de db) σ r p e =
      re-pr (pr-· (pr π₁) (pr π₂)) p (bindᵍ-R (pr π₁) (pr π₂) (fund de σ r (pr _) (env*One-envʳ-R σ {Γ = Γ} Ψ₂ Ψ₁ e))
               (λ v → fund db σ r (pr _) (envˡ-R σ {Γ = Γ} Ψ₂ (One *ᵘ Ψ₁) e , v)))
    fund {Γ = Γ} (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = Many} {π₁} {π₂} de db) σ r p e =
      re-pr (pr-· (pr π₁) (pr π₂)) p (bindᵍ-R (pr π₁) (pr π₂) (fund de σ r (pr _) (env*Many-envʳ-R σ {Γ = Γ} Ψ₂ Ψ₁ e))
               (λ v → fund db σ r (pr _) (envˡ-R σ {Γ = Γ} Ψ₂ (Many *ᵘ Ψ₁) e , v)))

    fund {Γ = Γ} (⊢pair {Ψ₁ = Ψ₁} {Ψ₂} {π₁} {π₂} da db) σ r p e =
      re-pr (pr-· (pr π₁) (pr π₂)) p (bindᵍ-R (pr π₁) (pr π₂) (fund da σ r (pr _) (envˡ-R σ {Γ = Γ} Ψ₁ Ψ₂ e))
               (λ va → fmap-R (pr π₂) (fund db σ r (pr _) (envʳ-R σ {Γ = Γ} Ψ₁ Ψ₂ e)) (λ vb → va , vb)))

    fund {Γ = Γ} (⊢case {Ψs = Ψs} {Ψ} {qℓ} {qr₀} {π₁} {π₂} {A} {B} ds dl dr) σ r p e =
      re-pr (pr-· (pr π₁) (pr π₂)) p (bindᵍ-R (pr π₁) (pr π₂) (fund ds σ r (pr _) (envˡ-R σ {Γ = Γ} Ψs Ψ e))
               (λ {v} {v′} h → case-R (g⟨⟩ noVars (A ⟨ σ ⟩)) (g⟨⟩ noVars (B ⟨ σ ⟩)) (pr π₂)
                  (λ ha → fund dl σ r (pr _) (bind-env-R σ {Γ = Γ} A qℓ (envʳ-R σ {Γ = Γ} Ψs Ψ e) ha))
                  (λ hb → fund dr σ r (pr _) (bind-env-R σ {Γ = Γ} B qr₀ (envʳ-R σ {Γ = Γ} Ψs Ψ e) hb))
                  v v′ h))

    fund (⊢roll wf d)           = c-roll wf d (fund d)
    fund (⊢fold wf da dt)       = c-fold wf da dt (fund da) (fund dt)
    fund (⊢unfold wf dc dx)     = c-unfold wf dc dx (fund dc) (fund dx)
    fund (⊢out wf d)            = c-out wf d (fund d)
    fund (⊢iter df dx)          = c-iter df dx (fund df) (fund dx)
    fund (⊢coerce p d)          = c-coerce p d (fund d)
    fund (⊢lit-int {i = i})     = c-lit-int {i = i}
    fund (⊢lit-float {d = d})   = c-lit-float {d = d}
    fund (⊢prim p d)            = c-prim p d (fund d)
    fund (⊢sigop mem)           = c-sigop mem
    fund (⊢ref d τ rs)          = c-ref d τ rs
