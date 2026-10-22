-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Core.TySubstRen — substituting types commutes with renaming
-- variables, for the Spec's core terms and their derivations.
--
-- The elaborated combinators weaken their arguments (`wk`, `wk-⊢`); a
-- polymorphic entry is instantiated by `ty-subst-⊢`. That the two commute is
-- what makes elaborating an instance the instance of the elaboration
-- (`Adequacy.ElabCommute`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Internal.Core.TySubstRen (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Spec.Type using (Ty; TySub; _⟨_⟩)
open import Once.Spec.Core.Syntax

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

ext-cong : ∀ {m n n′} {ρ ρ′ : Fin n → Fin n′} → (∀ i → ρ i ≡ ρ′ i) → ∀ i → ext {S = S} {m = m} ρ i ≡ ext {S = S} {m = m} ρ′ i
ext-cong h zero    = refl
ext-cong h (suc i) = cong suc (h i)

-- Renaming is determined by the renaming's values.
ren-cong : ∀ {m n n′} {ρ ρ′ : Fin n → Fin n′} → (∀ i → ρ i ≡ ρ′ i) → (t : Tm S m n) → ren ρ t ≡ ren ρ′ t
ren-cong h (var i)            = cong var (h i)
ren-cong {m} h (lam A q π t)      = cong (lam A q π) (ren-cong (ext-cong {m = m} h) t)
ren-cong h (app f x)          = cong₂ app (ren-cong h f) (ren-cong h x)
ren-cong {m} h (let′ q e b)       = cong₂ (let′ q) (ren-cong h e) (ren-cong (ext-cong {m = m} h) b)
ren-cong h unit               = refl
ren-cong h (pair a b)         = cong₂ pair (ren-cong h a) (ren-cong h b)
ren-cong h (fst p)            = cong fst (ren-cong h p)
ren-cong h (snd p)            = cong snd (ren-cong h p)
ren-cong h (inl B a)          = cong (inl B) (ren-cong h a)
ren-cong h (inr A b)          = cong (inr A) (ren-cong h b)
ren-cong {m} h (case qℓ qr e l r) =
  trans (cong₂ (λ x y → case qℓ qr x y (ren _ r)) (ren-cong h e) (ren-cong (ext-cong {m = m} h) l))
        (cong (case qℓ qr _ _) (ren-cong (ext-cong {m = m} h) r))
ren-cong h (absurd A e)       = cong (absurd A) (ren-cong h e)
ren-cong h (roll F t)         = cong (roll F) (ren-cong h t)
ren-cong h (fold F alg t)     = cong₂ (fold F) (ren-cong h alg) (ren-cong h t)
ren-cong h (unfold F c a)     = cong₂ (unfold F) (ren-cong h c) (ren-cong h a)
ren-cong h (out t)            = cong out (ren-cong h t)
ren-cong h (iter f a)         = cong₂ iter (ren-cong h f) (ren-cong h a)
ren-cong h (coerce A B t)     = cong (coerce A B) (ren-cong h t)
ren-cong h (lit l)            = refl
ren-cong h (prim p t)         = cong (prim p) (ren-cong h t)
ren-cong h (sigop c t)        = refl
ren-cong h (ref d τ)          = refl

module _ {m k : ℕ} (σ : TySub m k) where

  private
    -- Extending a renaming does not look at the type index.
    ext-ix : ∀ {n n′} (ρ : Fin n → Fin n′) → ∀ i → ext {S = S} {m = m} ρ i ≡ ext {S = S} {m = k} ρ i
    ext-ix ρ zero    = refl
    ext-ix ρ (suc i) = refl

  ⟪⟫-ren : ∀ {n n′} (ρ : Fin n → Fin n′) (t : Tm S m n) → ren ρ t ⟪ σ ⟫ₜ ≡ ren ρ (t ⟪ σ ⟫ₜ)
  ⟪⟫-ren ρ (var i)            = refl
  ⟪⟫-ren ρ (lam A q π t)      = cong (lam _ q π) (trans (⟪⟫-ren (ext {S = S} {m = m} ρ) t) (ren-cong (ext-ix ρ) (t ⟪ σ ⟫ₜ)))
  ⟪⟫-ren ρ (app f x)          = cong₂ app (⟪⟫-ren ρ f) (⟪⟫-ren ρ x)
  ⟪⟫-ren ρ (let′ q e b)       = cong₂ (let′ q) (⟪⟫-ren ρ e) (trans (⟪⟫-ren (ext {S = S} {m = m} ρ) b) (ren-cong (ext-ix ρ) (b ⟪ σ ⟫ₜ)))
  ⟪⟫-ren ρ unit               = refl
  ⟪⟫-ren ρ (pair a b)         = cong₂ pair (⟪⟫-ren ρ a) (⟪⟫-ren ρ b)
  ⟪⟫-ren ρ (fst p)            = cong fst (⟪⟫-ren ρ p)
  ⟪⟫-ren ρ (snd p)            = cong snd (⟪⟫-ren ρ p)
  ⟪⟫-ren ρ (inl B a)          = cong (inl _) (⟪⟫-ren ρ a)
  ⟪⟫-ren ρ (inr A b)          = cong (inr _) (⟪⟫-ren ρ b)
  ⟪⟫-ren ρ (case qℓ qr e l r) =
    trans (cong₂ (λ x y → case qℓ qr x y (ren (ext {S = S} {m = m} ρ) r ⟪ σ ⟫ₜ)) (⟪⟫-ren ρ e) (trans (⟪⟫-ren (ext {S = S} {m = m} ρ) l) (ren-cong (ext-ix ρ) (l ⟪ σ ⟫ₜ))))
          (cong (case qℓ qr _ _) (trans (⟪⟫-ren (ext {S = S} {m = m} ρ) r) (ren-cong (ext-ix ρ) (r ⟪ σ ⟫ₜ))))
  ⟪⟫-ren ρ (absurd A e)       = cong (absurd _) (⟪⟫-ren ρ e)
  ⟪⟫-ren ρ (roll F t)         = cong (roll _) (⟪⟫-ren ρ t)
  ⟪⟫-ren ρ (fold F alg t)     = cong₂ (fold _) (⟪⟫-ren ρ alg) (⟪⟫-ren ρ t)
  ⟪⟫-ren ρ (unfold F c a)     = cong₂ (unfold _) (⟪⟫-ren ρ c) (⟪⟫-ren ρ a)
  ⟪⟫-ren ρ (out t)            = cong out (⟪⟫-ren ρ t)
  ⟪⟫-ren ρ (iter f a)         = cong₂ iter (⟪⟫-ren ρ f) (⟪⟫-ren ρ a)
  ⟪⟫-ren ρ (coerce A B t)     = cong (coerce _ _) (⟪⟫-ren ρ t)
  ⟪⟫-ren ρ (lit l)            = refl
  ⟪⟫-ren ρ (prim p t)         = cong (prim p) (⟪⟫-ren ρ t)
  ⟪⟫-ren ρ (sigop c t)        = refl
  ⟪⟫-ren ρ (ref d τ)          = refl

  ⟪⟫-wk : ∀ {n} (t : Tm S m n) → wk t ⟪ σ ⟫ₜ ≡ wk (t ⟪ σ ⟫ₜ)
  ⟪⟫-wk t = ⟪⟫-ren suc t

------------------------------------------------------------------------
-- Derivations
------------------------------------------------------------------------

open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Once.Spec.Grade using (Quantity; Zero; Many; Purity; Finite; fin; mk-kind; positionGrade; act; eff; _·p_)
open import Once.Spec.Type using (KCtx; Respects; Fun; Void; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F; WFFun; _⟨_⟩F)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Context using (Ctx; ∅; _▸_; lookup; _⟨_⟩ᶜ; Usage; _⊑ᵘ_; _∷_)
open import Once.Spec.Core.Typing Σ S
import Once.Metatheory.TermModel.Subst Σ S as TM
open TM using (Thin; done; keep; skip; ⟦_⟧θ; CThin; cdone; ckeep; cskip; cid; idθ; idθ-id; ext-hρ)
import Once.Metatheory.TermModel.TySubst Σ S as TS

module Deriv {m k : ℕ} (σ : TySub m k) {Δ : KCtx m} {Δ′ : KCtx k} (rσ : Respects Δ Δ′ σ) where

  ty : ∀ {n} {Γ : Ctx m n} {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] t ⟪ σ ⟫ₜ ∷ A ⟨ σ ⟩ ! π
  ty = TS.ty-subst-⊢ σ rσ

  cthin-⟨⟩ : ∀ {n n′} {θ : Thin n n′} {Γ Γ′} → CThin θ Γ Γ′ → CThin θ (Γ ⟨ σ ⟩ᶜ) (Γ′ ⟨ σ ⟩ᶜ)
  cthin-⟨⟩ cdone     = cdone
  cthin-⟨⟩ (ckeep c) = ckeep (cthin-⟨⟩ c)
  cthin-⟨⟩ (cskip c) = cskip (cthin-⟨⟩ c)

  cid-⟨⟩ : ∀ {n} (Γ : Ctx m n) → cthin-⟨⟩ (cid Γ) ≡ cid (Γ ⟨ σ ⟩ᶜ)
  cid-⟨⟩ ∅       = refl
  cid-⟨⟩ (Γ ▸ A) = cong ckeep (cid-⟨⟩ Γ)

  private
    -- Transports erase.
    rtᵗ-≅ : ∀ {n} {Γ : Ctx k n} {Ψ t A A′ π} (e : A ≡ A′) (d : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → TS.retypeᵗ σ rσ e d ≅ d
    rtᵗ-≅ refl d = H.refl

    rt-≅ : ∀ {n} {Γ : Ctx k n} {Ψ t A A′ π} (e : A ≡ A′) (d : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → TM.retype e d ≅ d
    rt-≅ refl d = H.refl

    ty-rt : ∀ {n} {Γ : Ctx m n} {Ψ t A A′ π} (e : A ≡ A′) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → ty (TM.retype e d) ≅ ty d
    ty-rt refl d = H.refl

    R-rt : ∀ {n n′} (θ : Thin n n′) (ρ : Fin n → Fin n′) (h : ∀ i → ⟦ θ ⟧θ i ≡ ρ i) {Γ Γ′} (c : CThin θ Γ Γ′)
             {Ψ t A A′ π} (e : A ≡ A′) (d : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
         → TM.ren-⊢ θ ρ h c (TS.retypeᵗ σ rσ e d) ≅ TM.ren-⊢ θ ρ h c d
    R-rt θ ρ h c refl d = H.refl

    -- Congruences of the rules, along equal terms.
    c-sub-use : ∀ {n} {Γ : Ctx k n} {Ψ Ψ′ A A′ π t t′} {p : Ψ ⊑ᵘ Ψ′}
                  {x : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] t′ ∷ A′ ! π}
              → t ≡ t′ → A ≡ A′ → x ≅ y → ⊢sub-use p x ≅ ⊢sub-use p y
    c-sub-use refl refl H.refl = H.refl

    c-sub-eff : ∀ {n} {Γ : Ctx k n} {Ψ A π π′ t t′} {g : Once.Spec.Grade._⊑π_ π π′}
                  {x : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] t′ ∷ A ! π}
              → t ≡ t′ → x ≅ y → ⊢sub-eff g x ≅ ⊢sub-eff g y
    c-sub-eff refl H.refl = H.refl

    c-lam : ∀ {n} {Γ : Ctx k n} {Ψ q q′ π A B t t′} {le : Once.Spec.Grade._≤q_ q′ q}
              {x : Δ′ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ ] t ∷ B ! π} {y : Δ′ ⊩ (Γ ▸ A) ⊢[ q′ ∷ Ψ ] t′ ∷ B ! π}
          → t ≡ t′ → x ≅ y → ⊢lam le x ≅ ⊢lam le y
    c-lam refl H.refl = H.refl

    c-app : ∀ {n} {Γ : Ctx k n} {Ψ₁ Ψ₂ q π π₁ π₂ A B f f′ x x′}
              {df : Δ′ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! π₁} {df′ : Δ′ ⊩ Γ ⊢[ Ψ₁ ] f′ ∷ A ⇒[ mk-kind q π ] B ! π₁}
              {dx : Δ′ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! positionGrade q π₂} {dx′ : Δ′ ⊩ Γ ⊢[ Ψ₂ ] x′ ∷ A ! positionGrade q π₂}
          → f ≡ f′ → x ≡ x′ → df ≅ df′ → dx ≅ dx′ → ⊢app df dx ≅ ⊢app df′ dx′
    c-app refl refl H.refl H.refl = H.refl

    c-let : ∀ {n} {Γ : Ctx k n} {Ψ₁ Ψ₂ q π₁ π₂ A B e e′ b b′}
              {de : Δ′ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁} {de′ : Δ′ ⊩ Γ ⊢[ Ψ₁ ] e′ ∷ A ! positionGrade q π₁}
              {db : Δ′ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂} {db′ : Δ′ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b′ ∷ B ! π₂}
          → e ≡ e′ → b ≡ b′ → de ≅ de′ → db ≅ db′ → ⊢let de db ≅ ⊢let de′ db′
    c-let refl refl H.refl H.refl = H.refl

    c-pair : ∀ {n} {Γ : Ctx k n} {Ψ₁ Ψ₂ π₁ π₂ A B a a′ b b′}
               {da : Δ′ ⊩ Γ ⊢[ Ψ₁ ] a ∷ A ! π₁} {da′ : Δ′ ⊩ Γ ⊢[ Ψ₁ ] a′ ∷ A ! π₁}
               {db : Δ′ ⊩ Γ ⊢[ Ψ₂ ] b ∷ B ! π₂} {db′ : Δ′ ⊩ Γ ⊢[ Ψ₂ ] b′ ∷ B ! π₂}
           → a ≡ a′ → b ≡ b′ → da ≅ da′ → db ≅ db′ → ⊢pair da db ≅ ⊢pair da′ db′
    c-pair refl refl H.refl H.refl = H.refl

    c-fst : ∀ {n} {Γ : Ctx k n} {Ψ π A B p p′} {x : Δ′ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] p′ ∷ A * B ! π}
          → p ≡ p′ → x ≅ y → ⊢fst x ≅ ⊢fst y
    c-fst refl H.refl = H.refl

    c-snd : ∀ {n} {Γ : Ctx k n} {Ψ π A B p p′} {x : Δ′ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] p′ ∷ A * B ! π}
          → p ≡ p′ → x ≅ y → ⊢snd x ≅ ⊢snd y
    c-snd refl H.refl = H.refl

    c-inl : ∀ {n} {Γ : Ctx k n} {Ψ π A B a a′} {x : Δ′ ⊩ Γ ⊢[ Ψ ] a ∷ A ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] a′ ∷ A ! π}
          → a ≡ a′ → x ≅ y → ⊢inl {B = B} x ≅ ⊢inl {B = B} y
    c-inl refl H.refl = H.refl

    c-inr : ∀ {n} {Γ : Ctx k n} {Ψ π A B b b′} {x : Δ′ ⊩ Γ ⊢[ Ψ ] b ∷ B ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] b′ ∷ B ! π}
          → b ≡ b′ → x ≅ y → ⊢inr {A = A} x ≅ ⊢inr {A = A} y
    c-inr refl H.refl = H.refl

    c-case : ∀ {n} {Γ : Ctx k n} {Ψs Ψ qℓ qr π₁ π₂ A B C s s′ l l′ r r′}
               {ds : Δ′ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁} {ds′ : Δ′ ⊩ Γ ⊢[ Ψs ] s′ ∷ A + B ! π₁}
               {dl : Δ′ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π₂} {dl′ : Δ′ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψ ] l′ ∷ C ! π₂}
               {dr : Δ′ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψ ] r ∷ C ! π₂} {dr′ : Δ′ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψ ] r′ ∷ C ! π₂}
           → s ≡ s′ → l ≡ l′ → r ≡ r′ → ds ≅ ds′ → dl ≅ dl′ → dr ≅ dr′ → ⊢case ds dl dr ≅ ⊢case ds′ dl′ dr′
    c-case refl refl refl H.refl H.refl H.refl = H.refl

    c-absurd : ∀ {n} {Γ : Ctx k n} {Ψ π A e e′} {x : Δ′ ⊩ Γ ⊢[ Ψ ] e ∷ Void ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] e′ ∷ Void ! π}
             → e ≡ e′ → x ≅ y → ⊢absurd {A = A} x ≅ ⊢absurd {A = A} y
    c-absurd refl H.refl = H.refl

    c-roll : ∀ {n} {Γ : Ctx k n} {Ψ π F t t′} {w : WFFun Δ′ F}
               {x : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ ⟦ F ⟧F (μ F) ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] t′ ∷ ⟦ F ⟧F (μ F) ! π}
           → t ≡ t′ → x ≅ y → ⊢roll w x ≅ ⊢roll w y
    c-roll refl H.refl = H.refl

    c-fold : ∀ {n} {Γ : Ctx k n} {Ψa Ψt π π₁ π₂ F A a a′ t t′} {w : WFFun Δ′ F}
               {da : Δ′ ⊩ Γ ⊢[ Ψa ] a ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ! π₁} {da′ : Δ′ ⊩ Γ ⊢[ Ψa ] a′ ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ! π₁}
               {dt : Δ′ ⊩ Γ ⊢[ Ψt ] t ∷ μ F ! π₂} {dt′ : Δ′ ⊩ Γ ⊢[ Ψt ] t′ ∷ μ F ! π₂}
           → a ≡ a′ → t ≡ t′ → da ≅ da′ → dt ≅ dt′ → ⊢fold w da dt ≅ ⊢fold w da′ dt′
    c-fold refl refl H.refl H.refl = H.refl

    c-unfold : ∀ {n} {Γ : Ctx k n} {Ψc Ψs f π₁ π₂ F A c c′ a a′} {w : WFFun Δ′ F}
                 {dc : Δ′ ⊩ Γ ⊢[ Ψc ] c ∷ A ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A ! π₁}
                 {dc′ : Δ′ ⊩ Γ ⊢[ Ψc ] c′ ∷ A ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A ! π₁}
                 {da : Δ′ ⊩ Γ ⊢[ Ψs ] a ∷ A ! π₂} {da′ : Δ′ ⊩ Γ ⊢[ Ψs ] a′ ∷ A ! π₂}
             → c ≡ c′ → a ≡ a′ → dc ≅ dc′ → da ≅ da′ → ⊢unfold w dc da ≅ ⊢unfold w dc′ da′
    c-unfold refl refl H.refl H.refl = H.refl

    c-out : ∀ {n} {Γ : Ctx k n} {Ψ f π₁ F t t′} {w : WFFun Δ′ F}
              {x : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ ν F f ! π₁} {y : Δ′ ⊩ Γ ⊢[ Ψ ] t′ ∷ ν F f ! π₁}
          → t ≡ t′ → x ≅ y → ⊢out w x ≅ ⊢out w y
    c-out refl H.refl = H.refl

    c-iter : ∀ {n} {Γ : Ctx k n} {Ψf Ψs π₁ π₂ A B f f′ a a′}
               {df : Δ′ ⊩ Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind Many act ] (B + A) ! π₁} {df′ : Δ′ ⊩ Γ ⊢[ Ψf ] f′ ∷ A ⇒[ mk-kind Many act ] (B + A) ! π₁}
               {da : Δ′ ⊩ Γ ⊢[ Ψs ] a ∷ A ! π₂} {da′ : Δ′ ⊩ Γ ⊢[ Ψs ] a′ ∷ A ! π₂}
           → f ≡ f′ → a ≡ a′ → df ≅ df′ → da ≅ da′ → ⊢iter df da ≅ ⊢iter df′ da′
    c-iter refl refl H.refl H.refl = H.refl

    c-coerce : ∀ {n} {Γ : Ctx k n} {Ψ π A B t t′} {p : A <: B}
                 {x : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] t′ ∷ A ! π}
             → t ≡ t′ → x ≅ y → ⊢coerce p x ≅ ⊢coerce p y
    c-coerce refl H.refl = H.refl

    c-prim : ∀ {n} {Γ : Ctx k n} {Ψ π t t′} (p : Prim)
               {x : Δ′ ⊩ Γ ⊢[ Ψ ] t ∷ primDom p ! π} {y : Δ′ ⊩ Γ ⊢[ Ψ ] t′ ∷ primDom p ! π}
           → t ≡ t′ → x ≅ y → ⊢prim p x ≅ ⊢prim p y
    c-prim p refl H.refl = H.refl

  -- The renamed terms agree when the two renamings do.
  tm-eq : ∀ {n n′} {θ : Thin n n′} {ρ ρ′ : Fin n → Fin n′} → (∀ i → ⟦ θ ⟧θ i ≡ ρ i) → (∀ i → ⟦ θ ⟧θ i ≡ ρ′ i)
        → (t : Tm S m n) → ren ρ t ⟪ σ ⟫ₜ ≡ ren ρ′ (t ⟪ σ ⟫ₜ)
  tm-eq h h′ t = trans (⟪⟫-ren σ _ t) (ren-cong (λ i → trans (sym (h i)) (h′ i)) (t ⟪ σ ⟫ₜ))

  var-case : ∀ {n n′} {θ : Thin n n′} {Γ Γ′} (c : CThin θ Γ Γ′) (i : Fin n) {j j′} (e : ⟦ θ ⟧θ i ≡ j) (e′ : ⟦ θ ⟧θ i ≡ j′)
           → ty {Γ = Γ′} (TM.varAt c i e) ≅ TM.varAt {Δ = Δ′} (cthin-⟨⟩ c) i e′
  var-case {θ = θ} {Γ} {Γ′} c i refl refl =
    c-sub-use refl (sym (TS.lookup-⟨⟩ σ Γ i))
      (H.trans (ty-rt (TM.cthin-lookup c i) (⊢var (⟦ θ ⟧θ i)))
        (H.trans (rtᵗ-≅ (TS.lookup-⟨⟩ σ Γ′ (⟦ θ ⟧θ i)) (⊢var (⟦ θ ⟧θ i)))
          (H.sym (rt-≅ (TM.cthin-lookup (cthin-⟨⟩ c) i) (⊢var (⟦ θ ⟧θ i))))))

  open import Once.Spec.Type.Substitution using (⟨⟩-∘; respects-∘)
  open Schema using (type)

  -- Substituting types into a renamed derivation is renaming the substituted one.
  ty-ren : ∀ {n n′} (θ : Thin n n′) (ρ ρ′ : Fin n → Fin n′) (h : ∀ i → ⟦ θ ⟧θ i ≡ ρ i) (h′ : ∀ i → ⟦ θ ⟧θ i ≡ ρ′ i)
             {Γ Γ′} (c : CThin θ Γ Γ′) {Ψ t A π} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
         → ty (TM.ren-⊢ θ ρ h c d) ≅ TM.ren-⊢ θ ρ′ h′ (cthin-⟨⟩ c) (ty d)
  ty-ren θ ρ ρ′ h h′ {Γ = Γ} c (⊢var i) = H.trans (var-case c i (h i) (h′ i)) (H.sym (R-rt θ ρ′ h′ (cthin-⟨⟩ c) (TS.lookup-⟨⟩ σ Γ i) (⊢var i)))
  ty-ren θ ρ ρ′ h h′ c (⊢lam {t = t} le d) =
    c-lam (tm-eq (ext-hρ {m = m} θ ρ h) (ext-hρ {m = k} θ ρ′ h′) t)
      (ty-ren (keep θ) (ext {S = S} {m = m} ρ) (ext {S = S} {m = k} ρ′) (ext-hρ {m = m} θ ρ h) (ext-hρ {m = k} θ ρ′ h′) (ckeep c) d)
  ty-ren θ ρ ρ′ h h′ c (⊢app {f = f} {x = x} df dx) =
    c-sub-use (tm-eq h h′ (app f x)) refl
      (c-app (tm-eq h h′ f) (tm-eq h h′ x) (ty-ren θ ρ ρ′ h h′ c df) (ty-ren θ ρ ρ′ h h′ c dx))
  ty-ren θ ρ ρ′ h h′ c (⊢let {q = q} {e = e} {b = b} d₁ d₂) =
    c-sub-use (tm-eq h h′ (let′ q e b)) refl
      (c-let (tm-eq h h′ e) (tm-eq (ext-hρ {m = m} θ ρ h) (ext-hρ {m = k} θ ρ′ h′) b) (ty-ren θ ρ ρ′ h h′ c d₁)
             (ty-ren (keep θ) (ext {S = S} {m = m} ρ) (ext {S = S} {m = k} ρ′) (ext-hρ {m = m} θ ρ h) (ext-hρ {m = k} θ ρ′ h′) (ckeep c) d₂))
  ty-ren θ ρ ρ′ h h′ c ⊢unit = H.refl
  ty-ren θ ρ ρ′ h h′ c (⊢pair {a = a} {b = b} da db) =
    c-sub-use (tm-eq h h′ (pair a b)) refl (c-pair (tm-eq h h′ a) (tm-eq h h′ b) (ty-ren θ ρ ρ′ h h′ c da) (ty-ren θ ρ ρ′ h h′ c db))
  ty-ren θ ρ ρ′ h h′ c (⊢fst {p = p} d) = c-fst (tm-eq h h′ p) (ty-ren θ ρ ρ′ h h′ c d)
  ty-ren θ ρ ρ′ h h′ c (⊢snd {p = p} d) = c-snd (tm-eq h h′ p) (ty-ren θ ρ ρ′ h h′ c d)
  ty-ren θ ρ ρ′ h h′ c (⊢inl {a = a} d) = c-inl (tm-eq h h′ a) (ty-ren θ ρ ρ′ h h′ c d)
  ty-ren θ ρ ρ′ h h′ c (⊢inr {b = b} d) = c-inr (tm-eq h h′ b) (ty-ren θ ρ ρ′ h h′ c d)
  ty-ren θ ρ ρ′ h h′ c (⊢case {qℓ = qℓ} {qr = qr} {s = s} {l = l} {r = r} ds dl dr) =
    c-sub-use (tm-eq h h′ (case qℓ qr s l r)) refl
      (c-case (tm-eq h h′ s) (tm-eq (ext-hρ {m = m} θ ρ h) (ext-hρ {m = k} θ ρ′ h′) l)
              (tm-eq (ext-hρ {m = m} θ ρ h) (ext-hρ {m = k} θ ρ′ h′) r)
              (ty-ren θ ρ ρ′ h h′ c ds)
              (ty-ren (keep θ) (ext {S = S} {m = m} ρ) (ext {S = S} {m = k} ρ′) (ext-hρ {m = m} θ ρ h) (ext-hρ {m = k} θ ρ′ h′) (ckeep c) dl)
              (ty-ren (keep θ) (ext {S = S} {m = m} ρ) (ext {S = S} {m = k} ρ′) (ext-hρ {m = m} θ ρ h) (ext-hρ {m = k} θ ρ′ h′) (ckeep c) dr))
  ty-ren θ ρ ρ′ h h′ c (⊢absurd {e = e} d) = c-absurd (tm-eq h h′ e) (ty-ren θ ρ ρ′ h h′ c d)
  ty-ren θ ρ ρ′ h h′ c (⊢roll {F = F} {t = t} wf d) =
    c-roll (tm-eq h h′ t)
      (H.trans (rtᵗ-≅ E (ty (TM.ren-⊢ θ ρ h c d))) (H.trans (ty-ren θ ρ ρ′ h h′ c d) (H.sym (R-rt θ ρ′ h′ (cthin-⟨⟩ c) E (ty d)))))
    where E = TS.⟦⟧F-⟨⟩ σ F (μ F)
  ty-ren θ ρ ρ′ h h′ c (⊢fold {π = π} {F = F} {A = A} {alg = a} {t = t} wf da dt) =
    c-sub-use (tm-eq h h′ (fold _ a t)) refl
      (c-fold (tm-eq h h′ a) (tm-eq h h′ t)
        (H.trans (rtᵗ-≅ E (ty (TM.ren-⊢ θ ρ h c da))) (H.trans (ty-ren θ ρ ρ′ h h′ c da) (H.sym (R-rt θ ρ′ h′ (cthin-⟨⟩ c) E (ty da)))))
        (ty-ren θ ρ ρ′ h h′ c dt))
    where E = cong (λ X → X ⇒[ mk-kind Many π ] A ⟨ σ ⟩) (TS.⟦⟧F-⟨⟩ σ F A)
  ty-ren θ ρ ρ′ h h′ c (⊢unfold {f = f} {F = F} {A = A} {c = cc} {a = a} wf dc da) =
    c-sub-use (tm-eq h h′ (unfold _ cc a)) refl
      (c-unfold (tm-eq h h′ cc) (tm-eq h h′ a)
        (H.trans (rtᵗ-≅ E (ty (TM.ren-⊢ θ ρ h c dc))) (H.trans (ty-ren θ ρ ρ′ h h′ c dc) (H.sym (R-rt θ ρ′ h′ (cthin-⟨⟩ c) E (ty dc)))))
        (ty-ren θ ρ ρ′ h h′ c da))
    where E = cong (λ X → A ⟨ σ ⟩ ⇒[ mk-kind Many (fin f) ] X) (TS.⟦⟧F-⟨⟩ σ F A)
  ty-ren θ ρ ρ′ h h′ c (⊢out {f = f} {F = F} {t = t} wf d) =
    H.trans (rtᵗ-≅ E (⊢out W (ty (TM.ren-⊢ θ ρ h c d))))
      (H.trans (c-out (tm-eq h h′ t) (ty-ren θ ρ ρ′ h h′ c d)) (H.sym (R-rt θ ρ′ h′ (cthin-⟨⟩ c) E (⊢out W (ty d)))))
    where E = sym (TS.⟦⟧F-⟨⟩ σ F (ν F f))
          W = TS.wf-⟨⟩ σ rσ wf
  ty-ren θ ρ ρ′ h h′ c (⊢iter {f = f} {s = s} df ds) =
    c-sub-use (tm-eq h h′ (iter f s)) refl (c-iter (tm-eq h h′ f) (tm-eq h h′ s) (ty-ren θ ρ ρ′ h h′ c df) (ty-ren θ ρ ρ′ h h′ c ds))
  ty-ren θ ρ ρ′ h h′ c (⊢coerce {t = t} p d) = c-coerce (tm-eq h h′ t) (ty-ren θ ρ ρ′ h h′ c d)
  ty-ren θ ρ ρ′ h h′ c ⊢lit-int = H.refl
  ty-ren θ ρ ρ′ h h′ c ⊢lit-float = H.refl
  ty-ren θ ρ ρ′ h h′ c (⊢prim {t = t} p d) =
    H.trans (rtᵗ-≅ E₂ (⊢prim p (TS.retypeᵗ σ rσ E₁ (ty (TM.ren-⊢ θ ρ h c d)))))
      (H.trans (c-prim p (tm-eq h h′ t)
                 (H.trans (rtᵗ-≅ E₁ (ty (TM.ren-⊢ θ ρ h c d)))
                   (H.trans (ty-ren θ ρ ρ′ h h′ c d) (H.sym (R-rt θ ρ′ h′ (cthin-⟨⟩ c) E₁ (ty d))))))
               (H.sym (R-rt θ ρ′ h′ (cthin-⟨⟩ c) E₂ (⊢prim p (TS.retypeᵗ σ rσ E₁ (ty d))))))
    where E₁ = TS.primDom-⟨⟩ σ p
          E₂ = sym (TS.primCod-⟨⟩ σ p)
  ty-ren θ ρ ρ′ h h′ c (⊢sigop {t = t} mem) =
    H.trans (c-sub-use refl (TS.⌜⌝ᵈ-⟨⟩ σ t) (rtᵗ-≅ (sym (TS.⌜⌝ᵈ-⟨⟩ σ t)) (⊢sigop mem)))
            (H.sym (R-rt θ ρ′ h′ (cthin-⟨⟩ c) (sym (TS.⌜⌝ᵈ-⟨⟩ σ t)) (⊢sigop mem)))
  ty-ren θ ρ ρ′ h h′ c (⊢ref d τ r) =
    H.trans (c-sub-use refl (⟨⟩-∘ (type (S !! d)) τ σ) (rtᵗ-≅ (sym (⟨⟩-∘ (type (S !! d)) τ σ)) (⊢ref d (λ i → τ i ⟨ σ ⟩) (respects-∘ r rσ))))
            (H.sym (R-rt θ ρ′ h′ (cthin-⟨⟩ c) (sym (⟨⟩-∘ (type (S !! d)) τ σ)) (⊢ref d (λ i → τ i ⟨ σ ⟩) (respects-∘ r rσ))))
  ty-ren θ ρ ρ′ h h′ c (⊢sub-use {t = t} p d) = c-sub-use (tm-eq h h′ t) refl (ty-ren θ ρ ρ′ h h′ c d)
  ty-ren θ ρ ρ′ h h′ c (⊢sub-eff {t = t} g d) = c-sub-eff (tm-eq h h′ t) (ty-ren θ ρ ρ′ h h′ c d)

  -- Weakening.
  ty-wk : ∀ {n} {Γ : Ctx m n} {B Ψ t A π} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
        → ty (TM.wk-⊢ {B = B} d) ≅ TM.wk-⊢ {Δ = Δ′} {B = B ⟨ σ ⟩} (ty d)
  ty-wk {n} {Γ} {t = t} d =
    c-sub-use (⟪⟫-wk σ t) refl
      (H.trans (ty-ren (skip (idθ n)) suc suc (λ i → cong suc (idθ-id i)) (λ i → cong suc (idθ-id i)) (cskip (cid Γ)) d)
               (H.cong (λ c → TM.ren-⊢ (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip c) (ty d))
                       (H.≡-to-≅ (cid-⟨⟩ Γ))))
