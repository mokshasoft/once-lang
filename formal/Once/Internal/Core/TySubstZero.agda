-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Core.TySubstZero — substituting into a ground derivation
-- changes nothing: at `σ : TySub 0 0` (there is no variable),
-- `ty-subst-⊢ σ r D ≅ D`.
--
-- A monomorphic entry of the table is meant at its (only) instance through
-- `ty-subst-⊢`; this is why that is its meaning (plan 0.122; it replaces the
-- old abstraction round trip at arity 0).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Internal.Core.TySubstZero (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Once.Spec.Grade using (Many; mk-kind; positionGrade; act; fin)
open import Once.Spec.Type using (Ty; Fun; KCtx; TySub; Respects; WFFun; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F;
  K; Id; _⊕_; _⊗_; _⟨_⟩; _⟨_⟩F)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Context using (Ctx; ∅; _▸_; _⟨_⟩ᶜ; Usage; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Postulates using (extensionality)
open import Once.Functor.Translate using (WFFun-irrelevant)
open import Once.Internal.Laws.SubLaws using (<:-unique)
import Once.Metatheory.TermModel.TySubst Σ S as TS

module _ (σ : TySub 0 0) where

  mutual
    ⟨⟩-0 : (A : Ty 0) → A ⟨ σ ⟩ ≡ A
    ⟨⟩-0 (var ())
    ⟨⟩-0 Unit         = refl
    ⟨⟩-0 Void         = refl
    ⟨⟩-0 Int          = refl
    ⟨⟩-0 Float        = refl
    ⟨⟩-0 (A * B)      = cong₂ _*_ (⟨⟩-0 A) (⟨⟩-0 B)
    ⟨⟩-0 (A + B)      = cong₂ _+_ (⟨⟩-0 A) (⟨⟩-0 B)
    ⟨⟩-0 (A ⇒[ k ] B) = cong₂ (λ X Y → X ⇒[ k ] Y) (⟨⟩-0 A) (⟨⟩-0 B)
    ⟨⟩-0 (μ F)        = cong μ (⟨⟩F-0 F)
    ⟨⟩-0 (ν F f)      = cong (λ G → ν G f) (⟨⟩F-0 F)

    ⟨⟩F-0 : (F : Fun 0) → F ⟨ σ ⟩F ≡ F
    ⟨⟩F-0 (K A)   = cong K (⟨⟩-0 A)
    ⟨⟩F-0 Id      = refl
    ⟨⟩F-0 (F ⊕ G) = cong₂ _⊕_ (⟨⟩F-0 F) (⟨⟩F-0 G)
    ⟨⟩F-0 (F ⊗ G) = cong₂ _⊗_ (⟨⟩F-0 F) (⟨⟩F-0 G)

  ⟨⟩ᶜ-0 : ∀ {n} (Γ : Ctx 0 n) → Γ ⟨ σ ⟩ᶜ ≡ Γ
  ⟨⟩ᶜ-0 ∅       = refl
  ⟨⟩ᶜ-0 (Γ ▸ A) = cong₂ _▸_ (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A)

  ⟪⟫-0 : ∀ {n} (t : Tm S 0 n) → t ⟪ σ ⟫ₜ ≡ t
  ⟪⟫-0 (var i)            = refl
  ⟪⟫-0 (lam A q π t)      = cong₂ (λ X u → lam X q π u) (⟨⟩-0 A) (⟪⟫-0 t)
  ⟪⟫-0 (app f x)          = cong₂ app (⟪⟫-0 f) (⟪⟫-0 x)
  ⟪⟫-0 (let′ q e b)       = cong₂ (let′ q) (⟪⟫-0 e) (⟪⟫-0 b)
  ⟪⟫-0 unit               = refl
  ⟪⟫-0 (pair a b)         = cong₂ pair (⟪⟫-0 a) (⟪⟫-0 b)
  ⟪⟫-0 (fst p)            = cong fst (⟪⟫-0 p)
  ⟪⟫-0 (snd p)            = cong snd (⟪⟫-0 p)
  ⟪⟫-0 (inl B a)          = cong₂ inl (⟨⟩-0 B) (⟪⟫-0 a)
  ⟪⟫-0 (inr A b)          = cong₂ inr (⟨⟩-0 A) (⟪⟫-0 b)
  ⟪⟫-0 (case qℓ qr e l r) = trans (cong₂ (λ x y → case qℓ qr x y (r ⟪ σ ⟫ₜ)) (⟪⟫-0 e) (⟪⟫-0 l)) (cong (case qℓ qr e l) (⟪⟫-0 r))
  ⟪⟫-0 (absurd A e)       = cong₂ absurd (⟨⟩-0 A) (⟪⟫-0 e)
  ⟪⟫-0 (roll F t)         = cong₂ roll (⟨⟩F-0 F) (⟪⟫-0 t)
  ⟪⟫-0 (fold F a t)       = trans (cong₂ (λ G x → fold G x (t ⟪ σ ⟫ₜ)) (⟨⟩F-0 F) (⟪⟫-0 a)) (cong (fold F a) (⟪⟫-0 t))
  ⟪⟫-0 (unfold F c a)     = trans (cong₂ (λ G x → unfold G x (a ⟪ σ ⟫ₜ)) (⟨⟩F-0 F) (⟪⟫-0 c)) (cong (unfold F c) (⟪⟫-0 a))
  ⟪⟫-0 (out t)            = cong out (⟪⟫-0 t)
  ⟪⟫-0 (iter f a)         = cong₂ iter (⟪⟫-0 f) (⟪⟫-0 a)
  ⟪⟫-0 (coerce A B t)     = trans (cong₂ (λ X Y → coerce X Y (t ⟪ σ ⟫ₜ)) (⟨⟩-0 A) (⟨⟩-0 B)) (cong (coerce A B) (⟪⟫-0 t))
  ⟪⟫-0 (lit l)            = refl
  ⟪⟫-0 (prim p t)         = cong (prim p) (⟪⟫-0 t)
  ⟪⟫-0 (sigop c t)        = refl
  ⟪⟫-0 (ref d τ)          = cong (ref d) (extensionality λ i → ⟨⟩-0 (τ i))

  module _ {Δ : KCtx 0} (r : Respects Δ Δ σ) where

    private
      ty : ∀ {n} {Γ : Ctx 0 n} {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] t ⟪ σ ⟫ₜ ∷ A ⟨ σ ⟩ ! π
      ty = TS.ty-subst-⊢ σ r

      rt-≅ : ∀ {n} {Γ : Ctx 0 n} {Ψ t A A′ π} (e : A ≡ A′) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → TS.retypeᵗ σ r e d ≅ d
      rt-≅ refl d = H.refl

      -- Congruences along equal contexts, types and terms.
      J : ∀ {n} → Ctx 0 n → Usage n → Tm S 0 n → Ty 0 → _ → Set
      J Γ Ψ t A π = Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π

      g-var : ∀ {n} {Γ Γ′ : Ctx 0 n} (i : Fin n) → Γ ≡ Γ′ → ⊢var {Δ = Δ} {Γ = Γ} i ≅ ⊢var {Δ = Δ} {Γ = Γ′} i
      g-var i refl = H.refl

      g-sub-use : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ Ψ′ A A′ π t t′} {p : Once.Spec.Context._⊑ᵘ_ Ψ Ψ′} {x : J Γ Ψ t A π} {y : J Γ′ Ψ t′ A′ π}
                → Γ ≡ Γ′ → A ≡ A′ → t ≡ t′ → x ≅ y → ⊢sub-use p x ≅ ⊢sub-use p y
      g-sub-use refl refl refl H.refl = H.refl

      g-sub-eff : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ A A′ π π′ t t′} {g : Once.Spec.Grade._⊑π_ π π′} {x : J Γ Ψ t A π} {y : J Γ′ Ψ t′ A′ π}
                → Γ ≡ Γ′ → A ≡ A′ → t ≡ t′ → x ≅ y → ⊢sub-eff g x ≅ ⊢sub-eff g y
      g-sub-eff refl refl refl H.refl = H.refl

      g-lam : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ q q′ π A A′ B B′ t t′} {le : Once.Spec.Grade._≤q_ q′ q}
                {x : J (Γ ▸ A) (q′ ∷ Ψ) t B π} {y : J (Γ′ ▸ A′) (q′ ∷ Ψ) t′ B′ π}
            → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → t ≡ t′ → x ≅ y → ⊢lam le x ≅ ⊢lam le y
      g-lam refl refl refl refl H.refl = H.refl

      g-app : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ₁ Ψ₂ q π π₁ π₂ A A′ B B′ f f′ x x′}
                {df : J Γ Ψ₁ f (A ⇒[ mk-kind q π ] B) π₁} {df′ : J Γ′ Ψ₁ f′ (A′ ⇒[ mk-kind q π ] B′) π₁}
                {dx : J Γ Ψ₂ x A (positionGrade q π₂)} {dx′ : J Γ′ Ψ₂ x′ A′ (positionGrade q π₂)}
            → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → f ≡ f′ → x ≡ x′ → df ≅ df′ → dx ≅ dx′ → ⊢app df dx ≅ ⊢app df′ dx′
      g-app refl refl refl refl refl H.refl H.refl = H.refl

      g-let : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ₁ Ψ₂ q π₁ π₂ A A′ B B′ e e′ b b′}
                {de : J Γ Ψ₁ e A (positionGrade q π₁)} {de′ : J Γ′ Ψ₁ e′ A′ (positionGrade q π₁)}
                {db : J (Γ ▸ A) (q ∷ Ψ₂) b B π₂} {db′ : J (Γ′ ▸ A′) (q ∷ Ψ₂) b′ B′ π₂}
            → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → e ≡ e′ → b ≡ b′ → de ≅ de′ → db ≅ db′ → ⊢let de db ≅ ⊢let de′ db′
      g-let refl refl refl refl refl H.refl H.refl = H.refl

      g-unit : ∀ {n} {Γ Γ′ : Ctx 0 n} → Γ ≡ Γ′ → ⊢unit {Δ = Δ} {Γ = Γ} ≅ ⊢unit {Δ = Δ} {Γ = Γ′}
      g-unit refl = H.refl

      g-pair : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ₁ Ψ₂ π₁ π₂ A A′ B B′ a a′ b b′}
                 {da : J Γ Ψ₁ a A π₁} {da′ : J Γ′ Ψ₁ a′ A′ π₁} {db : J Γ Ψ₂ b B π₂} {db′ : J Γ′ Ψ₂ b′ B′ π₂}
             → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → a ≡ a′ → b ≡ b′ → da ≅ da′ → db ≅ db′ → ⊢pair da db ≅ ⊢pair da′ db′
      g-pair refl refl refl refl refl H.refl H.refl = H.refl

      g-fst : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ π A A′ B B′ p p′} {x : J Γ Ψ p (A * B) π} {y : J Γ′ Ψ p′ (A′ * B′) π}
            → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → p ≡ p′ → x ≅ y → ⊢fst x ≅ ⊢fst y
      g-fst refl refl refl refl H.refl = H.refl

      g-snd : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ π A A′ B B′ p p′} {x : J Γ Ψ p (A * B) π} {y : J Γ′ Ψ p′ (A′ * B′) π}
            → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → p ≡ p′ → x ≅ y → ⊢snd x ≅ ⊢snd y
      g-snd refl refl refl refl H.refl = H.refl

      g-inl : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ π A A′ B B′ a a′} {x : J Γ Ψ a A π} {y : J Γ′ Ψ a′ A′ π}
            → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → a ≡ a′ → x ≅ y → ⊢inl {B = B} x ≅ ⊢inl {B = B′} y
      g-inl refl refl refl refl H.refl = H.refl

      g-inr : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ π A A′ B B′ b b′} {x : J Γ Ψ b B π} {y : J Γ′ Ψ b′ B′ π}
            → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → b ≡ b′ → x ≅ y → ⊢inr {A = A} x ≅ ⊢inr {A = A′} y
      g-inr refl refl refl refl H.refl = H.refl

      g-case : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψs Ψ qℓ qr π₁ π₂ A A′ B B′ C C′ s s′ l l′ r₁ r₂}
                 {ds : J Γ Ψs s (A + B) π₁} {ds′ : J Γ′ Ψs s′ (A′ + B′) π₁}
                 {dl : J (Γ ▸ A) (qℓ ∷ Ψ) l C π₂} {dl′ : J (Γ′ ▸ A′) (qℓ ∷ Ψ) l′ C′ π₂}
                 {dr : J (Γ ▸ B) (qr ∷ Ψ) r₁ C π₂} {dr′ : J (Γ′ ▸ B′) (qr ∷ Ψ) r₂ C′ π₂}
             → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → C ≡ C′ → s ≡ s′ → l ≡ l′ → r₁ ≡ r₂ → ds ≅ ds′ → dl ≅ dl′ → dr ≅ dr′
             → ⊢case ds dl dr ≅ ⊢case ds′ dl′ dr′
      g-case refl refl refl refl refl refl refl H.refl H.refl H.refl = H.refl

      g-absurd : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ π A A′ e e′} {x : J Γ Ψ e Void π} {y : J Γ′ Ψ e′ Void π}
               → Γ ≡ Γ′ → A ≡ A′ → e ≡ e′ → x ≅ y → ⊢absurd {A = A} x ≅ ⊢absurd {A = A′} y
      g-absurd refl refl refl H.refl = H.refl

      g-roll : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ π F F′ t t′} {w : WFFun Δ F} {w′ : WFFun Δ F′}
                 {x : J Γ Ψ t (⟦ F ⟧F (μ F)) π} {y : J Γ′ Ψ t′ (⟦ F′ ⟧F (μ F′)) π}
             → Γ ≡ Γ′ → F ≡ F′ → t ≡ t′ → x ≅ y → ⊢roll w x ≅ ⊢roll w′ y
      g-roll {w = w} {w′} refl refl refl H.refl rewrite WFFun-irrelevant w w′ = H.refl

      g-fold : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψa Ψt π π₁ π₂ F F′ A A′ a a′ t t′} {w : WFFun Δ F} {w′ : WFFun Δ F′}
                 {da : J Γ Ψa a (⟦ F ⟧F A ⇒[ mk-kind Many π ] A) π₁} {da′ : J Γ′ Ψa a′ (⟦ F′ ⟧F A′ ⇒[ mk-kind Many π ] A′) π₁}
                 {dt : J Γ Ψt t (μ F) π₂} {dt′ : J Γ′ Ψt t′ (μ F′) π₂}
             → Γ ≡ Γ′ → F ≡ F′ → A ≡ A′ → a ≡ a′ → t ≡ t′ → da ≅ da′ → dt ≅ dt′ → ⊢fold w da dt ≅ ⊢fold w′ da′ dt′
      g-fold {w = w} {w′} refl refl refl refl refl H.refl H.refl rewrite WFFun-irrelevant w w′ = H.refl

      g-unfold : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψc Ψs f π₁ π₂ F F′ A A′ c c′ a a′} {w : WFFun Δ F} {w′ : WFFun Δ F′}
                   {dc : J Γ Ψc c (A ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A) π₁} {dc′ : J Γ′ Ψc c′ (A′ ⇒[ mk-kind Many (fin f) ] ⟦ F′ ⟧F A′) π₁}
                   {da : J Γ Ψs a A π₂} {da′ : J Γ′ Ψs a′ A′ π₂}
               → Γ ≡ Γ′ → F ≡ F′ → A ≡ A′ → c ≡ c′ → a ≡ a′ → dc ≅ dc′ → da ≅ da′ → ⊢unfold w dc da ≅ ⊢unfold w′ dc′ da′
      g-unfold {w = w} {w′} refl refl refl refl refl H.refl H.refl rewrite WFFun-irrelevant w w′ = H.refl

      g-out : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ f π₁ F F′ t t′} {w : WFFun Δ F} {w′ : WFFun Δ F′}
                {x : J Γ Ψ t (ν F f) π₁} {y : J Γ′ Ψ t′ (ν F′ f) π₁}
            → Γ ≡ Γ′ → F ≡ F′ → t ≡ t′ → x ≅ y → ⊢out w x ≅ ⊢out w′ y
      g-out {w = w} {w′} refl refl refl H.refl rewrite WFFun-irrelevant w w′ = H.refl

      g-iter : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψf Ψs π₁ π₂ A A′ B B′ f f′ a a′}
                 {df : J Γ Ψf f (A ⇒[ mk-kind Many act ] (B + A)) π₁} {df′ : J Γ′ Ψf f′ (A′ ⇒[ mk-kind Many act ] (B′ + A′)) π₁}
                 {da : J Γ Ψs a A π₂} {da′ : J Γ′ Ψs a′ A′ π₂}
             → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → f ≡ f′ → a ≡ a′ → df ≅ df′ → da ≅ da′ → ⊢iter df da ≅ ⊢iter df′ da′
      g-iter refl refl refl refl refl H.refl H.refl = H.refl

      g-coerce : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ π A A′ B B′ t t′} {p : A <: B} {p′ : A′ <: B′}
                   {x : J Γ Ψ t A π} {y : J Γ′ Ψ t′ A′ π}
               → Γ ≡ Γ′ → A ≡ A′ → B ≡ B′ → t ≡ t′ → x ≅ y → ⊢coerce p x ≅ ⊢coerce p′ y
      g-coerce {p = p} {p′} refl refl refl refl H.refl rewrite <:-unique p p′ = H.refl

      g-lit-int : ∀ {n} {Γ Γ′ : Ctx 0 n} {i} → Γ ≡ Γ′ → ⊢lit-int {Δ = Δ} {Γ = Γ} {i = i} ≅ ⊢lit-int {Δ = Δ} {Γ = Γ′} {i = i}
      g-lit-int refl = H.refl

      g-lit-float : ∀ {n} {Γ Γ′ : Ctx 0 n} {d} → Γ ≡ Γ′ → ⊢lit-float {Δ = Δ} {Γ = Γ} {d = d} ≅ ⊢lit-float {Δ = Δ} {Γ = Γ′} {d = d}
      g-lit-float refl = H.refl

      g-prim : ∀ {n} {Γ Γ′ : Ctx 0 n} {Ψ π t t′} (p : Prim) {x : J Γ Ψ t (primDom p) π} {y : J Γ′ Ψ t′ (primDom p) π}
             → Γ ≡ Γ′ → t ≡ t′ → x ≅ y → ⊢prim p x ≅ ⊢prim p y
      g-prim p refl refl H.refl = H.refl

      g-sigop : ∀ {n} {Γ Γ′ : Ctx 0 n} {c t} (m : _) → Γ ≡ Γ′ → ⊢sigop {Δ = Δ} {Γ = Γ} {c = c} {t = t} m ≅ ⊢sigop {Δ = Δ} {Γ = Γ′} m
      g-sigop m refl = H.refl

      g-ref : ∀ {n} {Γ Γ′ : Ctx 0 n} (d : Fin s) {τ τ′ : TySub (Schema.arity (S !! d)) 0} {r₁ r₂}
            → Γ ≡ Γ′ → τ ≡ τ′ → ⊢ref {Δ = Δ} {Γ = Γ} d τ r₁ ≅ ⊢ref {Δ = Δ} {Γ = Γ′} d τ′ r₂
      g-ref d {r₁ = r₁} {r₂} refl refl
        rewrite extensionality (λ i → extensionality (λ e → Once.Functor.Translate.Base-irrelevant (r₁ i e) (r₂ i e))) = H.refl

    -- Substituting at no variable is no change.
    ty0 : ∀ {n} {Γ : Ctx 0 n} {Ψ t A π} (D : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → ty D ≅ D
    ty0 {Γ = Γ} (⊢var i) = H.trans (rt-≅ _ _) (g-var i (⟨⟩ᶜ-0 Γ))
    ty0 {Γ = Γ} (⊢lam {A = A} {B} {t} le d) = g-lam (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 t) (ty0 d)
    ty0 {Γ = Γ} (⊢app {A = A} {B} {f} {x} df dx) =
      g-app (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 f) (⟪⟫-0 x) (ty0 df) (ty0 dx)
    ty0 {Γ = Γ} (⊢let {A = A} {B} {e} {b} d₁ d₂) =
      g-let (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 e) (⟪⟫-0 b) (ty0 d₁) (ty0 d₂)
    ty0 {Γ = Γ} ⊢unit = g-unit (⟨⟩ᶜ-0 Γ)
    ty0 {Γ = Γ} (⊢pair {A = A} {B} {a} {b} da db) =
      g-pair (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 a) (⟪⟫-0 b) (ty0 da) (ty0 db)
    ty0 {Γ = Γ} (⊢fst {A = A} {B} {p} d) = g-fst (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 p) (ty0 d)
    ty0 {Γ = Γ} (⊢snd {A = A} {B} {p} d) = g-snd (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 p) (ty0 d)
    ty0 {Γ = Γ} (⊢inl {A = A} {B} {a} d) = g-inl (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 a) (ty0 d)
    ty0 {Γ = Γ} (⊢inr {A = A} {B} {b} d) = g-inr (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 b) (ty0 d)
    ty0 {Γ = Γ} (⊢case {A = A} {B} {C} {s′} {l} {r′} ds dl dr) =
      g-case (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟨⟩-0 C) (⟪⟫-0 s′) (⟪⟫-0 l) (⟪⟫-0 r′) (ty0 ds) (ty0 dl) (ty0 dr)
    ty0 {Γ = Γ} (⊢absurd {A = A} {e} d) = g-absurd (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟪⟫-0 e) (ty0 d)
    ty0 {Γ = Γ} (⊢roll {F = F} {t} wf d) = g-roll (⟨⟩ᶜ-0 Γ) (⟨⟩F-0 F) (⟪⟫-0 t) (H.trans (rt-≅ _ _) (ty0 d))
    ty0 {Γ = Γ} (⊢fold {F = F} {A} {a} {t} wf da dt) =
      g-fold (⟨⟩ᶜ-0 Γ) (⟨⟩F-0 F) (⟨⟩-0 A) (⟪⟫-0 a) (⟪⟫-0 t) (H.trans (rt-≅ _ _) (ty0 da)) (ty0 dt)
    ty0 {Γ = Γ} (⊢unfold {F = F} {A} {c} {a} wf dc da) =
      g-unfold (⟨⟩ᶜ-0 Γ) (⟨⟩F-0 F) (⟨⟩-0 A) (⟪⟫-0 c) (⟪⟫-0 a) (H.trans (rt-≅ _ _) (ty0 dc)) (ty0 da)
    ty0 {Γ = Γ} (⊢out {F = F} {t} wf d) = H.trans (rt-≅ _ _) (g-out (⟨⟩ᶜ-0 Γ) (⟨⟩F-0 F) (⟪⟫-0 t) (ty0 d))
    ty0 {Γ = Γ} (⊢iter {A = A} {B} {f} {s′} df ds) =
      g-iter (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 f) (⟪⟫-0 s′) (ty0 df) (ty0 ds)
    ty0 {Γ = Γ} (⊢coerce {A = A} {B} {t} p d) = g-coerce (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟨⟩-0 B) (⟪⟫-0 t) (ty0 d)
    ty0 {Γ = Γ} ⊢lit-int = g-lit-int (⟨⟩ᶜ-0 Γ)
    ty0 {Γ = Γ} ⊢lit-float = g-lit-float (⟨⟩ᶜ-0 Γ)
    ty0 {Γ = Γ} (⊢prim {t = t} p d) =
      H.trans (rt-≅ _ _) (g-prim p (⟨⟩ᶜ-0 Γ) (⟪⟫-0 t) (H.trans (rt-≅ _ _) (ty0 d)))
    ty0 {Γ = Γ} (⊢sigop m) = H.trans (rt-≅ _ _) (g-sigop m (⟨⟩ᶜ-0 Γ))
    ty0 {Γ = Γ} (⊢ref d τ r′) = H.trans (rt-≅ _ _) (g-ref d (⟨⟩ᶜ-0 Γ) (extensionality λ i → ⟨⟩-0 (τ i)))
    ty0 {Γ = Γ} (⊢sub-use {A = A} {t} p d) = g-sub-use (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟪⟫-0 t) (ty0 d)
    ty0 {Γ = Γ} (⊢sub-eff {A = A} {t} g d) = g-sub-eff (⟨⟩ᶜ-0 Γ) (⟨⟩-0 A) (⟪⟫-0 t) (ty0 d)
