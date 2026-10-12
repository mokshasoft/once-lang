-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.DerivedTyping — plan 0.102 phase B (for plan 0.103 phase 6):
-- the combinators' typing rules are ADMISSIBLE in the core. Each lemma types a
-- `Derived` definition at the SURFACE rule's type and usage, so the surface →
-- core translation maps a combinator rule to its definition's derivation.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.DerivedTyping {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; cong; cong₂)

open import Once.Spec.Type.Grade using (mk-kind; Many; One; Zero; Purity; pure; eff; _·p_)
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type; Functor; ⟦_⟧T)
open import Once.Spec.Type.Sub using (⊑-pe; pure⊑; _⊑π_)
open import Once.Spec.Context using (Ctx; _,_; Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)
open import Once.Surface.Properties using (+ᵘ-comm; +ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-identityˡ; *ᵘ-zeroʳ)
open import Once.Surface.Thinning using (thin-usage-refl)
open import Once.Spec.Type.WellFormed using (WellFormedF)
open import Once.Spec.Core.Rename S using (wk-⊢)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
open import Once.Spec.Core.Derived S

-- Every grade is above `pure`.
-- `pure⊑` (every grade is above `pure`) is `Once.Type.Sub`'s.

-- A variable at any grade.
⊢var′ : ∀ {n} {Γ : Ctx n} (i : Fin n) (π : Purity) → Γ ⊢[ singleUse i One ] var i ∷ Once.Spec.Context.lookup Γ i ! π
⊢var′ i π = ⊢sub-eff (pure⊑ π) (⊢var i)

------------------------------------------------------------------------
-- The closed combinators: at zero usage, at any grade of their arrow. The
-- body is computed purely and then embedded at the arrow's grade (the unit,
-- once, outermost), so its meaning is the grade's `returnM` of a value.
------------------------------------------------------------------------

⊢idᶜ : ∀ {n} {Γ : Ctx n} {A : Type} {π : Purity} → Γ ⊢[ zeroUsage ] idᶜ A π ∷ A ⇒[ mk-kind Many π ] A ! pure
⊢idᶜ {π = π} = ⊢lam refl (⊢var′ zero π)

⊢fstᶜ : ∀ {n} {Γ : Ctx n} {A B : Type} {π : Purity} → Γ ⊢[ zeroUsage ] fstᶜ A B π ∷ (A * B) ⇒[ mk-kind Many π ] A ! pure
⊢fstᶜ {π = π} = ⊢lam refl (⊢sub-eff (pure⊑ π) (⊢fst (⊢var zero)))

⊢sndᶜ : ∀ {n} {Γ : Ctx n} {A B : Type} {π : Purity} → Γ ⊢[ zeroUsage ] sndᶜ A B π ∷ (A * B) ⇒[ mk-kind Many π ] B ! pure
⊢sndᶜ {π = π} = ⊢lam refl (⊢sub-eff (pure⊑ π) (⊢snd (⊢var zero)))

⊢inlᶜ : ∀ {n} {Γ : Ctx n} {A B : Type} {π : Purity} → Γ ⊢[ zeroUsage ] inlᶜ A B π ∷ A ⇒[ mk-kind Many π ] (A + B) ! pure
⊢inlᶜ {π = π} = ⊢lam refl (⊢sub-eff (pure⊑ π) (⊢inl (⊢var zero)))

⊢inrᶜ : ∀ {n} {Γ : Ctx n} {A B : Type} {π : Purity} → Γ ⊢[ zeroUsage ] inrᶜ A B π ∷ B ⇒[ mk-kind Many π ] (A + B) ! pure
⊢inrᶜ {π = π} = ⊢lam refl (⊢sub-eff (pure⊑ π) (⊢inr (⊢var zero)))

⊢terminalᶜ : ∀ {n} {Γ : Ctx n} {A : Type} {π : Purity} → Γ ⊢[ zeroUsage ] terminalᶜ A π ∷ A ⇒[ mk-kind Many π ] Unit ! pure
⊢terminalᶜ {π = π} = ⊢lam refl (⊢sub-eff (pure⊑ π) ⊢unit)

⊢initialᶜ : ∀ {n} {Γ : Ctx n} {A : Type} {π : Purity} → Γ ⊢[ zeroUsage ] initialᶜ A π ∷ Void ⇒[ mk-kind Many π ] A ! pure
⊢initialᶜ {π = π} = ⊢lam refl (⊢sub-eff (pure⊑ π) (⊢absurd (⊢var zero)))

------------------------------------------------------------------------
-- Usage algebra
------------------------------------------------------------------------

-- The usage arithmetic the derived typings transport along (public: the 6b
-- bridge names these transports when it moves them onto the environment).
z+qz : ∀ {n} (q : Once.Spec.Type.Grade.Quantity) → zeroUsage {n} +ᵘ q *ᵘ zeroUsage ≡ zeroUsage
z+qz q = trans (cong (zeroUsage +ᵘ_) (*ᵘ-zeroʳ q)) (+ᵘ-identityˡ _)

z⊔z : ∀ {n} → zeroUsage {n} ⊔ᵘ zeroUsage ≡ zeroUsage
z⊔z {0}     = refl
z⊔z {suc n} = cong (Zero ∷_) (z⊔z {n})

-- `Z +ᵘ q *ᵘ Ψ₂ +ᵘ One *ᵘ Ψ₁ ≡ Ψ₁ +ᵘ q *ᵘ Ψ₂` once `Z` is zero.
arms : ∀ {n} (q : Once.Spec.Type.Grade.Quantity) {Z : Usage n} (Ψ₁ Ψ₂ : Usage n) → Z ≡ zeroUsage
     → Z +ᵘ q *ᵘ Ψ₂ +ᵘ One *ᵘ Ψ₁ ≡ Ψ₁ +ᵘ q *ᵘ Ψ₂
arms q Ψ₁ Ψ₂ refl =
  trans (cong₂ _+ᵘ_ (+ᵘ-identityˡ (q *ᵘ Ψ₂)) (*ᵘ-identityˡ Ψ₁)) (+ᵘ-comm (q *ᵘ Ψ₂) Ψ₁)

-- Weakening under one `Many` binder, at the usage `Zero ∷ Ψ`.
wk-⊢′ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {t A π} (B : Type)
      → Γ ⊢[ Ψ ] t ∷ A ! π → (Γ , B) ⊢[ Zero ∷ Ψ ] wk t ∷ A ! π
wk-⊢′ {Γ = Γ} {Ψ = Ψ} B d = subst (λ U → _ ⊢[ Zero ∷ U ] _ ∷ _ ! _) (thin-usage-refl {Γ = Γ} Ψ) (wk-⊢ B d)

------------------------------------------------------------------------
-- The combinators with arms: each arm is evaluated once by `let`, so it
-- costs its own usage, scaled by how often the resulting arrow's body
-- reaches it (compose's `g` sits under `f`'s argument: `Many`).
------------------------------------------------------------------------

-- D311: `g` runs first, then `f`, so the composite's body is at `π₂ ·p π₁`,
-- and its arrow at any grade above that.
⊢composeᶜ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type} {π₁ π₂ π : Purity} {f g}
          → π₂ ·p π₁ ⊑π π
          → Γ ⊢[ Ψ₁ ] f ∷ B ⇒[ mk-kind Many π₁ ] C ! pure
          → Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π₂ ] B ! pure
          → Γ ⊢[ Ψ₁ +ᵘ Many *ᵘ Ψ₂ ] composeᶜ A π f g ∷ A ⇒[ mk-kind Many π ] C ! pure
⊢composeᶜ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {C} le df dg =
  subst (λ U → Γ ⊢[ U ] _ ∷ _ ! pure)
        (arms Many Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (z+qz Many))) (z+qz Many)))
        (⊢let df (⊢let (wk-⊢′ _ dg)
          (⊢lam refl (⊢sub-eff le (⊢app (⊢var (suc (suc zero))) (⊢app (⊢var (suc zero)) (⊢var zero)))))))

-- D311: `f` runs first, then `g`: the body is at `π₁ ·p π₂`.
⊢pairᶜ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type} {π₁ π₂ π : Purity} {f g}
       → π₁ ·p π₂ ⊑π π
       → Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π₁ ] B ! pure
       → Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π₂ ] C ! pure
       → Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] pairᶜ A π f g ∷ A ⇒[ mk-kind Many π ] (B * C) ! pure
⊢pairᶜ {Γ = Γ} {Ψ₁} {Ψ₂} le df dg =
  subst (λ U → Γ ⊢[ U ] _ ∷ _ ! pure)
        (trans (arms One Ψ₁ Ψ₂ (trans (cong₂ _+ᵘ_ (z+qz Many) (z+qz Many)) (+ᵘ-identityˡ zeroUsage)))
               (cong (Ψ₁ +ᵘ_) (*ᵘ-identityˡ Ψ₂)))
        (⊢let df (⊢let (wk-⊢′ _ dg)
          (⊢lam refl (⊢sub-eff le (⊢pair (⊢app (⊢var (suc (suc zero))) (⊢var zero))
                                         (⊢app (⊢var (suc zero)) (⊢var zero)))))))

⊢caseᶜ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type} {π : Purity} {f g}
       → Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] C ! pure
       → Γ ⊢[ Ψ₂ ] g ∷ B ⇒[ mk-kind Many π ] C ! pure
       → Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] caseᶜ A B π f g ∷ (A + B) ⇒[ mk-kind Many π ] C ! pure
⊢caseᶜ {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} df dg =
  subst (λ U → Γ ⊢[ U ] _ ∷ _ ! pure)
        (trans (arms One Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (trans (cong₂ _⊔ᵘ_ (z+qz Many) (z+qz Many)) z⊔z))
                                      (+ᵘ-identityˡ zeroUsage)))
               (cong (Ψ₁ +ᵘ_) (*ᵘ-identityˡ Ψ₂)))
        (⊢let df (⊢let (wk-⊢′ _ dg)
          (⊢lam refl (⊢case⊔ (⊢var zero)
                            (⊢app (⊢var (suc (suc (suc zero)))) (⊢var zero))
                            (⊢app (⊢var (suc (suc zero))) (⊢var zero))))))

⊢curryᶜ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B C : Type} {π₀ π : Purity} {f}
        → Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many π ] C ! pure
        → Γ ⊢[ Ψ ] curryᶜ A B π₀ π f ∷ A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C) ! pure
⊢curryᶜ {Γ = Γ} {Ψ} {π₀ = π₀} {π} df =
  subst (λ U → Γ ⊢[ U ] _ ∷ _ ! pure)
        (trans (cong₂ _+ᵘ_ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (+ᵘ-identityˡ zeroUsage))) (z+qz Many))
                           (*ᵘ-identityˡ Ψ))
               (+ᵘ-identityˡ Ψ))
        (⊢let df (⊢lam refl (⊢sub-eff (pure⊑ π₀)
          (⊢lam refl (⊢app (⊢var (suc (suc zero))) (⊢pair (⊢var (suc zero)) (⊢var zero)))))))

⊢cataᶜ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {F : Functor} {A : Type} {π : Purity} {alg}
       → WellFormedF F
       → Γ ⊢[ Ψ ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ! pure
       → Γ ⊢[ Many *ᵘ Ψ ] cataᶜ F π alg ∷ μ-type F ⇒[ mk-kind Many π ] A ! pure
-- Plan 0.113 B1: inside the body the algebra's variable is used ω times (the
-- fold applies it per node), so the `let` charges `Many *ᵘ Ψ` — the surface rule.
⊢cataᶜ {Γ = Γ} {Ψ} {π = π} wf da =
  subst (λ U → Γ ⊢[ U ] _ ∷ _ ! pure)
        (trans (cong (_+ᵘ (Many *ᵘ Ψ)) (trans (cong (_+ᵘ zeroUsage) (*ᵘ-zeroʳ Many)) (+ᵘ-identityˡ zeroUsage)))
               (+ᵘ-identityˡ (Many *ᵘ Ψ)))
        (⊢let da (⊢lam refl (⊢fold wf (⊢var (suc zero)) (⊢var zero))))

⊢anaᶜ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {F : Functor} {A : Type} {π₀ π : Purity} {c}
      → WellFormedF F
      → Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ! pure
      → Γ ⊢[ Many *ᵘ Ψ ] anaᶜ F A π₀ c ∷ A ⇒[ mk-kind Many π₀ ] ν-type F π ! pure
⊢anaᶜ {Γ = Γ} {Ψ} {A = A} {π₀ = π₀} wf dc =
  ⊢lam refl (subst (λ U → (Γ , A) ⊢[ One ∷ U ] _ ∷ _ ! π₀) (+ᵘ-identityʳ (Many *ᵘ Ψ))
                   (⊢sub-eff (pure⊑ π₀) (⊢unfold wf (wk-⊢′ A dc) (⊢var zero))))

------------------------------------------------------------------------
-- The remaining closed combinators and the suspensions.
------------------------------------------------------------------------

⊢applyᶜ : ∀ {n} {Γ : Ctx n} {A B : Type}
        → Γ ⊢[ zeroUsage ] applyᶜ A B ∷ ((A ⇒[ mk-kind Many pure ] B) * A) ⇒[ mk-kind Many pure ] B ! pure
⊢applyᶜ {Γ = Γ} = subst (λ U → Γ ⊢[ U ] applyᶜ _ _ ∷ _ ! pure) (z+qz Many)
  (⊢lam refl (⊢app (⊢fst (⊢var zero)) (⊢snd (⊢var zero))))

⊢inᶜ : ∀ {n} {Γ : Ctx n} {F : Functor}
     → WellFormedF F → Γ ⊢[ zeroUsage ] inᶜ F ∷ ⟦ F ⟧T (μ-type F) ⇒[ mk-kind Many pure ] μ-type F ! pure
⊢inᶜ wf = ⊢lam refl (⊢roll wf (⊢var zero))

⊢outᶜ : ∀ {n} {Γ : Ctx n} {F : Functor}
      → WellFormedF F → Γ ⊢[ zeroUsage ] outᶜ F ∷ ν-type F pure ⇒[ mk-kind Many pure ] ⟦ F ⟧T (ν-type F pure) ! pure
⊢outᶜ wf = ⊢lam refl (⊢out wf (⊢var zero))

⊢applyEffᶜ : ∀ {n} {Γ : Ctx n} {A B : Type}
           → Γ ⊢[ zeroUsage ] applyEffᶜ A B
               ∷ ((A ⇒[ mk-kind Many eff ] B) * A) ⇒[ mk-kind Many pure ] (Unit ⇒[ mk-kind Many eff ] B) ! pure
⊢applyEffᶜ {Γ = Γ} = subst (λ U → Γ ⊢[ U ] applyEffᶜ _ _ ∷ _ ! pure) (z+qz Many)
  (⊢lam refl (⊢lam refl (⊢app (⊢fst (⊢var′ (suc zero) eff)) (⊢snd (⊢var′ (suc zero) eff)))))

⊢outEffᶜ : ∀ {n} {Γ : Ctx n} {F : Functor}
         → WellFormedF F
         → Γ ⊢[ zeroUsage ] outEffᶜ F
             ∷ ν-type F eff ⇒[ mk-kind Many pure ] (Unit ⇒[ mk-kind Many eff ] ⟦ F ⟧T (ν-type F eff)) ! pure
⊢outEffᶜ wf = ⊢lam refl (⊢lam refl (⊢out wf (⊢var′ (suc zero) eff)))

-- Applying an effectful arrow builds its suspension: exactly the surface's
-- `Ψ₁ +ᵘ Many *ᵘ Ψ₂`.
⊢effAppᶜ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B : Type} {f x}
         → Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many eff ] B ! pure
         → Γ ⊢[ Ψ₂ ] x ∷ A ! pure
         → Γ ⊢[ Ψ₁ +ᵘ Many *ᵘ Ψ₂ ] effAppᶜ f x ∷ Unit ⇒[ mk-kind Many eff ] B ! pure
⊢effAppᶜ df dx = ⊢lam refl (⊢app (⊢sub-eff ⊑-pe (wk-⊢′ Unit df)) (⊢sub-eff ⊑-pe (wk-⊢′ Unit dx)))

