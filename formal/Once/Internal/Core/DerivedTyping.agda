-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Core.DerivedTyping — plan 0.102 phase B (for plan 0.103 phase 6):
-- the combinators' typing rules are ADMISSIBLE in the core. Each lemma types a
-- `Derived` definition at the SURFACE rule's type and usage, so the surface →
-- core translation maps a combinator rule to its definition's derivation.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Internal.Core.PolyTy using (Sig)

open import Once.Internal.Contract using (ISig)
module Once.Internal.Core.DerivedTyping {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; cong; cong₂)

open import Once.Spec.Grade using (mk-kind; Many; One; Zero; Purity; pure; act; eff; _·p_; Finite; fin; pureᶠ)
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_)
open import Once.Internal.Type using (μ-type; ν-type; Functor; ⟦_⟧T)
open import Once.Spec.Grade using (⊑-pe; _⊑π_)
open import Once.Internal.Context using (Ctx; _,_; Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)
open import Once.Surface.Properties using (+ᵘ-comm; +ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-identityˡ; *ᵘ-zeroʳ)
open import Once.Surface.Thinning using (thin-usage-refl)
open import Once.Internal.Type.WellFormed using (WellFormedF)
open import Once.Internal.Core.Rename S using (wk-⊢)
open import Once.Internal.Core.Syntax S
open import Once.Internal.Core.Typing S
open import Once.Internal.Core.Derived S

-- A variable at any grade (with its unit).
⊢var′ : ∀ {n} {Γ : Ctx n} (i : Fin n) {π : Purity} → pure ⊑π π → Γ ⊢[ singleUse i One ] var i ∷ Once.Internal.Context.lookup Γ i ! π
⊢var′ i u = ⊢sub-eff u (⊢var i)

------------------------------------------------------------------------
-- The closed combinators: at zero usage, at any grade of their arrow that has
-- a unit (`pure ⊑π π`). The body is computed purely and then embedded at the
-- arrow's grade (the unit, once, outermost), so its meaning is the grade's
-- `returnM` of a value.
------------------------------------------------------------------------

⊢idᶜ : ∀ {n} {Γ : Ctx n} {A : Type} {π : Purity} → pure ⊑π π → Γ ⊢[ zeroUsage ] idᶜ A π ∷ A ⇒[ mk-kind Many π ] A ! pure
⊢idᶜ u = ⊢lam refl (⊢var′ zero u)

⊢fstᶜ : ∀ {n} {Γ : Ctx n} {A B : Type} {π : Purity} → pure ⊑π π → Γ ⊢[ zeroUsage ] fstᶜ A B π ∷ (A * B) ⇒[ mk-kind Many π ] A ! pure
⊢fstᶜ u = ⊢lam refl (⊢sub-eff u (⊢fst (⊢var zero)))

⊢sndᶜ : ∀ {n} {Γ : Ctx n} {A B : Type} {π : Purity} → pure ⊑π π → Γ ⊢[ zeroUsage ] sndᶜ A B π ∷ (A * B) ⇒[ mk-kind Many π ] B ! pure
⊢sndᶜ u = ⊢lam refl (⊢sub-eff u (⊢snd (⊢var zero)))

⊢inlᶜ : ∀ {n} {Γ : Ctx n} {A B : Type} {π : Purity} → pure ⊑π π → Γ ⊢[ zeroUsage ] inlᶜ A B π ∷ A ⇒[ mk-kind Many π ] (A + B) ! pure
⊢inlᶜ u = ⊢lam refl (⊢sub-eff u (⊢inl (⊢var zero)))

⊢inrᶜ : ∀ {n} {Γ : Ctx n} {A B : Type} {π : Purity} → pure ⊑π π → Γ ⊢[ zeroUsage ] inrᶜ A B π ∷ B ⇒[ mk-kind Many π ] (A + B) ! pure
⊢inrᶜ u = ⊢lam refl (⊢sub-eff u (⊢inr (⊢var zero)))

⊢terminalᶜ : ∀ {n} {Γ : Ctx n} {A : Type} {π : Purity} → pure ⊑π π → Γ ⊢[ zeroUsage ] terminalᶜ A π ∷ A ⇒[ mk-kind Many π ] Unit ! pure
⊢terminalᶜ u = ⊢lam refl (⊢sub-eff u ⊢unit)

⊢initialᶜ : ∀ {n} {Γ : Ctx n} {A : Type} {π : Purity} → pure ⊑π π → Γ ⊢[ zeroUsage ] initialᶜ A π ∷ Void ⇒[ mk-kind Many π ] A ! pure
⊢initialᶜ u = ⊢lam refl (⊢sub-eff u (⊢absurd (⊢var zero)))

------------------------------------------------------------------------
-- Usage algebra
------------------------------------------------------------------------

-- The usage arithmetic the derived typings transport along (public: the 6b
-- bridge names these transports when it moves them onto the environment).
z+qz : ∀ {n} (q : Once.Spec.Grade.Quantity) → zeroUsage {n} +ᵘ q *ᵘ zeroUsage ≡ zeroUsage
z+qz q = trans (cong (zeroUsage +ᵘ_) (*ᵘ-zeroʳ q)) (+ᵘ-identityˡ _)

z⊔z : ∀ {n} → zeroUsage {n} ⊔ᵘ zeroUsage ≡ zeroUsage
z⊔z {0}     = refl
z⊔z {suc n} = cong (Zero ∷_) (z⊔z {n})

-- `Z +ᵘ q *ᵘ Ψ₂ +ᵘ One *ᵘ Ψ₁ ≡ Ψ₁ +ᵘ q *ᵘ Ψ₂` once `Z` is zero.
arms : ∀ {n} (q : Once.Spec.Grade.Quantity) {Z : Usage n} (Ψ₁ Ψ₂ : Usage n) → Z ≡ zeroUsage
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
        → pure ⊑π π₀ → Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many π ] C ! pure
        → Γ ⊢[ Ψ ] curryᶜ A B π₀ π f ∷ A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C) ! pure
⊢curryᶜ {Γ = Γ} {Ψ} {π₀ = π₀} {π} u₀ df =
  subst (λ U → Γ ⊢[ U ] _ ∷ _ ! pure)
        (trans (cong₂ _+ᵘ_ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (+ᵘ-identityˡ zeroUsage))) (z+qz Many))
                           (*ᵘ-identityˡ Ψ))
               (+ᵘ-identityˡ Ψ))
        (⊢let df (⊢lam refl (⊢sub-eff u₀
          (⊢lam refl (⊢app (⊢var (suc (suc zero))) (⊢pair (⊢var (suc zero)) (⊢var zero)))))))

⊢cataᶜ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {F : Functor} {A : Type} {π : Purity} {alg}
       → pure ⊑π π → WellFormedF F
       → Γ ⊢[ Ψ ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ! pure
       → Γ ⊢[ Many *ᵘ Ψ ] cataᶜ F π alg ∷ μ-type F ⇒[ mk-kind Many π ] A ! pure
-- Plan 0.113 B1: inside the body the algebra's variable is used ω times (the
-- fold applies it per node), so the `let` charges `Many *ᵘ Ψ` — the surface rule.
⊢cataᶜ {Γ = Γ} {Ψ} {π = π} u wf da =
  subst (λ U → Γ ⊢[ U ] _ ∷ _ ! pure)
        (trans (cong (_+ᵘ (Many *ᵘ Ψ)) (trans (cong (_+ᵘ zeroUsage) (*ᵘ-zeroʳ Many)) (+ᵘ-identityˡ zeroUsage)))
               (+ᵘ-identityˡ (Many *ᵘ Ψ)))
        (⊢let da (⊢lam refl (⊢fold u wf (⊢var (suc zero)) (⊢var zero))))

⊢anaᶜ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {F : Functor} {A : Type} {π₀ : Purity} {φ : Finite} {c}
      → pure ⊑π π₀ → WellFormedF F
      → Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A ! pure
      → Γ ⊢[ Many *ᵘ Ψ ] anaᶜ F A π₀ c ∷ A ⇒[ mk-kind Many π₀ ] ν-type F φ ! pure
⊢anaᶜ {Γ = Γ} {Ψ} {A = A} {π₀ = π₀} u₀ wf dc =
  ⊢lam refl (subst (λ U → (Γ , A) ⊢[ One ∷ U ] _ ∷ _ ! π₀) (+ᵘ-identityʳ (Many *ᵘ Ψ))
                   (⊢sub-eff u₀ (⊢unfold wf (wk-⊢′ A dc) (⊢var zero))))

⊢loopᶜ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B : Type} {c}
       → Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many act ] (B + A) ! pure
       → Γ ⊢[ Many *ᵘ Ψ ] loopᶜ A c ∷ A ⇒[ mk-kind Many eff ] B ! pure
⊢loopᶜ {Γ = Γ} {Ψ} dc =
  subst (λ U → Γ ⊢[ U ] _ ∷ _ ! pure)
        (trans (cong (_+ᵘ (Many *ᵘ Ψ)) (trans (cong (_+ᵘ zeroUsage) (*ᵘ-zeroʳ Many)) (+ᵘ-identityˡ zeroUsage)))
               (+ᵘ-identityˡ (Many *ᵘ Ψ)))
        (⊢let dc (⊢lam refl (⊢iter (⊢var (suc zero)) (⊢var zero))))

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
      → WellFormedF F → Γ ⊢[ zeroUsage ] outᶜ F ∷ ν-type F pureᶠ ⇒[ mk-kind Many pure ] ⟦ F ⟧T (ν-type F pureᶠ) ! pure
⊢outᶜ wf = ⊢lam refl (⊢out wf (⊢var zero))

⊢applyEffᶜ : ∀ {n} {Γ : Ctx n} {π : Purity} {A B : Type}
           → Γ ⊢[ zeroUsage ] applyEffᶜ π A B
               ∷ ((A ⇒[ mk-kind Many π ] B) * A) ⇒[ mk-kind Many pure ] (Unit ⇒[ mk-kind Many π ] B) ! pure
⊢applyEffᶜ {Γ = Γ} = subst (λ U → Γ ⊢[ U ] applyEffᶜ _ _ _ ∷ _ ! pure) (z+qz Many)
  (⊢lam refl (⊢lam refl (⊢app (⊢fst (⊢var (suc zero))) (⊢snd (⊢var (suc zero))))))

⊢outEffᶜ : ∀ {n} {Γ : Ctx n} {φ : Finite} {F : Functor}
         → WellFormedF F
         → Γ ⊢[ zeroUsage ] outEffᶜ φ F
             ∷ ν-type F φ ⇒[ mk-kind Many pure ] (Unit ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T (ν-type F φ)) ! pure
⊢outEffᶜ wf = ⊢lam refl (⊢lam refl (⊢out wf (⊢var (suc zero))))

-- Applying an effectful arrow builds its suspension: exactly the surface's
-- `Ψ₁ +ᵘ Many *ᵘ Ψ₂`.
⊢effAppᶜ : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {π : Purity} {A B : Type} {f x}
         → Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! pure
         → Γ ⊢[ Ψ₂ ] x ∷ A ! pure
         → Γ ⊢[ Ψ₁ +ᵘ Many *ᵘ Ψ₂ ] effAppᶜ π f x ∷ Unit ⇒[ mk-kind Many π ] B ! pure
⊢effAppᶜ df dx = ⊢lam refl (⊢app (wk-⊢′ Unit df) (wk-⊢′ Unit dx))

