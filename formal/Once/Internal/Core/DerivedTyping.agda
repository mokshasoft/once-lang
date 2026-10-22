-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Core.DerivedTyping — plan 0.102 phase B (for plan 0.103 phase 6):
-- the combinators' typing rules are ADMISSIBLE in the Spec's core. Each lemma
-- types a `Spec.Core.Derived` definition at the SURFACE rule's type and usage,
-- so the surface → core translation maps a combinator rule to its definition's
-- derivation. Plan 0.122: over the Spec's core (`Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Internal.Core.DerivedTyping (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; cong; cong₂)

open import Once.Spec.Grade using (mk-kind; Many; One; Zero; Quantity; Purity; pure; act; eff; _·p_; Finite; fin; pureᶠ; actᶠ; _⊑π_)
open import Once.Type.Grade using (≤qᵇ→≤q)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F)
open import Once.Internal.Type using (⟦_⟧T)
open import Once.Spec.Context using (Ctx; _▸_; lookup; _∷_)
open import Once.Internal.Context using (Usage; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊔ᵘ_; _⊑ᵘ_; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; z≤z; o≤o; m≤m)
open import Once.Spec.Context using (_⊑∷_)
open import Once.Surface.Properties using (+ᵘ-comm; +ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-identityˡ; *ᵘ-zeroʳ)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.TermModel.Subst Σ S using (wk-⊢)

module _ {m : ℕ} {Δ : KCtx m} where

  -- D276: the JOIN is derived: arms at their own usages are `⊢case` with each
  -- arm sub-used to the join.
  ⊑ᵘ-keep : ∀ {n} (q : Quantity) {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → (q ∷ Ψ) ⊑ᵘ (q ∷ Ψ′)
  ⊑ᵘ-keep Zero p = z≤z ⊑∷ p
  ⊑ᵘ-keep One  p = o≤o ⊑∷ p
  ⊑ᵘ-keep Many p = m≤m ⊑∷ p

  ⊢case⊔ : ∀ {n} {Γ : Ctx m n} {Ψs Ψₗ Ψᵣ : Usage n} {qℓ qr : Quantity} {π₁ π₂ : Purity} {A B C s l r}
         → Δ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁
         → Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψₗ ] l ∷ C ! π₂
         → Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψᵣ ] r ∷ C ! π₂
         → Δ ⊩ Γ ⊢[ Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ) ] case qℓ qr s l r ∷ C ! π₁ ·p π₂
  ⊢case⊔ {Ψₗ = Ψₗ} {Ψᵣ} {qℓ} {qr} ds dl dr =
    ⊢case ds (⊢sub-use (⊑ᵘ-keep qℓ (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)) dl) (⊢sub-use (⊑ᵘ-keep qr (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)) dr)

  -- A pure computation may sit in any position: `positionGrade q pure` is
  -- `pure` at every `q` (plan 0.116). By cases on `q`.
  ⊢let-pure : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {π : Purity} {A B e b} (q : Quantity)
            → Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! pure → Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π
            → Δ ⊩ Γ ⊢[ Ψ₂ +ᵘ (q *ᵘ Ψ₁) ] let′ q e b ∷ B ! π
  ⊢let-pure Zero d₁ d₂ = ⊢let {π₁ = pure} d₁ d₂
  ⊢let-pure One  d₁ d₂ = ⊢let d₁ d₂
  ⊢let-pure Many d₁ d₂ = ⊢let d₁ d₂

  ⊢app-pure : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {π : Purity} {A B f x} (q : Quantity)
            → Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind q π ] B ! pure → Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! pure
            → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ (q *ᵘ Ψ₂) ] app f x ∷ B ! π
  ⊢app-pure Zero df dx = ⊢app {π₂ = pure} df dx
  ⊢app-pure One  df dx = ⊢app df dx
  ⊢app-pure Many df dx = ⊢app df dx

  ⊢var′ : ∀ {n} {Γ : Ctx m n} (i : Fin n) {π : Purity} → pure ⊑π π → Δ ⊩ Γ ⊢[ singleUse i One ] var i ∷ lookup Γ i ! π
  ⊢var′ i u = ⊢sub-eff u (⊢var i)

  ------------------------------------------------------------------------
  -- The closed combinators: at zero usage, at any grade of their arrow that has
  -- a unit (`pure ⊑π π`). The body is computed purely and then embedded at the
  -- arrow's grade (the unit, once, outermost), so its meaning is the grade's
  -- `returnM` of a value.
  ------------------------------------------------------------------------

  ⊢idᶜ : ∀ {n} {Γ : Ctx m n} {A : Ty m} {π : Purity} → pure ⊑π π → Δ ⊩ Γ ⊢[ zeroUsage ] idᶜ A π ∷ A ⇒[ mk-kind Many π ] A ! pure
  ⊢idᶜ u = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢var′ zero u)

  ⊢fstᶜ : ∀ {n} {Γ : Ctx m n} {A B : Ty m} {π : Purity} → pure ⊑π π → Δ ⊩ Γ ⊢[ zeroUsage ] fstᶜ A B π ∷ (A * B) ⇒[ mk-kind Many π ] A ! pure
  ⊢fstᶜ u = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff u (⊢fst (⊢var zero)))

  ⊢sndᶜ : ∀ {n} {Γ : Ctx m n} {A B : Ty m} {π : Purity} → pure ⊑π π → Δ ⊩ Γ ⊢[ zeroUsage ] sndᶜ A B π ∷ (A * B) ⇒[ mk-kind Many π ] B ! pure
  ⊢sndᶜ u = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff u (⊢snd (⊢var zero)))

  ⊢inlᶜ : ∀ {n} {Γ : Ctx m n} {A B : Ty m} {π : Purity} → pure ⊑π π → Δ ⊩ Γ ⊢[ zeroUsage ] inlᶜ A B π ∷ A ⇒[ mk-kind Many π ] (A + B) ! pure
  ⊢inlᶜ u = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff u (⊢inl (⊢var zero)))

  ⊢inrᶜ : ∀ {n} {Γ : Ctx m n} {A B : Ty m} {π : Purity} → pure ⊑π π → Δ ⊩ Γ ⊢[ zeroUsage ] inrᶜ A B π ∷ B ⇒[ mk-kind Many π ] (A + B) ! pure
  ⊢inrᶜ u = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff u (⊢inr (⊢var zero)))

  ⊢terminalᶜ : ∀ {n} {Γ : Ctx m n} {A : Ty m} {π : Purity} → pure ⊑π π → Δ ⊩ Γ ⊢[ zeroUsage ] terminalᶜ A π ∷ A ⇒[ mk-kind Many π ] Unit ! pure
  ⊢terminalᶜ u = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff u ⊢unit)

  ⊢initialᶜ : ∀ {n} {Γ : Ctx m n} {A : Ty m} {π : Purity} → pure ⊑π π → Δ ⊩ Γ ⊢[ zeroUsage ] initialᶜ A π ∷ Void ⇒[ mk-kind Many π ] A ! pure
  ⊢initialᶜ u = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff u (⊢absurd (⊢var zero)))

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
  wk-⊢′ : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {t A π} (B : Ty m)
        → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ (Γ ▸ B) ⊢[ Zero ∷ Ψ ] wk t ∷ A ! π
  wk-⊢′ B d = wk-⊢ {B = B} d

  ------------------------------------------------------------------------
  -- The combinators with arms: each arm is evaluated once by `let`, so it
  -- costs its own usage, scaled by how often the resulting arrow's body
  -- reaches it (compose's `g` sits under `f`'s argument: `Many`).
  ------------------------------------------------------------------------

  -- D311: `g` runs first, then `f`, so the composite's body is at `π₂ ·p π₁`,
  -- and its arrow at any grade above that.
  compose-use : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → _ ≡ Ψ₁ +ᵘ Many *ᵘ Ψ₂
  compose-use Ψ₁ Ψ₂ =
    (arms Many Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (z+qz Many))) (z+qz Many)))

  ⊢composeᶜ : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π₁ π₂ π : Purity} {f g}
            → π₂ ·p π₁ ⊑π π
            → Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ B ⇒[ mk-kind Many π₁ ] C ! pure
            → Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π₂ ] B ! pure
            → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Many *ᵘ Ψ₂ ] composeᶜ A π f g ∷ A ⇒[ mk-kind Many π ] C ! pure
  ⊢composeᶜ {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {C} le df dg =
    subst (λ U → Δ ⊩ Γ ⊢[ U ] _ ∷ _ ! pure)
          (compose-use Ψ₁ Ψ₂)
          (⊢let df (⊢let (wk-⊢′ _ dg)
            (⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff le (⊢app (⊢var (suc (suc zero))) (⊢app (⊢var (suc zero)) (⊢var zero)))))))

  -- D311: `f` runs first, then `g`: the body is at `π₁ ·p π₂`.
  pair-use : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → _ ≡ Ψ₁ +ᵘ Ψ₂
  pair-use Ψ₁ Ψ₂ =
    (trans (arms One Ψ₁ Ψ₂ (trans (cong₂ _+ᵘ_ (z+qz Many) (z+qz Many)) (+ᵘ-identityˡ zeroUsage)))
                   (cong (Ψ₁ +ᵘ_) (*ᵘ-identityˡ Ψ₂)))

  ⊢pairᶜ : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π₁ π₂ π : Purity} {f g}
         → π₁ ·p π₂ ⊑π π
         → Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π₁ ] B ! pure
         → Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π₂ ] C ! pure
         → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] pairᶜ A π f g ∷ A ⇒[ mk-kind Many π ] (B * C) ! pure
  ⊢pairᶜ {Γ = Γ} {Ψ₁} {Ψ₂} le df dg =
    subst (λ U → Δ ⊩ Γ ⊢[ U ] _ ∷ _ ! pure)
          (pair-use Ψ₁ Ψ₂)
          (⊢let df (⊢let (wk-⊢′ _ dg)
            (⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff le (⊢pair (⊢app (⊢var (suc (suc zero))) (⊢var zero))
                                           (⊢app (⊢var (suc zero)) (⊢var zero)))))))

  case-use : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → _ ≡ Ψ₁ +ᵘ Ψ₂
  case-use Ψ₁ Ψ₂ =
    (trans (arms One Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (trans (cong₂ _⊔ᵘ_ (z+qz Many) (z+qz Many)) z⊔z))
                                          (+ᵘ-identityˡ zeroUsage)))
                   (cong (Ψ₁ +ᵘ_) (*ᵘ-identityˡ Ψ₂)))

  ⊢caseᶜ : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty m} {π : Purity} {f g}
         → Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] C ! pure
         → Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ B ⇒[ mk-kind Many π ] C ! pure
         → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Ψ₂ ] caseᶜ A B π f g ∷ (A + B) ⇒[ mk-kind Many π ] C ! pure
  ⊢caseᶜ {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} df dg =
    subst (λ U → Δ ⊩ Γ ⊢[ U ] _ ∷ _ ! pure)
          (case-use Ψ₁ Ψ₂)
          (⊢let df (⊢let (wk-⊢′ _ dg)
            (⊢lam (≤qᵇ→≤q _ _ refl) (⊢case⊔ (⊢var zero)
                              (⊢app (⊢var (suc (suc (suc zero)))) (⊢var zero))
                              (⊢app (⊢var (suc (suc zero))) (⊢var zero))))))

  curry-use : ∀ {n} (Ψ : Usage n) → _ ≡ Ψ
  curry-use Ψ =
    (trans (cong₂ _+ᵘ_ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (+ᵘ-identityˡ zeroUsage))) (z+qz Many))
                               (*ᵘ-identityˡ Ψ))
                   (+ᵘ-identityˡ Ψ))

  ⊢curryᶜ : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {A B C : Ty m} {π₀ π : Purity} {f}
          → pure ⊑π π₀ → Δ ⊩ Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many π ] C ! pure
          → Δ ⊩ Γ ⊢[ Ψ ] curryᶜ A B π₀ π f ∷ A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C) ! pure
  ⊢curryᶜ {Γ = Γ} {Ψ} {π₀ = π₀} {π} u₀ df =
    subst (λ U → Δ ⊩ Γ ⊢[ U ] _ ∷ _ ! pure)
          (curry-use Ψ)
          (⊢let df (⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff u₀
            (⊢lam (≤qᵇ→≤q _ _ refl) (⊢app (⊢var (suc (suc zero))) (⊢pair (⊢var (suc zero)) (⊢var zero)))))))

  cata-use : ∀ {n} (Ψ : Usage n) → (Many *ᵘ zeroUsage +ᵘ zeroUsage) +ᵘ Many *ᵘ Ψ ≡ Many *ᵘ Ψ
  cata-use Ψ = trans (cong (_+ᵘ (Many *ᵘ Ψ)) (trans (cong (_+ᵘ zeroUsage) (*ᵘ-zeroʳ Many)) (+ᵘ-identityˡ zeroUsage)))
                     (+ᵘ-identityˡ (Many *ᵘ Ψ))

  ⊢cataᶜ : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {F : Fun m} {A : Ty m} {π : Purity} {alg}
         → WFFun Δ F
         → Δ ⊩ Γ ⊢[ Ψ ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ! pure
         → Δ ⊩ Γ ⊢[ Many *ᵘ Ψ ] cataᶜ F π alg ∷ μ F ⇒[ mk-kind Many π ] A ! pure
  -- Plan 0.113 B1: inside the body the algebra's variable is used ω times (the
  -- fold applies it per node), so the `let` charges `Many *ᵘ Ψ` — the surface rule.
  ⊢cataᶜ {Γ = Γ} {Ψ} {π = π} wf da =
    subst (λ U → Δ ⊩ Γ ⊢[ U ] _ ∷ _ ! pure) (cata-use Ψ)
          (⊢let da (⊢lam (≤qᵇ→≤q _ _ refl) (⊢fold wf (⊢var (suc zero)) (⊢var zero))))

  ⊢anaᶜ : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {F : Fun m} {A : Ty m} {π₀ : Purity} {φ : Finite} {c}
        → pure ⊑π π₀ → WFFun Δ F
        → Δ ⊩ Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many (fin φ) ] ⟦ F ⟧T A ! pure
        → Δ ⊩ Γ ⊢[ Many *ᵘ Ψ ] anaᶜ F A π₀ c ∷ A ⇒[ mk-kind Many π₀ ] ν F φ ! pure
  ⊢anaᶜ {Γ = Γ} {Ψ} {A = A} {π₀ = π₀} u₀ wf dc =
    ⊢lam (≤qᵇ→≤q _ _ refl) (subst (λ U → Δ ⊩ (Γ ▸ A) ⊢[ One ∷ U ] _ ∷ _ ! π₀) (+ᵘ-identityʳ (Many *ᵘ Ψ))
                     (⊢sub-eff u₀ (⊢unfold wf (wk-⊢′ A dc) (⊢var zero))))

  loop-use : ∀ {n} (Ψ : Usage n) → _ ≡ Many *ᵘ Ψ
  loop-use Ψ =
    (trans (cong (_+ᵘ (Many *ᵘ Ψ)) (trans (cong (_+ᵘ zeroUsage) (*ᵘ-zeroʳ Many)) (+ᵘ-identityˡ zeroUsage)))
                   (+ᵘ-identityˡ (Many *ᵘ Ψ)))

  ⊢loopᶜ : ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {A B : Ty m} {c}
         → Δ ⊩ Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many act ] (B + A) ! pure
         → Δ ⊩ Γ ⊢[ Many *ᵘ Ψ ] loopᶜ A c ∷ A ⇒[ mk-kind Many eff ] B ! pure
  ⊢loopᶜ {Γ = Γ} {Ψ} dc =
    subst (λ U → Δ ⊩ Γ ⊢[ U ] _ ∷ _ ! pure)
          (loop-use Ψ)
          (⊢let dc (⊢lam (≤qᵇ→≤q _ _ refl) (⊢iter (⊢var (suc zero)) (⊢var zero))))

  ------------------------------------------------------------------------
  -- The remaining closed combinators and the suspensions.
  ------------------------------------------------------------------------

  ⊢applyᶜ : ∀ {n} {Γ : Ctx m n} {A B : Ty m}
          → Δ ⊩ Γ ⊢[ zeroUsage ] applyᶜ A B ∷ ((A ⇒[ mk-kind Many pure ] B) * A) ⇒[ mk-kind Many pure ] B ! pure
  ⊢applyᶜ {Γ = Γ} = subst (λ U → Δ ⊩ Γ ⊢[ U ] applyᶜ _ _ ∷ _ ! pure) (z+qz Many)
    (⊢lam (≤qᵇ→≤q _ _ refl) (⊢app (⊢fst (⊢var zero)) (⊢snd (⊢var zero))))

  ⊢inᶜ : ∀ {n} {Γ : Ctx m n} {F : Fun m}
       → WFFun Δ F → Δ ⊩ Γ ⊢[ zeroUsage ] inᶜ F ∷ ⟦ F ⟧T (μ F) ⇒[ mk-kind Many pure ] μ F ! pure
  ⊢inᶜ wf = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢roll wf (⊢var zero))

  ⊢outᶜ : ∀ {n} {Γ : Ctx m n} {F : Fun m}
        → WFFun Δ F → Δ ⊩ Γ ⊢[ zeroUsage ] outᶜ F ∷ ν F pureᶠ ⇒[ mk-kind Many pure ] ⟦ F ⟧T (ν F pureᶠ) ! pure
  ⊢outᶜ wf = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢out wf (⊢var zero))

  ⊢applyEffᶜ : ∀ {n} {Γ : Ctx m n} {π : Purity} {A B : Ty m}
             → Δ ⊩ Γ ⊢[ zeroUsage ] applyEffᶜ π A B
                 ∷ ((A ⇒[ mk-kind Many π ] B) * A) ⇒[ mk-kind Many pure ] (Unit ⇒[ mk-kind Many π ] B) ! pure
  ⊢applyEffᶜ {Γ = Γ} = subst (λ U → Δ ⊩ Γ ⊢[ U ] applyEffᶜ _ _ _ ∷ _ ! pure) (z+qz Many)
    (⊢lam (≤qᵇ→≤q _ _ refl) (⊢lam (≤qᵇ→≤q _ _ refl) (⊢app (⊢fst (⊢var (suc zero))) (⊢snd (⊢var (suc zero))))))

  ⊢outActᶜ : ∀ {n} {Γ : Ctx m n} {F : Fun m}
           → WFFun Δ F
           → Δ ⊩ Γ ⊢[ zeroUsage ] outActᶜ F
               ∷ ν F actᶠ ⇒[ mk-kind Many pure ] (Unit ⇒[ mk-kind Many act ] ⟦ F ⟧T (ν F actᶠ)) ! pure
  ⊢outActᶜ wf = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢lam (≤qᵇ→≤q _ _ refl) (⊢out wf (⊢var (suc zero))))

  ⊢effAppᶜ : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {π : Purity} {A B : Ty m} {f x}
           → Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! pure
           → Δ ⊩ Γ ⊢[ Ψ₂ ] x ∷ A ! pure
           → Δ ⊩ Γ ⊢[ Ψ₁ +ᵘ Many *ᵘ Ψ₂ ] effAppᶜ π f x ∷ Unit ⇒[ mk-kind Many π ] B ! pure
  ⊢effAppᶜ df dx = ⊢lam (≤qᵇ→≤q _ _ refl) (⊢app (wk-⊢′ Unit df) (wk-⊢′ Unit dx))

