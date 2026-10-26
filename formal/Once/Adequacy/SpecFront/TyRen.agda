-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.TyRen — the Spec's surface typing does not depend
-- on how its type variables are numbered (plan 0.121 `complete`).
--
-- A body is typed over its schema's variables, numbered as the schema lists
-- them; the Spec leaves the order free (`SchemaOf`). Renumbering the
-- variables by a bijection that keeps their kinds moves a surface
-- derivation to one of the renumbered type, naming the renumbered term
-- (`syn`, `chk`, `dom`; the core judgment's is `TySubst.ty-subst-⊢`). Only
-- the join needs the bijection: a least upper bound stays least because
-- every type is the image of one.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Adequacy.SpecFront.TyRen (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Once.Spec.Grade using (Purity; mk-kind; Many; pure)
open import Once.Metatheory.Types using (⊑π-refl)
open import Once.Spec.Type
open import Once.Spec.Type.Substitution using (respects-∘; ⟨⟩-∘)
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_; subᶜ-void; subᶜ-var; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-*; subᶜ-+; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived
open Schema using (arity; kinds; type)
import Once.Spec.Surface.Syntax as SX
import Once.Spec.Surface.Typing Σ S nm as U
open import Once.Metatheory.TermModel.TySubst Σ S using (⟦⟧F-⟨⟩; <:-⟨⟩; wf-⟨⟩; ⌜⌝ᵈ-⟨⟩)
open import Once.Core.TySubstRen Σ S using (⟪⟫-wk)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

mutual
  -- pointwise equal instances give the same type
  ⟨⟩-pt : ∀ {a k} (A : Ty a) {τ τ′ : TySub a k} → (∀ i → τ i ≡ τ′ i) → A ⟨ τ ⟩ ≡ A ⟨ τ′ ⟩
  ⟨⟩-pt (var i)      h = h i
  ⟨⟩-pt Unit         h = refl
  ⟨⟩-pt Void         h = refl
  ⟨⟩-pt (A * B)      h = cong₂ _*_ (⟨⟩-pt A h) (⟨⟩-pt B h)
  ⟨⟩-pt (A + B)      h = cong₂ _+_ (⟨⟩-pt A h) (⟨⟩-pt B h)
  ⟨⟩-pt (A ⇒[ k ] B) h = cong₂ (λ a b → a ⇒[ k ] b) (⟨⟩-pt A h) (⟨⟩-pt B h)
  ⟨⟩-pt (μ F)        h = cong μ (⟨⟩F-pt F h)
  ⟨⟩-pt (ν F f)      h = cong (λ G → ν G f) (⟨⟩F-pt F h)
  ⟨⟩-pt Int          h = refl
  ⟨⟩-pt Float        h = refl

  ⟨⟩F-pt : ∀ {a k} (F : Fun a) {τ τ′ : TySub a k} → (∀ i → τ i ≡ τ′ i) → F ⟨ τ ⟩F ≡ F ⟨ τ′ ⟩F
  ⟨⟩F-pt (K A)   h = cong K (⟨⟩-pt A h)
  ⟨⟩F-pt Id      h = refl
  ⟨⟩F-pt (F ⊕ G) h = cong₂ _⊕_ (⟨⟩F-pt F h) (⟨⟩F-pt G h)
  ⟨⟩F-pt (F ⊗ G) h = cong₂ _⊗_ (⟨⟩F-pt F h) (⟨⟩F-pt G h)

mutual
  -- the identity instance
  ⟨⟩-id : ∀ {a} (A : Ty a) → A ⟨ var ⟩ ≡ A
  ⟨⟩-id (var i)      = refl
  ⟨⟩-id Unit         = refl
  ⟨⟩-id Void         = refl
  ⟨⟩-id (A * B)      = cong₂ _*_ (⟨⟩-id A) (⟨⟩-id B)
  ⟨⟩-id (A + B)      = cong₂ _+_ (⟨⟩-id A) (⟨⟩-id B)
  ⟨⟩-id (A ⇒[ k ] B) = cong₂ (λ a b → a ⇒[ k ] b) (⟨⟩-id A) (⟨⟩-id B)
  ⟨⟩-id (μ F)        = cong μ (⟨⟩F-id F)
  ⟨⟩-id (ν F f)      = cong (λ G → ν G f) (⟨⟩F-id F)
  ⟨⟩-id Int          = refl
  ⟨⟩-id Float        = refl

  ⟨⟩F-id : ∀ {a} (F : Fun a) → F ⟨ var ⟩F ≡ F
  ⟨⟩F-id (K A)   = cong K (⟨⟩-id A)
  ⟨⟩F-id Id      = refl
  ⟨⟩F-id (F ⊕ G) = cong₂ _⊕_ (⟨⟩F-id F) (⟨⟩F-id G)
  ⟨⟩F-id (F ⊗ G) = cong₂ _⊗_ (⟨⟩F-id F) (⟨⟩F-id G)

-- `<:ᶜ` is reflexive, and survives an instance.
<:ᶜ-refl : ∀ {a} (A : Ty a) → A <:ᶜ A
<:ᶜ-refl (var i)              = subᶜ-var
<:ᶜ-refl Unit                 = subᶜ-unit
<:ᶜ-refl Void                 = subᶜ-void
<:ᶜ-refl (A * B)              = subᶜ-* (<:ᶜ-refl A) (<:ᶜ-refl B)
<:ᶜ-refl (A + B)              = subᶜ-+ (<:ᶜ-refl A) (<:ᶜ-refl B)
<:ᶜ-refl (A ⇒[ mk-kind q π ] B) = subᶜ-arr (<:ᶜ-refl B) (⊑π-refl π)
<:ᶜ-refl (μ F)                = subᶜ-μ
<:ᶜ-refl (ν F f)              = subᶜ-ν (⊑π-refl _)
<:ᶜ-refl Int                  = subᶜ-int
<:ᶜ-refl Float                = subᶜ-float

<:ᶜ-⟨⟩ : ∀ {a k} (τ : TySub a k) {A B : Ty a} → A <:ᶜ B → A ⟨ τ ⟩ <:ᶜ B ⟨ τ ⟩
<:ᶜ-⟨⟩ τ subᶜ-void        = subᶜ-void
<:ᶜ-⟨⟩ τ (subᶜ-var {i = i})   = <:ᶜ-refl (τ i)
<:ᶜ-⟨⟩ τ subᶜ-unit        = subᶜ-unit
<:ᶜ-⟨⟩ τ subᶜ-int         = subᶜ-int
<:ᶜ-⟨⟩ τ subᶜ-float       = subᶜ-float
<:ᶜ-⟨⟩ τ (subᶜ-arr b g)   = subᶜ-arr (<:ᶜ-⟨⟩ τ b) g
<:ᶜ-⟨⟩ τ (subᶜ-* a b)     = subᶜ-* (<:ᶜ-⟨⟩ τ a) (<:ᶜ-⟨⟩ τ b)
<:ᶜ-⟨⟩ τ (subᶜ-+ a b)     = subᶜ-+ (<:ᶜ-⟨⟩ τ a) (<:ᶜ-⟨⟩ τ b)
<:ᶜ-⟨⟩ τ subᶜ-μ           = subᶜ-μ
<:ᶜ-⟨⟩ τ (subᶜ-ν g)       = subᶜ-ν g

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

-- (moving a term under a binder commutes with an instance: `TySubstRen`)
private
  wk-⟪⟫ : ∀ {m k n} (σ : TySub m k) (t : Tm S m n) → (wk t) ⟪ σ ⟫ₜ ≡ wk (t ⟪ σ ⟫ₜ)
  wk-⟪⟫ σ = ⟪⟫-wk σ

module _ {m k : ℕ} (σ : TySub m k) where
  ⟪compose⟫ : ∀ {n} A π (f g : Tm S m n) → (composeᶜ A π f g) ⟪ σ ⟫ₜ ≡ composeᶜ (A ⟨ σ ⟩) π (f ⟪ σ ⟫ₜ) (g ⟪ σ ⟫ₜ)
  ⟪compose⟫ A π f g = cong (λ x → let′ _ _ (let′ _ x _)) (wk-⟪⟫ σ g)

  ⟪pair⟫ : ∀ {n} A π (f g : Tm S m n) → (pairᶜ A π f g) ⟪ σ ⟫ₜ ≡ pairᶜ (A ⟨ σ ⟩) π (f ⟪ σ ⟫ₜ) (g ⟪ σ ⟫ₜ)
  ⟪pair⟫ A π f g = cong (λ x → let′ _ _ (let′ _ x _)) (wk-⟪⟫ σ g)

  ⟪case⟫ : ∀ {n} A B π (f g : Tm S m n) → (caseᶜ A B π f g) ⟪ σ ⟫ₜ ≡ caseᶜ (A ⟨ σ ⟩) (B ⟨ σ ⟩) π (f ⟪ σ ⟫ₜ) (g ⟪ σ ⟫ₜ)
  ⟪case⟫ A B π f g = cong (λ x → let′ _ _ (let′ _ x _)) (wk-⟪⟫ σ g)

  ⟪ana⟫ : ∀ {n} F A π (c : Tm S m n) → (anaᶜ F A π c) ⟪ σ ⟫ₜ ≡ anaᶜ (F ⟨ σ ⟩F) (A ⟨ σ ⟩) π (c ⟪ σ ⟫ₜ)
  ⟪ana⟫ F A π c = cong (λ x → lam _ _ _ (unfold _ x _)) (wk-⟪⟫ σ c)

  ⟪effApp⟫ : ∀ {n} π (f x : Tm S m n) → (effAppᶜ π f x) ⟪ σ ⟫ₜ ≡ effAppᶜ π (f ⟪ σ ⟫ₜ) (x ⟪ σ ⟫ₜ)
  ⟪effApp⟫ π f x = cong₂ (λ a b → lam _ _ _ (app a b)) (wk-⟪⟫ σ f) (wk-⟪⟫ σ x)

  ⟪in⟫ : ∀ {n} F → (inᶜ {S = S} {n = n} F) ⟪ σ ⟫ₜ ≡ inᶜ (F ⟨ σ ⟩F)
  ⟪in⟫ F = cong (λ X → lam X Many pure (roll (F ⟨ σ ⟩F) (var zero))) (⟦⟧F-⟨⟩ σ F (μ F))

------------------------------------------------------------------------
-- A renumbering of the type variables
------------------------------------------------------------------------

module Bij {m k : ℕ} (σ : Fin m → Fin k) (σ⁻ : Fin k → Fin m)
           (inv : ∀ i → σ⁻ (σ i) ≡ i) (inv′ : ∀ j → σ (σ⁻ j) ≡ j)
           {Δ : KCtx m} {Δ′ : KCtx k} (kσ : ∀ i → Δ′ (σ i) ≡ Δ i) where

  sv : TySub m k
  sv i = var (σ i)

  sv⁻ : TySub k m
  sv⁻ j = var (σ⁻ j)

  rσ : Respects Δ Δ′ sv
  rσ i e = b-var (trans (kσ i) e)

  back : ∀ A → A ⟨ sv ⟩ ⟨ sv⁻ ⟩ ≡ A
  back A = trans (⟨⟩-∘ A sv sv⁻) (trans (⟨⟩-pt A (λ i → cong var (inv i))) (⟨⟩-id A))

  forth : ∀ D → D ⟨ sv⁻ ⟩ ⟨ sv ⟩ ≡ D
  forth D = trans (⟨⟩-∘ D sv⁻ sv) (trans (⟨⟩-pt D (λ j → cong var (inv′ j))) (⟨⟩-id D))

  -- a join stays least: every type is the image of one
  ⊔-ren : ∀ {A B C} → A ⊔ B ≔ C → (A ⟨ sv ⟩) ⊔ (B ⟨ sv ⟩) ≔ (C ⟨ sv ⟩)
  ⊔-ren {A} {B} {C} j = record
    { left  = <:ᶜ-⟨⟩ sv (_⊔_≔_.left j)
    ; right = <:ᶜ-⟨⟩ sv (_⊔_≔_.right j)
    ; least = λ {D} a b →
        subst (C ⟨ sv ⟩ <:ᶜ_) (forth D)
          (<:ᶜ-⟨⟩ sv (_⊔_≔_.least j (subst (_<:ᶜ D ⟨ sv⁻ ⟩) (back A) (<:ᶜ-⟨⟩ sv⁻ a))
                                     (subst (_<:ᶜ D ⟨ sv⁻ ⟩) (back B) (<:ᶜ-⟨⟩ sv⁻ b))))
    }

  -- a ground type stays itself
  ↑-ren : ∀ (T : Type) → U.↑ {m} T ⟨ sv ⟩ ≡ U.↑ T
  ↑-ren T = trans (⟨⟩-∘ T (λ ()) sv) (⟨⟩-pt T (λ ()))

  ⟨⟩-∘′ : ∀ {a} (A : Ty a) (τ : TySub a m) → A ⟨ τ ⟩ ⟨ sv ⟩ ≡ A ⟨ (λ i → τ i ⟨ sv ⟩) ⟩
  ⟨⟩-∘′ A τ = ⟨⟩-∘ A τ sv

  lt : ∀ {n} → U.Locals m n → U.Locals k n
  lt U.∅           = U.∅
  lt (L U.▹ x ∶ A) = lt L U.▹ x ∶ A ⟨ sv ⟩

  private
    lv : ∀ {n} {L : U.Locals m n} {x A i} → U._∋_⦂_at_ L x A i → U._∋_⦂_at_ (lt L) x (A ⟨ sv ⟩) i
    lv U.here         = U.here
    lv (U.there ne v) = U.there ne (lv v)

    s≡ : ∀ {n} {L : U.Locals k n} {e A A′ t t′} → A ≡ A′ → t ≡ t′ → U._⊢_⇒_↝_ Δ′ L e A t → U._⊢_⇒_↝_ Δ′ L e A′ t′
    s≡ refl refl d = d
    c≡ : ∀ {n} {L : U.Locals k n} {e A A′ t t′} → A ≡ A′ → t ≡ t′ → U._⊢_⇐_↝_ Δ′ L e A t → U._⊢_⇐_↝_ Δ′ L e A′ t′
    c≡ refl refl d = d
    d≡ : ∀ {n} {L : U.Locals k n} {e A π B B′ t t′} → B ≡ B′ → t ≡ t′ → U._⊢_⇐_⇒[_]↦_↝_ Δ′ L e A π B t → U._⊢_⇐_⇒[_]↦_↝_ Δ′ L e A π B′ t′
    d≡ refl refl d = d

  syn : ∀ {n} {L : U.Locals m n} {e A t} → U._⊢_⇒_↝_ Δ L e A t → U._⊢_⇒_↝_ Δ′ (lt L) e (A ⟨ sv ⟩) (t ⟪ sv ⟫ₜ)
  chk : ∀ {n} {L : U.Locals m n} {e A t} → U._⊢_⇐_↝_ Δ L e A t → U._⊢_⇐_↝_ Δ′ (lt L) e (A ⟨ sv ⟩) (t ⟪ sv ⟫ₜ)
  dom : ∀ {n} {L : U.Locals m n} {e A π B t} → U._⊢_⇐_⇒[_]↦_↝_ Δ L e A π B t
      → U._⊢_⇐_⇒[_]↦_↝_ Δ′ (lt L) e (A ⟨ sv ⟩) π (B ⟨ sv ⟩) (t ⟪ sv ⟫ₜ)

  syn (U.s-int i)                 = U.s-int i
  syn (U.s-float i f l)           = U.s-float i f l
  syn U.s-unit                    = U.s-unit
  syn U.s-unit-g                  = U.s-unit-g
  syn (U.s-var v)                 = U.s-var (lv v)
  syn (U.s-sigop {t = t} g M)     = s≡ (sym (⌜⌝ᵈ-⟨⟩ sv t)) refl (U.s-sigop g M)
  syn (U.s-def d e τ z)           = s≡ (sym (⟨⟩-∘′ (type (S !! d)) τ)) refl (U.s-def d e _ z)
  syn (U.s-annot {T = T} D)       = s≡ (sym (↑-ren T)) refl (U.s-annot (c≡ (↑-ren T) refl (chk D)))
  syn (U.s-pair D E)              = U.s-pair (syn D) (syn E)
  syn (U.s-neg D)                 = U.s-neg (syn D)
  syn (U.s-neg-float i f l)       = U.s-neg-float i f l
  syn (U.s-let q D E)             = U.s-let q (syn D) (syn E)
  syn (U.s-case ql qr D E F j)    = U.s-case ql qr (syn D) (syn E) (syn F) (⊔-ren j)
  syn (U.s-arith a D E)           = U.s-arith a (syn D) (syn E)
  syn (U.s-arith-float a D E)     = U.s-arith-float a (syn D) (syn E)
  syn (U.s-arith-float-il a D E)  = U.s-arith-float-il a (syn D) (syn E)
  syn (U.s-arith-float-ir a D E)  = U.s-arith-float-ir a (syn D) (syn E)
  syn (U.s-compare c D E)         = U.s-compare c (syn D) (syn E)
  syn (U.s-id-app D)              = U.s-id-app (syn D)
  syn (U.s-fst-app D)             = U.s-fst-app (syn D)
  syn (U.s-snd-app D)             = U.s-snd-app (syn D)
  syn (U.s-terminal-app D)        = U.s-terminal-app (syn D)
  syn (U.s-apply-app D)           = U.s-apply-app (syn D)
  syn (U.s-apply-eff-app g D)     = U.s-apply-eff-app g (syn D)
  syn (U.s-Out-app {F = F} w D)   = s≡ (sym (⟦⟧F-⟨⟩ sv F _)) refl (U.s-Out-app (wf-⟨⟩ sv rσ w) (syn D))
  syn (U.s-Out-act-app {F = F} w D) =
    s≡ (cong (λ X → _ ⇒[ _ ] X) (sym (⟦⟧F-⟨⟩ sv F _))) refl (U.s-Out-act-app (wf-⟨⟩ sv rσ w) (syn D))
  syn (U.s-app h D E)             = U.s-app h (syn D) (chk E)
  syn (U.s-effApp {π = π} {tf = tf} {tx = tx} h g D E) =
    s≡ refl (sym (⟪effApp⟫ sv π tf tx)) (U.s-effApp h g (syn D) (chk E))
  syn (U.s-app-spine h D E)       = U.s-app-spine h (syn D) (dom E)

  chk U.c-id                      = U.c-id
  chk U.c-fst                     = U.c-fst
  chk U.c-snd                     = U.c-snd
  chk U.c-terminal                = U.c-terminal
  chk U.c-initial                 = U.c-initial
  chk U.c-inl                     = U.c-inl
  chk U.c-inr                     = U.c-inr
  chk (U.c-compose-g {A = A} {π = π} {tf = tf} {tg = tg} D E) =
    c≡ refl (sym (⟪compose⟫ sv A π tf tg)) (U.c-compose-g (dom D) (chk E))
  chk (U.c-compose-f {A = A} {B = B} {C = C} {C′ = C′} {π = π} {π′ = π′} {tf = tf} {tg = tg} D s E) =
    c≡ refl (sym (⟪compose⟫ sv A π (coerce (B U.⇒⟨ π′ ⟩ C′) (B U.⇒⟨ π ⟩ C) tf) tg)) (U.c-compose-f (syn D) (<:-⟨⟩ sv s) (chk E))
  chk (U.c-case {A = A} {B = B} {π = π} {tf = tf} {tg = tg} D E) =
    c≡ refl (sym (⟪case⟫ sv A B π tf tg)) (U.c-case (chk D) (chk E))
  chk (U.c-pair {A = A} {π = π} {tf = tf} {tg = tg} D E) =
    c≡ refl (sym (⟪pair⟫ sv A π tf tg)) (U.c-pair (chk D) (chk E))
  chk (U.c-curry D)               = U.c-curry (chk D)
  chk (U.c-cata {F = F} {A = A} w D) =
    U.c-cata (wf-⟨⟩ sv rσ w) (c≡ (cong (λ X → X ⇒[ _ ] _) (⟦⟧F-⟨⟩ sv F A)) refl (chk D))
  chk (U.c-ana {F = F} {A = A} {π₀ = π₀} {t = t} le w D) =
    c≡ refl (sym (⟪ana⟫ sv F A π₀ t))
       (U.c-ana le (wf-⟨⟩ sv rσ w) (c≡ (cong (λ X → _ ⇒[ _ ] X) (⟦⟧F-⟨⟩ sv F A)) refl (chk D)))
  chk (U.c-loop D)                = U.c-loop (chk D)
  chk (U.c-sub D s)               = U.c-sub (syn D) (<:-⟨⟩ sv s)
  chk (U.c-lam D)                 = U.c-lam (chk D)
  chk (U.c-pair-lit D E)          = U.c-pair-lit (chk D) (chk E)
  chk (U.c-In-app {F = F} {t = t} w D) =
    c≡ refl (cong (λ x → app x (t ⟪ sv ⟫ₜ)) (sym (⟪in⟫ sv F)))
       (U.c-In-app (wf-⟨⟩ sv rσ w) (c≡ (⟦⟧F-⟨⟩ sv F (μ F)) refl (chk D)))
  chk (U.c-apply-app D)           = U.c-apply-app (syn D)
  chk (U.c-inl-app D)             = U.c-inl-app (chk D)
  chk (U.c-inr-app D)             = U.c-inr-app (chk D)
  chk (U.c-initial-app D)         = U.c-initial-app (chk D)
  chk (U.c-poly d e p τ r)        = c≡ (sym (⟨⟩-∘′ (type (S !! d)) τ)) refl (U.c-poly d e p _ (respects-∘ r rσ))

  dom (U.d-infer D s g)           = U.d-infer (syn D) (<:-⟨⟩ sv s) g
  dom (U.d-poly d e p {sd} {sc} eq occ τ r ea eb g) =
    U.d-poly d e p eq occ _ (respects-∘ r rσ) (trans (sym (⟨⟩-∘′ sd τ)) (cong (_⟨ sv ⟩) ea))
             (trans (sym (⟨⟩-∘′ sc τ)) (cong (_⟨ sv ⟩) eb)) g
  dom (U.d-lam D)                 = U.d-lam (syn D)
  dom (U.d-compose {A = A} {π = π} {tf = tf} {tg = tg} D E) =
    d≡ refl (sym (⟪compose⟫ sv A π tf tg)) (U.d-compose (dom D) (dom E))
  dom U.d-id                      = U.d-id
  dom U.d-fst                     = U.d-fst
  dom U.d-snd                     = U.d-snd
  dom U.d-terminal                = U.d-terminal
  dom U.d-initial                 = U.d-initial
  dom (U.d-case {A = A} {B = B} {Cf = Cf} {Cg = Cg} {C = C} {π = π} {tf = tf} {tg = tg} D E j) =
    d≡ refl (sym (⟪case⟫ sv A B π (coerce (A U.⇒⟨ π ⟩ Cf) (A U.⇒⟨ π ⟩ C) tf) (coerce (B U.⇒⟨ π ⟩ Cg) (B U.⇒⟨ π ⟩ C) tg))) (U.d-case (dom D) (dom E) (⊔-ren j))
  dom (U.d-pair {A = A} {π = π} {tf = tf} {tg = tg} D E) =
    d≡ refl (sym (⟪pair⟫ sv A π tf tg)) (U.d-pair (dom D) (dom E))
  dom (U.d-cata {F = F} {A = A} w D) =
    U.d-cata (wf-⟨⟩ sv rσ w) (s≡ (cong (λ X → X ⇒[ _ ] _) (⟦⟧F-⟨⟩ sv F A)) refl (syn D))
