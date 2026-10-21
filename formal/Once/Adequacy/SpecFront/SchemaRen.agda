-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.SchemaRen — two schemas that agree up to the
-- numbering of their variables (plan 0.121 `complete`).
--
-- `SchRen sc₁ sc₂ ρ`: each instance of `sc₁` is one of `sc₂`, its variables
-- renumbered by `ρ`, at the same type and respecting the kinds; and what the
-- Spec's rules ask of a schema — no variables, some, an arrow whose
-- codomain's variables are its domain's — holds of `sc₂` when it holds of
-- `sc₁`. Two readings of one written type (`SchemaOf`) agree so
-- (`schemaOf-ren`): `ρ` sends a variable to the one of the same name. So do
-- two schemas without variables at one type (`ren-0`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.SchemaRen where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Function using (Injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Grade using (mk-kind; Many)
open import Once.Spec.Type
open import Once.Spec.Core.Syntax using (Schema; schema)
open Schema using (arity; kinds; type)
open import Once.Spec.Surface.Program
  using (TypeOf; FunOf; SchemaOf; UnderK; UnderKF;
         to-var; to-unit; to-void; to-int; to-float; to-*; to-+; to-⇒; to-act; to-eff; to-μ; to-ν;
         fo-K; fo-Id; fo-⊕; fo-⊗;
         uk-*ˡ; uk-*ʳ; uk-+ˡ; uk-+ʳ; uk-⇒ˡ; uk-⇒ʳ; uk-μ; uk-ν; uk-K; uk-⊕ˡ; uk-⊕ʳ; uk-⊗ˡ; uk-⊗ʳ)

record SchRen (sc₁ sc₂ : Schema) (ρ : Fin (arity sc₂) → Fin (arity sc₁)) : Set where
  field
    ty     : ∀ {m} (τ : TySub (arity sc₁) m) → type sc₂ ⟨ (λ i → τ (ρ i)) ⟩ ≡ type sc₁ ⟨ τ ⟩
    resp   : ∀ {m} {Δ : KCtx m} (τ : TySub (arity sc₁) m) → Respects (kinds sc₁) Δ τ → Respects (kinds sc₂) Δ (λ i → τ (ρ i))
    ground : arity sc₁ ≡ 0 → arity sc₂ ≡ 0
    open′  : 0 < arity sc₁ → 0 < arity sc₂
    arrow  : ∀ {sd sc π′} → type sc₁ ≡ sd ⇒[ mk-kind Many π′ ] sc → (∀ i → Occurs i sc → Occurs i sd)
           → Σ[ sd₂ ∈ Ty (arity sc₂) ] Σ[ sc₂′ ∈ Ty (arity sc₂) ]
               (type sc₂ ≡ sd₂ ⇒[ mk-kind Many π′ ] sc₂′) × (∀ i → Occurs i sc₂′ → Occurs i sd₂)
               × (∀ {m} (τ : TySub (arity sc₁) m) → sd₂ ⟨ (λ i → τ (ρ i)) ⟩ ≡ sd ⟨ τ ⟩)
               × (∀ {m} (τ : TySub (arity sc₁) m) → sc₂′ ⟨ (λ i → τ (ρ i)) ⟩ ≡ sc ⟨ τ ⟩)

------------------------------------------------------------------------
-- Without variables
------------------------------------------------------------------------

ren-0 : ∀ {k₁ k₂ : KCtx 0} {A} → SchRen (schema 0 k₁ A) (schema 0 k₂ A) (λ i → i)
ren-0 = record
  { ty = λ τ → refl ; resp = λ τ r () ; ground = λ e → e ; open′ = λ p → p
  ; arrow = λ {sd} {sc} e occ → sd , sc , e , occ , (λ τ → refl) , (λ τ → refl) }

------------------------------------------------------------------------
-- Two readings of one written type
------------------------------------------------------------------------

module Readings {a b} (ns₁ : Fin a → String) (ns₂ : Fin b → String) (inj₁ : Injective _≡_ _≡_ ns₁)
                (ρ : Fin b → Fin a) (hρ : ∀ j → ns₁ (ρ j) ≡ ns₂ j) where

  private
    at-var : ∀ {x i j} → ns₁ i ≡ x → ns₂ j ≡ x → ρ j ≡ i
    at-var e₁ e₂ = inj₁ (trans (hρ _) (trans e₂ (sym e₁)))

  -- the same type, at every instance
  mutual
    sub-eq : ∀ {X Y₁ Y₂} → TypeOf ns₁ X Y₁ → TypeOf ns₂ X Y₂ → ∀ {m} (τ : TySub a m) → Y₂ ⟨ (λ j → τ (ρ j)) ⟩ ≡ Y₁ ⟨ τ ⟩
    sub-eq (to-var i e₁) (to-var j e₂) τ = cong τ (at-var e₁ e₂)
    sub-eq to-unit       to-unit       τ = refl
    sub-eq to-void       to-void       τ = refl
    sub-eq to-int        to-int        τ = refl
    sub-eq to-float      to-float      τ = refl
    sub-eq (to-* p q)    (to-* p′ q′)  τ = cong₂ _*_ (sub-eq p p′ τ) (sub-eq q q′ τ)
    sub-eq (to-+ p q)    (to-+ p′ q′)  τ = cong₂ _+_ (sub-eq p p′ τ) (sub-eq q q′ τ)
    sub-eq (to-⇒ p q)    (to-⇒ p′ q′)  τ = cong₂ (λ x y → x ⇒[ _ ] y) (sub-eq p p′ τ) (sub-eq q q′ τ)
    sub-eq (to-act p q)  (to-act p′ q′) τ = cong₂ (λ x y → x ⇒[ _ ] y) (sub-eq p p′ τ) (sub-eq q q′ τ)
    sub-eq (to-eff p q)  (to-eff p′ q′) τ = cong₂ (λ x y → x ⇒[ _ ] y) (sub-eq p p′ τ) (sub-eq q q′ τ)
    sub-eq (to-μ f)      (to-μ f′)     τ = cong μ (sub-eqF f f′ τ)
    sub-eq (to-ν f)      (to-ν f′)     τ = cong (λ G → ν G _) (sub-eqF f f′ τ)

    sub-eqF : ∀ {X Y₁ Y₂} → FunOf ns₁ X Y₁ → FunOf ns₂ X Y₂ → ∀ {m} (τ : TySub a m) → Y₂ ⟨ (λ j → τ (ρ j)) ⟩F ≡ Y₁ ⟨ τ ⟩F
    sub-eqF (fo-K p)    (fo-K p′)     τ = cong K (sub-eq p p′ τ)
    sub-eqF fo-Id       fo-Id         τ = refl
    sub-eqF (fo-⊕ f g)  (fo-⊕ f′ g′)  τ = cong₂ _⊕_ (sub-eqF f f′ τ) (sub-eqF g g′ τ)
    sub-eqF (fo-⊗ f g)  (fo-⊗ f′ g′)  τ = cong₂ _⊗_ (sub-eqF f f′ τ) (sub-eqF g g′ τ)

  -- a variable of the second reading occurs where its namesake does in the first
  mutual
    occ-map : ∀ {X Y₁ Y₂ j} → TypeOf ns₁ X Y₁ → TypeOf ns₂ X Y₂ → Occurs j Y₂ → Occurs (ρ j) Y₁
    occ-map (to-var i e₁) (to-var j e₂) o-var = subst (λ k → Occurs k (var i)) (sym (at-var e₁ e₂)) o-var
    occ-map (to-* p q)   (to-* p′ q′)  (o-*ˡ o) = o-*ˡ (occ-map p p′ o)
    occ-map (to-* p q)   (to-* p′ q′)  (o-*ʳ o) = o-*ʳ (occ-map q q′ o)
    occ-map (to-+ p q)   (to-+ p′ q′)  (o-+ˡ o) = o-+ˡ (occ-map p p′ o)
    occ-map (to-+ p q)   (to-+ p′ q′)  (o-+ʳ o) = o-+ʳ (occ-map q q′ o)
    occ-map (to-⇒ p q)   (to-⇒ p′ q′)  (o-⇒ˡ o) = o-⇒ˡ (occ-map p p′ o)
    occ-map (to-⇒ p q)   (to-⇒ p′ q′)  (o-⇒ʳ o) = o-⇒ʳ (occ-map q q′ o)
    occ-map (to-act p q) (to-act p′ q′) (o-⇒ˡ o) = o-⇒ˡ (occ-map p p′ o)
    occ-map (to-act p q) (to-act p′ q′) (o-⇒ʳ o) = o-⇒ʳ (occ-map q q′ o)
    occ-map (to-eff p q) (to-eff p′ q′) (o-⇒ˡ o) = o-⇒ˡ (occ-map p p′ o)
    occ-map (to-eff p q) (to-eff p′ q′) (o-⇒ʳ o) = o-⇒ʳ (occ-map q q′ o)
    occ-map (to-μ f)     (to-μ f′)     (o-μ o)  = o-μ (occ-mapF f f′ o)
    occ-map (to-ν f)     (to-ν f′)     (o-ν o)  = o-ν (occ-mapF f f′ o)

    occ-mapF : ∀ {X Y₁ Y₂ j} → FunOf ns₁ X Y₁ → FunOf ns₂ X Y₂ → OccursF j Y₂ → OccursF (ρ j) Y₁
    occ-mapF (fo-K p)   (fo-K p′)    (o-K o)  = o-K (occ-map p p′ o)
    occ-mapF (fo-⊕ f g) (fo-⊕ f′ g′) (o-⊕ˡ o) = o-⊕ˡ (occ-mapF f f′ o)
    occ-mapF (fo-⊕ f g) (fo-⊕ f′ g′) (o-⊕ʳ o) = o-⊕ʳ (occ-mapF g g′ o)
    occ-mapF (fo-⊗ f g) (fo-⊗ f′ g′) (o-⊗ˡ o) = o-⊗ˡ (occ-mapF f f′ o)
    occ-mapF (fo-⊗ f g) (fo-⊗ f′ g′) (o-⊗ʳ o) = o-⊗ʳ (occ-mapF g g′ o)

  -- …and so under a functor constant
  mutual
    uk-map : ∀ {X Y₁ Y₂ j} → TypeOf ns₁ X Y₁ → TypeOf ns₂ X Y₂ → UnderK j Y₂ → UnderK (ρ j) Y₁
    uk-map (to-* p q)   (to-* p′ q′)  (uk-*ˡ u) = uk-*ˡ (uk-map p p′ u)
    uk-map (to-* p q)   (to-* p′ q′)  (uk-*ʳ u) = uk-*ʳ (uk-map q q′ u)
    uk-map (to-+ p q)   (to-+ p′ q′)  (uk-+ˡ u) = uk-+ˡ (uk-map p p′ u)
    uk-map (to-+ p q)   (to-+ p′ q′)  (uk-+ʳ u) = uk-+ʳ (uk-map q q′ u)
    uk-map (to-⇒ p q)   (to-⇒ p′ q′)  (uk-⇒ˡ u) = uk-⇒ˡ (uk-map p p′ u)
    uk-map (to-⇒ p q)   (to-⇒ p′ q′)  (uk-⇒ʳ u) = uk-⇒ʳ (uk-map q q′ u)
    uk-map (to-act p q) (to-act p′ q′) (uk-⇒ˡ u) = uk-⇒ˡ (uk-map p p′ u)
    uk-map (to-act p q) (to-act p′ q′) (uk-⇒ʳ u) = uk-⇒ʳ (uk-map q q′ u)
    uk-map (to-eff p q) (to-eff p′ q′) (uk-⇒ˡ u) = uk-⇒ˡ (uk-map p p′ u)
    uk-map (to-eff p q) (to-eff p′ q′) (uk-⇒ʳ u) = uk-⇒ʳ (uk-map q q′ u)
    uk-map (to-μ f)     (to-μ f′)     (uk-μ u)  = uk-μ (uk-mapF f f′ u)
    uk-map (to-ν f)     (to-ν f′)     (uk-ν u)  = uk-ν (uk-mapF f f′ u)

    uk-mapF : ∀ {X Y₁ Y₂ j} → FunOf ns₁ X Y₁ → FunOf ns₂ X Y₂ → UnderKF j Y₂ → UnderKF (ρ j) Y₁
    uk-mapF (fo-K p)   (fo-K p′)    (uk-K o)  = uk-K (occ-map p p′ o)
    uk-mapF (fo-⊕ f g) (fo-⊕ f′ g′) (uk-⊕ˡ u) = uk-⊕ˡ (uk-mapF f f′ u)
    uk-mapF (fo-⊕ f g) (fo-⊕ f′ g′) (uk-⊕ʳ u) = uk-⊕ʳ (uk-mapF g g′ u)
    uk-mapF (fo-⊗ f g) (fo-⊗ f′ g′) (uk-⊗ˡ u) = uk-⊗ˡ (uk-mapF f f′ u)
    uk-mapF (fo-⊗ f g) (fo-⊗ f′ g′) (uk-⊗ʳ u) = uk-⊗ʳ (uk-mapF g g′ u)

  -- an arrow read both ways
  arrow-at : ∀ {X Y₁ Y₂ sd sc k} → TypeOf ns₁ X Y₁ → TypeOf ns₂ X Y₂ → Y₁ ≡ sd ⇒[ k ] sc
           → Σ[ Xd ∈ _ ] Σ[ Xc ∈ _ ] Σ[ sd₂ ∈ Ty b ] Σ[ sc₂ ∈ Ty b ]
               (Y₂ ≡ sd₂ ⇒[ k ] sc₂) × TypeOf ns₁ Xd sd × TypeOf ns₂ Xd sd₂ × TypeOf ns₁ Xc sc × TypeOf ns₂ Xc sc₂
  arrow-at (to-⇒ p q)   (to-⇒ p′ q′)   refl = _ , _ , _ , _ , refl , p , p′ , q , q′
  arrow-at (to-act p q) (to-act p′ q′) refl = _ , _ , _ , _ , refl , p , p′ , q , q′
  arrow-at (to-eff p q) (to-eff p′ q′) refl = _ , _ , _ , _ , refl , p , p′ , q , q′

-- A variable of one reading has a namesake in the other.
private
  mutual
    namesake : ∀ {a b} {ns₁ : Fin a → String} {ns₂ : Fin b → String} {X Y₁ Y₂ j}
             → TypeOf ns₁ X Y₁ → TypeOf ns₂ X Y₂ → Occurs j Y₂ → Σ[ i ∈ Fin a ] ns₁ i ≡ ns₂ j
    namesake (to-var i e₁) (to-var j e₂) o-var = i , trans e₁ (sym e₂)
    namesake (to-* p q)   (to-* p′ q′)  (o-*ˡ o) = namesake p p′ o
    namesake (to-* p q)   (to-* p′ q′)  (o-*ʳ o) = namesake q q′ o
    namesake (to-+ p q)   (to-+ p′ q′)  (o-+ˡ o) = namesake p p′ o
    namesake (to-+ p q)   (to-+ p′ q′)  (o-+ʳ o) = namesake q q′ o
    namesake (to-⇒ p q)   (to-⇒ p′ q′)  (o-⇒ˡ o) = namesake p p′ o
    namesake (to-⇒ p q)   (to-⇒ p′ q′)  (o-⇒ʳ o) = namesake q q′ o
    namesake (to-act p q) (to-act p′ q′) (o-⇒ˡ o) = namesake p p′ o
    namesake (to-act p q) (to-act p′ q′) (o-⇒ʳ o) = namesake q q′ o
    namesake (to-eff p q) (to-eff p′ q′) (o-⇒ˡ o) = namesake p p′ o
    namesake (to-eff p q) (to-eff p′ q′) (o-⇒ʳ o) = namesake q q′ o
    namesake (to-μ f)     (to-μ f′)     (o-μ o)  = namesakeF f f′ o
    namesake (to-ν f)     (to-ν f′)     (o-ν o)  = namesakeF f f′ o

    namesakeF : ∀ {a b} {ns₁ : Fin a → String} {ns₂ : Fin b → String} {X Y₁ Y₂ j}
              → FunOf ns₁ X Y₁ → FunOf ns₂ X Y₂ → OccursF j Y₂ → Σ[ i ∈ Fin a ] ns₁ i ≡ ns₂ j
    namesakeF (fo-K p)   (fo-K p′)    (o-K o)  = namesake p p′ o
    namesakeF (fo-⊕ f g) (fo-⊕ f′ g′) (o-⊕ˡ o) = namesakeF f f′ o
    namesakeF (fo-⊕ f g) (fo-⊕ f′ g′) (o-⊕ʳ o) = namesakeF g g′ o
    namesakeF (fo-⊗ f g) (fo-⊗ f′ g′) (o-⊗ˡ o) = namesakeF f f′ o
    namesakeF (fo-⊗ f g) (fo-⊗ f′ g′) (o-⊗ʳ o) = namesakeF g g′ o

-- The renumbering between two readings: each variable to its namesake.
ρ-of : ∀ {T sc₁ sc₂} → SchemaOf T sc₁ → SchemaOf T sc₂ → Fin (arity sc₂) → Fin (arity sc₁)
ρ-of so₁ so₂ j = proj₁ (namesake (SchemaOf.reads so₁) (SchemaOf.reads so₂) (SchemaOf.used so₂ j))

schemaOf-ren : ∀ {T sc₁ sc₂} (so₁ : SchemaOf T sc₁) (so₂ : SchemaOf T sc₂) → SchRen sc₁ sc₂ (ρ-of so₁ so₂)
schemaOf-ren {T} {sc₁} {sc₂} so₁ so₂ = record
  { ty     = R.sub-eq r₁ r₂
  ; resp   = λ τ r j kb → r (ρ j) (proj₁ (SchemaOf.kinded so₁ (ρ j)) (R.uk-map r₁ r₂ (proj₂ (SchemaOf.kinded so₂ j) kb)))
  ; ground = ground
  ; open′  = open′
  ; arrow  = arrow
  }
  where
    ρ = ρ-of so₁ so₂
    ρ′ = ρ-of so₂ so₁
    r₁ = SchemaOf.reads so₁
    r₂ = SchemaOf.reads so₂
    hρ : ∀ j → SchemaOf.names so₁ (ρ j) ≡ SchemaOf.names so₂ j
    hρ j = proj₂ (namesake r₁ r₂ (SchemaOf.used so₂ j))
    hρ′ : ∀ i → SchemaOf.names so₂ (ρ′ i) ≡ SchemaOf.names so₁ i
    hρ′ i = proj₂ (namesake r₂ r₁ (SchemaOf.used so₁ i))
    module R = Readings (SchemaOf.names so₁) (SchemaOf.names so₂) (SchemaOf.distinct so₁) ρ hρ
    module R′ = Readings (SchemaOf.names so₂) (SchemaOf.names so₁) (SchemaOf.distinct so₂) ρ′ hρ′

    ground : arity sc₁ ≡ 0 → arity sc₂ ≡ 0
    ground e = go (arity sc₂) refl
      where
        go : ∀ n → arity sc₂ ≡ n → arity sc₂ ≡ 0
        go zero    e′ = e′
        go (suc n) e′ = ⊥-elim (no (subst Fin e (ρ (subst Fin (sym e′) zero))))
          where
            no : Fin 0 → Data.Empty.⊥
            no ()
            import Data.Empty

    open′ : 0 < arity sc₁ → 0 < arity sc₂
    open′ p = go (arity sc₁) refl p
      where
        go : ∀ n → arity sc₁ ≡ n → 0 < n → 0 < arity sc₂
        go (suc n) e _ = at (arity sc₂) refl (ρ′ (subst Fin (sym e) zero))
          where
            at : ∀ k → arity sc₂ ≡ k → Fin (arity sc₂) → 0 < arity sc₂
            at (suc k) e′ _ = subst (0 <_) (sym e′) z<s
            at zero    e′ i = ⊥-elim (no (subst Fin e′ i))
              where
                no : Fin 0 → Data.Empty.⊥
                no ()
                import Data.Empty

    arrow : ∀ {sd sc π′} → type sc₁ ≡ sd ⇒[ mk-kind Many π′ ] sc → (∀ i → Occurs i sc → Occurs i sd)
          → Σ[ sd₂ ∈ Ty (arity sc₂) ] Σ[ sc₂′ ∈ Ty (arity sc₂) ]
              (type sc₂ ≡ sd₂ ⇒[ mk-kind Many π′ ] sc₂′) × (∀ i → Occurs i sc₂′ → Occurs i sd₂)
              × (∀ {m} (τ : TySub (arity sc₁) m) → sd₂ ⟨ (λ i → τ (ρ i)) ⟩ ≡ sd ⟨ τ ⟩)
              × (∀ {m} (τ : TySub (arity sc₁) m) → sc₂′ ⟨ (λ i → τ (ρ i)) ⟩ ≡ sc ⟨ τ ⟩)
    arrow e occ =
      let (_ , _ , sd₂ , sc₂′ , e₂ , pd , pd′ , pc , pc′) = R.arrow-at r₁ r₂ e
      in sd₂ , sc₂′ , e₂
         , (λ j o → subst (λ k → Occurs k sd₂) (back j) (R′.occ-map pd′ pd (occ (ρ j) (R.occ-map pc pc′ o))))
         , R.sub-eq pd pd′ , R.sub-eq pc pc′
      where
        -- the namesake of a namesake is the variable
        back : ∀ j → ρ′ (ρ j) ≡ j
        back j = SchemaOf.distinct so₂ (trans (hρ′ (ρ j)) (hρ j))
