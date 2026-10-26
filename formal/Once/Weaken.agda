-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Weaken — a ground type read over type variables means what
-- it means as a ground type.
--
-- A polymorphic body is typed over its parameters (`Ty m`); what it refers to
-- outside itself — an external operation, a monomorphic definition, an
-- annotation — has a ground type `T`, read there as `wk₀ T`. The meanings
-- agree: `⟦ wk₀ T ⟧ ≡ ⟦ T ⟧` in each domain, so a reference's meaning at its
-- ground type is transported to the body's.
------------------------------------------------------------------------

module Once.Weaken where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Once.Spec.Grade using (mk-kind; Zero; One; Many; pureᶠ; actᶠ)
open import Once.Spec.Type
  using (Ty; Fun; Type; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
open import Once.Type.Core using (wk₀; wk₀F)
open import Once.Internal.FunctorMeaning using (⟦_,_⟧-base; translateF; μ-sem; ν-sem)
open import Once.Internal.Polynomial using (νS)
open import Once.Spec.Polynomial using (SFunctor; SK; _S⊕_; _S⊗_; μS)

------------------------------------------------------------------------
-- Base values and functor codes
------------------------------------------------------------------------

base-wk₀ : ∀ {m} (I F : Set) (A : Type) → ⟦ I , F ⟧-base (wk₀ {m} A) ≡ ⟦ I , F ⟧-base A
base-wk₀ I F Unit         = refl
base-wk₀ I F Void         = refl
base-wk₀ I F Int          = refl
base-wk₀ I F Float        = refl
base-wk₀ I F (A * B)      = cong₂ _×_ (base-wk₀ I F A) (base-wk₀ I F B)
base-wk₀ I F (A + B)      = cong₂ _⊎_ (base-wk₀ I F A) (base-wk₀ I F B)
base-wk₀ I F (A ⇒[ _ ] B) = refl
base-wk₀ I F (μ _)        = refl
base-wk₀ I F (ν _ _)      = refl

translateF-wk₀ : ∀ {m} (I F : Set) (G : Fun 0) → translateF I F (wk₀F {m} G) ≡ translateF I F G
translateF-wk₀ I F (K A)   = cong SK (base-wk₀ I F A)
translateF-wk₀ I F Id      = refl
translateF-wk₀ I F (G ⊕ H) = cong₂ _S⊕_ (translateF-wk₀ I F G) (translateF-wk₀ I F H)
translateF-wk₀ I F (G ⊗ H) = cong₂ _S⊗_ (translateF-wk₀ I F G) (translateF-wk₀ I F H)

μ-sem-wk₀ : ∀ {m} (I F : Set) (G : Fun 0) → μ-sem I F (wk₀F {m} G) ≡ μ-sem I F G
μ-sem-wk₀ I F G = cong μS (translateF-wk₀ I F G)

ν-sem-wk₀ : ∀ {m} (I F : Set) (G : Fun 0) → ν-sem I F (wk₀F {m} G) ≡ ν-sem I F G
ν-sem-wk₀ I F G = cong νS (translateF-wk₀ I F G)

------------------------------------------------------------------------
-- The machine's value domain
------------------------------------------------------------------------

open import Once.Res using (Res)

module ValueWk₀ (I F : Set) where
  open import Once.Internal.Value I F using (⟦_⟧)

  ⟦wk₀⟧ : ∀ {m} (A : Type) → ⟦ wk₀ {m} A ⟧ ≡ ⟦ A ⟧
  ⟦wk₀⟧ Unit                       = refl
  ⟦wk₀⟧ Void                       = refl
  ⟦wk₀⟧ Int                        = refl
  ⟦wk₀⟧ Float                      = refl
  ⟦wk₀⟧ (A * B)                    = cong₂ _×_ (⟦wk₀⟧ A) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (A + B)                    = cong₂ _⊎_ (⟦wk₀⟧ A) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (A ⇒[ mk-kind Zero π ] B)  = cong (λ Y → ⟦ Unit {0} ⟧ → Res Y) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (A ⇒[ mk-kind One π ] B)   = cong₂ (λ X Y → X → Res Y) (⟦wk₀⟧ A) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (A ⇒[ mk-kind Many π ] B)  = cong₂ (λ X Y → X → Res Y) (⟦wk₀⟧ A) (⟦wk₀⟧ B)
  ⟦wk₀⟧ (μ G)                      = μ-sem-wk₀ I F G
  ⟦wk₀⟧ (ν G _)                    = ν-sem-wk₀ I F G

open import Once.Spec.Word using (Carrier)
open ValueWk₀ Carrier Carrier

------------------------------------------------------------------------
-- The denotational value domain
------------------------------------------------------------------------

open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Internal.Iterative using (T∞)
open import Once.Internal.StreamInf using (νᴵ)
open import Data.Unit using (⊤; tt)

⟦wk₀⟧ᴰ : ∀ {m} (A : Type) → ⟦ wk₀ {m} A ⟧ᴰ ≡ ⟦ A ⟧ᴰ
⟦wk₀⟧ᴰ Unit                       = refl
⟦wk₀⟧ᴰ Void                       = refl
⟦wk₀⟧ᴰ Int                        = refl
⟦wk₀⟧ᴰ Float                      = refl
⟦wk₀⟧ᴰ (A * B)                    = cong₂ _×_ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (A + B)                    = cong₂ _⊎_ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (A ⇒[ mk-kind Zero π ] B)  = cong (λ Y → ⊤ → T∞ Y) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (A ⇒[ mk-kind One π ] B)   = cong₂ (λ X Y → X → T∞ Y) (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (A ⇒[ mk-kind Many π ] B)  = cong₂ (λ X Y → X → T∞ Y) (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)
⟦wk₀⟧ᴰ (μ G)                      = ⟦wk₀⟧ (μ G)
⟦wk₀⟧ᴰ (ν G _)                    = cong νᴵ (translateF-wk₀ Carrier Carrier G)

------------------------------------------------------------------------
-- The value relation carries across: values related at `A` are related at
-- `wk₀ A` once transported, and back.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym; trans; cong-app)
open import Function using (id)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Once.Denotation.ValueRel using (RelD; StreamRel; RelS-mono)
open import Once.Denotation.TraceMonadInfLaws using (RelS)

private
  up : ∀ {m} (A : Type) → ⟦ A ⟧ᴰ → ⟦ wk₀ {m} A ⟧ᴰ
  up A = subst id (sym (⟦wk₀⟧ᴰ A))

  dn : ∀ {m} (A : Type) → ⟦ wk₀ {m} A ⟧ᴰ → ⟦ A ⟧ᴰ
  dn A = subst id (⟦wk₀⟧ᴰ A)

  -- How a transport along each type former's equation acts.
  tr-× : ∀ {X X′ Y Y′ : Set} (eX : X ≡ X′) (eY : Y ≡ Y′) (p : X × Y)
       → subst id (cong₂ _×_ eX eY) p ≡ (subst id eX (proj₁ p) , subst id eY (proj₂ p))
  tr-× refl refl p = refl

  tr-inj₁ : ∀ {X X′ Y Y′ : Set} (eX : X ≡ X′) (eY : Y ≡ Y′) (a : X)
          → subst id (cong₂ _⊎_ eX eY) (inj₁ a) ≡ inj₁ (subst id eX a)
  tr-inj₁ refl refl a = refl

  tr-inj₂ : ∀ {X X′ Y Y′ : Set} (eX : X ≡ X′) (eY : Y ≡ Y′) (b : Y)
          → subst id (cong₂ _⊎_ eX eY) (inj₂ b) ≡ inj₂ (subst id eY b)
  tr-inj₂ refl refl b = refl

  tr-→ : ∀ {X X′ Y Y′ : Set} (eX : X ≡ X′) (eY : Y ≡ Y′) (f : X → T∞ Y) (a : X′)
       → subst id (cong₂ (λ P Q → P → T∞ Q) eX eY) f a ≡ subst T∞ eY (f (subst id (sym eX) a))
  tr-→ refl refl f a = refl

  tr-→₀ : ∀ {Y Y′ : Set} (eY : Y ≡ Y′) (f : ⊤ → T∞ Y) (u : ⊤)
        → subst id (cong (λ Q → ⊤ → T∞ Q) eY) f u ≡ subst T∞ eY (f u)
  tr-→₀ refl f u = refl

  sym-cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) {a a′ b b′} (p : a ≡ a′) (q : b ≡ b′)
            → sym (cong₂ f p q) ≡ cong₂ f (sym p) (sym q)
  sym-cong₂ f refl refl = refl

  sym-cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {a a′} (p : a ≡ a′) → sym (cong f p) ≡ cong f (sym p)
  sym-cong f refl = refl

  sym-sym : ∀ {A : Set} {a b : A} (p : a ≡ b) → sym (sym p) ≡ p
  sym-sym refl = refl

  RelS-tr : ∀ {Y Y′ : Set} (e : Y ≡ Y′) {R : Y → Y → Set} {R′ : Y′ → Y′ → Set}
          → (∀ {a b} → R a b → R′ (subst id e a) (subst id e b))
          → ∀ {s s′} → RelS R s s′ → RelS R′ (subst T∞ e s) (subst T∞ e s′)
  RelS-tr refl h r = RelS-mono h r

  Stream-tr : ∀ {H H′ : SFunctor} (e : H ≡ H′) {x y} → StreamRel H x y
            → StreamRel H′ (subst id (cong νᴵ e) x) (subst id (cong νᴵ e) y)
  Stream-tr refl r = r

  e×  : ∀ {m} (A B : Type) {p : ⟦ A * B ⟧ᴰ} → up {m} (A * B) p ≡ (up A (proj₁ p) , up B (proj₂ p))
  e×  A B {p} = trans (cong (λ e → subst id e p) (sym-cong₂ _×_ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)))
                      (tr-× (sym (⟦wk₀⟧ᴰ A)) (sym (⟦wk₀⟧ᴰ B)) p)

  e₁  : ∀ {m} (A B : Type) (a : ⟦ A ⟧ᴰ) → up {m} (A + B) (inj₁ a) ≡ inj₁ (up A a)
  e₁  A B a = trans (cong (λ e → subst id e (inj₁ a)) (sym-cong₂ _⊎_ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)))
                    (tr-inj₁ (sym (⟦wk₀⟧ᴰ A)) (sym (⟦wk₀⟧ᴰ B)) a)

  e₂  : ∀ {m} (A B : Type) (b : ⟦ B ⟧ᴰ) → up {m} (A + B) (inj₂ b) ≡ inj₂ (up B b)
  e₂  A B b = trans (cong (λ e → subst id e (inj₂ b)) (sym-cong₂ _⊎_ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B)))
                    (tr-inj₂ (sym (⟦wk₀⟧ᴰ A)) (sym (⟦wk₀⟧ᴰ B)) b)

  e×ᵈ : ∀ {m} (A B : Type) {p : ⟦ wk₀ {m} (A * B) ⟧ᴰ} → dn (A * B) p ≡ (dn A (proj₁ p) , dn B (proj₂ p))
  e×ᵈ A B {p} = tr-× (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) p

mutual
  RelD-up : ∀ {m} (A : Type) {x y : ⟦ A ⟧ᴰ} → RelD A x y → RelD (wk₀ {m} A) (up A x) (up A y)
  RelD-up Unit r = r
  RelD-up Void {()} r
  RelD-up Int r = cong id r
  RelD-up Float r = cong id r
  RelD-up (A * B) {x} {y} (ra , rb) =
    subst₂ (RelD (wk₀ (A * B))) (sym (e× A B {x})) (sym (e× A B {y})) (RelD-up A ra , RelD-up B rb)
  RelD-up (A + B) {inj₁ a} {inj₁ a′} r = subst₂ (RelD (wk₀ (A + B))) (sym (e₁ A B a)) (sym (e₁ A B a′)) (RelD-up A r)
  RelD-up (A + B) {inj₂ b} {inj₂ b′} r = subst₂ (RelD (wk₀ (A + B))) (sym (e₂ A B b)) (sym (e₂ A B b′)) (RelD-up B r)
  RelD-up (A + B) {inj₁ _} {inj₂ _} ()
  RelD-up (A + B) {inj₂ _} {inj₁ _} ()
  RelD-up (A ⇒[ mk-kind Zero π ] B) {f} {g} r =
    subst₂ (RelS (RelD (wk₀ B))) (sym (up₀ A B {π} f)) (sym (up₀ A B {π} g)) (RelS-tr (sym (⟦wk₀⟧ᴰ B)) (RelD-up B) r)
  RelD-up (A ⇒[ mk-kind One π ] B) {f} {g} r {a} {a′} ra =
    subst₂ (RelS (RelD (wk₀ B))) (sym (up→₁ A B {π} f a)) (sym (up→₁ A B {π} g a′))
           (RelS-tr (sym (⟦wk₀⟧ᴰ B)) (RelD-up B) (r (RelD-dn A ra)))
  RelD-up (A ⇒[ mk-kind Many π ] B) {f} {g} r {a} {a′} ra =
    subst₂ (RelS (RelD (wk₀ B))) (sym (up→ω A B {π} f a)) (sym (up→ω A B {π} g a′))
           (RelS-tr (sym (⟦wk₀⟧ᴰ B)) (RelD-up B) (r (RelD-dn A ra)))
  RelD-up (μ G) r = cong (up (μ G)) r
  RelD-up (ν G φ) {x} {y} r =
    subst₂ (StreamRel _) (cong (λ e → subst id e x) (sym (sym-cong νᴵ (translateF-wk₀ Carrier Carrier G))))
                         (cong (λ e → subst id e y) (sym (sym-cong νᴵ (translateF-wk₀ Carrier Carrier G))))
           (Stream-tr (sym (translateF-wk₀ Carrier Carrier G)) r)

  RelD-dn : ∀ {m} (A : Type) {x y : ⟦ wk₀ {m} A ⟧ᴰ} → RelD (wk₀ A) x y → RelD A (dn A x) (dn A y)
  RelD-dn Unit r = r
  RelD-dn Void {()} r
  RelD-dn Int r = cong id r
  RelD-dn Float r = cong id r
  RelD-dn (A * B) {x} {y} (ra , rb) =
    subst₂ (RelD (A * B)) (sym (e×ᵈ A B {x})) (sym (e×ᵈ A B {y})) (RelD-dn A ra , RelD-dn B rb)
  RelD-dn (A + B) {inj₁ a} {inj₁ a′} r =
    subst₂ (RelD (A + B)) (sym (tr-inj₁ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) a)) (sym (tr-inj₁ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) a′)) (RelD-dn A r)
  RelD-dn (A + B) {inj₂ b} {inj₂ b′} r =
    subst₂ (RelD (A + B)) (sym (tr-inj₂ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) b)) (sym (tr-inj₂ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) b′)) (RelD-dn B r)
  RelD-dn (A + B) {inj₁ _} {inj₂ _} ()
  RelD-dn (A + B) {inj₂ _} {inj₁ _} ()
  RelD-dn (A ⇒[ mk-kind Zero π ] B) {f} {g} r =
    subst₂ (RelS (RelD B)) (sym (tr-→₀ (⟦wk₀⟧ᴰ B) f _)) (sym (tr-→₀ (⟦wk₀⟧ᴰ B) g _)) (RelS-tr (⟦wk₀⟧ᴰ B) (RelD-dn B) r)
  RelD-dn (A ⇒[ mk-kind One π ] B) {f} {g} r {a} {a′} ra =
    subst₂ (RelS (RelD B)) (sym (tr-→ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) f a)) (sym (tr-→ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) g a′))
           (RelS-tr (⟦wk₀⟧ᴰ B) (RelD-dn B) (r (RelD-up A ra)))
  RelD-dn (A ⇒[ mk-kind Many π ] B) {f} {g} r {a} {a′} ra =
    subst₂ (RelS (RelD B)) (sym (tr-→ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) f a)) (sym (tr-→ (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) g a′))
           (RelS-tr (⟦wk₀⟧ᴰ B) (RelD-dn B) (r (RelD-up A ra)))
  RelD-dn (μ G) r = cong (dn (μ G)) r
  RelD-dn (ν G φ) {x} {y} r = Stream-tr (translateF-wk₀ Carrier Carrier G) r

  up₀ : ∀ {m} (A B : Type) {π} (f : ⊤ → T∞ ⟦ B ⟧ᴰ)
      → up {m} (A ⇒[ mk-kind Zero π ] B) f tt ≡ subst T∞ (sym (⟦wk₀⟧ᴰ B)) (f tt)
  up₀ A B f = trans (cong (λ e → subst id e f tt) (sym-cong (λ Y → ⊤ → T∞ Y) (⟦wk₀⟧ᴰ B)))
                    (tr-→₀ (sym (⟦wk₀⟧ᴰ B)) f tt)

  up→₁ : ∀ {m} (A B : Type) {π} (f : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ) (a : ⟦ wk₀ {m} A ⟧ᴰ)
       → up (A ⇒[ mk-kind One π ] B) f a ≡ subst T∞ (sym (⟦wk₀⟧ᴰ B)) (f (dn A a))
  up→₁ A B f a = up→-gen (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) f a

  up→ω : ∀ {m} (A B : Type) {π} (f : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ) (a : ⟦ wk₀ {m} A ⟧ᴰ)
       → up (A ⇒[ mk-kind Many π ] B) f a ≡ subst T∞ (sym (⟦wk₀⟧ᴰ B)) (f (dn A a))
  up→ω A B f a = up→-gen (⟦wk₀⟧ᴰ A) (⟦wk₀⟧ᴰ B) f a

  up→-gen : ∀ {X X′ Y Y′ : Set} (eX : X′ ≡ X) (eY : Y′ ≡ Y) (f : X → T∞ Y) (a : X′)
          → subst id (sym (cong₂ (λ P Q → P → T∞ Q) eX eY)) f a ≡ subst T∞ (sym eY) (f (subst id eX a))
  up→-gen refl refl f a = refl

-- Related computations at `A` are related at `wk₀ A`, transported.
RelS-wk₀ : ∀ {m} (A : Type) {s s′ : T∞ ⟦ A ⟧ᴰ} → RelS (RelD A) s s′
         → RelS (RelD (wk₀ {m} A)) (subst T∞ (sym (⟦wk₀⟧ᴰ A)) s) (subst T∞ (sym (⟦wk₀⟧ᴰ A)) s′)
RelS-wk₀ A = RelS-tr (sym (⟦wk₀⟧ᴰ A)) (RelD-up A)

-- A comparison's result type `Unit + Unit` is closed: related at one index, at any.
RelD-bool : ∀ {m m′} {x y} → RelD {m} (Unit + Unit) x y → RelD {m′} (Unit + Unit) x y
RelD-bool {x = inj₁ _} {inj₁ _} r = r
RelD-bool {x = inj₂ _} {inj₂ _} r = r

------------------------------------------------------------------------
-- At the ground index the weakening is the identity, so its transports
-- collapse: whatever holds at `A` holds at `wk₀ A`, transported.
------------------------------------------------------------------------

mutual
  wk₀-id : (A : Type) → wk₀ {0} A ≡ A
  wk₀-id (var ())
  wk₀-id Unit           = refl
  wk₀-id Void           = refl
  wk₀-id Int            = refl
  wk₀-id Float          = refl
  wk₀-id (A * B)        = cong₂ _*_ (wk₀-id A) (wk₀-id B)
  wk₀-id (A + B)        = cong₂ _+_ (wk₀-id A) (wk₀-id B)
  wk₀-id (A ⇒[ k ] B)   = cong₂ (λ X Y → X ⇒[ k ] Y) (wk₀-id A) (wk₀-id B)
  wk₀-id (μ G)          = cong μ (wk₀F-id G)
  wk₀-id (ν G π)        = cong (λ H → ν H π) (wk₀F-id G)

  wk₀F-id : (G : Fun 0) → wk₀F {0} G ≡ G
  wk₀F-id (K A)   = cong K (wk₀-id A)
  wk₀F-id Id      = refl
  wk₀F-id (G ⊕ H) = cong₂ _⊕_ (wk₀F-id G) (wk₀F-id H)
  wk₀F-id (G ⊗ H) = cong₂ _⊗_ (wk₀F-id G) (wk₀F-id H)

-- A computation chosen per ground type, at `wk₀ A`, is the one at `A`.
T∞-wk₀ : (F : (U : Type) → T∞ ⟦ U ⟧ᴰ) (A : Type) → F (wk₀ {0} A) ≡ subst T∞ (sym (⟦wk₀⟧ᴰ A)) (F A)
T∞-wk₀ F A = go (wk₀ A) (wk₀-id A) (sym (⟦wk₀⟧ᴰ A))
  where
    go : (U : Type) → U ≡ A → (q : ⟦ A ⟧ᴰ ≡ ⟦ U ⟧ᴰ) → F U ≡ subst T∞ q (F A)
    go .A refl refl = refl
