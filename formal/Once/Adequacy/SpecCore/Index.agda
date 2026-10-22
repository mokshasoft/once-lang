-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Index — the indices of the meaning relation (plan
-- 0.121 §3.5; plan 0.122: the compiler's core IS the Spec's).
--
-- The compiler's meaning and the Spec's run over the same derivations, so the
-- grades, usages and ground types on the two sides are the same. The relation
-- is still indexed by graphs (`PR`, `QR`, `UR`, `GR`), now of the identity:
-- each has one proof (`*-unique`), and the canonical one (`pr`, `qr`, `ur`,
-- `gr`) is what the fundamental lemma reads.
------------------------------------------------------------------------

module Once.Adequacy.SpecCore.Index where

open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Once.Spec.Grade
open import Once.Spec.Type using (Type; Fun; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_; ⟦_⟧F)
open import Once.Spec.Context using (Usage; []; _∷_; _+ᵘ_; _*ᵘ_)

------------------------------------------------------------------------
-- Grades and usages
------------------------------------------------------------------------

data PR : Purity → Purity → Set where
  pr-pure : PR pure pure
  pr-act  : PR act  act
  pr-eff  : PR eff  eff

pr : ∀ π → PR π π
pr pure = pr-pure
pr act  = pr-act
pr eff  = pr-eff

pr-fin : ∀ φ → PR (fin φ) (fin φ)
pr-fin φ = pr (fin φ)

pr-· : ∀ {π₁ π₁′ π₂ π₂′} → PR π₁ π₁′ → PR π₂ π₂′ → PR (π₁ ·p π₂) (π₁′ ·p π₂′)
pr-· pr-pure p       = p
pr-· pr-act  pr-pure = pr-act
pr-· pr-act  pr-act  = pr-act
pr-· pr-act  pr-eff  = pr-eff
pr-· pr-eff  p       = pr-eff

pr-pos : ∀ q {π π′} → PR π π′ → PR (positionGrade q π) (positionGrade q π′)
pr-pos Zero p = pr-pure
pr-pos One  p = p
pr-pos Many p = p

data QR : Quantity → Quantity → Set where
  qr-zero : QR Zero Zero
  qr-one  : QR One  One
  qr-many : QR Many Many

qr : ∀ q → QR q q
qr Zero = qr-zero
qr One  = qr-one
qr Many = qr-many

data UR : ∀ {n} → Usage n → Usage n → Set where
  ur-[] : UR [] []
  ur-∷  : ∀ {n q q′} {Ψ Φ : Usage n} → QR q q′ → UR Ψ Φ → UR (q ∷ Ψ) (q′ ∷ Φ)

ur : ∀ {n} (Ψ : Usage n) → UR Ψ Ψ
ur []      = ur-[]
ur (q ∷ Ψ) = ur-∷ (qr q) (ur Ψ)

qr-+ : ∀ {p p′ q q′} → QR p p′ → QR q q′ → QR (p +q q) (p′ +q q′)
qr-+ qr-zero b       = b
qr-+ qr-one  qr-zero = qr-one
qr-+ qr-one  qr-one  = qr-many
qr-+ qr-one  qr-many = qr-many
qr-+ qr-many b       = qr-many

qr-* : ∀ {p p′ q q′} → QR p p′ → QR q q′ → QR (p *q q) (p′ *q q′)
qr-* qr-zero b       = qr-zero
qr-* qr-one  qr-zero = qr-zero
qr-* qr-one  qr-one  = qr-one
qr-* qr-one  qr-many = qr-many
qr-* qr-many qr-zero = qr-zero
qr-* qr-many qr-one  = qr-many
qr-* qr-many qr-many = qr-many

ur-+ : ∀ {n} {Ψ₁ Ψ₂ Φ₁ Φ₂ : Usage n} → UR Ψ₁ Φ₁ → UR Ψ₂ Φ₂ → UR (Ψ₁ +ᵘ Ψ₂) (Φ₁ +ᵘ Φ₂)
ur-+ ur-[]        ur-[]        = ur-[]
ur-+ (ur-∷ a u)  (ur-∷ b v)   = ur-∷ (qr-+ a b) (ur-+ u v)

ur-* : ∀ {n q q′} {Ψ Φ : Usage n} → QR q q′ → UR Ψ Φ → UR (q *ᵘ Ψ) (q′ *ᵘ Φ)
ur-* a ur-[]       = ur-[]
ur-* a (ur-∷ b u)  = ur-∷ (qr-* a b) (ur-* a u)

------------------------------------------------------------------------
-- Ground types
------------------------------------------------------------------------

mutual
  data GR : Type → Type → Set where
    g-unit  : GR Unit Unit
    g-void  : GR Void Void
    g-int   : GR Int Int
    g-float : GR Float Float
    g-*     : ∀ {A A′ B B′} → GR A A′ → GR B B′ → GR (A * B) (A′ * B′)
    g-+     : ∀ {A A′ B B′} → GR A A′ → GR B B′ → GR (A + B) (A′ + B′)
    g-⇒     : ∀ {A A′ B B′ q π} → GR A A′ → GR B B′
            → GR (A ⇒[ mk-kind q π ] B) (A′ ⇒[ mk-kind q π ] B′)
    g-μ     : ∀ {F F′} → GF F F′ → GR (μ F) (μ F′)
    g-ν     : ∀ {F F′ φ} → GF F F′ → GR (ν F φ) (ν F′ φ)

  data GF : Fun 0 → Fun 0 → Set where
    g-K  : ∀ {A A′} → GR A A′ → GF (K A) (K A′)
    g-Id : GF Id Id
    g-⊕  : ∀ {F F′ G G′} → GF F F′ → GF G G′ → GF (F ⊕ G) (F′ ⊕ G′)
    g-⊗  : ∀ {F F′ G G′} → GF F F′ → GF G G′ → GF (F ⊗ G) (F′ ⊗ G′)

mutual
  gr : (A : Type) → GR A A
  gr (Once.Spec.Type.var ())
  gr Unit         = g-unit
  gr Void         = g-void
  gr Int          = g-int
  gr Float        = g-float
  gr (A * B)      = g-* (gr A) (gr B)
  gr (A + B)      = g-+ (gr A) (gr B)
  gr (A ⇒[ mk-kind q π ] B) = g-⇒ (gr A) (gr B)
  gr (μ F)        = g-μ (gf F)
  gr (ν F φ)      = g-ν (gf F)

  gf : (F : Fun 0) → GF F F
  gf (K A)   = g-K (gr A)
  gf Id      = g-Id
  gf (F ⊕ G) = g-⊕ (gf F) (gf G)
  gf (F ⊗ G) = g-⊗ (gf F) (gf G)

GR-⟦⟧ : ∀ {F F′ X X′} → GF F F′ → GR X X′ → GR (⟦ F ⟧F X) (⟦ F′ ⟧F X′)
GR-⟦⟧ (g-K a)   x = a
GR-⟦⟧ g-Id      x = x
GR-⟦⟧ (g-⊕ f g) x = g-+ (GR-⟦⟧ f x) (GR-⟦⟧ g x)
GR-⟦⟧ (g-⊗ f g) x = g-* (GR-⟦⟧ f x) (GR-⟦⟧ g x)

------------------------------------------------------------------------
-- Each graph has one proof
------------------------------------------------------------------------

PR-unique : ∀ {π π′} (p p′ : PR π π′) → p ≡ p′
PR-unique pr-pure pr-pure = refl
PR-unique pr-act  pr-act  = refl
PR-unique pr-eff  pr-eff  = refl

QR-unique : ∀ {q q′} (a b : QR q q′) → a ≡ b
QR-unique qr-zero qr-zero = refl
QR-unique qr-one  qr-one  = refl
QR-unique qr-many qr-many = refl

UR-unique : ∀ {n} {Ψ Φ : Usage n} (u v : UR Ψ Φ) → u ≡ v
UR-unique ur-[]      ur-[]      = refl
UR-unique (ur-∷ a u) (ur-∷ b v) = cong₂ ur-∷ (QR-unique a b) (UR-unique u v)

mutual
  GR-unique : ∀ {A A′} (a b : GR A A′) → a ≡ b
  GR-unique g-unit    g-unit      = refl
  GR-unique g-void    g-void      = refl
  GR-unique g-int     g-int       = refl
  GR-unique g-float   g-float     = refl
  GR-unique (g-* a b) (g-* a′ b′) = cong₂ g-* (GR-unique a a′) (GR-unique b b′)
  GR-unique (g-+ a b) (g-+ a′ b′) = cong₂ g-+ (GR-unique a a′) (GR-unique b b′)
  GR-unique (g-⇒ a b) (g-⇒ a′ b′) = cong₂ g-⇒ (GR-unique a a′) (GR-unique b b′)
  GR-unique (g-μ f)   (g-μ f′)    = cong g-μ (GF-unique f f′)
  GR-unique (g-ν f)   (g-ν f′)    = cong g-ν (GF-unique f f′)

  GF-unique : ∀ {F F′} (f g : GF F F′) → f ≡ g
  GF-unique (g-K a)   (g-K b)     = cong g-K (GR-unique a b)
  GF-unique g-Id      g-Id        = refl
  GF-unique (g-⊕ f g) (g-⊕ f′ g′) = cong₂ g-⊕ (GF-unique f f′) (GF-unique g g′)
  GF-unique (g-⊗ f g) (g-⊗ f′ g′) = cong₂ g-⊗ (GF-unique f f′) (GF-unique g g′)
