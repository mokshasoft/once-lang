-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Index — the graphs of the translations of grades,
-- usages, types and contexts (plan 0.121 §3.5).
--
-- Each translation (`πS`, `uS`, `ptyS`, `pctxS`, and ground types) is a
-- function; its graph, a relation built constructor by constructor, is what
-- the meaning relation is indexed by. Where the two judgments' indices are
-- equal only propositionally (an instance, a functor applied, a grade
-- combined), the graph still relates them, by a lemma rather than a rewrite.
------------------------------------------------------------------------

module Once.Adequacy.SpecCore.Index where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Spec.Grade as LG
import Once.Internal.Context as LC
import Once.Internal.Core.PolyTy as LP
import Once.Spec.Type as ST
import Once.Spec.Grade as SG
import Once.Spec.Context as SCx
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS)

------------------------------------------------------------------------
-- Grades and usages
------------------------------------------------------------------------

data PR : LG.Purity → SG.Purity → Set where
  pr-pure : PR LG.pure SG.pure
  pr-act  : PR LG.act  SG.act
  pr-eff  : PR LG.eff  SG.eff

pr : ∀ π → PR π (πS π)
pr LG.pure = pr-pure
pr LG.act  = pr-act
pr LG.eff  = pr-eff

pr-fin : ∀ φ → PR (LG.fin φ) (SG.fin (φS φ))
pr-fin LG.pureᶠ = pr-pure
pr-fin LG.actᶠ  = pr-act

pr-· : ∀ {π₁ π₁′ π₂ π₂′} → PR π₁ π₁′ → PR π₂ π₂′ → PR (π₁ LG.·p π₂) (π₁′ SG.·p π₂′)
pr-· pr-pure p       = p
pr-· pr-act  pr-pure = pr-act
pr-· pr-act  pr-act  = pr-act
pr-· pr-act  pr-eff  = pr-eff
pr-· pr-eff  p       = pr-eff

pr-pos : ∀ q {π π′} → PR π π′ → PR (LG.positionGrade q π) (SG.positionGrade (qS q) π′)
pr-pos LG.Zero p = pr-pure
pr-pos LG.One  p = p
pr-pos LG.Many p = p

data QR : LG.Quantity → SG.Quantity → Set where
  qr-zero : QR LG.Zero SG.Zero
  qr-one  : QR LG.One  SG.One
  qr-many : QR LG.Many SG.Many

qr : ∀ q → QR q (qS q)
qr LG.Zero = qr-zero
qr LG.One  = qr-one
qr LG.Many = qr-many

data UR : ∀ {n} → LC.Usage n → SCx.Usage n → Set where
  ur-[] : UR SCx.[] SCx.[]
  ur-∷  : ∀ {n q q′} {Ψ : LC.Usage n} {Φ} → QR q q′ → UR Ψ Φ → UR (q SCx.∷ Ψ) (q′ SCx.∷ Φ)

------------------------------------------------------------------------
-- Open types and contexts
------------------------------------------------------------------------

mutual
  data PTR {m} : LP.Ty m → ST.Ty m → Set where
    p-var   : ∀ {i} → PTR (LP.var i) (ST.var i)
    p-unit  : PTR LP.Unit ST.Unit
    p-void  : PTR LP.Void ST.Void
    p-int   : PTR LP.Int ST.Int
    p-float : PTR LP.Float ST.Float
    p-*     : ∀ {A A′ B B′} → PTR A A′ → PTR B B′ → PTR (A LP.* B) (A′ ST.* B′)
    p-+     : ∀ {A A′ B B′} → PTR A A′ → PTR B B′ → PTR (A LP.+ B) (A′ ST.+ B′)
    p-⇒     : ∀ {A A′ B B′ q π} → PTR A A′ → PTR B B′
            → PTR (A LP.⇒[ LG.mk-kind q π ] B) (A′ ST.⇒[ SG.mk-kind (qS q) (πS π) ] B′)
    p-μ     : ∀ {F F′} → PFR F F′ → PTR (LP.μ-type F) (ST.μ F′)
    p-ν     : ∀ {F F′ φ} → PFR F F′ → PTR (LP.ν-type F φ) (ST.ν F′ (φS φ))
    p-rigid : ∀ {k i} → PTR (LP.rigid k i) ST.Unit

  data PFR {m} : LP.Fun m → ST.Fun m → Set where
    p-K  : ∀ {A A′} → PTR A A′ → PFR (LP.K A) (ST.K A′)
    p-Id : PFR LP.Id ST.Id
    p-⊕  : ∀ {F F′ G G′} → PFR F F′ → PFR G G′ → PFR (F LP.⊕ G) (F′ ST.⊕ G′)
    p-⊗  : ∀ {F F′ G G′} → PFR F F′ → PFR G G′ → PFR (F LP.⊗ G) (F′ ST.⊗ G′)

PTR-⟦⟧ : ∀ {m} {F F′} {X : LP.Ty m} {X′ : ST.Ty m} → PFR F F′ → PTR X X′ → PTR (LP.⟦ F ⟧F X) (ST.⟦ F′ ⟧F X′)
PTR-⟦⟧ (p-K a)   x = a
PTR-⟦⟧ p-Id      x = x
PTR-⟦⟧ (p-⊕ f g) x = p-+ (PTR-⟦⟧ f x) (PTR-⟦⟧ g x)
PTR-⟦⟧ (p-⊗ f g) x = p-* (PTR-⟦⟧ f x) (PTR-⟦⟧ g x)

------------------------------------------------------------------------
-- Ground types
------------------------------------------------------------------------

mutual
  data GR : LT.Type → ST.Type → Set where
    g-unit  : GR LT.Unit ST.Unit
    g-void  : GR LT.Void ST.Void
    g-int   : GR LT.Int ST.Int
    g-float : GR LT.Float ST.Float
    g-*     : ∀ {A A′ B B′} → GR A A′ → GR B B′ → GR (A LT.* B) (A′ ST.* B′)
    g-+     : ∀ {A A′ B B′} → GR A A′ → GR B B′ → GR (A LT.+ B) (A′ ST.+ B′)
    g-⇒     : ∀ {A A′ B B′ q π} → GR A A′ → GR B B′
            → GR (A LT.⇒[ LG.mk-kind q π ] B) (A′ ST.⇒[ SG.mk-kind (qS q) (πS π) ] B′)
    g-μ     : ∀ {F F′} → GF F F′ → GR (LT.μ-type F) (ST.μ F′)
    g-ν     : ∀ {F F′ φ} → GF F F′ → GR (LT.ν-type F φ) (ST.ν F′ (φS φ))
    g-rigid : ∀ {k i} → GR (LT.rigid k i) ST.Unit

  data GF : LT.Functor → ST.Fun 0 → Set where
    g-K  : ∀ {A A′} → GR A A′ → GF (LT.K A) (ST.K A′)
    g-Id : GF LT.Id ST.Id
    g-⊕  : ∀ {F F′ G G′} → GF F F′ → GF G G′ → GF (F LT.⊕ G) (F′ ST.⊕ G′)
    g-⊗  : ∀ {F F′ G G′} → GF F F′ → GF G G′ → GF (F LT.⊗ G) (F′ ST.⊗ G′)

-- An instance of related types, at related instances.
InstG : ∀ {m} → LP.GSub m → ST.TySub m 0 → Set
InstG σ σ′ = ∀ i → GR (σ i) (σ′ i)

mutual
  GR-inst : ∀ {m} {A : LP.Ty m} {A′ σ σ′} → PTR A A′ → InstG σ σ′ → GR (A LP.⟪ σ ⟫) (A′ ST.⟨ σ′ ⟩)
  GR-inst {A = LP.var i} p-var g = g i
  GR-inst p-unit  g = g-unit
  GR-inst p-void  g = g-void
  GR-inst p-int   g = g-int
  GR-inst p-float g = g-float
  GR-inst (p-* a b) g = g-* (GR-inst a g) (GR-inst b g)
  GR-inst (p-+ a b) g = g-+ (GR-inst a g) (GR-inst b g)
  GR-inst (p-⇒ a b) g = g-⇒ (GR-inst a g) (GR-inst b g)
  GR-inst (p-μ f)   g = g-μ (GF-inst f g)
  GR-inst (p-ν f)   g = g-ν (GF-inst f g)
  GR-inst p-rigid   g = g-rigid

  GF-inst : ∀ {m} {F : LP.Fun m} {F′ σ σ′} → PFR F F′ → InstG σ σ′ → GF (F LP.⟪ σ ⟫F) (F′ ST.⟨ σ′ ⟩F)
  GF-inst (p-K a)   g = g-K (GR-inst a g)
  GF-inst p-Id      g = g-Id
  GF-inst (p-⊕ f h) g = g-⊕ (GF-inst f g) (GF-inst h g)
  GF-inst (p-⊗ f h) g = g-⊗ (GF-inst f g) (GF-inst h g)

------------------------------------------------------------------------
-- Contexts (as the compiler's polymorphic contexts carry them)
------------------------------------------------------------------------

module _ {Fs} {s} (S : LP.Sig Fs s) where
  import Once.Internal.Core.PolyTyping S as PT

  data CR {m} : ∀ {n} → PT.PCtx m n → SCx.Ctx m n → Set where
    cr-∅ : CR PT.∅ SCx.∅
    cr-▸ : ∀ {n} {Γ : PT.PCtx m n} {Γ′ A A′ q} → CR Γ Γ′ → PTR A A′ → CR (Γ PT., A ^ q) (Γ′ SCx.▸ A′)

------------------------------------------------------------------------
-- The canonical graphs, and each graph has one proof
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Adequacy.SpecCore.Context using (uS)
open import Once.Adequacy.SpecCore.Schema using (ptyS; pfunS)

ur : ∀ {n} (Ψ : LC.Usage n) → UR Ψ (uS Ψ)
ur SCx.[]      = ur-[]
ur (q SCx.∷ Ψ) = ur-∷ (qr q) (ur Ψ)

mutual
  ptr : ∀ {m} (A : LP.Ty m) → PTR A (ptyS A)
  ptr (LP.var i)       = p-var
  ptr LP.Unit          = p-unit
  ptr LP.Void          = p-void
  ptr LP.Int           = p-int
  ptr LP.Float         = p-float
  ptr (A LP.* B)       = p-* (ptr A) (ptr B)
  ptr (A LP.+ B)       = p-+ (ptr A) (ptr B)
  ptr (A LP.⇒[ LG.mk-kind q π ] B) = p-⇒ (ptr A) (ptr B)
  ptr (LP.μ-type F)    = p-μ (pfr F)
  ptr (LP.ν-type F φ)  = p-ν (pfr F)
  ptr (LP.rigid k i)   = p-rigid

  pfr : ∀ {m} (F : LP.Fun m) → PFR F (pfunS F)
  pfr (LP.K A)    = p-K (ptr A)
  pfr LP.Id       = p-Id
  pfr (F LP.⊕ G)  = p-⊕ (pfr F) (pfr G)
  pfr (F LP.⊗ G)  = p-⊗ (pfr F) (pfr G)

qr-+ : ∀ {p p′ q q′} → QR p p′ → QR q q′ → QR (p LG.+q q) (p′ SG.+q q′)
qr-+ qr-zero b       = b
qr-+ qr-one  qr-zero = qr-one
qr-+ qr-one  qr-one  = qr-many
qr-+ qr-one  qr-many = qr-many
qr-+ qr-many b       = qr-many

qr-* : ∀ {p p′ q q′} → QR p p′ → QR q q′ → QR (p LG.*q q) (p′ SG.*q q′)
qr-* qr-zero b       = qr-zero
qr-* qr-one  qr-zero = qr-zero
qr-* qr-one  qr-one  = qr-one
qr-* qr-one  qr-many = qr-many
qr-* qr-many qr-zero = qr-zero
qr-* qr-many qr-one  = qr-many
qr-* qr-many qr-many = qr-many

ur-+ : ∀ {n} {Ψ₁ Ψ₂ : LC.Usage n} {Φ₁ Φ₂} → UR Ψ₁ Φ₁ → UR Ψ₂ Φ₂ → UR (Ψ₁ LC.+ᵘ Ψ₂) (Φ₁ SCx.+ᵘ Φ₂)
ur-+ ur-[]        ur-[]        = ur-[]
ur-+ (ur-∷ a u)  (ur-∷ b v)   = ur-∷ (qr-+ a b) (ur-+ u v)

ur-* : ∀ {n q q′} {Ψ : LC.Usage n} {Φ} → QR q q′ → UR Ψ Φ → UR (q LC.*ᵘ Ψ) (q′ SCx.*ᵘ Φ)
ur-* a ur-[]       = ur-[]
ur-* a (ur-∷ b u)  = ur-∷ (qr-* a b) (ur-* a u)

PR-unique : ∀ {π π′} (p p′ : PR π π′) → p ≡ p′
PR-unique pr-pure pr-pure = refl
PR-unique pr-act  pr-act  = refl
PR-unique pr-eff  pr-eff  = refl

QR-unique : ∀ {q q′} (a b : QR q q′) → a ≡ b
QR-unique qr-zero qr-zero = refl
QR-unique qr-one  qr-one  = refl
QR-unique qr-many qr-many = refl

UR-unique : ∀ {n} {Ψ : LC.Usage n} {Φ} (u v : UR Ψ Φ) → u ≡ v
UR-unique ur-[]      ur-[]      = refl
UR-unique (ur-∷ a u) (ur-∷ b v) = cong₂ ur-∷ (QR-unique a b) (UR-unique u v)

mutual
  PTR-unique : ∀ {m} {A : LP.Ty m} {A′} (a b : PTR A A′) → a ≡ b
  PTR-unique p-var     p-var       = refl
  PTR-unique p-unit    p-unit      = refl
  PTR-unique p-void    p-void      = refl
  PTR-unique p-int     p-int       = refl
  PTR-unique p-float   p-float     = refl
  PTR-unique (p-* a b) (p-* a′ b′) = cong₂ p-* (PTR-unique a a′) (PTR-unique b b′)
  PTR-unique (p-+ a b) (p-+ a′ b′) = cong₂ p-+ (PTR-unique a a′) (PTR-unique b b′)
  PTR-unique (p-⇒ a b) (p-⇒ a′ b′) = cong₂ p-⇒ (PTR-unique a a′) (PTR-unique b b′)
  PTR-unique (p-μ f)   (p-μ f′)    = cong p-μ (PFR-unique f f′)
  PTR-unique (p-ν f)   (p-ν f′)    = cong p-ν (PFR-unique f f′)
  PTR-unique p-rigid   p-rigid     = refl

  PFR-unique : ∀ {m} {F : LP.Fun m} {F′} (f g : PFR F F′) → f ≡ g
  PFR-unique (p-K a)   (p-K b)     = cong p-K (PTR-unique a b)
  PFR-unique p-Id      p-Id        = refl
  PFR-unique (p-⊕ f g) (p-⊕ f′ g′) = cong₂ p-⊕ (PFR-unique f f′) (PFR-unique g g′)
  PFR-unique (p-⊗ f g) (p-⊗ f′ g′) = cong₂ p-⊗ (PFR-unique f f′) (PFR-unique g g′)

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
  GR-unique g-rigid   g-rigid     = refl

  GF-unique : ∀ {F F′} (f g : GF F F′) → f ≡ g
  GF-unique (g-K a)   (g-K b)     = cong g-K (GR-unique a b)
  GF-unique g-Id      g-Id        = refl
  GF-unique (g-⊕ f g) (g-⊕ f′ g′) = cong₂ g-⊕ (GF-unique f f′) (GF-unique g g′)
  GF-unique (g-⊗ f g) (g-⊗ f′ g′) = cong₂ g-⊗ (GF-unique f f′) (GF-unique g g′)

------------------------------------------------------------------------
-- Definitions' instances
------------------------------------------------------------------------

import Once.Spec.Core.Syntax as SC
open import Once.Adequacy.SpecCore.Schema using (defsS; castSub)

-- An instance of the `d`-th definition, on both sides.
InstD : ∀ {Fs s₀} (S₀ : LP.Sig Fs s₀) (d : Fin s₀) → LP.GSub (LP.Schema.arity (S₀ LP.!! d))
      → ST.TySub (SC.Schema.arity (defsS S₀ SC.!! d)) 0 → Set
InstD (S₀ LP.▷ sc) zero    τ τ′ = InstG τ τ′
InstD (S₀ LP.▷ sc) (suc d) τ τ′ = InstD S₀ d τ τ′

GR-def : ∀ {Fs s₀} (S₀ : LP.Sig Fs s₀) (d : Fin s₀) {τ τ′} → InstD S₀ d τ τ′
       → GR (LP.Schema.type (S₀ LP.!! d) LP.⟪ τ ⟫) (SC.Schema.type (defsS S₀ SC.!! d) ST.⟨ τ′ ⟩)
GR-def (S₀ LP.▷ sc) zero    i = GR-inst (ptr (LP.Schema.type sc)) i
GR-def (S₀ LP.▷ sc) (suc d) i = GR-def S₀ d i

-- A reference's instance, instantiated on both sides.
inst-ref : ∀ {Fs s₀ m} (S₀ : LP.Sig Fs s₀) (d : Fin s₀) (τ : LP.Sub (LP.Schema.arity (S₀ LP.!! d)) m)
           {σ σ′} → InstG σ σ′
         → InstD S₀ d (λ i → τ i LP.⟪ σ ⟫) (λ i → castSub S₀ d (λ j → ptyS (τ j)) i ST.⟨ σ′ ⟩)
inst-ref (S₀ LP.▷ sc) zero    τ g i = GR-inst (ptr (τ i)) g
inst-ref (S₀ LP.▷ sc) (suc d) τ g   = inst-ref S₀ d τ g

