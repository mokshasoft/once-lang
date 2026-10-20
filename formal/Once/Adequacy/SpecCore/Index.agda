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

import Once.Lang.Type as LT
import Once.Lang.Type.Grade as LG
import Once.Lang.Context as LC
import Once.Lang.Core.PolyTy as LP
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
pr-fin LG.pure = pr-pure
pr-fin LG.act  = pr-act

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
  ur-[] : UR LC.[] SCx.[]
  ur-∷  : ∀ {n q q′} {Ψ : LC.Usage n} {Φ} → QR q q′ → UR Ψ Φ → UR (q LC.∷ Ψ) (q′ SCx.∷ Φ)

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
  import Once.Lang.Core.PolyTyping S as PT

  data CR {m} : ∀ {n} → PT.PCtx m n → SCx.Ctx m n → Set where
    cr-∅ : CR PT.∅ SCx.∅
    cr-▸ : ∀ {n} {Γ : PT.PCtx m n} {Γ′ A A′ q} → CR Γ Γ′ → PTR A A′ → CR (Γ PT., A ^ q) (Γ′ SCx.▸ A′)
