{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.TermModel.Usage — usages form a module over the
-- semiring `0 ≤ 1 ≤ ω` (`Spec.Grade`, `Spec.Context`): the laws the
-- substitution lemma rearranges usages with.
--
-- A substitution `Φ` gives each variable of the old context the usage of
-- its replacement term in the new one; a term used `Ψ` in the old context is
-- used `Ψ ·ᵐ Φ` (each variable's count times its replacement's usage,
-- summed) in the new one.
------------------------------------------------------------------------

module Once.Metatheory.TermModel.Usage where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; _+q_; _*q_; _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Context
  using (Usage; []; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_)

------------------------------------------------------------------------
-- The semiring
------------------------------------------------------------------------

+q-identityʳ : ∀ q → q +q Zero ≡ q
+q-identityʳ Zero = refl
+q-identityʳ One  = refl
+q-identityʳ Many = refl

+q-comm : ∀ p q → p +q q ≡ q +q p
+q-comm Zero q    = sym (+q-identityʳ q)
+q-comm One  Zero = refl
+q-comm One  One  = refl
+q-comm One  Many = refl
+q-comm Many Zero = refl
+q-comm Many One  = refl
+q-comm Many Many = refl

+q-assoc : ∀ p q r → (p +q q) +q r ≡ p +q (q +q r)
+q-assoc Zero q r = refl
+q-assoc One Zero r = refl
+q-assoc One One Zero = refl
+q-assoc One One One = refl
+q-assoc One One Many = refl
+q-assoc One Many r = refl
+q-assoc Many q r = refl

*q-zeroʳ : ∀ q → q *q Zero ≡ Zero
*q-zeroʳ Zero = refl
*q-zeroʳ One  = refl
*q-zeroʳ Many = refl

*q-identityʳ : ∀ q → q *q One ≡ q
*q-identityʳ Zero = refl
*q-identityʳ One  = refl
*q-identityʳ Many = refl

*q-assoc : ∀ p q r → (p *q q) *q r ≡ p *q (q *q r)
*q-assoc Zero q r = refl
*q-assoc One q r = refl
*q-assoc Many Zero r = refl
*q-assoc Many One r = refl
*q-assoc Many Many Zero = refl
*q-assoc Many Many One = refl
*q-assoc Many Many Many = refl

*q-distribˡ : ∀ p q r → p *q (q +q r) ≡ (p *q q) +q (p *q r)
*q-distribˡ Zero q r = refl
*q-distribˡ One q r = refl
*q-distribˡ Many Zero r = refl
*q-distribˡ Many One Zero = refl
*q-distribˡ Many One One = refl
*q-distribˡ Many One Many = refl
*q-distribˡ Many Many Zero = refl
*q-distribˡ Many Many One = refl
*q-distribˡ Many Many Many = refl

*q-distribʳ : ∀ p q r → (p +q q) *q r ≡ (p *q r) +q (q *q r)
*q-distribʳ Zero q r = refl
*q-distribʳ One Zero r = sym (+q-identityʳ (One *q r))
*q-distribʳ One One Zero = refl
*q-distribʳ One One One = refl
*q-distribʳ One One Many = refl
*q-distribʳ One Many Zero = refl
*q-distribʳ One Many One = refl
*q-distribʳ One Many Many = refl
*q-distribʳ Many Zero Zero = refl
*q-distribʳ Many Zero One = refl
*q-distribʳ Many Zero Many = refl
*q-distribʳ Many One Zero = refl
*q-distribʳ Many One One = refl
*q-distribʳ Many One Many = refl
*q-distribʳ Many Many Zero = refl
*q-distribʳ Many Many One = refl
*q-distribʳ Many Many Many = refl

-- The order is a congruence for both operations.
≤q-+ : ∀ {p p′ q q′} → p ≤q p′ → q ≤q q′ → (p +q q) ≤q (p′ +q q′)
≤q-+ (0≤q {Zero}) (0≤q {Zero}) = 0≤q
≤q-+ (0≤q {Zero}) (0≤q {One}) = 0≤q
≤q-+ (0≤q {Zero}) (0≤q {Many}) = 0≤q
≤q-+ (0≤q {Zero}) 1≤1 = 1≤1
≤q-+ (0≤q {Zero}) 1≤ω = 1≤ω
≤q-+ (0≤q {Zero}) ω≤ω = ω≤ω
≤q-+ (0≤q {One}) (0≤q {Zero}) = 0≤q
≤q-+ (0≤q {One}) (0≤q {One}) = 0≤q
≤q-+ (0≤q {One}) (0≤q {Many}) = 0≤q
≤q-+ (0≤q {One}) 1≤1 = 1≤ω
≤q-+ (0≤q {One}) 1≤ω = 1≤ω
≤q-+ (0≤q {One}) ω≤ω = ω≤ω
≤q-+ (0≤q {Many}) (0≤q {Zero}) = 0≤q
≤q-+ (0≤q {Many}) (0≤q {One}) = 0≤q
≤q-+ (0≤q {Many}) (0≤q {Many}) = 0≤q
≤q-+ (0≤q {Many}) 1≤1 = 1≤ω
≤q-+ (0≤q {Many}) 1≤ω = 1≤ω
≤q-+ (0≤q {Many}) ω≤ω = ω≤ω
≤q-+ 1≤1 (0≤q {Zero}) = 1≤1
≤q-+ 1≤1 (0≤q {One}) = 1≤ω
≤q-+ 1≤1 (0≤q {Many}) = 1≤ω
≤q-+ 1≤1 1≤1 = ω≤ω
≤q-+ 1≤1 1≤ω = ω≤ω
≤q-+ 1≤1 ω≤ω = ω≤ω
≤q-+ 1≤ω (0≤q {Zero}) = 1≤ω
≤q-+ 1≤ω (0≤q {One}) = 1≤ω
≤q-+ 1≤ω (0≤q {Many}) = 1≤ω
≤q-+ 1≤ω 1≤1 = ω≤ω
≤q-+ 1≤ω 1≤ω = ω≤ω
≤q-+ 1≤ω ω≤ω = ω≤ω
≤q-+ ω≤ω (0≤q {Zero}) = ω≤ω
≤q-+ ω≤ω (0≤q {One}) = ω≤ω
≤q-+ ω≤ω (0≤q {Many}) = ω≤ω
≤q-+ ω≤ω 1≤1 = ω≤ω
≤q-+ ω≤ω 1≤ω = ω≤ω
≤q-+ ω≤ω ω≤ω = ω≤ω

≤q-*ˡ : ∀ {p p′} r → p ≤q p′ → (p *q r) ≤q (p′ *q r)
≤q-*ˡ Zero (0≤q {Zero}) = 0≤q
≤q-*ˡ Zero (0≤q {One}) = 0≤q
≤q-*ˡ Zero (0≤q {Many}) = 0≤q
≤q-*ˡ Zero 1≤1 = 0≤q
≤q-*ˡ Zero 1≤ω = 0≤q
≤q-*ˡ Zero ω≤ω = 0≤q
≤q-*ˡ One (0≤q {Zero}) = 0≤q
≤q-*ˡ One (0≤q {One}) = 0≤q
≤q-*ˡ One (0≤q {Many}) = 0≤q
≤q-*ˡ One 1≤1 = 1≤1
≤q-*ˡ One 1≤ω = 1≤ω
≤q-*ˡ One ω≤ω = ω≤ω
≤q-*ˡ Many (0≤q {Zero}) = 0≤q
≤q-*ˡ Many (0≤q {One}) = 0≤q
≤q-*ˡ Many (0≤q {Many}) = 0≤q
≤q-*ˡ Many 1≤1 = ω≤ω
≤q-*ˡ Many 1≤ω = ω≤ω
≤q-*ˡ Many ω≤ω = ω≤ω

≤q-*ʳ : ∀ r {p p′} → p ≤q p′ → (r *q p) ≤q (r *q p′)
≤q-*ʳ Zero (0≤q {Zero}) = 0≤q
≤q-*ʳ Zero (0≤q {One}) = 0≤q
≤q-*ʳ Zero (0≤q {Many}) = 0≤q
≤q-*ʳ Zero 1≤1 = 0≤q
≤q-*ʳ Zero 1≤ω = 0≤q
≤q-*ʳ Zero ω≤ω = 0≤q
≤q-*ʳ One (0≤q {Zero}) = 0≤q
≤q-*ʳ One (0≤q {One}) = 0≤q
≤q-*ʳ One (0≤q {Many}) = 0≤q
≤q-*ʳ One 1≤1 = 1≤1
≤q-*ʳ One 1≤ω = 1≤ω
≤q-*ʳ One ω≤ω = ω≤ω
≤q-*ʳ Many (0≤q {Zero}) = 0≤q
≤q-*ʳ Many (0≤q {One}) = 0≤q
≤q-*ʳ Many (0≤q {Many}) = 0≤q
≤q-*ʳ Many 1≤1 = ω≤ω
≤q-*ʳ Many 1≤ω = ω≤ω
≤q-*ʳ Many ω≤ω = ω≤ω

≤q-refl : ∀ q → q ≤q q
≤q-refl Zero = 0≤q
≤q-refl One = 1≤1
≤q-refl Many = ω≤ω


------------------------------------------------------------------------
-- Usages, pointwise
------------------------------------------------------------------------

+ᵘ-identityˡ : ∀ {n} (Ψ : Usage n) → zeroUsage +ᵘ Ψ ≡ Ψ
+ᵘ-identityˡ []      = refl
+ᵘ-identityˡ (q ∷ Ψ) = cong (q ∷_) (+ᵘ-identityˡ Ψ)

+ᵘ-identityʳ : ∀ {n} (Ψ : Usage n) → Ψ +ᵘ zeroUsage ≡ Ψ
+ᵘ-identityʳ []      = refl
+ᵘ-identityʳ (q ∷ Ψ) = cong₂ _∷_ (+q-identityʳ q) (+ᵘ-identityʳ Ψ)

+ᵘ-comm : ∀ {n} (Ψ Ψ′ : Usage n) → Ψ +ᵘ Ψ′ ≡ Ψ′ +ᵘ Ψ
+ᵘ-comm []      []        = refl
+ᵘ-comm (p ∷ Ψ) (q ∷ Ψ′) = cong₂ _∷_ (+q-comm p q) (+ᵘ-comm Ψ Ψ′)

+ᵘ-assoc : ∀ {n} (Ψ₁ Ψ₂ Ψ₃ : Usage n) → (Ψ₁ +ᵘ Ψ₂) +ᵘ Ψ₃ ≡ Ψ₁ +ᵘ (Ψ₂ +ᵘ Ψ₃)
+ᵘ-assoc []       []       []       = refl
+ᵘ-assoc (p ∷ Ψ₁) (q ∷ Ψ₂) (r ∷ Ψ₃) = cong₂ _∷_ (+q-assoc p q r) (+ᵘ-assoc Ψ₁ Ψ₂ Ψ₃)

-- Swapping the middle of two sums.
+ᵘ-interchange : ∀ {n} (a b c d : Usage n) → (a +ᵘ b) +ᵘ (c +ᵘ d) ≡ (a +ᵘ c) +ᵘ (b +ᵘ d)
+ᵘ-interchange a b c d =
  trans (+ᵘ-assoc a b (c +ᵘ d))
    (trans (cong (a +ᵘ_) (trans (sym (+ᵘ-assoc b c d)) (trans (cong (_+ᵘ d) (+ᵘ-comm b c)) (+ᵘ-assoc c b d))))
           (sym (+ᵘ-assoc a c (b +ᵘ d))))

*ᵘ-zero : ∀ {n} q → q *ᵘ zeroUsage {n} ≡ zeroUsage
*ᵘ-zero {zero}  q = refl
*ᵘ-zero {suc n} q = cong₂ _∷_ (*q-zeroʳ q) (*ᵘ-zero q)

Zero*ᵘ : ∀ {n} (Ψ : Usage n) → Zero *ᵘ Ψ ≡ zeroUsage
Zero*ᵘ []      = refl
Zero*ᵘ (q ∷ Ψ) = cong (Zero ∷_) (Zero*ᵘ Ψ)

One*ᵘ : ∀ {n} (Ψ : Usage n) → One *ᵘ Ψ ≡ Ψ
One*ᵘ []      = refl
One*ᵘ (q ∷ Ψ) = cong (q ∷_) (One*ᵘ Ψ)

*ᵘ-assoc : ∀ {n} p q (Ψ : Usage n) → (p *q q) *ᵘ Ψ ≡ p *ᵘ (q *ᵘ Ψ)
*ᵘ-assoc p q []      = refl
*ᵘ-assoc p q (r ∷ Ψ) = cong₂ _∷_ (*q-assoc p q r) (*ᵘ-assoc p q Ψ)

*ᵘ-distribˡ : ∀ {n} q (Ψ Ψ′ : Usage n) → q *ᵘ (Ψ +ᵘ Ψ′) ≡ q *ᵘ Ψ +ᵘ q *ᵘ Ψ′
*ᵘ-distribˡ q []      []        = refl
*ᵘ-distribˡ q (a ∷ Ψ) (b ∷ Ψ′) = cong₂ _∷_ (*q-distribˡ q a b) (*ᵘ-distribˡ q Ψ Ψ′)

*ᵘ-distribʳ : ∀ {n} p q (Ψ : Usage n) → (p +q q) *ᵘ Ψ ≡ p *ᵘ Ψ +ᵘ q *ᵘ Ψ
*ᵘ-distribʳ p q []      = refl
*ᵘ-distribʳ p q (r ∷ Ψ) = cong₂ _∷_ (*q-distribʳ p q r) (*ᵘ-distribʳ p q Ψ)

⊑ᵘ-refl : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ Ψ
⊑ᵘ-refl []      = []
⊑ᵘ-refl (q ∷ Ψ) = ≤q-refl q ⊑∷ ⊑ᵘ-refl Ψ

⊑ᵘ-+ : ∀ {n} {Ψ₁ Ψ₁′ Ψ₂ Ψ₂′ : Usage n} → Ψ₁ ⊑ᵘ Ψ₁′ → Ψ₂ ⊑ᵘ Ψ₂′ → (Ψ₁ +ᵘ Ψ₂) ⊑ᵘ (Ψ₁′ +ᵘ Ψ₂′)
⊑ᵘ-+ []        []        = []
⊑ᵘ-+ (a ⊑∷ as) (b ⊑∷ bs) = ≤q-+ a b ⊑∷ ⊑ᵘ-+ as bs

⊑ᵘ-*ʳ : ∀ {n} q {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → (q *ᵘ Ψ) ⊑ᵘ (q *ᵘ Ψ′)
⊑ᵘ-*ʳ q []        = []
⊑ᵘ-*ʳ q (a ⊑∷ as) = ≤q-*ʳ q a ⊑∷ ⊑ᵘ-*ʳ q as

⊑ᵘ-*ˡ : ∀ {n} {p p′} (Ψ : Usage n) → p ≤q p′ → (p *ᵘ Ψ) ⊑ᵘ (p′ *ᵘ Ψ)
⊑ᵘ-*ˡ []      a = []
⊑ᵘ-*ˡ (r ∷ Ψ) a = ≤q-*ˡ r a ⊑∷ ⊑ᵘ-*ˡ Ψ a

⊑ᵘ-≡ : ∀ {n} {Ψ Ψ′ : Usage n} → Ψ ≡ Ψ′ → Ψ ⊑ᵘ Ψ′
⊑ᵘ-≡ {Ψ = Ψ} refl = ⊑ᵘ-refl Ψ

------------------------------------------------------------------------
-- A usage, through a substitution
------------------------------------------------------------------------

_·ᵐ_ : ∀ {n n′} → Usage n′ → (Fin n′ → Usage n) → Usage n
[]      ·ᵐ Φ = zeroUsage
(q ∷ Ψ) ·ᵐ Φ = q *ᵘ Φ zero +ᵘ Ψ ·ᵐ (λ i → Φ (suc i))

infixl 65 _·ᵐ_

·ᵐ-zero : ∀ {n n′} (Φ : Fin n′ → Usage n) → zeroUsage ·ᵐ Φ ≡ zeroUsage
·ᵐ-zero {n′ = 0}     Φ = refl
·ᵐ-zero {n′ = suc k} Φ = trans (cong (λ z → z +ᵘ (zeroUsage ·ᵐ (λ i → Φ (suc i)))) (Zero*ᵘ (Φ zero))) (trans (+ᵘ-identityˡ _) (·ᵐ-zero (λ i → Φ (suc i))))

·ᵐ-+ : ∀ {n n′} (Ψ Ψ′ : Usage n′) (Φ : Fin n′ → Usage n) → (Ψ +ᵘ Ψ′) ·ᵐ Φ ≡ Ψ ·ᵐ Φ +ᵘ Ψ′ ·ᵐ Φ
·ᵐ-+ []      []        Φ = sym (+ᵘ-identityˡ zeroUsage)
·ᵐ-+ (p ∷ Ψ) (q ∷ Ψ′) Φ =
  trans (cong₂ _+ᵘ_ (*ᵘ-distribʳ p q (Φ zero)) (·ᵐ-+ Ψ Ψ′ (λ i → Φ (suc i))))
        (+ᵘ-interchange (p *ᵘ Φ zero) (q *ᵘ Φ zero) (Ψ ·ᵐ _) (Ψ′ ·ᵐ _))

·ᵐ-* : ∀ {n n′} q (Ψ : Usage n′) (Φ : Fin n′ → Usage n) → (q *ᵘ Ψ) ·ᵐ Φ ≡ q *ᵘ (Ψ ·ᵐ Φ)
·ᵐ-* q []      Φ = sym (*ᵘ-zero q)
·ᵐ-* q (p ∷ Ψ) Φ =
  trans (cong₂ _+ᵘ_ (*ᵘ-assoc q p (Φ zero)) (·ᵐ-* q Ψ (λ i → Φ (suc i))))
        (sym (*ᵘ-distribˡ q (p *ᵘ Φ zero) (Ψ ·ᵐ _)))

·ᵐ-single : ∀ {n n′} (i : Fin n′) (Φ : Fin n′ → Usage n) → singleUse i One ·ᵐ Φ ≡ Φ i
·ᵐ-single zero    Φ = trans (cong₂ _+ᵘ_ (One*ᵘ (Φ zero)) (·ᵐ-zero (λ i → Φ (suc i)))) (+ᵘ-identityʳ (Φ zero))
·ᵐ-single (suc i) Φ = trans (cong (λ z → z +ᵘ (singleUse i One ·ᵐ (λ j → Φ (suc j)))) (Zero*ᵘ (Φ zero))) (trans (+ᵘ-identityˡ _) (·ᵐ-single i (λ j → Φ (suc j))))

·ᵐ-mono : ∀ {n n′} {Ψ Ψ′ : Usage n′} (Φ : Fin n′ → Usage n) → Ψ ⊑ᵘ Ψ′ → Ψ ·ᵐ Φ ⊑ᵘ Ψ′ ·ᵐ Φ
·ᵐ-mono Φ []        = ⊑ᵘ-refl zeroUsage
·ᵐ-mono Φ (a ⊑∷ as) = ⊑ᵘ-+ (⊑ᵘ-*ˡ (Φ zero) a) (·ᵐ-mono (λ i → Φ (suc i)) as)

------------------------------------------------------------------------
-- The order facts (moved from `Spec.Context`, D335): a part of a term uses
-- at most what the whole does
------------------------------------------------------------------------

private
  ≤q-+ˡ : ∀ p q → p ≤q (p +q q)
  ≤q-+ˡ Zero q    = 0≤q
  ≤q-+ˡ One Zero  = 1≤1
  ≤q-+ˡ One One   = 1≤ω
  ≤q-+ˡ One Many  = 1≤ω
  ≤q-+ˡ Many q    = ω≤ω

  ≤q-+ʳ : ∀ p q → q ≤q (p +q q)
  ≤q-+ʳ Zero Zero = 0≤q
  ≤q-+ʳ Zero One  = 1≤1
  ≤q-+ʳ Zero Many = ω≤ω
  ≤q-+ʳ One Zero  = 0≤q
  ≤q-+ʳ One One   = 1≤ω
  ≤q-+ʳ One Many  = ω≤ω
  ≤q-+ʳ Many Zero = 0≤q
  ≤q-+ʳ Many One  = 1≤ω
  ≤q-+ʳ Many Many = ω≤ω

  ≤q-trans : ∀ {a b c} → a ≤q b → b ≤q c → a ≤q c
  ≤q-trans 0≤q _   = 0≤q
  ≤q-trans 1≤1 b≤c = b≤c
  ≤q-trans 1≤ω ω≤ω = 1≤ω
  ≤q-trans ω≤ω ω≤ω = ω≤ω

  ≤q-*One : ∀ q → q ≤q (One *q q)
  ≤q-*One Zero = 0≤q
  ≤q-*One One  = 1≤1
  ≤q-*One Many = ω≤ω

  ≤q-*Many : ∀ q → q ≤q (Many *q q)
  ≤q-*Many Zero = 0≤q
  ≤q-*Many One  = 1≤ω
  ≤q-*Many Many = ω≤ω

⊑ᵘ-+ˡ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₁ ⊑ᵘ Ψ₁ +ᵘ Ψ₂
⊑ᵘ-+ˡ []       []       = []
⊑ᵘ-+ˡ (p ∷ Ψ₁) (q ∷ Ψ₂) = ≤q-+ˡ p q ⊑∷ ⊑ᵘ-+ˡ Ψ₁ Ψ₂

⊑ᵘ-+ʳ : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₂ ⊑ᵘ Ψ₁ +ᵘ Ψ₂
⊑ᵘ-+ʳ []       []       = []
⊑ᵘ-+ʳ (p ∷ Ψ₁) (q ∷ Ψ₂) = ≤q-+ʳ p q ⊑∷ ⊑ᵘ-+ʳ Ψ₁ Ψ₂

⊑ᵘ-trans : ∀ {n} {Ψ₁ Ψ₂ Ψ₃ : Usage n} → Ψ₁ ⊑ᵘ Ψ₂ → Ψ₂ ⊑ᵘ Ψ₃ → Ψ₁ ⊑ᵘ Ψ₃
⊑ᵘ-trans []       []       = []
⊑ᵘ-trans (a ⊑∷ as) (b ⊑∷ bs) = ≤q-trans a b ⊑∷ ⊑ᵘ-trans as bs

⊑ᵘ-*One : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ One *ᵘ Ψ
⊑ᵘ-*One []      = []
⊑ᵘ-*One (q ∷ Ψ) = ≤q-*One q ⊑∷ ⊑ᵘ-*One Ψ

⊑ᵘ-*Many : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ Many *ᵘ Ψ
⊑ᵘ-*Many []      = []
⊑ᵘ-*Many (q ∷ Ψ) = ≤q-*Many q ⊑∷ ⊑ᵘ-*Many Ψ
