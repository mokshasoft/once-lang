-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.GradeMatrix — plan 0.102 phase B (D276): HOW GRADES SEE
-- COMPOSITION.
--
-- A substitution `σ : Sub n m` comes with a GRADE MATRIX `Φ : Fin n → Usage m`
-- (row `i` = what `σ i` uses). A term used at `Ψ` then uses `Ψ ⋆ Φ` after
-- substitution: each variable's grade scales the row of what replaced it.
-- `_⋆ Φ` is a MONOTONE LINEAR MAP of usage vectors — it preserves `+ᵘ`, `*ᵘ`,
-- `zeroUsage` and `⊑ᵘ`, and a single use selects a row. These are exactly the
-- laws the typing substitution lemma consumes, one per rule shape.
--
-- The quantity laws are finite and proved by enumeration (generated, each
-- clause checked against the operations' tables).
------------------------------------------------------------------------

module Once.Surface.GradeMatrix where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Type using (Quantity; Zero; One; Many; _+q_; _*q_)
open import Once.Surface.Context
  using (Usage; []; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; ⊑[]; _⊑∷_;
         _≤q'_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.Surface.Properties using (+ᵘ-comm; +ᵘ-assoc; +ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-zeroˡ; *ᵘ-zeroʳ; *ᵘ-identityˡ; +q-identityʳ)

------------------------------------------------------------------------
-- The quantity semiring's remaining laws, and its order's monotonicity
------------------------------------------------------------------------

*q-assoc : ∀ (a b c : Quantity) → (a *q b) *q c ≡ a *q (b *q c)
*q-assoc Zero Zero Zero = refl
*q-assoc Zero Zero One = refl
*q-assoc Zero Zero Many = refl
*q-assoc Zero One Zero = refl
*q-assoc Zero One One = refl
*q-assoc Zero One Many = refl
*q-assoc Zero Many Zero = refl
*q-assoc Zero Many One = refl
*q-assoc Zero Many Many = refl
*q-assoc One Zero Zero = refl
*q-assoc One Zero One = refl
*q-assoc One Zero Many = refl
*q-assoc One One Zero = refl
*q-assoc One One One = refl
*q-assoc One One Many = refl
*q-assoc One Many Zero = refl
*q-assoc One Many One = refl
*q-assoc One Many Many = refl
*q-assoc Many Zero Zero = refl
*q-assoc Many Zero One = refl
*q-assoc Many Zero Many = refl
*q-assoc Many One Zero = refl
*q-assoc Many One One = refl
*q-assoc Many One Many = refl
*q-assoc Many Many Zero = refl
*q-assoc Many Many One = refl
*q-assoc Many Many Many = refl

*q-distribˡ : ∀ (a b c : Quantity) → a *q (b +q c) ≡ (a *q b) +q (a *q c)
*q-distribˡ Zero Zero Zero = refl
*q-distribˡ Zero Zero One = refl
*q-distribˡ Zero Zero Many = refl
*q-distribˡ Zero One Zero = refl
*q-distribˡ Zero One One = refl
*q-distribˡ Zero One Many = refl
*q-distribˡ Zero Many Zero = refl
*q-distribˡ Zero Many One = refl
*q-distribˡ Zero Many Many = refl
*q-distribˡ One Zero Zero = refl
*q-distribˡ One Zero One = refl
*q-distribˡ One Zero Many = refl
*q-distribˡ One One Zero = refl
*q-distribˡ One One One = refl
*q-distribˡ One One Many = refl
*q-distribˡ One Many Zero = refl
*q-distribˡ One Many One = refl
*q-distribˡ One Many Many = refl
*q-distribˡ Many Zero Zero = refl
*q-distribˡ Many Zero One = refl
*q-distribˡ Many Zero Many = refl
*q-distribˡ Many One Zero = refl
*q-distribˡ Many One One = refl
*q-distribˡ Many One Many = refl
*q-distribˡ Many Many Zero = refl
*q-distribˡ Many Many One = refl
*q-distribˡ Many Many Many = refl

*q-distribʳ : ∀ (a b c : Quantity) → (a +q b) *q c ≡ (a *q c) +q (b *q c)
*q-distribʳ Zero Zero Zero = refl
*q-distribʳ Zero Zero One = refl
*q-distribʳ Zero Zero Many = refl
*q-distribʳ Zero One Zero = refl
*q-distribʳ Zero One One = refl
*q-distribʳ Zero One Many = refl
*q-distribʳ Zero Many Zero = refl
*q-distribʳ Zero Many One = refl
*q-distribʳ Zero Many Many = refl
*q-distribʳ One Zero Zero = refl
*q-distribʳ One Zero One = refl
*q-distribʳ One Zero Many = refl
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

*q-zeroʳ : ∀ (a : Quantity) → a *q Zero ≡ Zero
*q-zeroʳ Zero = refl
*q-zeroʳ One = refl
*q-zeroʳ Many = refl

*q-oneʳ : ∀ (a : Quantity) → a *q One ≡ a
*q-oneʳ Zero = refl
*q-oneʳ One = refl
*q-oneʳ Many = refl

+q-mono : ∀ {a a′ b b′ : Quantity} → a ≤q' a′ → b ≤q' b′ → (a +q b) ≤q' (a′ +q b′)
+q-mono z≤z z≤z = z≤z
+q-mono z≤z z≤o = z≤o
+q-mono z≤z z≤m = z≤m
+q-mono z≤z o≤o = o≤o
+q-mono z≤z o≤m = o≤m
+q-mono z≤z m≤m = m≤m
+q-mono z≤o z≤z = z≤o
+q-mono z≤o z≤o = z≤m
+q-mono z≤o z≤m = z≤m
+q-mono z≤o o≤o = o≤m
+q-mono z≤o o≤m = o≤m
+q-mono z≤o m≤m = m≤m
+q-mono z≤m z≤z = z≤m
+q-mono z≤m z≤o = z≤m
+q-mono z≤m z≤m = z≤m
+q-mono z≤m o≤o = o≤m
+q-mono z≤m o≤m = o≤m
+q-mono z≤m m≤m = m≤m
+q-mono o≤o z≤z = o≤o
+q-mono o≤o z≤o = o≤m
+q-mono o≤o z≤m = o≤m
+q-mono o≤o o≤o = m≤m
+q-mono o≤o o≤m = m≤m
+q-mono o≤o m≤m = m≤m
+q-mono o≤m z≤z = o≤m
+q-mono o≤m z≤o = o≤m
+q-mono o≤m z≤m = o≤m
+q-mono o≤m o≤o = m≤m
+q-mono o≤m o≤m = m≤m
+q-mono o≤m m≤m = m≤m
+q-mono m≤m z≤z = m≤m
+q-mono m≤m z≤o = m≤m
+q-mono m≤m z≤m = m≤m
+q-mono m≤m o≤o = m≤m
+q-mono m≤m o≤m = m≤m
+q-mono m≤m m≤m = m≤m

*q-monoˡ : ∀ {a a′ : Quantity} (c : Quantity) → a ≤q' a′ → (a *q c) ≤q' (a′ *q c)
*q-monoˡ Zero z≤z = z≤z
*q-monoˡ One z≤z = z≤z
*q-monoˡ Many z≤z = z≤z
*q-monoˡ Zero z≤o = z≤z
*q-monoˡ One z≤o = z≤o
*q-monoˡ Many z≤o = z≤m
*q-monoˡ Zero z≤m = z≤z
*q-monoˡ One z≤m = z≤m
*q-monoˡ Many z≤m = z≤m
*q-monoˡ Zero o≤o = z≤z
*q-monoˡ One o≤o = o≤o
*q-monoˡ Many o≤o = m≤m
*q-monoˡ Zero o≤m = z≤z
*q-monoˡ One o≤m = o≤m
*q-monoˡ Many o≤m = m≤m
*q-monoˡ Zero m≤m = z≤z
*q-monoˡ One m≤m = m≤m
*q-monoˡ Many m≤m = m≤m

*q-monoʳ : ∀ {a a′ : Quantity} (c : Quantity) → a ≤q' a′ → (c *q a) ≤q' (c *q a′)
*q-monoʳ Zero z≤z = z≤z
*q-monoʳ One z≤z = z≤z
*q-monoʳ Many z≤z = z≤z
*q-monoʳ Zero z≤o = z≤z
*q-monoʳ One z≤o = z≤o
*q-monoʳ Many z≤o = z≤m
*q-monoʳ Zero z≤m = z≤z
*q-monoʳ One z≤m = z≤m
*q-monoʳ Many z≤m = z≤m
*q-monoʳ Zero o≤o = z≤z
*q-monoʳ One o≤o = o≤o
*q-monoʳ Many o≤o = m≤m
*q-monoʳ Zero o≤m = z≤z
*q-monoʳ One o≤m = o≤m
*q-monoʳ Many o≤m = m≤m
*q-monoʳ Zero m≤m = z≤z
*q-monoʳ One m≤m = m≤m
*q-monoʳ Many m≤m = m≤m

≤q'-refl : ∀ (q : Quantity) → q ≤q' q
≤q'-refl Zero = z≤z
≤q'-refl One = o≤o
≤q'-refl Many = m≤m

------------------------------------------------------------------------
-- Usage vectors: the module laws
------------------------------------------------------------------------

*ᵘ-assoc : ∀ {n} (a b : Quantity) (Ψ : Usage n) → (a *q b) *ᵘ Ψ ≡ a *ᵘ (b *ᵘ Ψ)
*ᵘ-assoc a b []      = refl
*ᵘ-assoc a b (q ∷ Ψ) = cong₂ _∷_ (*q-assoc a b q) (*ᵘ-assoc a b Ψ)

*ᵘ-distribˡ : ∀ {n} (a : Quantity) (Ψ₁ Ψ₂ : Usage n) → a *ᵘ (Ψ₁ +ᵘ Ψ₂) ≡ (a *ᵘ Ψ₁) +ᵘ (a *ᵘ Ψ₂)
*ᵘ-distribˡ a []        []        = refl
*ᵘ-distribˡ a (q ∷ Ψ₁) (r ∷ Ψ₂)  = cong₂ _∷_ (*q-distribˡ a q r) (*ᵘ-distribˡ a Ψ₁ Ψ₂)

*ᵘ-distribʳ : ∀ {n} (a b : Quantity) (Ψ : Usage n) → (a +q b) *ᵘ Ψ ≡ (a *ᵘ Ψ) +ᵘ (b *ᵘ Ψ)
*ᵘ-distribʳ a b []      = refl
*ᵘ-distribʳ a b (q ∷ Ψ) = cong₂ _∷_ (*q-distribʳ a b q) (*ᵘ-distribʳ a b Ψ)

-- (A + B) + (C + D) ≡ (A + C) + (B + D)
+ᵘ-interchange : ∀ {n} (A B C D : Usage n) → (A +ᵘ B) +ᵘ (C +ᵘ D) ≡ (A +ᵘ C) +ᵘ (B +ᵘ D)
+ᵘ-interchange A B C D =
  trans (+ᵘ-assoc A B (C +ᵘ D))
    (trans (cong (A +ᵘ_) (trans (sym (+ᵘ-assoc B C D)) (trans (cong (_+ᵘ D) (+ᵘ-comm B C)) (+ᵘ-assoc C B D))))
           (sym (+ᵘ-assoc A C (B +ᵘ D))))

+ᵘ-mono : ∀ {n} {A A′ B B′ : Usage n} → A ⊑ᵘ A′ → B ⊑ᵘ B′ → (A +ᵘ B) ⊑ᵘ (A′ +ᵘ B′)
+ᵘ-mono ⊑[]      ⊑[]      = ⊑[]
+ᵘ-mono (p ⊑∷ u) (r ⊑∷ v) = +q-mono p r ⊑∷ +ᵘ-mono u v

*ᵘ-monoˡ : ∀ {n} {a a′ : Quantity} (Ψ : Usage n) → a ≤q' a′ → (a *ᵘ Ψ) ⊑ᵘ (a′ *ᵘ Ψ)
*ᵘ-monoˡ []      p = ⊑[]
*ᵘ-monoˡ (q ∷ Ψ) p = *q-monoˡ q p ⊑∷ *ᵘ-monoˡ Ψ p

*ᵘ-monoʳ : ∀ {n} (c : Quantity) {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → (c *ᵘ Ψ) ⊑ᵘ (c *ᵘ Ψ′)
*ᵘ-monoʳ c ⊑[]      = ⊑[]
*ᵘ-monoʳ c (p ⊑∷ u) = *q-monoʳ c p ⊑∷ *ᵘ-monoʳ c u

------------------------------------------------------------------------
-- The grade matrix and its action
------------------------------------------------------------------------

Grades : ℕ → ℕ → Set
Grades n m = Fin n → Usage m

infixl 65 _⋆_
_⋆_ : ∀ {n m} → Usage n → Grades n m → Usage m
[]      ⋆ Φ = zeroUsage
(q ∷ Ψ) ⋆ Φ = (q *ᵘ Φ zero) +ᵘ (Ψ ⋆ (λ i → Φ (suc i)))

⋆-zero : ∀ {n m} (Φ : Grades n m) → zeroUsage ⋆ Φ ≡ zeroUsage
⋆-zero {ℕ.zero}  Φ = refl
⋆-zero {ℕ.suc n} Φ = trans (cong₂ _+ᵘ_ (*ᵘ-zeroˡ (Φ zero)) (⋆-zero (λ i → Φ (suc i)))) (+ᵘ-identityˡ zeroUsage)

⋆-+ : ∀ {n m} (Ψ₁ Ψ₂ : Usage n) (Φ : Grades n m) → (Ψ₁ +ᵘ Ψ₂) ⋆ Φ ≡ (Ψ₁ ⋆ Φ) +ᵘ (Ψ₂ ⋆ Φ)
⋆-+ []        []        Φ = sym (+ᵘ-identityˡ zeroUsage)
⋆-+ (q ∷ Ψ₁) (r ∷ Ψ₂)  Φ =
  trans (cong₂ _+ᵘ_ (*ᵘ-distribʳ q r (Φ zero)) (⋆-+ Ψ₁ Ψ₂ (λ i → Φ (suc i))))
        (+ᵘ-interchange (q *ᵘ Φ zero) (r *ᵘ Φ zero) (Ψ₁ ⋆ (λ i → Φ (suc i))) (Ψ₂ ⋆ (λ i → Φ (suc i))))

⋆-* : ∀ {n m} (a : Quantity) (Ψ : Usage n) (Φ : Grades n m) → (a *ᵘ Ψ) ⋆ Φ ≡ a *ᵘ (Ψ ⋆ Φ)
⋆-* a []      Φ = sym (*ᵘ-zeroʳ a)
⋆-* a (q ∷ Ψ) Φ =
  trans (cong₂ _+ᵘ_ (*ᵘ-assoc a q (Φ zero)) (⋆-* a Ψ (λ i → Φ (suc i))))
        (sym (*ᵘ-distribˡ a (q *ᵘ Φ zero) (Ψ ⋆ (λ i → Φ (suc i)))))

⋆-single : ∀ {n m} (i : Fin n) (Φ : Grades n m) → singleUse i One ⋆ Φ ≡ Φ i
⋆-single zero    Φ = trans (cong₂ _+ᵘ_ (*ᵘ-identityˡ (Φ zero)) (⋆-zero (λ i → Φ (suc i)))) (+ᵘ-identityʳ (Φ zero))
⋆-single (suc i) Φ = trans (cong (_+ᵘ (singleUse i One ⋆ (λ j → Φ (suc j)))) (*ᵘ-zeroˡ (Φ zero)))
                           (trans (+ᵘ-identityˡ _) (⋆-single i (λ j → Φ (suc j))))

⋆-mono : ∀ {n m} {Ψ Ψ′ : Usage n} (Φ : Grades n m) → Ψ ⊑ᵘ Ψ′ → (Ψ ⋆ Φ) ⊑ᵘ (Ψ′ ⋆ Φ)
⋆-mono Φ ⊑[]      = ⊑ᵘ-refl′ zeroUsage
  where
    ⊑ᵘ-refl′ : ∀ {m} (Ψ : Usage m) → Ψ ⊑ᵘ Ψ
    ⊑ᵘ-refl′ []      = ⊑[]
    ⊑ᵘ-refl′ (q ∷ Ψ) = ≤q'-refl q ⊑∷ ⊑ᵘ-refl′ Ψ
⋆-mono Φ (p ⊑∷ u) = +ᵘ-mono (*ᵘ-monoˡ (Φ zero) p) (⋆-mono (λ i → Φ (suc i)) u)

------------------------------------------------------------------------
-- Under a binder
------------------------------------------------------------------------

-- Rows weakened by an unused variable.
⋆-weak : ∀ {n m} (Ψ : Usage n) (Φ : Grades n m) → Ψ ⋆ (λ i → Zero ∷ Φ i) ≡ Zero ∷ (Ψ ⋆ Φ)
⋆-weak []      Φ = refl
⋆-weak (q ∷ Ψ) Φ =
  trans (cong ((q *ᵘ (Zero ∷ Φ zero)) +ᵘ_) (⋆-weak Ψ (λ i → Φ (suc i))))
        (cong (_∷ ((q *ᵘ Φ zero) +ᵘ (Ψ ⋆ (λ i → Φ (suc i))))) (trans (+q-identityʳ (q *q Zero)) (*q-zeroʳ q)))

-- The grade matrix of `extS σ`: the new variable uses itself once.
extΦ : ∀ {n m} → Grades n m → Grades (ℕ.suc n) (ℕ.suc m)
extΦ Φ zero    = singleUse zero One
extΦ Φ (suc i) = Zero ∷ Φ i

⋆-ext : ∀ {n m} (q : Quantity) (Ψ : Usage n) (Φ : Grades n m) → (q ∷ Ψ) ⋆ extΦ Φ ≡ q ∷ (Ψ ⋆ Φ)
⋆-ext q Ψ Φ =
  trans (cong₂ _+ᵘ_ (refl {x = q *ᵘ singleUse zero One}) (⋆-weak Ψ Φ))
        (cong₂ _∷_ (trans (cong (_+q Zero) (*q-oneʳ q)) (+q-identityʳ q))
                   (trans (cong (_+ᵘ (Ψ ⋆ Φ)) (*ᵘ-zeroʳ q)) (+ᵘ-identityˡ (Ψ ⋆ Φ))))

-- The identity substitution's matrix is the identity.
⋆-id : ∀ {n} (Ψ : Usage n) → Ψ ⋆ (λ i → singleUse i One) ≡ Ψ
⋆-id []      = refl
⋆-id (q ∷ Ψ) = trans (cong (λ R → (q *ᵘ singleUse zero One) +ᵘ R) (trans (⋆-weak Ψ (λ i → singleUse i One)) (cong (Zero ∷_) (⋆-id Ψ))))
                     (cong₂ _∷_ (trans (cong (_+q Zero) (*q-oneʳ q)) (+q-identityʳ q))
                                (trans (cong (_+ᵘ Ψ) (*ᵘ-zeroʳ q)) (+ᵘ-identityˡ Ψ)))
