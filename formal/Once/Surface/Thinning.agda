-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Thinning
--
-- Order-Preserving Embeddings (Thinnings) for context manipulation.
--
-- A thinning Γ ⊆ Δ witnesses that Γ is a sub-context of Δ.
-- This gives us a compositional way to handle weakening and exchange.
--
-- Key insight: instead of proving exchange₀, exchange₁, ..., exchange₈
-- separately, we prove ONE lemma (rename) and derive all exchanges
-- as specific thinnings.
------------------------------------------------------------------------

module Once.Surface.Thinning where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat as Nat using (_+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym)

open import Once.Type
open import Once.Surface.Syntax as Surface
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)

------------------------------------------------------------------------
-- Thinnings (Order-Preserving Embeddings)
------------------------------------------------------------------------

-- A thinning from Γ to Δ says "Γ's variables appear in Δ in order,
-- but Δ may have extra variables interspersed."

data _⊆_ : ∀ {n m} → SCtx n → SCtx m → Set where
  -- Empty context embeds into empty context
  done : S∅ ⊆ S∅

  -- Skip: Δ has an extra variable that Γ doesn't have
  skip : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m} {A : Type} {q : Quantity}
       → Γ ⊆ Δ → Γ ⊆ (_S,_^_ Δ A q)

  -- Keep: both contexts have the same variable at this position
  keep : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m} {A : Type} {q : Quantity}
       → Γ ⊆ Δ → (_S,_^_ Γ A q) ⊆ (_S,_^_ Δ A q)

infixr 4 _⊆_

------------------------------------------------------------------------
-- Basic Thinnings
------------------------------------------------------------------------

-- Identity thinning: Γ ⊆ Γ
⊆-refl : ∀ {n} {Γ : SCtx n} → Γ ⊆ Γ
⊆-refl {Γ = S∅}            = done
⊆-refl {Γ = _S,_^_ Γ' _ _} = keep ⊆-refl

-- Weakening thinning: Γ ⊆ (Γ , A ^ q)
⊆-wk : ∀ {n} {Γ : SCtx n} {A : Type} {q : Quantity} → Γ ⊆ (Γ S, A ^ q)
⊆-wk = skip ⊆-refl

------------------------------------------------------------------------
-- Thinning Composition
------------------------------------------------------------------------

_∘⊆_ : ∀ {n m k} {Γ : SCtx n} {Δ : SCtx m} {Θ : SCtx k}
     → Δ ⊆ Θ → Γ ⊆ Δ → Γ ⊆ Θ
done      ∘⊆ done      = done
skip θ    ∘⊆ δ         = skip (θ ∘⊆ δ)
keep θ    ∘⊆ skip δ    = skip (θ ∘⊆ δ)
keep θ    ∘⊆ keep δ    = keep (θ ∘⊆ δ)

------------------------------------------------------------------------
-- Variable Thinning
------------------------------------------------------------------------

-- Apply thinning to a variable index
thin-var : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m}
         → Γ ⊆ Δ → Fin n → Fin m
thin-var (skip θ) i       = suc (thin-var θ i)
thin-var (keep θ) zero    = zero
thin-var (keep θ) (suc i) = suc (thin-var θ i)

-- Key lemma: thinning preserves lookup
thin-var-lookup : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m}
                → (θ : Γ ⊆ Δ) → (i : Fin n)
                → lookup Γ i ≡ lookup Δ (thin-var θ i)
thin-var-lookup (skip θ) i       = thin-var-lookup θ i
thin-var-lookup (keep θ) zero    = refl
thin-var-lookup (keep θ) (suc i) = thin-var-lookup θ i

------------------------------------------------------------------------
-- Expression Renaming via Thinning
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Thinning on Usage Vectors
------------------------------------------------------------------------

-- Apply a thinning to a usage vector.
-- skip inserts Zero at the new position (the skipped variable is unused).
-- keep copies the head, recurses on the tail.
thin-usage : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m}
           → Γ ⊆ Δ → Usage n → Usage m
thin-usage done     []        = []
thin-usage (skip θ) Ψ         = Zero ∷ thin-usage θ Ψ
thin-usage (keep θ) (q ∷ Ψ)  = q ∷ thin-usage θ Ψ

-- Distribution lemmas: thin-usage commutes with QTT usage arithmetic.

thin-usage-+ᵘ : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m}
              → (θ : Γ ⊆ Δ) (Ψ₁ Ψ₂ : Usage n)
              → thin-usage θ (Ψ₁ +ᵘ Ψ₂) ≡ thin-usage θ Ψ₁ +ᵘ thin-usage θ Ψ₂
thin-usage-+ᵘ done     [] []               = refl
thin-usage-+ᵘ (skip θ) Ψ₁ Ψ₂
  rewrite thin-usage-+ᵘ θ Ψ₁ Ψ₂             = refl
thin-usage-+ᵘ (keep θ) (q₁ ∷ Ψ₁) (q₂ ∷ Ψ₂)
  rewrite thin-usage-+ᵘ θ Ψ₁ Ψ₂             = refl

thin-usage-*ᵘ : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m}
              → (θ : Γ ⊆ Δ) (q : Quantity) (Ψ : Usage n)
              → thin-usage θ (q *ᵘ Ψ) ≡ q *ᵘ thin-usage θ Ψ
thin-usage-*ᵘ done     q []                 = refl
thin-usage-*ᵘ {Γ = Γ} {Δ = Δ S, _ ^ _} (skip θ) q Ψ
  rewrite thin-usage-*ᵘ θ q Ψ               = cong (_∷ (q *ᵘ thin-usage θ Ψ)) (sym (q*q-zero q))
  where
    -- q *q Zero = Zero for all q (needed for the skip case)
    q*q-zero : (q : Quantity) → q *q Zero ≡ Zero
    q*q-zero Zero = refl
    q*q-zero One  = refl
    q*q-zero Many = refl
thin-usage-*ᵘ (keep θ) q (q' ∷ Ψ)
  rewrite thin-usage-*ᵘ θ q Ψ               = refl

thin-usage-⊔ᵘ : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m}
              → (θ : Γ ⊆ Δ) (Ψ₁ Ψ₂ : Usage n)
              → thin-usage θ (Ψ₁ ⊔ᵘ Ψ₂) ≡ thin-usage θ Ψ₁ ⊔ᵘ thin-usage θ Ψ₂
thin-usage-⊔ᵘ done     [] []               = refl
thin-usage-⊔ᵘ (skip θ) Ψ₁ Ψ₂
  rewrite thin-usage-⊔ᵘ θ Ψ₁ Ψ₂             = refl
thin-usage-⊔ᵘ (keep θ) (q₁ ∷ Ψ₁) (q₂ ∷ Ψ₂)
  rewrite thin-usage-⊔ᵘ θ Ψ₁ Ψ₂             = refl

thin-usage-zeroUsage : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m}
                     → (θ : Γ ⊆ Δ) → thin-usage θ (zeroUsage {n}) ≡ zeroUsage {m}
thin-usage-zeroUsage done     = refl
thin-usage-zeroUsage (skip θ) = cong (Zero ∷_) (thin-usage-zeroUsage θ)
thin-usage-zeroUsage (keep θ) = cong (Zero ∷_) (thin-usage-zeroUsage θ)

thin-usage-refl : ∀ {n} {Γ : SCtx n} (Ψ : Usage n)
                → thin-usage (⊆-refl {Γ = Γ}) Ψ ≡ Ψ
thin-usage-refl {Γ = S∅} []                = refl
thin-usage-refl {Γ = _ S, _ ^ _} (q ∷ Ψ)  = cong (q ∷_) (thin-usage-refl Ψ)

thin-usage-singleUse : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m}
                     → (θ : Γ ⊆ Δ) (i : Fin n) (q : Quantity)
                     → thin-usage θ (singleUse i q) ≡ singleUse (thin-var θ i) q
thin-usage-singleUse done     ()       q
thin-usage-singleUse (skip θ) i        q
  rewrite thin-usage-singleUse θ i q    = refl
thin-usage-singleUse (keep θ) zero     q = cong (q ∷_) (thin-usage-zeroUsage θ)
thin-usage-singleUse (keep θ) (suc i) q  = cong (Zero ∷_) (thin-usage-singleUse θ i q)


------------------------------------------------------------------------
-- Expression Renaming via Thinning
------------------------------------------------------------------------

-- THE CORE OPERATION: rename an expression through a thinning
-- This single function replaces ALL exchange functions!
-- Preserves the usage vector via thin-usage propagation.

rename : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m} {Ψ : Usage n} {A : Type}
       → (θ : Γ ⊆ Δ) → SExpr Γ Ψ A → SExpr Δ (thin-usage θ Ψ) A
rename {Δ = Δ} θ (Surface.var i) =
  subst₂ (SExpr Δ) (sym (thin-usage-singleUse θ i One))
         (sym (thin-var-lookup θ i)) (Surface.var (thin-var θ i))
  where
    subst₂ : ∀ {a b c} {A : Set a} {B : Set b} (C : A → B → Set c)
           → {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → C x₁ y₁ → C x₂ y₂
    subst₂ C refl refl z = z
rename θ (Surface.lam q p e) = Surface.lam q p (rename (keep θ) e)
rename {Δ = Δ} θ (Surface.app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} f x) =
  subst (λ Ψ → SExpr Δ Ψ _)
        (sym (trans (thin-usage-+ᵘ θ Ψ₁ (q *ᵘ Ψ₂))
                    (cong (thin-usage θ Ψ₁ +ᵘ_) (thin-usage-*ᵘ θ q Ψ₂))))
        (Surface.app (rename θ f) (rename θ x))
rename {Δ = Δ} θ (Surface.effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f x) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂))
        (Surface.effApp (rename θ f) (rename θ x))
rename {Δ = Δ} θ (Surface.pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂))
        (Surface.pair (rename θ a) (rename θ b))
rename θ (Surface.fst' p) = Surface.fst' (rename θ p)
rename θ (Surface.arr' f) = Surface.arr' (rename θ f)
rename θ (Surface.snd' p) = Surface.snd' (rename θ p)
rename θ (Surface.inl' a) = Surface.inl' (rename θ a)
rename θ (Surface.inr' b) = Surface.inr' (rename θ b)
rename {Δ = Δ} θ (Surface.case' {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} s l r) =
  subst (λ Ψ → SExpr Δ Ψ _)
        (sym (trans (thin-usage-+ᵘ θ Ψs (Ψₗ ⊔ᵘ Ψᵣ))
                    (cong (thin-usage θ Ψs +ᵘ_) (thin-usage-⊔ᵘ θ Ψₗ Ψᵣ))))
        (Surface.case' (rename θ s) (rename (keep θ) l) (rename (keep θ) r))
rename {Δ = Δ} θ Surface.unit = subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-zeroUsage θ)) Surface.unit
rename θ (Surface.absurd v) = Surface.absurd (rename θ v)
rename {Δ = Δ} θ (Surface.let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} e₁ e₂) =
  subst (λ Ψ → SExpr Δ Ψ _)
        (sym (trans (thin-usage-+ᵘ θ Ψ₂ (q *ᵘ Ψ₁))
                    (cong (thin-usage θ Ψ₂ +ᵘ_) (thin-usage-*ᵘ θ q Ψ₁))))
        (Surface.let' (rename θ e₁) (rename (keep θ) e₂))
rename {Δ = Δ} θ (Surface.int n) = subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-zeroUsage θ)) (Surface.int n)
rename {Δ = Δ} θ (Surface.add {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.add (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.sub {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.sub (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.mul {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.mul (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.div {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.div (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.mod' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.mod' (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.str s) = subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-zeroUsage θ)) (Surface.str s)
rename θ (Surface.neg a) = Surface.neg (rename θ a)
rename {Δ = Δ} θ (Surface.lt {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.lt (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.le {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.le (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.gt {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.gt (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.ge {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.ge (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.eq {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.eq (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.ne {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)) (Surface.ne (rename θ a) (rename θ b))
rename {Δ = Δ} θ (Surface.sigOp name conc) = subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-zeroUsage θ)) (Surface.sigOp name conc)
-- Plan 0.19: user-defined closure reference. Same shape as sigOp —
-- closed by construction (zeroUsage), no context dependency.
rename {Δ = Δ} θ (Surface.closure name) = subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-zeroUsage θ)) (Surface.closure name)
rename {Δ = Δ} θ (Surface.poly name T) = subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-zeroUsage θ)) (Surface.poly name T)
-- Plan 0.2.4.5 D2: morphism realm. `lift-morphism` carries no
-- context dependency (closed by construction, zeroUsage), so renaming
-- threads through unchanged modulo the `thin-usage-zeroUsage` adjustment.
rename {Δ = Δ} θ (Surface.lift-morphism m) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-zeroUsage θ)) (Surface.lift-morphism m)
-- Plan 0.36 Phase 2a: cata is zeroUsage and its algebra lives in the
-- EMPTY context (`∅`), so the thinning θ : Γ ⊆ Δ never touches it —
-- same shape as `lift-morphism`.
rename {Δ = Δ} θ (Surface.cata wfF alg) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-zeroUsage θ)) (Surface.cata wfF alg)
-- `ana` (dual of `cata`): also zeroUsage with a coalgebra in `∅`, so θ never
-- touches it.
rename {Δ = Δ} θ (Surface.ana wfF coalg) =
  subst (λ Ψ → SExpr Δ Ψ _) (sym (thin-usage-zeroUsage θ)) (Surface.ana wfF coalg)
-- Plan 0.2.4.5 D2: morphism-realm application. Usage shape mirrors
-- `Surface.app` (with f-usage = zeroUsage, q = Many): renaming the
-- argument propagates through `+ᵘ` and `*ᵘ` and `zeroUsage`.
rename {Δ = Δ} θ (Surface.morph-app {Ψ = Ψ} m x) =
  subst (λ Ψ' → SExpr Δ Ψ' _)
        (sym (trans (thin-usage-+ᵘ θ Surface.zeroUsage (Many *ᵘ Ψ))
                    (cong₂ _+ᵘ_ (thin-usage-zeroUsage θ)
                                (thin-usage-*ᵘ θ Many Ψ))))
        (Surface.morph-app m (rename θ x))

------------------------------------------------------------------------
-- Telescopes (for generalized exchange)
------------------------------------------------------------------------

-- A telescope is a list of types to extend a context with
data Telescope : ℕ → Set where
  []  : Telescope 0
  _∷_ : ∀ {d} → Type → Telescope d → Telescope (suc d)

infixr 5 _∷_

-- Apply a telescope to extend a context
-- applyTel Γ [B, C, D] = (((Γ , B) , C) , D)
applyTel : ∀ {n d} → SCtx n → Telescope d → SCtx (n Nat.+ d)
applyTel {n} {zero}  Γ []       = subst SCtx (sym (+-identityʳ n)) Γ
applyTel {n} {suc d} Γ (B ∷ tel) = subst SCtx (sym (+-suc n d)) (applyTel (Γ S, B) tel)

-- Simpler version that avoids subst by using a helper
-- We build the context directly without worrying about indices

------------------------------------------------------------------------
-- Generalized Exchange Thinning via Telescopes
------------------------------------------------------------------------

-- For exchange at depth d, we need to express:
--   applyTel Γ tel ⊆ applyTel (Γ , A) tel
--
-- where tel has d elements.
--
-- The thinning is: keep^d (skip ⊆-refl)

-- A generalized `keeps` that applies keep^d to a base thinning would require
-- complex type-level arithmetic to track context growth. Instead, we use
-- the direct exchange thinnings below, which are simpler and sufficient.

------------------------------------------------------------------------
-- Direct Exchange Thinnings (without telescope arithmetic)
------------------------------------------------------------------------

-- Exchange at depth 0: this is just weakening
-- Γ ⊆ (Γ , A)
⊆-exch₀ : ∀ {n} {Γ : SCtx n} {A : Type} → Γ ⊆ (Γ S, A)
⊆-exch₀ = skip ⊆-refl

-- Exchange at depth 1: (Γ , B) ⊆ ((Γ , A) , B)
⊆-exch₁ : ∀ {n} {Γ : SCtx n} {A B : Type} → (Γ S, B) ⊆ ((Γ S, A) S, B)
⊆-exch₁ = keep ⊆-exch₀

-- Exchange at depth 2: ((Γ , B) , C) ⊆ (((Γ , A) , B) , C)
⊆-exch₂ : ∀ {n} {Γ : SCtx n} {A B C : Type}
        → ((Γ S, B) S, C) ⊆ (((Γ S, A) S, B) S, C)
⊆-exch₂ = keep ⊆-exch₁

-- Exchange at depth 3
⊆-exch₃ : ∀ {n} {Γ : SCtx n} {A B C D : Type}
        → (((Γ S, B) S, C) S, D) ⊆ ((((Γ S, A) S, B) S, C) S, D)
⊆-exch₃ = keep ⊆-exch₂

-- Exchange at depth 4
⊆-exch₄ : ∀ {n} {Γ : SCtx n} {A B C D E : Type}
        → ((((Γ S, B) S, C) S, D) S, E) ⊆ (((((Γ S, A) S, B) S, C) S, D) S, E)
⊆-exch₄ = keep ⊆-exch₃

-- Exchange at depth 5
⊆-exch₅ : ∀ {n} {Γ : SCtx n} {A B C D E F : Type}
        → (((((Γ S, B) S, C) S, D) S, E) S, F) ⊆ ((((((Γ S, A) S, B) S, C) S, D) S, E) S, F)
⊆-exch₅ = keep ⊆-exch₄

-- Exchange at depth 6
⊆-exch₆ : ∀ {n} {Γ : SCtx n} {A B C D E F G : Type}
        → ((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) ⊆ (((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G)
⊆-exch₆ = keep ⊆-exch₅

-- Exchange at depth 7
⊆-exch₇ : ∀ {n} {Γ : SCtx n} {A B C D E F G H : Type}
        → (((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) S, H) ⊆ ((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H)
⊆-exch₇ = keep ⊆-exch₆

-- Exchange at depth 8 (for completeness, though depth > 7 is rejected)
⊆-exch₈ : ∀ {n} {Γ : SCtx n} {A B C D E F G H I : Type}
        → ((((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) S, H) S, I) ⊆ (((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H) S, I)
⊆-exch₈ = keep ⊆-exch₇

------------------------------------------------------------------------
-- Derived Weaken and Exchange Operations
------------------------------------------------------------------------

-- Weaken: Γ → (Γ , A ^ q)
-- The new variable is unused (Zero), so the usage prefix gets Zero.
weaken : ∀ {n} {Γ : SCtx n} {Ψ : Usage n} {A B : Type} {q : Quantity}
       → SExpr Γ Ψ B → SExpr (Γ S, A ^ q) (Zero ∷ Ψ) B
weaken {Γ = Γ} {Ψ = Ψ} e =
  subst (λ Ψ' → SExpr _ (Zero ∷ Ψ') _) (thin-usage-refl Ψ) (rename ⊆-wk e)

-- Exchange at depth 1 (insert A at position 1, below B)
exchange : ∀ {n} {Γ : SCtx n} {Ψ : Usage (suc n)} {A B C : Type}
         → SExpr (Γ S, B) Ψ C
         → SExpr ((Γ S, A) S, B) (thin-usage (⊆-exch₁ {A = A}) Ψ) C
exchange = rename ⊆-exch₁

-- Exchange at depth 2
exchange₂ : ∀ {n} {Γ : SCtx n} {Ψ : Usage (suc (suc n))} {A B C D : Type}
          → SExpr ((Γ S, B) S, C) Ψ D
          → SExpr (((Γ S, A) S, B) S, C) (thin-usage (⊆-exch₂ {A = A}) Ψ) D
exchange₂ = rename ⊆-exch₂

-- Exchange at depth 3
exchange₃ : ∀ {n} {Γ : SCtx n} {Ψ : Usage (suc (suc (suc n)))} {A B C D E : Type}
          → SExpr (((Γ S, B) S, C) S, D) Ψ E
          → SExpr ((((Γ S, A) S, B) S, C) S, D) (thin-usage (⊆-exch₃ {A = A}) Ψ) E
exchange₃ = rename ⊆-exch₃

-- Exchange at depth 4
exchange₄ : ∀ {n} {Γ : SCtx n} {Ψ : Usage (suc (suc (suc (suc n))))} {A B C D E F : Type}
          → SExpr ((((Γ S, B) S, C) S, D) S, E) Ψ F
          → SExpr (((((Γ S, A) S, B) S, C) S, D) S, E) (thin-usage (⊆-exch₄ {A = A}) Ψ) F
exchange₄ = rename ⊆-exch₄

-- Exchange at depth 5
exchange₅ : ∀ {n} {Γ : SCtx n} {Ψ : Usage (suc (suc (suc (suc (suc n)))))} {A B C D E F G : Type}
          → SExpr (((((Γ S, B) S, C) S, D) S, E) S, F) Ψ G
          → SExpr ((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) (thin-usage (⊆-exch₅ {A = A}) Ψ) G
exchange₅ = rename ⊆-exch₅

-- Exchange at depth 6
exchange₆ : ∀ {n} {Γ : SCtx n} {Ψ : Usage (suc (suc (suc (suc (suc (suc n))))))} {A B C D E F G H : Type}
          → SExpr ((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) Ψ H
          → SExpr (((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) (thin-usage (⊆-exch₆ {A = A}) Ψ) H
exchange₆ = rename ⊆-exch₆

-- Exchange at depth 7
exchange₇ : ∀ {n} {Γ : SCtx n} {Ψ : Usage (suc (suc (suc (suc (suc (suc (suc n)))))))} {A B C D E F G H I : Type}
          → SExpr (((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) S, H) Ψ I
          → SExpr ((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H) (thin-usage (⊆-exch₇ {A = A}) Ψ) I
exchange₇ = rename ⊆-exch₇

-- Exchange at depth 8
exchange₈ : ∀ {n} {Γ : SCtx n} {Ψ : Usage (suc (suc (suc (suc (suc (suc (suc (suc n))))))))} {A B C D E F G H I J : Type}
          → SExpr ((((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) S, H) S, I) Ψ J
          → SExpr (((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H) S, I) (thin-usage (⊆-exch₈ {A = A}) Ψ) J
exchange₈ = rename ⊆-exch₈

------------------------------------------------------------------------
-- Weaken from empty context
------------------------------------------------------------------------

-- Repeatedly weaken to go from empty context to any context.
-- Lifts a closed expression (zeroUsage) into any context; usage stays zero
-- in the larger context because we only add unused variables.
weakenFromEmpty : ∀ {n} {Γ : SCtx n} {A : Type}
                → SExpr S∅ [] A → SExpr Γ (zeroUsage {n}) A
weakenFromEmpty {Γ = S∅}            e = e
weakenFromEmpty {Γ = _S,_^_ Γ' _ _} e = weaken (weakenFromEmpty {Γ = Γ'} e)

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- OLD APPROACH (in TypeCheck.Elaborate):
--   - 8 separate lookup lemmas (lookup-suc, lookup-suc-suc, ...)
--   - 8 separate exchange functions, each ~20 lines
--   - {-# TERMINATING #-} pragma needed
--   - exchange₈ was a POSTULATE
--
-- NEW APPROACH (this module):
--   - 1 lookup lemma (thin-var-lookup)
--   - 1 rename function (~30 lines)
--   - 9 one-line thinning definitions (⊆-exch₀ through ⊆-exch₈)
--   - 9 one-line exchange definitions
--   - Structural recursion on Expr (no TERMINATING pragma needed)
--
-- BONUS: Works for ANY depth by adding more one-line thinnings