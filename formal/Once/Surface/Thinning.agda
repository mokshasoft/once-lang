-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans; sym)

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

-- THE CORE OPERATION: rename an expression through a thinning
-- This single function replaces ALL exchange functions!

rename : ∀ {n m} {Γ : SCtx n} {Δ : SCtx m} {A : Type}
       → Γ ⊆ Δ → SExpr Γ A → SExpr Δ A
rename {Δ = Δ} θ (Surface.var i) =
  subst (SExpr Δ) (sym (thin-var-lookup θ i)) (Surface.var (thin-var θ i))
rename θ (Surface.lam q e) = Surface.lam q (rename (keep θ) e)
rename θ (Surface.app f x) = Surface.app (rename θ f) (rename θ x)
rename θ (Surface.effApp f x) = Surface.effApp (rename θ f) (rename θ x)
rename θ (Surface.pair a b) = Surface.pair (rename θ a) (rename θ b)
rename θ (Surface.fst' p) = Surface.fst' (rename θ p)
rename θ (Surface.snd' p) = Surface.snd' (rename θ p)
rename θ (Surface.inl' a) = Surface.inl' (rename θ a)
rename θ (Surface.inr' b) = Surface.inr' (rename θ b)
rename θ (Surface.case' s l r) =
  Surface.case' (rename θ s) (rename (keep θ) l) (rename (keep θ) r)
rename θ Surface.unit = Surface.unit
rename θ (Surface.absurd v) = Surface.absurd (rename θ v)
rename θ (Surface.let' e₁ e₂) =
  Surface.let' (rename θ e₁) (rename (keep θ) e₂)
rename θ (Surface.int n) = Surface.int n
rename θ (Surface.str s) = Surface.str s
rename θ (Surface.add a b) = Surface.add (rename θ a) (rename θ b)
rename θ (Surface.sub a b) = Surface.sub (rename θ a) (rename θ b)
rename θ (Surface.mul a b) = Surface.mul (rename θ a) (rename θ b)
rename θ (Surface.div a b) = Surface.div (rename θ a) (rename θ b)
rename θ (Surface.mod' a b) = Surface.mod' (rename θ a) (rename θ b)
rename θ (Surface.neg a) = Surface.neg (rename θ a)
rename θ (Surface.lt a b) = Surface.lt (rename θ a) (rename θ b)
rename θ (Surface.le a b) = Surface.le (rename θ a) (rename θ b)
rename θ (Surface.gt a b) = Surface.gt (rename θ a) (rename θ b)
rename θ (Surface.ge a b) = Surface.ge (rename θ a) (rename θ b)
rename θ (Surface.eq a b) = Surface.eq (rename θ a) (rename θ b)
rename θ (Surface.ne a b) = Surface.ne (rename θ a) (rename θ b)
rename θ (Surface.arr' f) = Surface.arr' (rename θ f)
rename θ (Surface.roll' e) = Surface.roll' (rename θ e)
rename θ (Surface.unroll' e) = Surface.unroll' (rename θ e)
rename θ (Surface.prim name) = Surface.prim name

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
weaken : ∀ {n} {Γ : SCtx n} {A B : Type} {q : Quantity} → SExpr Γ B → SExpr (Γ S, A ^ q) B
weaken = rename ⊆-wk

-- Exchange at depth 1 (insert A at position 1, below B)
exchange : ∀ {n} {Γ : SCtx n} {A B C : Type}
         → SExpr (Γ S, B) C → SExpr ((Γ S, A) S, B) C
exchange = rename ⊆-exch₁

-- Exchange at depth 2
exchange₂ : ∀ {n} {Γ : SCtx n} {A B C D : Type}
          → SExpr ((Γ S, B) S, C) D → SExpr (((Γ S, A) S, B) S, C) D
exchange₂ = rename ⊆-exch₂

-- Exchange at depth 3
exchange₃ : ∀ {n} {Γ : SCtx n} {A B C D E : Type}
          → SExpr (((Γ S, B) S, C) S, D) E → SExpr ((((Γ S, A) S, B) S, C) S, D) E
exchange₃ = rename ⊆-exch₃

-- Exchange at depth 4
exchange₄ : ∀ {n} {Γ : SCtx n} {A B C D E F : Type}
          → SExpr ((((Γ S, B) S, C) S, D) S, E) F → SExpr (((((Γ S, A) S, B) S, C) S, D) S, E) F
exchange₄ = rename ⊆-exch₄

-- Exchange at depth 5
exchange₅ : ∀ {n} {Γ : SCtx n} {A B C D E F G : Type}
          → SExpr (((((Γ S, B) S, C) S, D) S, E) S, F) G → SExpr ((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) G
exchange₅ = rename ⊆-exch₅

-- Exchange at depth 6
exchange₆ : ∀ {n} {Γ : SCtx n} {A B C D E F G H : Type}
          → SExpr ((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) H → SExpr (((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) H
exchange₆ = rename ⊆-exch₆

-- Exchange at depth 7
exchange₇ : ∀ {n} {Γ : SCtx n} {A B C D E F G H I : Type}
          → SExpr (((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) S, H) I
          → SExpr ((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H) I
exchange₇ = rename ⊆-exch₇

-- Exchange at depth 8
exchange₈ : ∀ {n} {Γ : SCtx n} {A B C D E F G H I J : Type}
          → SExpr ((((((((Γ S, B) S, C) S, D) S, E) S, F) S, G) S, H) S, I) J
          → SExpr (((((((((Γ S, A) S, B) S, C) S, D) S, E) S, F) S, G) S, H) S, I) J
exchange₈ = rename ⊆-exch₈

------------------------------------------------------------------------
-- Weaken from empty context
------------------------------------------------------------------------

-- Repeatedly weaken to go from empty context to any context
weakenFromEmpty : ∀ {n} {Γ : SCtx n} {A : Type} → SExpr S∅ A → SExpr Γ A
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