-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Derived — the categorical combinators AS DEFINITIONS
-- (plan 0.102 A, D231).
--
-- SPEC. Each combinator the surface writes is a λ-term of the core; its
-- meaning is DERIVED from the formers', never listed. Call-by-value with the
-- evaluation order of today's meaning: a combinator's ARMS are evaluated
-- once, eagerly, left to right (`let`), and the resulting arrow runs them per
-- application — exactly `⟦ t-compose-check-g ⟧ᶜ`'s
-- `⟦df⟧ >>= vf → ⟦dg⟧ >>= vg → returnT (λ a → vg a >>= vf)`.
--
-- Arms are consumed by `let`, not by application, so they cost their own
-- usage (D127: composition is LINEAR in each arm), not an application's
-- `Many *ᵘ Ψ`.
--
-- The compiler does not go through these terms: it emits `IR.compose` etc.
-- directly, and owes one model lemma per combinator (the IR morphism means
-- what the definition means). Their typing rules are admissible (plan 0.102 B).
------------------------------------------------------------------------

module Once.Spec.Core.Derived where

open import Data.Nat using (ℕ)
open import Data.Fin using (zero; suc)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.Spec.Core.Syntax

private
  v0 : ∀ {n} → Tm (ℕ.suc n)
  v0 = var zero
  v1 : ∀ {n} → Tm (ℕ.suc (ℕ.suc n))
  v1 = var (suc zero)
  v2 : ∀ {n} → Tm (ℕ.suc (ℕ.suc (ℕ.suc n)))
  v2 = var (suc (suc zero))
  v3 : ∀ {n} → Tm (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc n))))
  v3 = var (suc (suc (suc zero)))

-- Closed morphisms.
idᶜ fstᶜ sndᶜ inlᶜ inrᶜ terminalᶜ initialᶜ applyᶜ inᶜ outᶜ : ∀ {n} → Tm n
idᶜ       = lam v0
fstᶜ      = lam (fst v0)
sndᶜ      = lam (snd v0)
inlᶜ      = lam (inl v0)
inrᶜ      = lam (inr v0)
terminalᶜ = lam unit
initialᶜ  = lam (absurd v0)
applyᶜ    = lam (app (fst v0) (snd v0))
inᶜ       = lam (roll v0)
outᶜ      = lam (out v0)

-- `compose f g` = f ∘ g: `f` evaluated first, `g` applied first.
composeᶜ : ∀ {n} → Tm n → Tm n → Tm n
composeᶜ f g = let′ f (let′ (wk g) (lam (app v2 (app v1 v0))))

-- `⟨ f , g ⟩`: one shared grade (D222) — the arrow runs both arms.
pairᶜ : ∀ {n} → Tm n → Tm n → Tm n
pairᶜ f g = let′ f (let′ (wk g) (lam (pair (app v2 v0) (app v1 v0))))

-- `[ f , g ]`.
caseᶜ : ∀ {n} → Tm n → Tm n → Tm n
caseᶜ f g = let′ f (let′ (wk g) (lam (case v0 (app v3 v0) (app v2 v0))))

-- `curry f`: building the closure runs nothing (D222: the outer arrow is
-- effect-free; the body's grade rides the inner arrow).
curryᶜ : ∀ {n} → Tm n → Tm n
curryᶜ f = let′ f (lam (lam (app v2 (pair v1 v0))))

-- `cata alg` / `ana coalg`: the algebra is evaluated once (D131).
cataᶜ anaᶜ : ∀ {n} → Tm n → Tm n
cataᶜ alg = let′ alg (lam (fold v1 v0))
anaᶜ  c   = let′ c   (lam (unfold v1 v0))

-- Applying an effectful arrow at the surface builds a SUSPENSION
-- `Unit ⇒[eff] B`; head and argument are evaluated when it runs
-- (`⟦ t-effApp ⟧ᵢ`).
effAppᶜ : ∀ {n} → Tm n → Tm n → Tm n
effAppᶜ f x = lam (app (wk f) (wk x))

------------------------------------------------------------------------
-- The functor's action on terms: `mapᶜ F h v` applies `h` (a body over one
-- extra variable) at every recursive position of `v : ⟦ F ⟧T A`, left to
-- right. What the μ/ν β-rows and Lambek's `out` for μ are stated with.
------------------------------------------------------------------------

mapᶜ : ∀ {n} → Functor → Tm (ℕ.suc n) → Tm n → Tm n
mapᶜ (K _)   h v = v
mapᶜ Id      h v = h [ v ]
mapᶜ (F ⊕ G) h v = case v (inl (mapᶜ F (ren (extR suc) h) v0)) (inr (mapᶜ G (ren (extR suc) h) v0))
mapᶜ (F ⊗ G) h v = let′ v (pair (mapᶜ F (ren (extR suc) h) (fst v0)) (mapᶜ G (ren (extR suc) h) (snd v0)))
