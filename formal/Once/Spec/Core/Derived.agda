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
-- A core term determines its type (D310: every `lam` names its domain,
-- quantity and grade), so a combinator takes the types it is used at:
-- `composeᶜ A π f g` is `f ∘ g` at `A ⇒[ Many , π ] _`.
--
-- The compiler does not go through these terms: it emits `IR.compose` etc.
-- directly, and owes one model lemma per combinator (the IR morphism means
-- what the definition means). Their typing rules are admissible (plan 0.102 B).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

open import Once.Spec.Contract using (ISig)
module Once.Spec.Core.Derived {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (ℕ)
open import Data.Fin using (zero; suc)
open import Once.Spec.Type using (Type; Functor; Unit; Void; _*_; _+_; _⇒[_]_; ⟦_⟧T; μ-type; ν-type)
open import Once.Spec.Type.Grade using (Purity; pure; eff; mk-kind; One; Many)
open import Once.Spec.Core.Syntax S

private
  v0 : ∀ {n} → Tm (ℕ.suc n)
  v0 = var zero
  v1 : ∀ {n} → Tm (ℕ.suc (ℕ.suc n))
  v1 = var (suc zero)
  v2 : ∀ {n} → Tm (ℕ.suc (ℕ.suc (ℕ.suc n)))
  v2 = var (suc (suc zero))
  v3 : ∀ {n} → Tm (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc n))))
  v3 = var (suc (suc (suc zero)))

-- Closed morphisms, at the arrow `_ ⇒[ Many , π ] _`.
idᶜ terminalᶜ : ∀ {n} → Type → Purity → Tm n
idᶜ       A π = lam A Many π v0
terminalᶜ A π = lam A Many π unit

-- `fstᶜ A B π : A * B ⇒ A`, `sndᶜ A B π : A * B ⇒ B`; `inlᶜ A B π : A ⇒ A + B`, …
fstᶜ sndᶜ inlᶜ inrᶜ : ∀ {n} → Type → Type → Purity → Tm n
fstᶜ A B π = lam (A * B) Many π (fst v0)
sndᶜ A B π = lam (A * B) Many π (snd v0)
inlᶜ A B π = lam A Many π (inl B v0)
inrᶜ A B π = lam B Many π (inr A v0)

-- `initialᶜ A π : Void ⇒ A`.
initialᶜ : ∀ {n} → Type → Purity → Tm n
initialᶜ A π = lam Void Many π (absurd A v0)

-- `applyᶜ A B : (A ⇒ B) * A ⇒ B`, at pure arrows.
applyᶜ : ∀ {n} → Type → Type → Tm n
applyᶜ A B = lam ((A ⇒[ mk-kind Many pure ] B) * A) Many pure (app (fst v0) (snd v0))

inᶜ outᶜ : ∀ {n} → Functor → Tm n
inᶜ  F = lam (⟦ F ⟧T (μ-type F)) Many pure (roll F v0)
outᶜ F = lam (ν-type F pure) Many pure (out v0)

-- `compose f g` = f ∘ g: `f` evaluated first, `g` applied first.
composeᶜ : ∀ {n} → Type → Purity → Tm n → Tm n → Tm n
composeᶜ A π f g = let′ One f (let′ Many (wk g) (lam A Many π (app v2 (app v1 v0))))

-- `⟨ f , g ⟩`: one shared grade (D222) — the arrow runs both arms.
pairᶜ : ∀ {n} → Type → Purity → Tm n → Tm n → Tm n
pairᶜ A π f g = let′ One f (let′ One (wk g) (lam A Many π (pair (app v2 v0) (app v1 v0))))

-- `[ f , g ]`.
caseᶜ : ∀ {n} → Type → Type → Purity → Tm n → Tm n → Tm n
caseᶜ A B π f g =
  let′ One f (let′ One (wk g) (lam (A + B) Many π (case Many Many v0 (app v3 v0) (app v2 v0))))

-- `curry f`: building the closure runs nothing (D222: the outer arrow is
-- effect-free; the body's grade rides the inner arrow).
curryᶜ : ∀ {n} → Type → Type → Purity → Purity → Tm n → Tm n
curryᶜ A B π₀ π f = let′ One f (lam A Many π₀ (lam B Many π (app v2 (pair v1 v0))))

-- `cata alg` / `ana coalg`: the algebra is evaluated once (D131).
cataᶜ : ∀ {n} → Functor → Purity → Tm n → Tm n
cataᶜ F π alg = let′ Many alg (lam (μ-type F) Many π (fold F v1 v0))
-- D247: `ana`'s coalgebra is not evaluated at build — the ν stores it (D192).
anaᶜ : ∀ {n} → Functor → Type → Purity → Tm n → Tm n
anaᶜ F A π₀ c = lam A Many π₀ (unfold F (wk c) v0)

-- Applying an effectful arrow at the surface builds a SUSPENSION
-- `Unit ⇒[eff] B`; head and argument are evaluated when it runs
-- (`⟦ t-effApp ⟧ᵢ`).
effAppᶜ : ∀ {n} → Purity → Tm n → Tm n → Tm n
effAppᶜ π f x = lam Unit Many π (app (wk f) (wk x))

-- The SUSPENDED forms of the surface's effectful applied builtins: the
-- argument is evaluated now, the effect when the suspension runs
-- (`t-apply-eff-app-infer`, `t-Out-eff-app-infer`).
applyEffᶜ : ∀ {n} → Purity → Type → Type → Tm n
applyEffᶜ π A B = lam ((A ⇒[ mk-kind Many π ] B) * A) Many pure (lam Unit Many π (app (fst v1) (snd v1)))

outEffᶜ : ∀ {n} → Purity → Functor → Tm n
outEffᶜ π F = lam (ν-type F π) Many pure (lam Unit Many π (out v1))
