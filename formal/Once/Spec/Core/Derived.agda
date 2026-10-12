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
-- A core term records the types its derivation would otherwise choose (D310),
-- so a combinator takes the types its arms are used at: `composeᶜ A B C π f g`
-- is `f ∘ g` for `g : A ⇒ B` and `f : B ⇒ C` at grade `π`.
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
open import Once.Spec.Type using (Type; Functor; _*_; _⇒[_]_; ⟦_⟧T)
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

-- Closed morphisms.
idᶜ inlᶜ inrᶜ terminalᶜ initialᶜ inᶜ : ∀ {n} → Tm n
idᶜ       = lam v0
inlᶜ      = lam (inl v0)
inrᶜ      = lam (inr v0)
terminalᶜ = lam unit
initialᶜ  = lam (absurd v0)
inᶜ       = lam (roll v0)

-- `fstᶜ B : A * B ⇒ A`, `sndᶜ A : A * B ⇒ B`.
fstᶜ sndᶜ : ∀ {n} → Type → Tm n
fstᶜ B = lam (fst B v0)
sndᶜ A = lam (snd A v0)

-- `applyᶜ A B : (A ⇒ B) * A ⇒ B`, at a pure arrow.
applyᶜ : ∀ {n} → Type → Type → Tm n
applyᶜ A B = lam (app A Many (fst A v0) (snd (A ⇒[ mk-kind Many pure ] B) v0))

outᶜ : ∀ {n} → Functor → Tm n
outᶜ F = lam (out F v0)

-- `compose f g` = f ∘ g: `f` evaluated first, `g` applied first.
composeᶜ : ∀ {n} → Type → Type → Type → Purity → Tm n → Tm n → Tm n
composeᶜ A B C π f g =
  let′ (B ⇒[ mk-kind Many π ] C) One f
    (let′ (A ⇒[ mk-kind Many π ] B) Many (wk g) (lam (app B Many v2 (app A Many v1 v0))))

-- `⟨ f , g ⟩`: one shared grade (D222) — the arrow runs both arms.
pairᶜ : ∀ {n} → Type → Type → Type → Purity → Tm n → Tm n → Tm n
pairᶜ A B C π f g =
  let′ (A ⇒[ mk-kind Many π ] B) One f
    (let′ (A ⇒[ mk-kind Many π ] C) One (wk g) (lam (pair (app A Many v2 v0) (app A Many v1 v0))))

-- `[ f , g ]`.
caseᶜ : ∀ {n} → Type → Type → Type → Purity → Tm n → Tm n → Tm n
caseᶜ A B C π f g =
  let′ (A ⇒[ mk-kind Many π ] C) One f
    (let′ (B ⇒[ mk-kind Many π ] C) One (wk g)
      (lam (case A B Many Many v0 (app A Many v3 v0) (app B Many v2 v0))))

-- `curry f`: building the closure runs nothing (D222: the outer arrow is
-- effect-free; the body's grade rides the inner arrow).
curryᶜ : ∀ {n} → Type → Type → Type → Purity → Tm n → Tm n
curryᶜ A B C π f = let′ ((A * B) ⇒[ mk-kind Many π ] C) One f (lam (lam (app (A * B) Many v2 (pair v1 v0))))

-- `cata alg` / `ana coalg`: the algebra is evaluated once (D131).
cataᶜ : ∀ {n} → Functor → Type → Purity → Tm n → Tm n
cataᶜ F A π alg = let′ (⟦ F ⟧T A ⇒[ mk-kind Many π ] A) Many alg (lam (fold F v1 v0))
-- D247: `ana`'s coalgebra is not evaluated at build — the ν stores it (D192).
anaᶜ : ∀ {n} → Type → Tm n → Tm n
anaᶜ A c = lam (unfold A (wk c) v0)

-- Applying an effectful arrow at the surface builds a SUSPENSION
-- `Unit ⇒[eff] B`; head and argument are evaluated when it runs
-- (`⟦ t-effApp ⟧ᵢ`).
effAppᶜ : ∀ {n} → Type → Tm n → Tm n → Tm n
effAppᶜ A f x = lam (app A Many (wk f) (wk x))

-- The SUSPENDED forms of the surface's effectful applied builtins: the
-- argument is evaluated now, the effect when the suspension runs
-- (`t-apply-eff-app-infer`, `t-Out-eff-app-infer`).
applyEffᶜ : ∀ {n} → Type → Type → Tm n
applyEffᶜ A B = lam (lam (app A Many (fst A v1) (snd (A ⇒[ mk-kind Many eff ] B) v1)))

outEffᶜ : ∀ {n} → Functor → Tm n
outEffᶜ F = lam (lam (out F v1))
