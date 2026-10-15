{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Derived — the categorical combinators, as λ-terms.
--
-- Each combinator a program writes is a term of the core, so its meaning is
-- derived, never listed. A combinator's arms are evaluated once, left to
-- right (by `let`), and the arrow it builds runs them at each application;
-- an arm consumed by `let` costs its own usage (composition is linear in each
-- arm). Each takes the types it is used at (a core term determines its type).
------------------------------------------------------------------------

module Once.Spec.Core.Derived where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (zero; suc)
open import Once.Spec.Grade using (Purity; pure; mk-kind; One; Many)
open import Once.Spec.Type using (Ty; Fun; Unit; Void; _*_; _+_; _⇒[_]_; ⟦_⟧F; μ; ν)
open import Once.Spec.Core.Syntax

module _ {s} {S : Defs s} {m : ℕ} where

  private
    v0 : ∀ {n} → Tm S m (suc n)
    v0 = var zero
    v1 : ∀ {n} → Tm S m (suc (suc n))
    v1 = var (suc zero)
    v2 : ∀ {n} → Tm S m (suc (suc (suc n)))
    v2 = var (suc (suc zero))
    v3 : ∀ {n} → Tm S m (suc (suc (suc (suc n))))
    v3 = var (suc (suc (suc zero)))

  -- The closed morphisms, at the arrow `_ ⇒[ Many , π ] _`.
  idᶜ terminalᶜ initialᶜ : ∀ {n} → Ty m → Purity → Tm S m n
  idᶜ       A π = lam A Many π v0
  terminalᶜ A π = lam A Many π unit
  initialᶜ  A π = lam Void Many π (absurd A v0)

  fstᶜ sndᶜ inlᶜ inrᶜ : ∀ {n} → Ty m → Ty m → Purity → Tm S m n
  fstᶜ A B π = lam (A * B) Many π (fst v0)
  sndᶜ A B π = lam (A * B) Many π (snd v0)
  inlᶜ A B π = lam A Many π (inl B v0)
  inrᶜ A B π = lam B Many π (inr A v0)

  applyᶜ : ∀ {n} → Ty m → Ty m → Tm S m n
  applyᶜ A B = lam ((A ⇒[ mk-kind Many pure ] B) * A) Many pure (app (fst v0) (snd v0))

  inᶜ outᶜ : ∀ {n} → Fun m → Tm S m n
  inᶜ  F = lam (⟦ F ⟧F (μ F)) Many pure (roll F v0)
  outᶜ F = lam (ν F pure) Many pure (out v0)

  -- `compose f g` = f ∘ g: `f` evaluated first, `g` applied first.
  composeᶜ : ∀ {n} → Ty m → Purity → Tm S m n → Tm S m n → Tm S m n
  composeᶜ A π f g = let′ One f (let′ Many (wk g) (lam A Many π (app v2 (app v1 v0))))

  -- `⟨ f , g ⟩`: the arrow runs both arms, left first.
  pairᶜ : ∀ {n} → Ty m → Purity → Tm S m n → Tm S m n → Tm S m n
  pairᶜ A π f g = let′ One f (let′ One (wk g) (lam A Many π (pair (app v2 v0) (app v1 v0))))

  -- `[ f , g ]`.
  caseᶜ : ∀ {n} → Ty m → Ty m → Purity → Tm S m n → Tm S m n → Tm S m n
  caseᶜ A B π f g =
    let′ One f (let′ One (wk g) (lam (A + B) Many π (case Many Many v0 (app v3 v0) (app v2 v0))))

  -- `curry f`: building the closure runs nothing; the body's effect rides the
  -- inner arrow.
  curryᶜ : ∀ {n} → Ty m → Ty m → Purity → Purity → Tm S m n → Tm S m n
  curryᶜ A B π₀ π f = let′ One f (lam A Many π₀ (lam B Many π (app v2 (pair v1 v0))))

  -- `cata alg`: the algebra is evaluated once.
  cataᶜ : ∀ {n} → Fun m → Purity → Tm S m n → Tm S m n
  cataᶜ F π alg = let′ Many alg (lam (μ F) Many π (fold F v1 v0))

  -- `ana coalg` into `ν F`: the stream stores the coalgebra.
  anaᶜ : ∀ {n} → Fun m → Ty m → Purity → Tm S m n → Tm S m n
  anaᶜ F A π₀ c = lam A Many π₀ (unfold F (wk c) v0)

  -- Applying an effectful arrow builds a suspension `Unit ⇒[ π ] B`; the head
  -- and the argument are evaluated when it runs.
  effAppᶜ : ∀ {n} → Purity → Tm S m n → Tm S m n → Tm S m n
  effAppᶜ π f x = lam Unit Many π (app (wk f) (wk x))

  applyEffᶜ : ∀ {n} → Purity → Ty m → Ty m → Tm S m n
  applyEffᶜ π A B = lam ((A ⇒[ mk-kind Many π ] B) * A) Many pure (lam Unit Many π (app (fst v1) (snd v1)))

  outEffᶜ : ∀ {n} → Purity → Fun m → Tm S m n
  outEffᶜ π F = lam (ν F π) Many pure (lam Unit Many π (out v1))
