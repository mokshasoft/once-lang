{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Derived — the categorical combinators, as λ-terms.
--
-- Each combinator a program writes is a term of the core, so its meaning is
-- derived, never listed. A combinator's arms are evaluated once, left to
-- right (by `let`), and the arrow it builds runs them at each application.
-- Usage is standard QTT: an arm costs its usage scaled by how often the
-- arrow it builds consumes it — `compose f g`'s inner arm sits in `f`'s
-- argument, so it costs `ω·Ψg`. Each takes the types it is used at (a core
-- term determines its type).
------------------------------------------------------------------------

module Once.Spec.Core.Derived where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (zero; suc)
open import Once.Spec.Grade using (Purity; pure; act; eff; fin; pureᶠ; actᶠ; mk-kind; One; Many)
open import Once.Spec.Type
  using (Ty; var; Fun; K; Id; _⊕_; _⊗_; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; ⟦_⟧F; μ; ν;
         _⟨_⟩; _⟨_⟩F; at₀; shiftᵗ)
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
  outᶜ F = lam (ν F pureᶠ) Many pure (out v0)

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

  -- `ana round` into `Eff`: the loop; the round is evaluated once.
  loopᶜ : ∀ {n} → Ty m → Tm S m n → Tm S m n
  loopᶜ A c = let′ Many c (lam A Many eff (iter v1 v0))

  -- `ana coalg` into `ν F`: the stream stores the coalgebra.
  anaᶜ : ∀ {n} → Fun m → Ty m → Purity → Tm S m n → Tm S m n
  anaᶜ F A π₀ c = lam A Many π₀ (unfold F (wk c) v0)

  -- `map T f`: a type is a functor in its 0th variable, and `map T f : T⟨A⟩ → T⟨B⟩`
  -- is its action on an EFFECT-FREE arrow `f : A → B`, by the type's structure
  -- (plan 0.79 D4; docs/decisions/language.md). Running an effectful `f` across
  -- a structure is a traversal, and a tree has several lawful ones: library
  -- code, not this. `f` is evaluated once. The variable itself is `f`, another
  -- variable or a base type is left alone, a product and a sum go by their
  -- parts, `μ` is the fold that maps each layer, `ν` the unfold that maps each
  -- forced layer, and an arrow is post-composed (when the variable is not in
  -- its domain, the only case it types).
  --
  -- Its body, from `A` to `B` (`h` the arrow, `x` a value of `T⟨A⟩`: a
  -- variable or its projections), and one layer of `G` (the constants mapped,
  -- the recursive positions `R` kept), named so they can be reasoned about.
  mutual
    mapAtᶜ : ∀ {n} → Ty m → Ty m → Ty (suc m) → Tm S m n → Tm S m n → Tm S m n
    mapAtᶜ A B (var zero)    h x = app h x
    mapAtᶜ A B (var (suc i)) h x = x
    mapAtᶜ A B Unit          h x = x
    mapAtᶜ A B Void          h x = x
    mapAtᶜ A B Int           h x = x
    mapAtᶜ A B Float         h x = x
    mapAtᶜ A B (T₁ * T₂)     h x = pair (mapAtᶜ A B T₁ h (fst x)) (mapAtᶜ A B T₂ h (snd x))
    mapAtᶜ A B (T₁ + T₂)     h x = case Many Many x (inl (T₂ ⟨ at₀ B ⟩) (mapAtᶜ A B T₁ (wk h) v0))
                                                    (inr (T₁ ⟨ at₀ B ⟩) (mapAtᶜ A B T₂ (wk h) v0))
    mapAtᶜ A B (T₁ ⇒[ mk-kind q π ] T₂) h x =
      lam (T₁ ⟨ at₀ A ⟩) q π (let′ Many (app (wk x) v0) (mapAtᶜ A B T₂ (wk (wk h)) v0))
    mapAtᶜ A B (μ G) h x =
      fold (G ⟨ at₀ A ⟩F)
           (lam (⟦ G ⟨ at₀ A ⟩F ⟧F (μ (G ⟨ at₀ B ⟩F))) Many pure
                (roll (G ⟨ at₀ B ⟩F) (mapLayerᶜ A B (μ (G ⟨ at₀ B ⟩F)) G (wk h) v0))) x
    mapAtᶜ A B (ν G f) h x =
      unfold (G ⟨ at₀ B ⟩F)
             (lam (ν (G ⟨ at₀ A ⟩F) f) Many (fin f)
                  (let′ One (out v0) (mapLayerᶜ A B (ν (G ⟨ at₀ A ⟩F) f) G (wk (wk h)) v0))) x

    mapLayerᶜ : ∀ {n} → Ty m → Ty m → Ty m → Fun (suc m) → Tm S m n → Tm S m n → Tm S m n
    mapLayerᶜ A B R (K C)   h y = mapAtᶜ A B C h y
    mapLayerᶜ A B R Id      h y = y
    mapLayerᶜ A B R (F ⊕ G) h y = case Many Many y (inl (⟦ G ⟨ at₀ B ⟩F ⟧F R) (mapLayerᶜ A B R F (wk h) v0))
                                                   (inr (⟦ F ⟨ at₀ B ⟩F ⟧F R) (mapLayerᶜ A B R G (wk h) v0))
    mapLayerᶜ A B R (F ⊗ G) h y = pair (mapLayerᶜ A B R F h (fst y)) (mapLayerᶜ A B R G h (snd y))

  mapᶜ : ∀ {n} → Ty (suc m) → Ty m → Ty m → Tm S m n → Tm S m n
  mapᶜ T A B f = let′ Many f (lam (T ⟨ at₀ A ⟩) Many pure (mapAtᶜ A B T v1 v0))

  -- `F`'s own action on arrows, one layer: `map` at `⟦ F ⟧F x`, the recursive
  -- position as the variable (what the fold and unfold laws are stated with).
  layerᶜ : ∀ {n} → Fun m → Ty m → Ty m → Tm S m n → Tm S m n
  layerᶜ F A B f = mapᶜ (⟦ F ⟨ shiftᵗ ⟩F ⟧F (var zero)) A B f

  -- Applying an effectful arrow builds a suspension `Unit ⇒[ π ] B`; the head
  -- and the argument are evaluated when it runs.
  effAppᶜ : ∀ {n} → Purity → Tm S m n → Tm S m n → Tm S m n
  effAppᶜ π f x = lam Unit Many π (app (wk f) (wk x))

  applyEffᶜ : ∀ {n} → Purity → Ty m → Ty m → Tm S m n
  applyEffᶜ π A B = lam ((A ⇒[ mk-kind Many π ] B) * A) Many pure (lam Unit Many π (app (fst v1) (snd v1)))

  -- Forcing a stream whose layers are blocks builds a suspension.
  outActᶜ : ∀ {n} → Fun m → Tm S m n
  outActᶜ F = lam (ν F actᶠ) Many pure (lam Unit Many act (out v1))
