-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Stream — effectful streams: the final coalgebra of `T ∘ F`.
--
-- INTERNAL (D333). A stream `νᵈ F` is forced to a computation of a layer; `anaᵈ` unfolds
-- a Kleisli coalgebra `A → T (F A)`, running it once per forced layer;
-- `in-νᵈ` wraps a layer already at hand; `seqF` sequences a layer of
-- computations (what a fold runs). Every corecursive call sits under the
-- copattern, so productivity is checked.
------------------------------------------------------------------------

module Once.Internal.Stream where

open import Once.Spec.Type using (Fun)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Once.Spec.Type using (K; Id; _⊕_; _⊗_)
open import Once.Internal.Trace using (T; ret; call; halt; returnT; fmapT; _>>=T_)
open import Once.Spec.Word using (Carrier)
open import Once.Internal.Value Carrier Carrier using (⟦_⟧F; coerce-ν-in)
open import Once.Spec.Polynomial using (SFunctor; SId; SK; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Internal.FunctorMeaning using (translateF)

------------------------------------------------------------------------
-- The effectful greatest fixed point.
--
-- `νS`'s layer is a value; `νᵈ`'s is a COMPUTATION. That single `T` is the
-- whole difference, and it is what lets an anamorphism over an effectful
-- coalgebra be a value at all.
--
-- D062's rule applies to everything below: a corecursive call must sit
-- STRUCTURALLY under the guard, never be passed to a defined function. So the
-- functor maps are inlined (never `sfmap`) and the bind is unfolded by hand
-- (never `_>>=T_`). Both were checked against negative controls; each one
-- fails the termination checker when written the convenient way.
------------------------------------------------------------------------

record νᵈ (F : SFunctor) : Set where
  coinductive
  field
    forceᵈ : T (⟦ F ⟧SF (νᵈ F))

open νᵈ

-- `in-νᵈ` — THE MISSING INTRODUCTION FORM (plan 0.93).
--
-- A `νᵈ` IS what forcing gives (the record has one field), so wrapping an
-- ALREADY-AVAILABLE layer is a copattern and nothing more. Forcing emits `[]`
-- and hands the layer back UNCHANGED at every budget: there is nothing left to
-- compute, which is exactly the difference from `anaᵈ`, whose budget-dependence
-- comes from running the coalgebra.
--
-- WHY IT HAS TO EXIST, rather than reusing `injectν`. `injectν` maps itself
-- over the children (`mapInjectν`, below), and its children come from the PURE
-- model `νS` — so a child's events are gone. That is fine for `inject`, whose
-- job is to lift a trace-free value. It is WRONG for `in-ν`, whose children are
-- already `νᵈ` values that force themselves: mapping over them would discard
-- the very events the machine will emit. `in-νᵈ` keeps them.
--
-- Symmetric with `Ana` (D179): both BUILD a suspension and emit NOTHING; the
-- events come at `Out`, when a layer is forced. `in-νᵈ` does even less than
-- `anaᵈ` — no recursive call, so no guardedness obligation at all — and
-- `forceᵈ (in-νᵈ l) ≡ ([] , l)` is the Lambek round trip `Out ∘ in-ν ≡ id`,
-- definitionally.
in-νᵈ : ∀ {F} → ⟦ F ⟧SF (νᵈ F) → νᵈ F
forceᵈ (in-νᵈ layer) = ret layer

-- Sequence a functor layer of COMPUTATIONS into a computation of a layer.
--
-- This is what lets a `Cata` share ONE budget across a layer instead of
-- handing every child the full `n` and concatenating: the threading is
-- `_>>=T_`'s, so `bounded` holds by construction rather than by a bespoke
-- argument. Same reason `events-Fᵇ` replaced `events-F` on the ana side —
-- except here the layer is already monadic, so the traversal IS the fix.
seqF : ∀ {m} (G : Fun m) {X : Set} → ⟦ G ⟧F (T X) → T (⟦ G ⟧F X)
seqF (K A)   x        = returnT x
seqF Id      m        = m
seqF (G ⊕ H) (inj₁ x) = fmapT inj₁ (seqF G x)
seqF (G ⊕ H) (inj₂ y) = fmapT inj₂ (seqF H y)
seqF (G ⊗ H) (x , y)  = seqF G x >>=T λ u → seqF H y >>=T λ v → returnT (u , v)

-- The effectful anamorphism: `sem-ana` with the coalgebra's step made a
-- COMPUTATION. Forcing a layer runs the coalgebra once and emits exactly that
-- layer's events; the children are suspensions and emit nothing until they are
-- forced in turn. So the trace order is the order the program FORCES layers —
-- there is no traversal chosen here, which is the whole point.
mutual
  anaᵈ : ∀ (H : SFunctor) {A : Set} → (A → T (⟦ H ⟧SF A)) → A → νᵈ H
  -- plan 0.97: the layer's VALUE no longer reads the budget — that is the
  -- lens property showing up at the one place that used to thread it — and a
  -- coalgebra that stops makes the forced layer stop.
  -- plan 0.98: the flag and the value are ONE `Res`, so "the coalgebra stopped"
  -- and "there is no layer" stop being two facts that could disagree.
  -- The layer map is NAMED and applied directly, not handed to `mapRes` as a
  -- partial application: `mapAnaᵈ H H coalg` passed to a higher-order function
  -- is opaque to the termination checker, which then cannot see that the
  -- corecursive call sits under a constructor.
  -- plan 0.105: forcing a layer RUNS the coalgebra's computation — its calls,
  -- in order — and its result's children become suspensions. The map over the
  -- tree is written by hand (structural on the inductive tree), never as
  -- `fmapT`, so the corecursive call stays visibly guarded (D062).
  forceᵈ (anaᵈ H coalg a) = anaTree H coalg (coalg a)

  anaTree : ∀ (H : SFunctor) {A : Set}
          → (A → T (⟦ H ⟧SF A)) → T (⟦ H ⟧SF A) → T (⟦ H ⟧SF (νᵈ H))
  anaTree H coalg (ret l)      = ret (mapAnaᵈ H H coalg l)
  anaTree H coalg (call o a k) = call o a (λ b → anaTree H coalg (k b))
  anaTree H coalg (halt o a)   = halt o a

  mapAnaᵈ : ∀ (H G : SFunctor) {A : Set}
          → (A → T (⟦ H ⟧SF A)) → ⟦ G ⟧SF A → ⟦ G ⟧SF (νᵈ H)
  mapAnaᵈ H (SK B)     coalg x        = x
  mapAnaᵈ H SId        coalg a        = anaᵈ H coalg a
  mapAnaᵈ H (G₁ S⊕ G₂) coalg (inj₁ x) = inj₁ (mapAnaᵈ H G₁ coalg x)
  mapAnaᵈ H (G₁ S⊕ G₂) coalg (inj₂ y) = inj₂ (mapAnaᵈ H G₂ coalg y)
  mapAnaᵈ H (G₁ S⊗ G₂) coalg (x , y)  = (mapAnaᵈ H G₁ coalg x , mapAnaᵈ H G₂ coalg y)

-- Erasure round-trip, functor index only. Matching `heq` to `refl` reduces it
-- to "the two coalgebras are the same function" — which is what the coalgebra
-- IH gives. No bisimulation and no axiom, because `anaᵈ` is indexed by the


-- The Functor-level form the IR and surface clauses actually call: coerce the
-- layer at the boundary, then unfold.
anaFᵈ : ∀ {m} (F : Fun m) {A : Set}
      → (A → T (⟦ F ⟧F A)) → A → νᵈ (translateF Carrier Carrier F)
anaFᵈ F {A} coalg = anaᵈ (translateF Carrier Carrier F) (λ a → fmapT (coerce-ν-in F A) (coalg a))

