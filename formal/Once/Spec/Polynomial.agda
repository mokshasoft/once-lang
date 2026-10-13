-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Polynomial — the polynomial functors on sets, their initial
-- algebras and their final coalgebras.
--
-- SPEC. A code `SFunctor` is a polynomial: constants (a set), the identity,
-- sums and products; `⟦ F ⟧SF` is the functor it denotes and `sfmap` its
-- action. `μS F` is the initial algebra (`⟨_⟩`, `outS`) with its fold
-- `cataS`; `νS F` is the final coalgebra of `Res ∘ ⟦ F ⟧SF` — a stream that
-- may end — with its unfold `anaS`. Every corecursive call sits under the
-- copattern, so productivity is checked, not assumed.
------------------------------------------------------------------------

module Once.Spec.Polynomial where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.Spec.Res using (Res; stopped; returns)


------------------------------------------------------------------------
-- Semantic Functor (Set-level)
--
-- Unlike Once.Spec.Type.Functor where K takes a Type, here K takes a Set
-- directly. This breaks the dependency on the type interpretation.
------------------------------------------------------------------------

-- | Semantic functor codes
--
-- These represent polynomial functors at the Set level.
-- K takes a Set directly, not a Type.
--
data SFunctor : Set₁ where
  SK   : Set → SFunctor              -- Constant (takes Set directly)
  SId  : SFunctor                    -- Recursive position
  _S⊕_ : SFunctor → SFunctor → SFunctor  -- Sum
  _S⊗_ : SFunctor → SFunctor → SFunctor  -- Product

infixr 30 _S⊕_
infixr 40 _S⊗_

------------------------------------------------------------------------
-- Functor Interpretation
------------------------------------------------------------------------

-- | Interpret semantic functor as Set → Set
--
⟦_⟧SF : SFunctor → Set → Set
⟦ SK A ⟧SF X = A           -- A is already a Set!
⟦ SId ⟧SF X = X            -- Recursive position
⟦ F S⊕ G ⟧SF X = ⟦ F ⟧SF X ⊎ ⟦ G ⟧SF X
⟦ F S⊗ G ⟧SF X = ⟦ F ⟧SF X × ⟦ G ⟧SF X

------------------------------------------------------------------------
-- Functorial Map
------------------------------------------------------------------------

-- | Functorial map for semantic functors
--
sfmap : ∀ F → {X Y : Set} → (X → Y) → ⟦ F ⟧SF X → ⟦ F ⟧SF Y
sfmap (SK A) f x = x
sfmap SId f x = f x
sfmap (F S⊕ G) f (inj₁ x) = inj₁ (sfmap F f x)
sfmap (F S⊕ G) f (inj₂ y) = inj₂ (sfmap G f y)
sfmap (F S⊗ G) f (x , y) = (sfmap F f x , sfmap G f y)

------------------------------------------------------------------------
-- Fixed Points
------------------------------------------------------------------------

-- | Initial algebra (least fixed point)
--
-- μS F represents the least fixed point of F.
-- μS F ≅ ⟦ F ⟧SF (μS F)
--
data μS (F : SFunctor) : Set where
  ⟨_⟩ : ⟦ F ⟧SF (μS F) → μS F

-- | Destructor for μS
outS : ∀ (F : SFunctor) → μS F → ⟦ F ⟧SF (μS F)
outS F ⟨ x ⟩ = x

-- | Greatest fixed point (coinductive)
--
-- plan 0.98: the layer is a `Res`, so `νS` is the final coalgebra of
-- `Res ∘ ⟦ F ⟧SF` — a POSSIBLY-FINITE stream rather than an infinite one.
--
-- WHY. `forget : ⟦A⟧ᴰ → Val.⟦A⟧` erases the monadic domain to this one, and
-- it must erase exactly ONE thing: the TRACE. Partiality is not a trace fact
-- — "does this unfold produce another layer?" is a fact about the VALUE — so
-- if `νᵈ` can stop (an `Ana` whose coalgebra reaches a halting SigOp) and
-- `νS` cannot, then no total erasure between them exists. Making the two
-- domains differ by the trace ALONE is what makes `forget` total by
-- construction instead of by a premise nobody can supply.
record νS (F : SFunctor) : Set where
  coinductive
  field
    unfoldS : Res (⟦ F ⟧SF (νS F))

open νS

------------------------------------------------------------------------
-- Catamorphism
------------------------------------------------------------------------

-- | Catamorphism (fold)
--
mutual
  cataS : ∀ {F} {A : Set} → (⟦ F ⟧SF A → A) → μS F → A
  cataS {F} alg ⟨ x ⟩ = alg (sfmapCata F alg x)

  sfmapCata : ∀ F {G} {A : Set} → (⟦ G ⟧SF A → A) → ⟦ F ⟧SF (μS G) → ⟦ F ⟧SF A
  sfmapCata (SK B) alg x = x
  sfmapCata SId alg x = cataS alg x
  sfmapCata (F S⊕ G) alg (inj₁ x) = inj₁ (sfmapCata F alg x)
  sfmapCata (F S⊕ G) alg (inj₂ y) = inj₂ (sfmapCata G alg y)
  sfmapCata (F S⊗ G) alg (x , y) = (sfmapCata F alg x , sfmapCata G alg y)

------------------------------------------------------------------------
-- Anamorphism
------------------------------------------------------------------------

-- | Anamorphism (unfold)
--
-- D062: guardedness-CHECKED corecursion (global `--guardedness`) — the
-- corecursive `anaS` calls are placed structurally at `SId` leaves by the
-- mutual `sfmapAna` (the coinductive dual of `cataS`'s `sfmapCata`), so Agda
-- sees the guard. No `TERMINATING` assertion: productivity is verified.
mutual
  anaS : ∀ {F} {A : Set} → (A → Res (⟦ F ⟧SF A)) → A → νS F
  unfoldS (anaS {F} coalg a) = anaLayerS F coalg (coalg a)

  -- The layer map is NAMED and applied directly rather than handed to
  -- `mapRes`: a partial application passed to a higher-order function is
  -- opaque to the termination checker, which then cannot see the corecursive
  -- call sitting under a constructor.
  anaLayerS : ∀ {F : SFunctor} (H : SFunctor) {A : Set}
            → (A → Res (⟦ F ⟧SF A)) → Res (⟦ H ⟧SF A) → Res (⟦ H ⟧SF (νS F))
  anaLayerS H coalg stopped     = stopped
  anaLayerS H coalg (returns x) = returns (sfmapAna H coalg x)

  sfmapAna : ∀ {F : SFunctor} (H : SFunctor) {A : Set}
           → (A → Res (⟦ F ⟧SF A)) → ⟦ H ⟧SF A → ⟦ H ⟧SF (νS F)
  sfmapAna (SK B)     coalg x        = x
  sfmapAna SId        coalg a        = anaS coalg a
  sfmapAna (H₁ S⊕ H₂) coalg (inj₁ x) = inj₁ (sfmapAna H₁ coalg x)
  sfmapAna (H₁ S⊕ H₂) coalg (inj₂ y) = inj₂ (sfmapAna H₂ coalg y)
  sfmapAna (H₁ S⊗ H₂) coalg (x , y)  = (sfmapAna H₁ coalg x , sfmapAna H₂ coalg y)
