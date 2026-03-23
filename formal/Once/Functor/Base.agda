------------------------------------------------------------------------
-- Once.Functor.Base
--
-- Base functor interpretation without dependency on full ⟦_⟧.
--
-- This module provides a functor interpretation that takes Set directly
-- in the K case, avoiding the circular dependency:
--   ⟦_⟧ → ⟦_⟧F → SPF.μ → ⟦μ⟧ → ⟦_⟧
--
-- By having K take a Set directly, we can define:
--   SPF.μ without depending on ⟦_⟧
--   Then Core can define ⟦μ⟧ = SPF.μ
--
-- OCP-0003 Phase 6: Enables proving μ-coherence.
------------------------------------------------------------------------

module Once.Functor.Base where

open import Level using (Level; 0ℓ; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

------------------------------------------------------------------------
-- Semantic Functor (Set-level)
--
-- Unlike Once.Type.Functor where K takes a Type, here K takes a Set
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
-- Functor Laws
------------------------------------------------------------------------

-- | sfmap preserves identity
sfmap-id : ∀ F {X : Set} (x : ⟦ F ⟧SF X) → sfmap F (λ z → z) x ≡ x
sfmap-id (SK A) x = refl
sfmap-id SId x = refl
sfmap-id (F S⊕ G) (inj₁ x) = cong inj₁ (sfmap-id F x)
sfmap-id (F S⊕ G) (inj₂ y) = cong inj₂ (sfmap-id G y)
sfmap-id (F S⊗ G) (x , y) = cong₂ _,_ (sfmap-id F x) (sfmap-id G y)
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B}
          → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl

-- | sfmap preserves composition
sfmap-comp : ∀ F {X Y Z : Set} (f : X → Y) (g : Y → Z) (x : ⟦ F ⟧SF X)
           → sfmap F (λ z → g (f z)) x ≡ sfmap F g (sfmap F f x)
sfmap-comp (SK A) f g x = refl
sfmap-comp SId f g x = refl
sfmap-comp (F S⊕ G) f g (inj₁ x) = cong inj₁ (sfmap-comp F f g x)
sfmap-comp (F S⊕ G) f g (inj₂ y) = cong inj₂ (sfmap-comp G f g y)
sfmap-comp (F S⊗ G) f g (x , y) = cong₂ _,_ (sfmap-comp F f g x) (sfmap-comp G f g y)
  where
    cong₂ : ∀ {A B C : Set} (h : A → B → C) {x x' : A} {y y' : B}
          → x ≡ x' → y ≡ y' → h x y ≡ h x' y'
    cong₂ h refl refl = refl

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
record νS (F : SFunctor) : Set where
  coinductive
  field
    unfoldS : ⟦ F ⟧SF (νS F)

open νS public

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
{-# TERMINATING #-}
anaS : ∀ {F} {A : Set} → (A → ⟦ F ⟧SF A) → A → νS F
unfoldS (anaS {F} coalg a) = sfmap F (anaS coalg) (coalg a)

------------------------------------------------------------------------
-- Lambek's Lemma
------------------------------------------------------------------------

-- | fold-unfold: out ∘ In = id
fold-unfoldS : ∀ (F : SFunctor) (x : ⟦ F ⟧SF (μS F)) → outS F ⟨ x ⟩ ≡ x
fold-unfoldS F x = refl

-- | unfold-fold: In ∘ out = id
unfold-foldS : ∀ (F : SFunctor) (x : μS F) → ⟨ outS F x ⟩ ≡ x
unfold-foldS F ⟨ x ⟩ = refl

------------------------------------------------------------------------
-- Catamorphism Laws
------------------------------------------------------------------------

mutual
  sfmapCata-is-sfmap : ∀ F {G} {A : Set} (alg : ⟦ G ⟧SF A → A) (x : ⟦ F ⟧SF (μS G))
                     → sfmapCata F alg x ≡ sfmap F (cataS alg) x
  sfmapCata-is-sfmap (SK B) alg x = refl
  sfmapCata-is-sfmap SId alg x = refl
  sfmapCata-is-sfmap (F S⊕ G) alg (inj₁ x) = cong inj₁ (sfmapCata-is-sfmap F alg x)
  sfmapCata-is-sfmap (F S⊕ G) alg (inj₂ y) = cong inj₂ (sfmapCata-is-sfmap G alg y)
  sfmapCata-is-sfmap (F S⊗ G) alg (x , y) =
    cong₂ _,_ (sfmapCata-is-sfmap F alg x) (sfmapCata-is-sfmap G alg y)
    where
      cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B}
            → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
      cong₂ f refl refl = refl

-- | Catamorphism computation law
cataS-computation : ∀ (F : SFunctor) {A : Set} (alg : ⟦ F ⟧SF A → A) (x : ⟦ F ⟧SF (μS F))
                  → cataS {F} alg ⟨ x ⟩ ≡ alg (sfmap F (cataS {F} alg) x)
cataS-computation F {A} alg x = cong alg (sfmapCata-is-sfmap F {F} {A} alg x)

-- | Identity catamorphism
mutual
  cataS-In-id : ∀ {F} (x : μS F) → cataS ⟨_⟩ x ≡ x
  cataS-In-id {F} ⟨ x ⟩ = cong ⟨_⟩ (sfmapCata-In-id F x)

  sfmapCata-In-id : ∀ F {G} (x : ⟦ F ⟧SF (μS G)) → sfmapCata F ⟨_⟩ x ≡ x
  sfmapCata-In-id (SK B) x = refl
  sfmapCata-In-id SId x = cataS-In-id x
  sfmapCata-In-id (F S⊕ G) (inj₁ x) = cong inj₁ (sfmapCata-In-id F x)
  sfmapCata-In-id (F S⊕ G) (inj₂ y) = cong inj₂ (sfmapCata-In-id G y)
  sfmapCata-In-id (F S⊗ G) (x , y) =
    cong₂ _,_ (sfmapCata-In-id F x) (sfmapCata-In-id G y)
    where
      cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B}
            → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
      cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Anamorphism Laws
------------------------------------------------------------------------

-- | ana-unfold (computation)
anaS-unfold : ∀ (F : SFunctor) {A : Set} (coalg : A → ⟦ F ⟧SF A) (a : A)
            → unfoldS (anaS {F} coalg a) ≡ sfmap F (anaS coalg) (coalg a)
anaS-unfold F coalg a = refl

-- | Identity anamorphism (requires coinductive proof)
postulate
  anaS-Out-id : ∀ (F : SFunctor) (x : νS F) → anaS {F} unfoldS x ≡ x
