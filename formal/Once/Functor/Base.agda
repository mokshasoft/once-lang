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

------------------------------------------------------------------------
-- Bisimulation for Coinductive Types
--
-- To prove properties of coinductive values, we need bisimulation rather
-- than induction. Two νS F values are bisimilar if they produce the same
-- observations at every level.
------------------------------------------------------------------------

-- | Relational interpretation of semantic functors
--
-- Lifts a relation R : A → B → Set through functor structure.
-- Two F-structures are related if corresponding parts are related.
--
⟦_⟧SF-rel : (F : SFunctor) {A B : Set} (R : A → B → Set)
          → ⟦ F ⟧SF A → ⟦ F ⟧SF B → Set
⟦ SK _ ⟧SF-rel R x y = x ≡ y
⟦ SId ⟧SF-rel R x y = R x y
⟦ F S⊕ G ⟧SF-rel R (inj₁ x) (inj₁ y) = ⟦ F ⟧SF-rel R x y
⟦ F S⊕ G ⟧SF-rel R (inj₁ _) (inj₂ _) = ⊥
⟦ F S⊕ G ⟧SF-rel R (inj₂ _) (inj₁ _) = ⊥
⟦ F S⊕ G ⟧SF-rel R (inj₂ x) (inj₂ y) = ⟦ G ⟧SF-rel R x y
⟦ F S⊗ G ⟧SF-rel R (x₁ , x₂) (y₁ , y₂) = ⟦ F ⟧SF-rel R x₁ y₁ × ⟦ G ⟧SF-rel R x₂ y₂

-- | Bisimulation relation on νS F (coinductive)
--
-- Two coinductive values are bisimilar if their unfoldings are related
-- through the relational interpretation, with bisimilarity at recursive positions.
--
record _∼S_ {F : SFunctor} (x y : νS F) : Set where
  coinductive
  field
    unfoldS-∼ : ⟦ F ⟧SF-rel (_∼S_ {F}) (unfoldS x) (unfoldS y)

open _∼S_

-- | Bisimulation implies equality (coalgebraic extensionality)
--
-- This is a standard principle in coalgebra theory: bisimilar values are equal.
-- In Cubical Agda this can be proven; in standard Agda we postulate it.
--
-- This is a more principled postulate than anaS-Out-id directly, as it
-- captures a general mathematical fact rather than a specific property.
--
postulate
  bisimS-to-eq : ∀ {F : SFunctor} (x y : νS F) → x ∼S y → x ≡ y

-- | sfmap preserves relational structure
--
-- If R relates recursive positions, then sfmap lifts R through F.
--
sfmap-rel : ∀ F {A B : Set} {R : A → B → Set} {f : A → A} {g : B → B}
          → (∀ a b → R a b → R (f a) (g b))
          → ∀ x y → ⟦ F ⟧SF-rel R x y → ⟦ F ⟧SF-rel R (sfmap F f x) (sfmap F g y)
sfmap-rel (SK _) pres x y r = r
sfmap-rel SId pres x y r = pres x y r
sfmap-rel (F S⊕ G) pres (inj₁ x) (inj₁ y) r = sfmap-rel F pres x y r
sfmap-rel (F S⊕ G) pres (inj₂ x) (inj₂ y) r = sfmap-rel G pres x y r
sfmap-rel (F S⊗ G) pres (x₁ , x₂) (y₁ , y₂) (r₁ , r₂) =
  sfmap-rel F pres x₁ y₁ r₁ , sfmap-rel G pres x₂ y₂ r₂

-- | sfmap f relates to identity when f relates to identity
--
-- If (f a) R a for all a, then (sfmap F f x) R-lifted x.
-- This is the key lemma for proving anaS unfoldS ∼S id.
--
sfmap-f-rel : ∀ F {A : Set} {R : A → A → Set} {f : A → A}
            → (∀ a → R (f a) a)
            → ∀ x → ⟦ F ⟧SF-rel R (sfmap F f x) x
sfmap-f-rel (SK _) hyp x = refl
sfmap-f-rel SId hyp x = hyp x
sfmap-f-rel (F S⊕ G) hyp (inj₁ x) = sfmap-f-rel F hyp x
sfmap-f-rel (F S⊕ G) hyp (inj₂ x) = sfmap-f-rel G hyp x
sfmap-f-rel (F S⊗ G) hyp (x₁ , x₂) = sfmap-f-rel F hyp x₁ , sfmap-f-rel G hyp x₂

------------------------------------------------------------------------
-- Identity Anamorphism (Proven via Bisimulation)
------------------------------------------------------------------------

-- | anaS unfoldS is bisimilar to id (coinductive proof)
--
-- Proof by coinduction:
--   unfoldS (anaS unfoldS x) = sfmap F (anaS unfoldS) (unfoldS x)  [by ana def]
--   We need: ⟦ F ⟧SF-rel _∼S_ (sfmap F (anaS unfoldS) (unfoldS x)) (unfoldS x)
--   By sfmap-f-rel with coinductive hypothesis (anaS unfoldS y ∼S y), this holds.
--
{-# TERMINATING #-}
anaS-unfoldS-bisim : ∀ {F : SFunctor} (x : νS F) → anaS {F} unfoldS x ∼S x
unfoldS-∼ (anaS-unfoldS-bisim {F} x) = sfmap-f-rel F (anaS-unfoldS-bisim {F}) (unfoldS x)

-- | Identity anamorphism: anaS unfoldS ≡ id (PROVEN via bisimulation)
--
-- When the coalgebra is the destructor (unfoldS), anaS gives back the original value.
--
-- Proof: anaS unfoldS x ∼S x (by coinduction), then bisimS-to-eq gives equality.
--
anaS-Out-id : ∀ (F : SFunctor) (x : νS F) → anaS {F} unfoldS x ≡ x
anaS-Out-id F x = bisimS-to-eq (anaS unfoldS x) x (anaS-unfoldS-bisim x)
