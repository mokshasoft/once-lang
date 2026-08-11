------------------------------------------------------------------------
-- Once.Semantics.Coherence
--
-- Semantic coherence lemmas for OCP-0003.
--
-- This module provides PROVEN coherence lemmas that don't require postulates:
--   - Base type interpretation coherence
--   - Functor interpretation coherence
--   - fmap coherence (sem-fmap ≡ SPF.fmap)
--   - Functor laws for sem-fmap
--
-- HISTORICAL NOTE (2026-03-24):
-- This module previously contained postulates (μ-coherence, ν-coherence)
-- to relate Core's definitions to SPF. Those have been removed because:
--   1. Core.agda now has direct proofs for all key laws (WellFormedF)
--   2. The postulates were unprovable (different Agda data types)
--   3. They were not needed for any proofs outside this module
--
-- All remaining content is fully proven.
------------------------------------------------------------------------

module Once.Semantics.Coherence where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.Type using (Type; Functor; K; Id; _⊕_; _⊗_;
                               Unit; Void; Int; Float; Str; Buffer; _*_; _+_)
open import Once.Semantics.Machine using (⟦_⟧; ⟦_⟧F; sem-fmap)
import Once.SPF as SPF
open import Once.Functor.Translate using (IsBaseType; WellFormedF; ⟦_⟧-base; ⟦_⟧F-base;
                                          base-Unit; base-Void; base-Int; base-Float;
                                          base-Str; base-Buffer; base-Prod; base-Sum;
                                          wf-K; wf-Id; wf-Sum; wf-Prod)
open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Base Type Interpretation Coherence (PROVEN)
--
-- For well-formed functors (K only with base types), the base
-- interpretation ⟦_⟧-base equals the full interpretation ⟦_⟧.
------------------------------------------------------------------------

-- | For base types, the base interpretation equals the full interpretation
--
-- Proof by induction on the IsBaseType predicate.
--
base-interp-coherence : ∀ A → IsBaseType A → ⟦ ℕ ⟧-base A ≡ ⟦ A ⟧
base-interp-coherence .Unit base-Unit = refl
base-interp-coherence .Void base-Void = refl
base-interp-coherence .Int base-Int = refl
base-interp-coherence .Float base-Float = refl
base-interp-coherence .Str base-Str = refl
base-interp-coherence .Buffer base-Buffer = refl
base-interp-coherence (A * B) (base-Prod pA pB) =
  cong₂-× (base-interp-coherence A pA) (base-interp-coherence B pB)
  where
    cong₂-× : ∀ {A A' B B' : Set} → A ≡ A' → B ≡ B' → (A × B) ≡ (A' × B')
    cong₂-× refl refl = refl
base-interp-coherence (A + B) (base-Sum pA pB) =
  cong₂-⊎ (base-interp-coherence A pA) (base-interp-coherence B pB)
  where
    cong₂-⊎ : ∀ {A A' B B' : Set} → A ≡ A' → B ≡ B' → (A ⊎ B) ≡ (A' ⊎ B')
    cong₂-⊎ refl refl = refl

-- | For well-formed functors, base interpretation equals full interpretation
--
-- Proof by induction on the WellFormedF predicate.
--
functor-interp-coherence : ∀ F → WellFormedF F → ∀ X → ⟦ ℕ ⟧F-base F X ≡ ⟦ F ⟧F X
functor-interp-coherence (K A) (wf-K pA) X = base-interp-coherence A pA
functor-interp-coherence Id wf-Id X = refl
functor-interp-coherence (F ⊕ G) (wf-Sum pF pG) X =
  cong₂-⊎ (functor-interp-coherence F pF X) (functor-interp-coherence G pG X)
  where
    cong₂-⊎ : ∀ {A A' B B' : Set} → A ≡ A' → B ≡ B' → (A ⊎ B) ≡ (A' ⊎ B')
    cong₂-⊎ refl refl = refl
functor-interp-coherence (F ⊗ G) (wf-Prod pF pG) X =
  cong₂-× (functor-interp-coherence F pF X) (functor-interp-coherence G pG X)
  where
    cong₂-× : ∀ {A A' B B' : Set} → A ≡ A' → B ≡ B' → (A × B) ≡ (A' × B')
    cong₂-× refl refl = refl

------------------------------------------------------------------------
-- Functor Map Coherence (PROVEN)
--
-- Core's sem-fmap and SPF's fmap are extensionally equal.
------------------------------------------------------------------------

-- | fmap coherence: sem-fmap ≡ SPF.fmap
--
-- Both map a function over all recursive positions in a functor structure.
--
fmap-coherence : ∀ F {X Y : Set} (f : X → Y) (x : ⟦ F ⟧F X)
               → sem-fmap F f x ≡ SPF.fmap F f x
fmap-coherence (K A) f x = refl
fmap-coherence Id f x = refl
fmap-coherence (F ⊕ G) f (inj₁ x) = cong inj₁ (fmap-coherence F f x)
fmap-coherence (F ⊕ G) f (inj₂ y) = cong inj₂ (fmap-coherence G f y)
fmap-coherence (F ⊗ G) f (x , y) = cong₂ _,_ (fmap-coherence F f x) (fmap-coherence G f y)
  where
    cong₂ : ∀ {A B C : Set} (h : A → B → C) {x x' : A} {y y' : B}
          → x ≡ x' → y ≡ y' → h x y ≡ h x' y'
    cong₂ h refl refl = refl

------------------------------------------------------------------------
-- Functor Laws for sem-fmap (PROVEN)
--
-- Since sem-fmap ≡ SPF.fmap, we inherit SPF's functor laws.
------------------------------------------------------------------------

-- | sem-fmap preserves identity
--
sem-fmap-id : ∀ F {X : Set} (x : ⟦ F ⟧F X) → sem-fmap F (λ z → z) x ≡ x
sem-fmap-id F x = trans (fmap-coherence F (λ z → z) x) (SPF.fmap-id F x)

-- | sem-fmap preserves composition
--
sem-fmap-comp : ∀ F {X Y Z : Set} (f : X → Y) (g : Y → Z) (x : ⟦ F ⟧F X)
              → sem-fmap F (λ z → g (f z)) x ≡ sem-fmap F g (sem-fmap F f x)
sem-fmap-comp F f g x =
  trans step1 (trans step2 (trans step3 step4))
  where
    step1 : sem-fmap F (λ z → g (f z)) x ≡ SPF.fmap F (λ z → g (f z)) x
    step1 = fmap-coherence F (λ z → g (f z)) x

    step2 : SPF.fmap F (λ z → g (f z)) x ≡ SPF.fmap F g (SPF.fmap F f x)
    step2 = SPF.fmap-comp F f g x

    step3 : SPF.fmap F g (SPF.fmap F f x) ≡ SPF.fmap F g (sem-fmap F f x)
    step3 = cong (SPF.fmap F g) (sym (fmap-coherence F f x))

    step4 : SPF.fmap F g (sem-fmap F f x) ≡ sem-fmap F g (sem-fmap F f x)
    step4 = sym (fmap-coherence F g (sem-fmap F f x))

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------
--
-- This module provides fully PROVEN coherence lemmas:
--
-- 1. Base Type Interpretation Coherence:
--    - base-interp-coherence: ⟦ ℕ ⟧-base A ≡ ⟦ A ⟧ for IsBaseType A
--    - functor-interp-coherence: ⟦ ℕ ⟧F-base F X ≡ ⟦ F ⟧F X for WellFormedF F
--
-- 2. Functor Map Coherence:
--    - fmap-coherence: sem-fmap F f x ≡ SPF.fmap F f x
--
-- 3. Functor Laws:
--    - sem-fmap-id: sem-fmap F id ≡ id
--    - sem-fmap-comp: sem-fmap F (g ∘ f) ≡ sem-fmap F g ∘ sem-fmap F f
--
-- The primary recursion scheme proofs are in Once.Semantics.Value:
--    - sem-Out-In, sem-In-Out (Lambek's Lemma)
--    - sem-cata-compute, sem-cata-In-id (catamorphism laws)
--    - sem-ana-Out-id (identity anamorphism)
--
-- All proofs require WellFormedF for the functor.
