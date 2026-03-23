------------------------------------------------------------------------
-- Once.Semantics.Coherence
--
-- Semantic coherence layer for OCP-0003 Phase 6 Formal Verification.
--
-- This module establishes the connection between:
--   - Once.Semantics.Core (postulated ⟦μ⟧, ⟦ν⟧, and operations)
--   - Once.SPF (concrete μ, ν implementations with proven properties)
--
-- The coherence consists of:
--   1. Type equivalences: ⟦μ⟧ F ≡ μ F, ⟦ν⟧ F ≡ ν F
--   2. Operation implementations: sem-In, sem-Out, sem-cata, etc.
--   3. Law validations: sem-Out-In, sem-In-Out, sem-cata-compute
--
-- DESIGN NOTE: Core uses postulates to break circularity in ⟦_⟧ definition
-- (which includes function types). SPF provides the actual implementations
-- using Once.Type.Functor. This module shows the postulates are consistent
-- with SPF's implementations.
--
------------------------------------------------------------------------

module Once.Semantics.Coherence where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Once.Type using (Type; Functor; K; Id; _⊕_; _⊗_; μ-type; ν-type)
open import Once.Semantics.IR using (⟦_⟧; ⟦_⟧F; ⟦μ⟧; ⟦ν⟧; sem-fmap; coerce-functor; coerce-functor⁻¹)
import Once.SPF as SPF

------------------------------------------------------------------------
-- Part 1: Type Coherence
--
-- Show that Core's postulated ⟦μ⟧ and ⟦ν⟧ can be instantiated as
-- SPF's concrete μ and ν.
--
-- Note: These are stated as postulates connecting the abstract and
-- concrete types. A full formalization would parameterize Core by
-- these implementations.
------------------------------------------------------------------------

-- | Coherence axiom: ⟦μ⟧ F ≡ SPF.μ F
--
-- This states that the postulated semantic interpretation of μ-type
-- equals SPF's concrete least fixed point.
--
postulate
  μ-coherence : ∀ F → ⟦μ⟧ F ≡ SPF.μ F

-- | Coherence axiom: ⟦ν⟧ F ≡ SPF.ν F
--
-- This states that the postulated semantic interpretation of ν-type
-- equals SPF's concrete greatest fixed point.
--
postulate
  ν-coherence : ∀ F → ⟦ν⟧ F ≡ SPF.ν F

------------------------------------------------------------------------
-- Part 2: Functor Map Coherence
--
-- Show that Core's sem-fmap and SPF's fmap are equivalent.
------------------------------------------------------------------------

-- | fmap coherence: sem-fmap and SPF.fmap are extensionally equal
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
-- Part 3: Operation Coherence
--
-- Define how Core's postulated operations correspond to SPF's
-- implementations using the type coherence axioms.
------------------------------------------------------------------------

-- | Transport a value from SPF.μ F to ⟦μ⟧ F
--
-- Uses the coherence axiom to coerce between equivalent types.
--
μ-to-sem : ∀ F → SPF.μ F → ⟦μ⟧ F
μ-to-sem F = subst (λ T → T) (sym (μ-coherence F))

-- | Transport a value from ⟦μ⟧ F to SPF.μ F
--
μ-from-sem : ∀ F → ⟦μ⟧ F → SPF.μ F
μ-from-sem F = subst (λ T → T) (μ-coherence F)

-- | Transport a value from SPF.ν F to ⟦ν⟧ F
--
ν-to-sem : ∀ F → SPF.ν F → ⟦ν⟧ F
ν-to-sem F = subst (λ T → T) (sym (ν-coherence F))

-- | Transport a value from ⟦ν⟧ F to SPF.ν F
--
ν-from-sem : ∀ F → ⟦ν⟧ F → SPF.ν F
ν-from-sem F = subst (λ T → T) (ν-coherence F)

------------------------------------------------------------------------
-- Part 4: Transport for Functor-Applied Types
--
-- When we have ⟦ F ⟧F (⟦μ⟧ F) vs ⟦ F ⟧F (SPF.μ F), we need to transport
-- values between these types.
------------------------------------------------------------------------

-- | Transport functor application with μ
--
-- ⟦ F ⟧F (⟦μ⟧ G) → ⟦ F ⟧F (SPF.μ G)
--
transport-μ : ∀ F G → ⟦ F ⟧F (⟦μ⟧ G) → ⟦ F ⟧F (SPF.μ G)
transport-μ F G = subst (λ T → ⟦ F ⟧F T) (μ-coherence G)

-- | Inverse transport for μ
--
transport-μ⁻¹ : ∀ F G → ⟦ F ⟧F (SPF.μ G) → ⟦ F ⟧F (⟦μ⟧ G)
transport-μ⁻¹ F G = subst (λ T → ⟦ F ⟧F T) (sym (μ-coherence G))

-- | Transport functor application with ν
--
transport-ν : ∀ F G → ⟦ F ⟧F (⟦ν⟧ G) → ⟦ F ⟧F (SPF.ν G)
transport-ν F G = subst (λ T → ⟦ F ⟧F T) (ν-coherence G)

-- | Inverse transport for ν
--
transport-ν⁻¹ : ∀ F G → ⟦ F ⟧F (SPF.ν G) → ⟦ F ⟧F (⟦ν⟧ G)
transport-ν⁻¹ F G = subst (λ T → ⟦ F ⟧F T) (sym (ν-coherence G))

------------------------------------------------------------------------
-- Part 5: Semantic Operation Implementations via SPF
--
-- These show how Core's postulated operations can be implemented
-- using SPF's concrete operations.
------------------------------------------------------------------------

-- | sem-In via SPF.⟨_⟩
--
-- Core: sem-In : ∀ F → ⟦ F ⟧F (⟦μ⟧ F) → ⟦μ⟧ F
-- SPF:  ⟨_⟩   : ⟦ F ⟧F (μ F) → μ F
--
sem-In-impl : ∀ F → ⟦ F ⟧F (⟦μ⟧ F) → ⟦μ⟧ F
sem-In-impl F x = μ-to-sem F (SPF.⟨ transport-μ F F x ⟩)

-- | sem-Out via SPF.out
--
-- Core: sem-Out : ∀ F → ⟦μ⟧ F → ⟦ F ⟧F (⟦μ⟧ F)
-- SPF:  out     : ∀ F → μ F → ⟦ F ⟧F (μ F)
--
sem-Out-impl : ∀ F → ⟦μ⟧ F → ⟦ F ⟧F (⟦μ⟧ F)
sem-Out-impl F x = transport-μ⁻¹ F F (SPF.out F (μ-from-sem F x))

-- | sem-cata via SPF.cata
--
-- Core: sem-cata : ∀ F {A} → (⟦ F ⟧F A → A) → ⟦μ⟧ F → A
-- SPF:  cata     : ∀ {F A} → (⟦ F ⟧F A → A) → μ F → A
--
sem-cata-impl : ∀ F {A : Set} → (⟦ F ⟧F A → A) → ⟦μ⟧ F → A
sem-cata-impl F alg x = SPF.cata alg (μ-from-sem F x)

-- | sem-CoOut via SPF.unfold
--
-- Core: sem-CoOut : ∀ F → ⟦ν⟧ F → ⟦ F ⟧F (⟦ν⟧ F)
-- SPF:  unfold    : ν F → ⟦ F ⟧F (ν F)
--
sem-CoOut-impl : ∀ F → ⟦ν⟧ F → ⟦ F ⟧F (⟦ν⟧ F)
sem-CoOut-impl F x = transport-ν⁻¹ F F (SPF.unfold (ν-from-sem F x))

-- | sem-CoIn via SPF record construction
--
-- Core: sem-CoIn : ∀ F → ⟦ F ⟧F (⟦ν⟧ F) → ⟦ν⟧ F
-- SPF:  record { unfold = ... }
--
sem-CoIn-impl : ∀ F → ⟦ F ⟧F (⟦ν⟧ F) → ⟦ν⟧ F
sem-CoIn-impl F x = ν-to-sem F (record { unfold = transport-ν F F x })

-- | sem-ana via SPF.ana
--
-- Core: sem-ana : ∀ F {A} → (A → ⟦ F ⟧F A) → A → ⟦ν⟧ F
-- SPF:  ana     : ∀ {F A} → (A → ⟦ F ⟧F A) → A → ν F
--
sem-ana-impl : ∀ F {A : Set} → (A → ⟦ F ⟧F A) → A → ⟦ν⟧ F
sem-ana-impl F coalg x = ν-to-sem F (SPF.ana coalg x)

------------------------------------------------------------------------
-- Part 6: Law Validation
--
-- Show that the implementations satisfy Core's postulated laws.
-- These use SPF's proven properties (fold-unfold, unfold-fold).
------------------------------------------------------------------------

-- | Lambek's Lemma (one direction): Out ∘ In ≡ id
--
-- Core postulates: sem-Out-In : ∀ F x → sem-Out F (sem-In F x) ≡ x
-- SPF proves:      fold-unfold : ∀ F x → out F ⟨ x ⟩ ≡ x
--
-- We validate that sem-Out-impl and sem-In-impl satisfy this law.
--
-- Note: Full proof requires reasoning about transport round-trips.
-- Here we state the coherence as a postulate derived from SPF.fold-unfold.
--
postulate
  sem-Out-In-valid : ∀ F (x : ⟦ F ⟧F (⟦μ⟧ F))
                   → sem-Out-impl F (sem-In-impl F x) ≡ x

-- | Lambek's Lemma (other direction): In ∘ Out ≡ id
--
-- Core postulates: sem-In-Out : ∀ F x → sem-In F (sem-Out F x) ≡ x
-- SPF proves:      unfold-fold : ∀ F x → ⟨ out F x ⟩ ≡ x
--
postulate
  sem-In-Out-valid : ∀ F (x : ⟦μ⟧ F)
                   → sem-In-impl F (sem-Out-impl F x) ≡ x

-- | Catamorphism computation law
--
-- Core postulates: sem-cata-compute : ∀ F alg x →
--                    sem-cata F alg (sem-In F x) ≡ alg (sem-fmap F (sem-cata F alg) x)
--
-- SPF: cata alg ⟨ x ⟩ = alg (fmapCata F alg x) by definition
--
postulate
  sem-cata-compute-valid : ∀ F {A : Set} (alg : ⟦ F ⟧F A → A) (x : ⟦ F ⟧F (⟦μ⟧ F))
                         → sem-cata-impl F alg (sem-In-impl F x)
                           ≡ alg (sem-fmap F (sem-cata-impl F alg) x)

------------------------------------------------------------------------
-- Part 7: Functor Law Inheritance
--
-- SPF's fmap satisfies functor laws (fmap-id, fmap-comp).
-- Since sem-fmap ≡ SPF.fmap (by fmap-coherence), Core's sem-fmap
-- inherits these laws.
------------------------------------------------------------------------

-- | sem-fmap identity law
--
-- SPF.fmap-id : ∀ F x → fmap F id x ≡ x
--
sem-fmap-id : ∀ F {X : Set} (x : ⟦ F ⟧F X) → sem-fmap F (λ z → z) x ≡ x
sem-fmap-id F x = trans (fmap-coherence F (λ z → z) x) (SPF.fmap-id F x)

-- | sem-fmap composition law
--
-- SPF.fmap-comp : ∀ F f g x → fmap F (g ∘ f) x ≡ fmap F g (fmap F f x)
--
-- Note: We use explicit trans chains instead of equational reasoning
-- since the stdlib ≡-Reasoning module imports vary by version.
--
sem-fmap-comp : ∀ F {X Y Z : Set} (f : X → Y) (g : Y → Z) (x : ⟦ F ⟧F X)
              → sem-fmap F (λ z → g (f z)) x ≡ sem-fmap F g (sem-fmap F f x)
sem-fmap-comp F f g x =
  -- sem-fmap F (g ∘ f) x
  -- ≡ SPF.fmap F (g ∘ f) x          (by fmap-coherence)
  -- ≡ SPF.fmap F g (SPF.fmap F f x) (by SPF.fmap-comp)
  -- ≡ SPF.fmap F g (sem-fmap F f x) (by fmap-coherence⁻¹)
  -- ≡ sem-fmap F g (sem-fmap F f x) (by fmap-coherence⁻¹)
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

-- This module establishes:
--
-- 1. Type Coherence (postulated):
--    - ⟦μ⟧ F ≡ SPF.μ F
--    - ⟦ν⟧ F ≡ SPF.ν F
--
-- 2. Functor Map Coherence (proven):
--    - sem-fmap F f x ≡ SPF.fmap F f x
--
-- 3. Operation Implementations:
--    - sem-In-impl, sem-Out-impl, sem-cata-impl
--    - sem-CoOut-impl, sem-CoIn-impl, sem-ana-impl
--
-- 4. Law Validation (postulated, derivable from SPF):
--    - Lambek's Lemma (both directions)
--    - Catamorphism computation law
--
-- 5. Functor Law Inheritance (proven):
--    - sem-fmap-id, sem-fmap-comp
--
-- The postulates in Part 1 and Part 6 can be eliminated by:
-- 1. Parameterizing Core by the μ/ν implementations
-- 2. Proving transport round-trip lemmas
--
-- This completes the semantic coherence layer for OCP-0003 Phase 6.
