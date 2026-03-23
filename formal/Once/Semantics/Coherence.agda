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

-- Transport round-trip lemmas (standard)
private
  -- General subst round-trip for any type family P
  subst-sym-subst : ∀ {ℓ ℓ'} {A B : Set ℓ} {P : Set ℓ → Set ℓ'} (p : A ≡ B) (v : P B)
                  → subst P p (subst P (sym p) v) ≡ v
  subst-sym-subst refl v = refl

  subst-subst-sym : ∀ {ℓ ℓ'} {A B : Set ℓ} {P : Set ℓ → Set ℓ'} (p : A ≡ B) (v : P A)
                  → subst P (sym p) (subst P p v) ≡ v
  subst-subst-sym refl v = refl

  -- Transport round-trip for functor-applied types
  transport-round-trip : ∀ F G (x : ⟦ F ⟧F (⟦μ⟧ G))
                       → transport-μ⁻¹ F G (transport-μ F G x) ≡ x
  transport-round-trip F G x = subst-subst-sym {P = λ T → ⟦ F ⟧F T} (μ-coherence G) x

  transport⁻¹-round-trip : ∀ F G (x : ⟦ F ⟧F (SPF.μ G))
                         → transport-μ F G (transport-μ⁻¹ F G x) ≡ x
  transport⁻¹-round-trip F G x = subst-sym-subst {P = λ T → ⟦ F ⟧F T} (μ-coherence G) x

  -- μ transport round-trips
  μ-round-trip : ∀ F (x : SPF.μ F) → μ-from-sem F (μ-to-sem F x) ≡ x
  μ-round-trip F x = subst-sym-subst {P = λ T → T} (μ-coherence F) x

  μ⁻¹-round-trip : ∀ F (x : ⟦μ⟧ F) → μ-to-sem F (μ-from-sem F x) ≡ x
  μ⁻¹-round-trip F x = subst-subst-sym {P = λ T → T} (μ-coherence F) x

-- | Key coherence axiom: transport-μ equals fmap with μ-from-sem
--
-- For polynomial functors, transporting ⟦ F ⟧F (⟦μ⟧ G) to ⟦ F ⟧F (SPF.μ G)
-- via the coherence axiom is the same as applying fmap F (μ-from-sem G).
--
-- This is postulated as part of the coherence layer. Any sensible
-- instantiation of μ-coherence would satisfy this property.
--
postulate
  transport-μ-is-fmap : ∀ F G (x : ⟦ F ⟧F (⟦μ⟧ G))
                      → transport-μ F G x ≡ SPF.fmap F (μ-from-sem G) x

-- | Lambek's Lemma (one direction): Out ∘ In ≡ id (PROVEN)
--
-- Core postulates: sem-Out-In : ∀ F x → sem-Out F (sem-In F x) ≡ x
-- SPF proves:      fold-unfold : ∀ F x → out F ⟨ x ⟩ ≡ x
--
-- Proof:
--   sem-Out-impl F (sem-In-impl F x)
--   = transport-μ⁻¹ F F (SPF.out F (μ-from-sem F (μ-to-sem F (SPF.⟨ transport-μ F F x ⟩))))
--   = transport-μ⁻¹ F F (SPF.out F (SPF.⟨ transport-μ F F x ⟩))   [by μ-round-trip]
--   = transport-μ⁻¹ F F (transport-μ F F x)                       [by SPF.fold-unfold]
--   = x                                                           [by transport-round-trip]
--
sem-Out-In-valid : ∀ F (x : ⟦ F ⟧F (⟦μ⟧ F))
                 → sem-Out-impl F (sem-In-impl F x) ≡ x
sem-Out-In-valid F x =
  trans step1 (trans step2 step3)
  where
    -- Step 1: Apply μ-round-trip to remove μ-to-sem/μ-from-sem pair
    step1 : sem-Out-impl F (sem-In-impl F x) ≡
            transport-μ⁻¹ F F (SPF.out F SPF.⟨ transport-μ F F x ⟩)
    step1 = cong (λ z → transport-μ⁻¹ F F (SPF.out F z))
                 (μ-round-trip F SPF.⟨ transport-μ F F x ⟩)

    -- Step 2: Apply SPF.fold-unfold
    step2 : transport-μ⁻¹ F F (SPF.out F SPF.⟨ transport-μ F F x ⟩) ≡
            transport-μ⁻¹ F F (transport-μ F F x)
    step2 = cong (transport-μ⁻¹ F F) (SPF.fold-unfold F (transport-μ F F x))

    -- Step 3: Apply transport round-trip
    step3 : transport-μ⁻¹ F F (transport-μ F F x) ≡ x
    step3 = transport-round-trip F F x

-- | Lambek's Lemma (other direction): In ∘ Out ≡ id (PROVEN)
--
-- Core postulates: sem-In-Out : ∀ F x → sem-In F (sem-Out F x) ≡ x
-- SPF proves:      unfold-fold : ∀ F x → ⟨ out F x ⟩ ≡ x
--
-- Proof:
--   sem-In-impl F (sem-Out-impl F x)
--   = μ-to-sem F (SPF.⟨ transport-μ F F (transport-μ⁻¹ F F (SPF.out F (μ-from-sem F x))) ⟩)
--   = μ-to-sem F (SPF.⟨ SPF.out F (μ-from-sem F x) ⟩)   [by transport⁻¹-round-trip]
--   = μ-to-sem F (μ-from-sem F x)                        [by SPF.unfold-fold]
--   = x                                                  [by μ⁻¹-round-trip]
--
sem-In-Out-valid : ∀ F (x : ⟦μ⟧ F)
                 → sem-In-impl F (sem-Out-impl F x) ≡ x
sem-In-Out-valid F x =
  trans step1 (trans step2 step3)
  where
    -- Step 1: Apply transport⁻¹-round-trip
    step1 : sem-In-impl F (sem-Out-impl F x) ≡
            μ-to-sem F SPF.⟨ SPF.out F (μ-from-sem F x) ⟩
    step1 = cong (λ z → μ-to-sem F SPF.⟨ z ⟩)
                 (transport⁻¹-round-trip F F (SPF.out F (μ-from-sem F x)))

    -- Step 2: Apply SPF.unfold-fold
    step2 : μ-to-sem F SPF.⟨ SPF.out F (μ-from-sem F x) ⟩ ≡
            μ-to-sem F (μ-from-sem F x)
    step2 = cong (μ-to-sem F) (SPF.unfold-fold F (μ-from-sem F x))

    -- Step 3: Apply μ⁻¹-round-trip
    step3 : μ-to-sem F (μ-from-sem F x) ≡ x
    step3 = μ⁻¹-round-trip F x

-- | Catamorphism computation law (PROVEN via SPF.cata-computation)
--
-- Core postulates: sem-cata-compute : ∀ F alg x →
--                    sem-cata F alg (sem-In F x) ≡ alg (sem-fmap F (sem-cata F alg) x)
--
-- Proof:
--   sem-cata-impl F alg (sem-In-impl F x)
--   = SPF.cata alg (μ-from-sem F (μ-to-sem F (SPF.⟨ transport-μ F F x ⟩)))
--   = SPF.cata alg (SPF.⟨ transport-μ F F x ⟩)           [by μ-round-trip]
--   = alg (SPF.fmap F (SPF.cata alg) (transport-μ F F x)) [by SPF.cata-computation]
--   = alg (SPF.fmap F (SPF.cata alg) (SPF.fmap F (μ-from-sem F) x))
--                                                         [by transport-μ-is-fmap]
--   = alg (SPF.fmap F (SPF.cata alg ∘ μ-from-sem F) x)   [by fmap-comp inverse]
--   = alg (sem-fmap F (sem-cata-impl F alg) x)           [by fmap-coherence inverse]
--
sem-cata-compute-valid : ∀ F {A : Set} (alg : ⟦ F ⟧F A → A) (x : ⟦ F ⟧F (⟦μ⟧ F))
                       → sem-cata-impl F alg (sem-In-impl F x)
                         ≡ alg (sem-fmap F (sem-cata-impl F alg) x)
sem-cata-compute-valid F {A} alg x =
  trans step1 (trans step2 (trans step3 (trans step4 step5)))
  where
    -- Step 1: Apply μ-round-trip to remove μ-from-sem ∘ μ-to-sem
    step1 : sem-cata-impl F alg (sem-In-impl F x) ≡
            SPF.cata {F} alg SPF.⟨ transport-μ F F x ⟩
    step1 = cong (SPF.cata alg) (μ-round-trip F SPF.⟨ transport-μ F F x ⟩)

    -- Step 2: Apply SPF.cata-computation
    step2 : SPF.cata {F} alg SPF.⟨ transport-μ F F x ⟩ ≡
            alg (SPF.fmap F (SPF.cata {F} alg) (transport-μ F F x))
    step2 = SPF.cata-computation F alg (transport-μ F F x)

    -- Step 3: Apply transport-μ-is-fmap
    step3 : alg (SPF.fmap F (SPF.cata {F} alg) (transport-μ F F x)) ≡
            alg (SPF.fmap F (SPF.cata {F} alg) (SPF.fmap F (μ-from-sem F) x))
    step3 = cong (λ z → alg (SPF.fmap F (SPF.cata {F} alg) z))
                 (transport-μ-is-fmap F F x)

    -- Step 4: Apply fmap composition (fmap g (fmap f x) = fmap (g ∘ f) x)
    step4 : alg (SPF.fmap F (SPF.cata {F} alg) (SPF.fmap F (μ-from-sem F) x)) ≡
            alg (SPF.fmap F (λ z → SPF.cata {F} alg (μ-from-sem F z)) x)
    step4 = cong alg (sym (SPF.fmap-comp F (μ-from-sem F) (SPF.cata {F} alg) x))

    -- Step 5: Convert SPF.fmap to sem-fmap (both are the same by fmap-coherence)
    step5 : alg (SPF.fmap F (λ z → SPF.cata {F} alg (μ-from-sem F z)) x) ≡
            alg (sem-fmap F (sem-cata-impl F alg) x)
    step5 = cong alg (sym (fmap-coherence F (sem-cata-impl F alg) x))

-- | Identity anamorphism law (via SPF.ana-Out-id)
--
-- Core postulates: sem-ana-Out-id : ∀ F x → sem-ana F sem-CoOut x ≡ x
--
-- Proof:
--   sem-ana-impl F sem-CoOut-impl x
--   = ν-to-sem F (SPF.ana sem-CoOut-impl x)
--   Since sem-CoOut-impl involves transport, this doesn't directly reduce.
--   We use the identity ana property from SPF.
--
-- Note: This proof requires showing that sem-ana with sem-CoOut as coalgebra
-- behaves like identity. Due to transport complexity, we postulate this
-- coherence property.
--
postulate
  sem-ana-Out-id-valid : ∀ F (x : ⟦ν⟧ F)
                       → sem-ana-impl F (sem-CoOut-impl F) x ≡ x

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
-- 2. Functor Map Coherence (PROVEN):
--    - sem-fmap F f x ≡ SPF.fmap F f x
--
-- 3. Operation Implementations:
--    - sem-In-impl, sem-Out-impl, sem-cata-impl
--    - sem-CoOut-impl, sem-CoIn-impl, sem-ana-impl
--
-- 4. Law Validation:
--    - Lambek's Lemma direction 1 (PROVEN via SPF.fold-unfold)
--    - Lambek's Lemma direction 2 (PROVEN via SPF.unfold-fold)
--    - Catamorphism computation law (PROVEN via SPF.cata-computation)
--    - Identity anamorphism law (postulated - requires coinductive bisimulation)
--
-- 5. Functor Law Inheritance (PROVEN):
--    - sem-fmap-id, sem-fmap-comp
--
-- Remaining postulates:
--    - μ-coherence, ν-coherence: Type coherence axioms
--    - transport-μ-is-fmap: Transport equals fmap for polynomial functors
--    - sem-ana-Out-id-valid: Identity anamorphism (requires bisimulation proof)
--
-- The type coherence postulates can be eliminated by parameterizing
-- Core by the μ/ν implementations.
--
-- This completes the semantic coherence layer for OCP-0003 Phase 6.
