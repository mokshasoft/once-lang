-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Semantics.Core
--
-- Core semantic interpretation, parameterized by integer representation.
--
-- This module provides:
--   - ⟦_⟧: Type → Set (semantic interpretation)
--   - sem-*: Semantic operations (products, sums, recursion schemes)
--   - Semantic laws
--
-- Instantiate with ℕ for machine semantics, ℤ for proof semantics.
------------------------------------------------------------------------

module Once.Semantics.Core (IntRep : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type

-- OCP-0003: ⟦Fix⟧ wrapper removed. Use μ/ν from SPF.agda.

------------------------------------------------------------------------
-- Semantic Interpretation
--
-- Functions are plain Agda functions (not Closure records).
-- Int is parameterized (ℕ for machine, ℤ for proofs).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Polynomial Functor Semantics (via Once.Functor.Translate)
--
-- OCP-0003 Phase 6: Instead of postulating ⟦μ⟧ and ⟦ν⟧, we now define
-- them using Once.Functor.Base's μS and νS via translation.
--
-- This breaks the circular dependency:
--   Old: ⟦_⟧ → ⟦_⟧F → SPF.μ → ⟦μ⟧ → ⟦_⟧ (circular!)
--   New: ⟦_⟧-base → translateF → μS (no cycle)
--        Then: ⟦μ⟧ = μS ∘ translateF
--
-- For well-formed functors (K only with base types), the base
-- interpretation equals the full interpretation.
------------------------------------------------------------------------

open import Once.Functor.Translate using (μ-sem; ν-sem)

-- | Semantic interpretation of μ-type (initial algebra)
--
-- Defined via translation to SFunctor, not postulated.
-- μ-coherence is now provable (essentially refl).
--
⟦μ⟧ : Functor → Set
⟦μ⟧ = μ-sem IntRep

-- | Semantic interpretation of ν-type (final coalgebra)
--
-- Defined via translation to SFunctor, not postulated.
-- ν-coherence is now provable (essentially refl).
--
⟦ν⟧ : Functor → Set
⟦ν⟧ = ν-sem IntRep

-- | Semantic interpretation of GuardedT (guarded functor values)
--
-- ⟦Guarded⟧ F A represents guarded F-shaped values with A at recursive positions.
-- This is postulated here but instantiated properly via Once.CCC.IR.Guarded.
--
-- The actual type would be: Guarded ⟦_⟧ F A from Guarded.agda, but that's at
-- Set₁ due to universe polymorphism. We postulate at Set for simplicity.
--
postulate
  ⟦Guarded⟧ : Functor → Set → Set

⟦_⟧ : Type → Set
⟦ Unit ⟧         = ⊤
⟦ Void ⟧         = ⊥
⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒[ _ ] B ⟧   = ⟦ A ⟧ → ⟦ B ⟧
⟦ Eff A B ⟧      = ⟦ A ⟧ → ⟦ B ⟧
-- OCP-0003: Fix removed, use μ-type/ν-type
⟦ μ-type F ⟧     = ⟦μ⟧ F
⟦ ν-type F ⟧     = ⟦ν⟧ F
-- OCP-0003: GuardedT for productive corecursion
⟦ GuardedT F A ⟧ = ⟦Guarded⟧ F ⟦ A ⟧
⟦ Int ⟧          = IntRep
⟦ Float ⟧        = AgdaFloat
⟦ Str ⟧          = String
⟦ Buffer ⟧       = String
⟦ TVar _ ⟧       = ⊤

------------------------------------------------------------------------
-- Functor Interpretation (Set level)
--
-- Interprets Functor codes as Set → Set functions.
-- This parallels ⟦_⟧T at the Type level.
------------------------------------------------------------------------

⟦_⟧F : Functor → Set → Set
⟦ K A ⟧F X = ⟦ A ⟧
⟦ Id ⟧F X = X
⟦ F ⊕ G ⟧F X = ⟦ F ⟧F X ⊎ ⟦ G ⟧F X
⟦ F ⊗ G ⟧F X = ⟦ F ⟧F X × ⟦ G ⟧F X

------------------------------------------------------------------------
-- Type/Set Functor Coherence
--
-- The Type-level functor interpretation ⟦_⟧T followed by semantic
-- interpretation ⟦_⟧ equals the Set-level functor interpretation ⟦_⟧F.
-- We prove this by structural induction on F.
------------------------------------------------------------------------

-- | Coherence: ⟦ ⟦ F ⟧T X ⟧ ≡ ⟦ F ⟧F ⟦ X ⟧
--
-- This allows converting between Type-level and Set-level functor apps.
--
sem-functor-coherence : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ ≡ ⟦ F ⟧F ⟦ X ⟧
sem-functor-coherence (K A) X = refl
sem-functor-coherence Id X = refl
sem-functor-coherence (F ⊕ G) X rewrite sem-functor-coherence F X
                                      | sem-functor-coherence G X = refl
sem-functor-coherence (F ⊗ G) X rewrite sem-functor-coherence F X
                                      | sem-functor-coherence G X = refl

-- | Coercion from Type-level to Set-level functor application
--
-- Uses the coherence proof via subst.
--
coerce-functor : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ → ⟦ F ⟧F ⟦ X ⟧
coerce-functor F X = subst (λ z → z) (sem-functor-coherence F X)
  where
    open import Relation.Binary.PropositionalEquality using (subst)

-- | Inverse coercion
coerce-functor⁻¹ : ∀ F X → ⟦ F ⟧F ⟦ X ⟧ → ⟦ ⟦ F ⟧T X ⟧
coerce-functor⁻¹ F X = subst (λ z → z) (sym (sem-functor-coherence F X))
  where
    open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- Coercion Round-Trip Lemmas
--
-- These lemmas establish that coerce-functor and coerce-functor⁻¹ are
-- inverses. This is essential for proving recursion scheme laws.
------------------------------------------------------------------------

private
  open import Relation.Binary.PropositionalEquality using (subst; sym)

  -- Standard lemma: subst followed by subst with sym cancels
  subst-sym-subst : ∀ {A B : Set} (p : A ≡ B) (v : B)
                  → subst (λ z → z) p (subst (λ z → z) (sym p) v) ≡ v
  subst-sym-subst refl v = refl

  -- Dual: subst with sym followed by subst cancels
  subst-subst-sym : ∀ {A B : Set} (p : A ≡ B) (v : A)
                  → subst (λ z → z) (sym p) (subst (λ z → z) p v) ≡ v
  subst-subst-sym refl v = refl

-- | Round-trip: coerce then coerce⁻¹ is identity
coerce-round-trip : ∀ F X (x : ⟦ ⟦ F ⟧T X ⟧)
                  → coerce-functor⁻¹ F X (coerce-functor F X x) ≡ x
coerce-round-trip F X x = subst-subst-sym (sem-functor-coherence F X) x

-- | Round-trip: coerce⁻¹ then coerce is identity
coerce⁻¹-round-trip : ∀ F X (x : ⟦ F ⟧F ⟦ X ⟧)
                    → coerce-functor F X (coerce-functor⁻¹ F X x) ≡ x
coerce⁻¹-round-trip F X x = subst-sym-subst (sem-functor-coherence F X) x

------------------------------------------------------------------------
-- Semantic Operations
--
-- These mirror IR constructors but operate on semantic values.
-- Named sem-<ir> to distinguish from IR constructors.
------------------------------------------------------------------------

-- Pair operations
sem-fst : ∀ {A B} → ⟦ A * B ⟧ → ⟦ A ⟧
sem-fst = proj₁

sem-snd : ∀ {A B} → ⟦ A * B ⟧ → ⟦ B ⟧
sem-snd = proj₂

sem-pair : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A * B ⟧
sem-pair a b = a , b

-- Sum operations
sem-inl : ∀ {A B} → ⟦ A ⟧ → ⟦ A + B ⟧
sem-inl = inj₁

sem-inr : ∀ {A B} → ⟦ B ⟧ → ⟦ A + B ⟧
sem-inr = inj₂

sem-case : ∀ {A B C} → (⟦ A ⟧ → ⟦ C ⟧) → (⟦ B ⟧ → ⟦ C ⟧) → ⟦ A + B ⟧ → ⟦ C ⟧
sem-case f g (inj₁ a) = f a
sem-case f g (inj₂ b) = g b

-- OCP-0003: sem-fold/sem-unfold removed. Use sem-In/sem-cata/sem-CoOut/sem-ana.

------------------------------------------------------------------------
-- Semantic Laws
------------------------------------------------------------------------

sem-fst-pair : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) → sem-fst (sem-pair a b) ≡ a
sem-fst-pair a b = refl

sem-snd-pair : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) → sem-snd (sem-pair a b) ≡ b
sem-snd-pair a b = refl

sem-case-inl : ∀ {A B C} (f : ⟦ A ⟧ → ⟦ C ⟧) (g : ⟦ B ⟧ → ⟦ C ⟧) (a : ⟦ A ⟧) →
  sem-case f g (sem-inl a) ≡ f a
sem-case-inl f g a = refl

sem-case-inr : ∀ {A B C} (f : ⟦ A ⟧ → ⟦ C ⟧) (g : ⟦ B ⟧ → ⟦ C ⟧) (b : ⟦ B ⟧) →
  sem-case f g (sem-inr b) ≡ g b
sem-case-inr f g b = refl

-- OCP-0003: sem-fold-unfold and sem-unfold-fold laws removed

------------------------------------------------------------------------
-- Recursion Scheme Semantic Operations (Postulated)
--
-- These operations parallel the IR constructors for recursion schemes.
-- They are postulated here but implemented properly in Once.SPF.
--
-- F is explicit where needed for Agda to resolve constraints.
------------------------------------------------------------------------

-- | Functorial map for polynomials (defined first for use in postulates)
sem-fmap : ∀ F {X Y : Set} → (X → Y) → ⟦ F ⟧F X → ⟦ F ⟧F Y
sem-fmap (K A) f x = x
sem-fmap Id f x = f x
sem-fmap (F ⊕ G) f (inj₁ x) = inj₁ (sem-fmap F f x)
sem-fmap (F ⊕ G) f (inj₂ y) = inj₂ (sem-fmap G f y)
sem-fmap (F ⊗ G) f (x , y) = (sem-fmap F f x , sem-fmap G f y)

-- | In: F(μF) → μF (algebra)
postulate
  sem-In : ∀ (F : Functor) → ⟦ F ⟧F (⟦μ⟧ F) → ⟦μ⟧ F

-- | Out: μF → F(μF) (destructor, inverse of In)
postulate
  sem-Out : ∀ (F : Functor) → ⟦μ⟧ F → ⟦ F ⟧F (⟦μ⟧ F)

-- | Catamorphism: given algebra F(A) → A, fold μF → A
postulate
  sem-cata : ∀ (F : Functor) {A : Set} → (⟦ F ⟧F A → A) → ⟦μ⟧ F → A

-- | CoOut: νF → F(νF) (observation)
postulate
  sem-CoOut : ∀ (F : Functor) → ⟦ν⟧ F → ⟦ F ⟧F (⟦ν⟧ F)

-- | CoIn: F(νF) → νF (coalgebra)
postulate
  sem-CoIn : ∀ (F : Functor) → ⟦ F ⟧F (⟦ν⟧ F) → ⟦ν⟧ F

-- | Anamorphism: given coalgebra A → F(A), unfold A → νF
postulate
  sem-ana : ∀ (F : Functor) {A : Set} → (A → ⟦ F ⟧F A) → A → ⟦ν⟧ F

------------------------------------------------------------------------
-- Guarded Operations (OCP-0003)
--
-- These operations support the GuardedT type for productive corecursion.
------------------------------------------------------------------------

-- | Unguard: extract functor value from guarded value
-- This "consumes" the guardedness - the F-layer has been observed.
postulate
  sem-unguard : ∀ (F : Functor) {A : Set} → ⟦Guarded⟧ F A → ⟦ F ⟧F A

-- | Guarded anamorphism: given guarded coalgebra A → Guarded F A, unfold A → νF
-- This is the productive version of sem-ana.
-- Semantically: sem-ana-guarded F coalg = sem-ana F (sem-unguard F ∘ coalg)
postulate
  sem-ana-guarded : ∀ (F : Functor) {A : Set} → (A → ⟦Guarded⟧ F A) → A → ⟦ν⟧ F

-- | Guarded hylomorphism: fused cata with guarded coalgebra
postulate
  sem-hylo-guarded : ∀ (F : Functor) {A B : Set}
                   → (⟦ F ⟧F B → B)           -- algebra
                   → (A → ⟦Guarded⟧ F A)      -- guarded coalgebra
                   → A → B

-- | Hylomorphism: fused cata ∘ ana, computed directly
-- Semantically: hylo alg coalg = cata alg ∘ ana coalg
-- But computed without building intermediate structure
postulate
  sem-hylo : ∀ (F : Functor) {A B : Set}
           → (⟦ F ⟧F B → B)  -- algebra
           → (A → ⟦ F ⟧F A)  -- coalgebra
           → A → B

------------------------------------------------------------------------
-- Recursion Scheme Laws (Postulated)
--
-- These capture the key properties of initial algebras and final
-- coalgebras. They are implemented properly in Once.SPF.
------------------------------------------------------------------------

-- | In and Out are inverses (Lambek's Lemma, one direction)
postulate
  sem-Out-In : ∀ (F : Functor) (x : ⟦ F ⟧F (⟦μ⟧ F)) → sem-Out F (sem-In F x) ≡ x

-- | In and Out are inverses (Lambek's Lemma, other direction)
postulate
  sem-In-Out : ∀ (F : Functor) (x : ⟦μ⟧ F) → sem-In F (sem-Out F x) ≡ x

-- | Catamorphism computation law
postulate
  sem-cata-compute : ∀ (F : Functor) {A : Set} (alg : ⟦ F ⟧F A → A) (x : ⟦ F ⟧F (⟦μ⟧ F))
                   → sem-cata F alg (sem-In F x) ≡ alg (sem-fmap F (sem-cata F alg) x)

-- | Identity catamorphism: cata with In algebra is identity
--
-- This is the canonical expression of μF ≅ F(μF) at the semantic level.
-- Proof sketch: By induction, cata In ⟨x⟩ = In (fmap (cata In) x) = In x = ⟨x⟩
-- when fmap id = id (functor law).
--
postulate
  sem-cata-In-id : ∀ (F : Functor) (x : ⟦μ⟧ F) → sem-cata F (sem-In F) x ≡ x

-- | Identity anamorphism: ana with Out coalgebra is identity
--
-- Dual to sem-cata-In-id for final coalgebras.
-- Proof sketch: By coinduction, ana Out x = record { unfold = fmap (ana Out) (Out x) }
--             = record { unfold = Out x } = x  (when fmap id = id)
--
postulate
  sem-ana-Out-id : ∀ (F : Functor) (x : ⟦ν⟧ F) → sem-ana F (sem-CoOut F) x ≡ x

-- | Hylomorphism computation law
--
-- hylo alg coalg x = alg (fmap (hylo alg coalg) (coalg x))
--
postulate
  sem-hylo-compute : ∀ (F : Functor) {A B : Set} (alg : ⟦ F ⟧F B → B) (coalg : A → ⟦ F ⟧F A) (x : A)
                   → sem-hylo F alg coalg x ≡ alg (sem-fmap F (sem-hylo F alg coalg) (coalg x))