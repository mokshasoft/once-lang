-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Semantics.Value
--
-- Core semantic interpretation, parameterized by the `Int` carrier.
--
-- This module provides:
--   - ⟦_⟧: Type → Set (semantic interpretation)
--   - sem-*: Semantic operations (products, sums, recursion schemes)
--   - Semantic laws
--
-- D054: `Int`'s denotation is the modular machine `Word`, NOT ℤ and NOT
-- unbounded ℕ. Instantiate `IntRep` with the width-agnostic machine-word
-- carrier `Once.Word.Carrier`; `Once.Semantics.Machine` does this.
-- (`IntRep : Set` rather than `bits : ℕ` only because a top-level Agda
-- module can't take a ℕ parameter — and the carrier IS width-invariant
-- in the residue representation, so width is threaded from the arch into
-- the modular ops (D059), never baked into this carrier. The old ℤ
-- "proof instance" is the parked `BigInt` spec — unused.)
--
-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  WARNING — Eff IS DENOTED AS A PLAIN ARROW.                      ║
-- ║                                                                  ║
-- ║      ⟦ A ⇒[ _ ] B ⟧ = ⟦ A ⟧ → ⟦ B ⟧                              ║
-- ║                                                                  ║
-- ║  Pure (`mk-kind _ pure`) and effectful (`mk-kind _ eff`) arrows  ║
-- ║  collapse to the same Agda function type. Effects are INVISIBLE  ║
-- ║  at this denotation level; there is no SigOp trace, no exit-     ║
-- ║  code preservation, nothing observable beyond the function       ║
-- ║  shape.                                                          ║
-- ║                                                                  ║
-- ║  Reading note: a program of type `Eff Unit Unit` denotes         ║
-- ║  `⊤ → ⊤` (the constant function). Programs DO NOT RETURN A      ║
-- ║  VALUE — they invoke SigOps. Any observable based on those       ║
-- ║  SigOps (syscall trace, exit code as an exit-syscall argument)  ║
-- ║  lives ELSEWHERE; see `Once.Denotation.Behavior`.                  ║
-- ║                                                                  ║
-- ║  Use `⟦_⟧` for value-level reasoning only (CCC laws, structural  ║
-- ║  recursion). Don't try to project effects from it.               ║
-- ╚══════════════════════════════════════════════════════════════════╝
------------------------------------------------------------------------

module Once.Semantics.Value (IntRep : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst; subst₂)
open import Function using (_∘_)

open import Once.Type


-- OCP-0003: ⟦Fix⟧ wrapper removed. Use μ/ν from SPF.agda.

------------------------------------------------------------------------
-- Semantic Interpretation
--
-- Functions are plain Agda functions (not Closure records).
-- ⟦ Int ⟧ = IntRep, the modular `Word` carrier (D054); supplied by the
-- instantiation (`Once.Semantics.Machine` = `Once.Word.Carrier`).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Polynomial Functor Semantics (via Once.Functor.Translate)
--
-- OCP-0003 Phase 6: Instead of postulating ⟦μ⟧ and ⟦ν⟧, we now define
-- them using Once.Semantics.Functor's μS and νS via translation.
--
-- This breaks the circular dependency:
--   Old: ⟦_⟧ → ⟦_⟧F → SPF.μ → ⟦μ⟧ → ⟦_⟧ (circular!)
--   New: ⟦_⟧-base → translateF → μS (no cycle)
--        Then: ⟦μ⟧ = μS ∘ translateF
--
-- For well-formed functors (K only with base types), the base
-- interpretation equals the full interpretation.
------------------------------------------------------------------------

open import Once.Functor.Translate using (μ-sem; ν-sem; translateF; ⟦_⟧-base; IsBaseType; WellFormedF)
open import Once.Functor.Translate
  using ( base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer
        ; base-Prod; base-Sum; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Semantics.Functor
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; ⟨_⟩; outS; νS; unfoldS;
         sfmap; cataS; cataS-cong; sfmapCata; sfmapCata-is-sfmap; anaS; sfmapAna; sfmapAna-is-sfmap; fuseNatS; fuseNatW;
         fold-unfoldS; unfold-foldS; cataS-computation; cataS-In-id)
-- D062/0.47: the bisimulation machinery (⟦_⟧SF-rel, _∼S_, bisimS-to-eq, …) and
-- the axiom-using identity laws moved to `Once.Semantics.Functor.Laws` /
-- `Once.Semantics.Value.Laws`, so this module holds definitions only.

-- | Semantic interpretation of μ-type (initial algebra)
--
-- Defined via translation to SFunctor.
-- μ-coherence is now provable (essentially refl).
--
⟦μ⟧ : Functor → Set
⟦μ⟧ = μ-sem IntRep

-- | Semantic interpretation of ν-type (final coalgebra)
--
-- Defined via translation to SFunctor.
-- ν-coherence is now provable (essentially refl).
--
⟦ν⟧ : Functor → Set
⟦ν⟧ = ν-sem IntRep

-- ⟦Guarded⟧ removed: productivity follows from IR totality (see IR/Totality.agda)

------------------------------------------------------------------------
-- Type Interpretation
------------------------------------------------------------------------

-- | Type interpretation
⟦_⟧ : Type → Set
⟦ Unit ⟧         = ⊤
⟦ Void ⟧         = ⊥
⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒[ _ ] B ⟧   = ⟦ A ⟧ → ⟦ B ⟧
-- OCP-0003: Fix removed, use μ-type/ν-type
⟦ μ-type F ⟧     = ⟦μ⟧ F
⟦ ν-type F ⟧     = ⟦ν⟧ F
-- GuardedT removed: productivity follows from IR totality
⟦ Int ⟧          = IntRep
⟦ Float ⟧        = AgdaFloat
⟦ Str ⟧          = String
⟦ Buffer ⟧       = String
-- TVar removed from Type; now in PolyType (see Once.Type)

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
-- Proven by structural induction on F.
--
sem-functor-coherence : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ ≡ ⟦ F ⟧F ⟦ X ⟧
sem-functor-coherence (K A) X = refl
sem-functor-coherence Id X = refl
sem-functor-coherence (F ⊕ G) X rewrite sem-functor-coherence F X
                                      | sem-functor-coherence G X = refl
sem-functor-coherence (F ⊗ G) X rewrite sem-functor-coherence F X
                                      | sem-functor-coherence G X = refl

------------------------------------------------------------------------
-- Coercions (Structural Definition)
--
-- Key insight: Define coercions by structural recursion on F, NOT via
-- subst on the coherence proof. This makes them compute properly and
-- allows definitional equality with structural operations.
------------------------------------------------------------------------

-- | Coercion from Type-level to Set-level functor application
coerce-functor : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ → ⟦ F ⟧F ⟦ X ⟧
coerce-functor (K A) X x = x
coerce-functor Id X x = x
coerce-functor (F ⊕ G) X (inj₁ x) = inj₁ (coerce-functor F X x)
coerce-functor (F ⊕ G) X (inj₂ y) = inj₂ (coerce-functor G X y)
coerce-functor (F ⊗ G) X (x , y) = (coerce-functor F X x , coerce-functor G X y)

-- | Inverse coercion
coerce-functor⁻¹ : ∀ F X → ⟦ F ⟧F ⟦ X ⟧ → ⟦ ⟦ F ⟧T X ⟧
coerce-functor⁻¹ (K A) X x = x
coerce-functor⁻¹ Id X x = x
coerce-functor⁻¹ (F ⊕ G) X (inj₁ x) = inj₁ (coerce-functor⁻¹ F X x)
coerce-functor⁻¹ (F ⊕ G) X (inj₂ y) = inj₂ (coerce-functor⁻¹ G X y)
coerce-functor⁻¹ (F ⊗ G) X (x , y) = (coerce-functor⁻¹ F X x , coerce-functor⁻¹ G X y)

------------------------------------------------------------------------
-- Coercion Round-Trip Lemmas
--
-- Now that coercions are defined structurally, the round-trip proofs
-- are simple structural induction (no subst manipulation needed).
------------------------------------------------------------------------

-- | Round-trip: coerce then coerce⁻¹ is identity
coerce-round-trip : ∀ F X (x : ⟦ ⟦ F ⟧T X ⟧)
                  → coerce-functor⁻¹ F X (coerce-functor F X x) ≡ x
coerce-round-trip (K A) X x = refl
coerce-round-trip Id X x = refl
coerce-round-trip (F ⊕ G) X (inj₁ x) = cong inj₁ (coerce-round-trip F X x)
coerce-round-trip (F ⊕ G) X (inj₂ y) = cong inj₂ (coerce-round-trip G X y)
coerce-round-trip (F ⊗ G) X (x , y) = cong₂ _,_ (coerce-round-trip F X x) (coerce-round-trip G X y)

-- | Round-trip: coerce⁻¹ then coerce is identity
coerce⁻¹-round-trip : ∀ F X (x : ⟦ F ⟧F ⟦ X ⟧)
                    → coerce-functor F X (coerce-functor⁻¹ F X x) ≡ x
coerce⁻¹-round-trip (K A) X x = refl
coerce⁻¹-round-trip Id X x = refl
coerce⁻¹-round-trip (F ⊕ G) X (inj₁ x) = cong inj₁ (coerce⁻¹-round-trip F X x)
coerce⁻¹-round-trip (F ⊕ G) X (inj₂ y) = cong inj₂ (coerce⁻¹-round-trip G X y)
coerce⁻¹-round-trip (F ⊗ G) X (x , y) = cong₂ _,_ (coerce⁻¹-round-trip F X x) (coerce⁻¹-round-trip G X y)

------------------------------------------------------------------------
-- Structural Coercion Aliases (for backwards compatibility)
--
-- Now that coerce-functor is defined structurally, these are just aliases.
------------------------------------------------------------------------

-- | Alias for coerce-functor (backwards compatibility)
coerce-struct : ∀ F X → ⟦ ⟦ F ⟧T X ⟧ → ⟦ F ⟧F ⟦ X ⟧
coerce-struct = coerce-functor

-- | Alias for coerce-functor⁻¹ (backwards compatibility)
coerce-struct⁻¹ : ∀ F X → ⟦ F ⟧F ⟦ X ⟧ → ⟦ ⟦ F ⟧T X ⟧
coerce-struct⁻¹ = coerce-functor⁻¹

-- | Alias for coerce-round-trip
coerce-struct-round-trip : ∀ F X (x : ⟦ ⟦ F ⟧T X ⟧)
                         → coerce-struct⁻¹ F X (coerce-struct F X x) ≡ x
coerce-struct-round-trip = coerce-round-trip

-- | Alias for coerce⁻¹-round-trip
coerce-struct⁻¹-round-trip : ∀ F X (x : ⟦ F ⟧F ⟦ X ⟧)
                           → coerce-struct F X (coerce-struct⁻¹ F X x) ≡ x
coerce-struct⁻¹-round-trip = coerce⁻¹-round-trip

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

------------------------------------------------------------------------
-- Fmap-Coercion Coherence (using structural coercions)
--
-- These lemmas show that structural coercions commute with sem-fmap.
-- They're used to prove the IR-level recursion scheme laws.
------------------------------------------------------------------------

-- | Type-level functorial map (works on ⟦ ⟦ F ⟧T X ⟧)
-- This mirrors sem-fmap but at the Type level
sem-fmap-Type : ∀ F {X Y : Type} → (⟦ X ⟧ → ⟦ Y ⟧) → ⟦ ⟦ F ⟧T X ⟧ → ⟦ ⟦ F ⟧T Y ⟧
sem-fmap-Type (K A) f x = x
sem-fmap-Type Id f x = f x
sem-fmap-Type (F ⊕ G) f (inj₁ x) = inj₁ (sem-fmap-Type F f x)
sem-fmap-Type (F ⊕ G) f (inj₂ y) = inj₂ (sem-fmap-Type G f y)
sem-fmap-Type (F ⊗ G) f (x , y) = (sem-fmap-Type F f x , sem-fmap-Type G f y)

-- | coerce-struct⁻¹ ∘ sem-fmap ∘ coerce-struct ≡ sem-fmap-Type
fmap-struct-coherence : ∀ F {X Y : Type} (f : ⟦ X ⟧ → ⟦ Y ⟧) (x : ⟦ ⟦ F ⟧T X ⟧)
                      → coerce-struct⁻¹ F Y (sem-fmap F f (coerce-struct F X x)) ≡ sem-fmap-Type F f x
fmap-struct-coherence (K A) f x = refl
fmap-struct-coherence Id f x = refl
fmap-struct-coherence (F ⊕ G) f (inj₁ x) = cong inj₁ (fmap-struct-coherence F f x)
fmap-struct-coherence (F ⊕ G) f (inj₂ y) = cong inj₂ (fmap-struct-coherence G f y)
fmap-struct-coherence (F ⊗ G) f (x , y) = cong₂ _,_ (fmap-struct-coherence F f x) (fmap-struct-coherence G f y)

-- | coerce-struct⁻¹ ∘ sem-fmap ≡ sem-fmap-Type ∘ coerce-struct⁻¹
fmap-struct-coherence′ : ∀ F {X Y : Type} (f : ⟦ X ⟧ → ⟦ Y ⟧) (y : ⟦ F ⟧F ⟦ X ⟧)
                       → coerce-struct⁻¹ F Y (sem-fmap F f y) ≡ sem-fmap-Type F f (coerce-struct⁻¹ F X y)
fmap-struct-coherence′ (K A) f y = refl
fmap-struct-coherence′ Id f y = refl
fmap-struct-coherence′ (F ⊕ G) f (inj₁ x) = cong inj₁ (fmap-struct-coherence′ F f x)
fmap-struct-coherence′ (F ⊕ G) f (inj₂ y) = cong inj₂ (fmap-struct-coherence′ G f y)
fmap-struct-coherence′ (F ⊗ G) f (x , y) = cong₂ _,_ (fmap-struct-coherence′ F f x) (fmap-struct-coherence′ G f y)

------------------------------------------------------------------------
-- Type Coercions (Full ↔ Base Interpretation)
--
-- OCP-0003: For well-formed functors (K only with base types), the full
-- interpretation ⟦_⟧ equals the base interpretation ⟦_⟧-base. We prove
-- this by pattern matching on the Type.
--
-- For base types: definitionally equal
-- For complex types: ⟦_⟧-base returns ⊤, which is a "fallback" that
--   should never be reached for well-formed functors.
------------------------------------------------------------------------

-- | Coerce from full to base interpretation
--
-- This direction always works:
-- - Base types: identity (definitionally equal)
-- - Complex types: produce tt (base interp returns ⊤)
--
coerce-full-to-base : ∀ A → ⟦ A ⟧ → ⟦ IntRep ⟧-base A
coerce-full-to-base Unit x = x
coerce-full-to-base Void x = x
coerce-full-to-base (A * B) (a , b) = (coerce-full-to-base A a , coerce-full-to-base B b)
coerce-full-to-base (A + B) (inj₁ a) = inj₁ (coerce-full-to-base A a)
coerce-full-to-base (A + B) (inj₂ b) = inj₂ (coerce-full-to-base B b)
coerce-full-to-base (_ ⇒[ _ ] _) _ = tt   -- Functions (all kinds) → ⊤
coerce-full-to-base (μ-type _) _ = tt      -- μ → ⊤
coerce-full-to-base (ν-type _) _ = tt      -- ν → ⊤
-- GuardedT removed: productivity follows from IR totality
coerce-full-to-base Int x = x
coerce-full-to-base Float x = x
coerce-full-to-base Str x = x
coerce-full-to-base Buffer x = x
-- TVar removed from Type; now in PolyType (see Once.Type)

-- | Coerce from base to full interpretation
--
------------------------------------------------------------------------
-- Well-Formed Type Coercion
--
-- OCP-0003: Coercion from base to full interpretation requires an
-- IsBaseType proof, which is what makes it total.
--
-- For base types, the coercion is an identity (structurally).
-- Complex types (functions, μ-type, ν-type, GuardedT) are excluded
-- by the IsBaseType predicate, so we never need to produce values
-- we can't construct.
------------------------------------------------------------------------

-- | Coerce from base to full interpretation
--
-- Requires an IsBaseType proof, which is what makes it total.
--
coerce-base-to-full : ∀ {A} → IsBaseType A → ⟦ IntRep ⟧-base A → ⟦ A ⟧
coerce-base-to-full base-Unit x = x
coerce-base-to-full base-Void ()
coerce-base-to-full base-Int x = x
coerce-base-to-full base-Float x = x
coerce-base-to-full base-Str x = x
coerce-base-to-full base-Buffer x = x
coerce-base-to-full (base-Prod pA pB) (a , b) =
  (coerce-base-to-full pA a , coerce-base-to-full pB b)
coerce-base-to-full (base-Sum pA pB) (inj₁ a) = inj₁ (coerce-base-to-full pA a)
coerce-base-to-full (base-Sum pA pB) (inj₂ b) = inj₂ (coerce-base-to-full pB b)

------------------------------------------------------------------------
-- Type Coercion Round-Trip Properties (Well-Formed Only)
--
-- For base types (IsBaseType A), the coercions are definitionally identity.
-- So well-formed functors have a fully computed path through the coercions.
------------------------------------------------------------------------

-- | For base types, coerce-base-to-full ∘ coerce-full-to-base = id (PROVEN)
--
-- This is the key lemma for well-formed functors.
--
coerce-base-type-round-trip : ∀ {A} → (pA : IsBaseType A) → (x : ⟦ A ⟧)
                            → coerce-base-to-full pA (coerce-full-to-base A x) ≡ x
coerce-base-type-round-trip base-Unit x = refl
coerce-base-type-round-trip base-Void ()
coerce-base-type-round-trip base-Int x = refl
coerce-base-type-round-trip base-Float x = refl
coerce-base-type-round-trip base-Str x = refl
coerce-base-type-round-trip base-Buffer x = refl
coerce-base-type-round-trip (base-Prod pA pB) (a , b) =
  cong₂ _,_ (coerce-base-type-round-trip pA a) (coerce-base-type-round-trip pB b)
coerce-base-type-round-trip (base-Sum pA pB) (inj₁ a) =
  cong inj₁ (coerce-base-type-round-trip pA a)
coerce-base-type-round-trip (base-Sum pA pB) (inj₂ b) =
  cong inj₂ (coerce-base-type-round-trip pB b)

-- | For base types, coerce-full-to-base ∘ coerce-base-to-full = id (PROVEN)
--
coerce-base-type⁻¹-round-trip : ∀ {A} → (pA : IsBaseType A) → (x : ⟦ IntRep ⟧-base A)
                              → coerce-full-to-base A (coerce-base-to-full pA x) ≡ x
coerce-base-type⁻¹-round-trip base-Unit x = refl
coerce-base-type⁻¹-round-trip base-Void ()
coerce-base-type⁻¹-round-trip base-Int x = refl
coerce-base-type⁻¹-round-trip base-Float x = refl
coerce-base-type⁻¹-round-trip base-Str x = refl
coerce-base-type⁻¹-round-trip base-Buffer x = refl
coerce-base-type⁻¹-round-trip (base-Prod pA pB) (a , b) =
  cong₂ _,_ (coerce-base-type⁻¹-round-trip pA a) (coerce-base-type⁻¹-round-trip pB b)
coerce-base-type⁻¹-round-trip (base-Sum pA pB) (inj₁ a) =
  cong inj₁ (coerce-base-type⁻¹-round-trip pA a)
coerce-base-type⁻¹-round-trip (base-Sum pA pB) (inj₂ b) =
  cong inj₂ (coerce-base-type⁻¹-round-trip pB b)

------------------------------------------------------------------------
-- μ-type Coercions (OCP-0003)
--
-- Structural coercions between ⟦ F ⟧F X and ⟦ translateF IntRep F ⟧SF X.
-- These use the type coercions above for the K case.
------------------------------------------------------------------------

-- | Coerce from ⟦ F ⟧F to ⟦ translateF F ⟧SF (for μ-type operations)
--
coerce-μ-in : ∀ F (X : Set) → ⟦ F ⟧F X → ⟦ translateF IntRep F ⟧SF X
coerce-μ-in (K A) X x = coerce-full-to-base A x
coerce-μ-in Id X x = x
coerce-μ-in (F ⊕ G) X (inj₁ x) = inj₁ (coerce-μ-in F X x)
coerce-μ-in (F ⊕ G) X (inj₂ y) = inj₂ (coerce-μ-in G X y)
coerce-μ-in (F ⊗ G) X (x , y) = (coerce-μ-in F X x , coerce-μ-in G X y)

-- | Coerce from ⟦ translateF F ⟧SF to ⟦ F ⟧F (for μ-type operations)
--
-- Requires a WellFormedF proof to ensure K positions only use base types.
--
coerce-μ-out : ∀ {F} → WellFormedF F → (X : Set) → ⟦ translateF IntRep F ⟧SF X → ⟦ F ⟧F X
coerce-μ-out (wf-K pA) X x = coerce-base-to-full pA x
coerce-μ-out wf-Id X x = x
coerce-μ-out (wf-Sum wfF wfG) X (inj₁ x) = inj₁ (coerce-μ-out wfF X x)
coerce-μ-out (wf-Sum wfF wfG) X (inj₂ y) = inj₂ (coerce-μ-out wfG X y)
coerce-μ-out (wf-Prod wfF wfG) X (x , y) = (coerce-μ-out wfF X x , coerce-μ-out wfG X y)

------------------------------------------------------------------------
-- Well-Formed μ-Coercion Round-Trip (PROVEN)
--
-- For well-formed functors, the μ-coercion round-trips are provable
-- using the base-type round-trip lemmas.
------------------------------------------------------------------------

-- | coerce-μ-out ∘ coerce-μ-in = id (PROVEN)
--
coerce-μ-round-trip : ∀ {F} → (wf : WellFormedF F) → ∀ (X : Set) (x : ⟦ F ⟧F X)
                    → coerce-μ-out wf X (coerce-μ-in F X x) ≡ x
coerce-μ-round-trip (wf-K pA) X x = coerce-base-type-round-trip pA x
coerce-μ-round-trip wf-Id X x = refl
coerce-μ-round-trip (wf-Sum wfF wfG) X (inj₁ x) =
  cong inj₁ (coerce-μ-round-trip wfF X x)
coerce-μ-round-trip (wf-Sum wfF wfG) X (inj₂ y) =
  cong inj₂ (coerce-μ-round-trip wfG X y)
coerce-μ-round-trip (wf-Prod wfF wfG) X (x , y) =
  cong₂ _,_ (coerce-μ-round-trip wfF X x) (coerce-μ-round-trip wfG X y)

-- | coerce-μ-in ∘ coerce-μ-out = id (PROVEN)
--
coerce-μ⁻¹-round-trip : ∀ {F} → (wf : WellFormedF F) → ∀ (X : Set) (x : ⟦ translateF IntRep F ⟧SF X)
                      → coerce-μ-in F X (coerce-μ-out wf X x) ≡ x
coerce-μ⁻¹-round-trip (wf-K pA) X x = coerce-base-type⁻¹-round-trip pA x
coerce-μ⁻¹-round-trip wf-Id X x = refl
coerce-μ⁻¹-round-trip (wf-Sum wfF wfG) X (inj₁ x) =
  cong inj₁ (coerce-μ⁻¹-round-trip wfF X x)
coerce-μ⁻¹-round-trip (wf-Sum wfF wfG) X (inj₂ y) =
  cong inj₂ (coerce-μ⁻¹-round-trip wfG X y)
coerce-μ⁻¹-round-trip (wf-Prod wfF wfG) X (x , y) =
  cong₂ _,_ (coerce-μ⁻¹-round-trip wfF X x) (coerce-μ⁻¹-round-trip wfG X y)

------------------------------------------------------------------------
-- μ-type Operations (OCP-0003: Defined via SPF)
--
-- These use the SPF operations ⟨_⟩, outS, and cataS with structural
-- coercions to bridge between our ⟦_⟧F and SPF's ⟦_⟧SF.
------------------------------------------------------------------------

-- | In: F(μF) → μF (algebra)
--
-- OCP-0003: Defined via SPF's ⟨_⟩ constructor with coercion.
--
sem-In : ∀ (F : Functor) → ⟦ F ⟧F (⟦μ⟧ F) → ⟦μ⟧ F
sem-In F x = ⟨ coerce-μ-in F (⟦μ⟧ F) x ⟩

-- | Out: μF → F(μF) (destructor, inverse of In)
--
-- OCP-0003: Defined via SPF's outS with coercion.
-- Requires a WellFormedF proof, which is what defines the coercion.
--
sem-Out : ∀ {F : Functor} → WellFormedF F → ⟦μ⟧ F → ⟦ F ⟧F (⟦μ⟧ F)
sem-Out {F} wf x = coerce-μ-out wf (⟦μ⟧ F) (outS (translateF IntRep F) x)

-- | Catamorphism: given algebra F(A) → A, fold μF → A
--
-- OCP-0003: Defined via SPF's cataS with coercions.
-- Requires a WellFormedF proof, which is what defines the coercion.
--
sem-cata : ∀ {F : Functor} → WellFormedF F → {A : Set} → (⟦ F ⟧F A → A) → ⟦μ⟧ F → A
sem-cata {F} wf {A} alg = cataS {translateF IntRep F} (λ x → alg (coerce-μ-out wf A x))

-- | Paramorphism: fold with access to original substructure
--
-- OCP-0003 Phase 10: Derived from sem-cata, so termination is sem-cata's.
-- Para's algebra receives (⟦ F ⟧F (⟦μ⟧ F × A)), giving access to both
-- the original substructure (⟦μ⟧ F) and the recursive result (A).
--
-- Implementation: Encode via sem-cata with a product that carries both
-- the original structure and the recursive result.
--
sem-para : ∀ {F : Functor} → WellFormedF F → {A : Set}
         → (⟦ F ⟧F (⟦μ⟧ F × A) → A) → ⟦μ⟧ F → A
sem-para {F} wf {A} alg x = proj₂ (sem-cata wf alg' x)
  where
    alg' : ⟦ F ⟧F (⟦μ⟧ F × A) → (⟦μ⟧ F × A)
    alg' fx = (sem-In F (sem-fmap F proj₁ fx) , alg fx)

------------------------------------------------------------------------
-- ν-type Coercions (OCP-0003)
--
-- Similar to μ-type coercions, for ν-type (coinductive) operations.
------------------------------------------------------------------------

-- | Coerce from ⟦ F ⟧F to ⟦ translateF F ⟧SF (for ν-type operations)
coerce-ν-in : ∀ F (X : Set) → ⟦ F ⟧F X → ⟦ translateF IntRep F ⟧SF X
coerce-ν-in = coerce-μ-in  -- Same structure

-- | Coerce from ⟦ translateF F ⟧SF to ⟦ F ⟧F (for ν-type operations)
-- Requires a WellFormedF proof, which is what defines the coercion.
coerce-ν-out : ∀ {F} → WellFormedF F → (X : Set) → ⟦ translateF IntRep F ⟧SF X → ⟦ F ⟧F X
coerce-ν-out = coerce-μ-out  -- Same structure

------------------------------------------------------------------------
-- ν-type Operations (OCP-0003: Defined via SPF)
------------------------------------------------------------------------

-- | CoOut: νF → F(νF) (observation)
--
-- OCP-0003: Defined via SPF's unfoldS with coercion.
-- Requires a WellFormedF proof, which is what defines the coercion.
--
sem-CoOut : ∀ {F : Functor} → WellFormedF F → ⟦ν⟧ F → ⟦ F ⟧F (⟦ν⟧ F)
sem-CoOut {F} wf x = coerce-ν-out wf (⟦ν⟧ F) (unfoldS x)

-- | CoIn: F(νF) → νF (coalgebra)
--
-- OCP-0003: Defined via SPF's anaS with the identity coalgebra.
-- CoIn packages an F-layer observation as a ν-value.
--
sem-CoIn : ∀ (F : Functor) → ⟦ F ⟧F (⟦ν⟧ F) → ⟦ν⟧ F
unfoldS (sem-CoIn F x) = coerce-ν-in F (⟦ν⟧ F) x

------------------------------------------------------------------------
-- ν-type Lambek Laws (OCP-0003)
--
-- By Lambek's Lemma (dual), Out and in-ν are inverses:
--   sem-CoOut ∘ sem-CoIn = id  (Out ∘ in-ν = id)
--   sem-CoIn ∘ sem-CoOut = id  (in-ν ∘ Out = id)
------------------------------------------------------------------------

-- | Out ∘ in-ν = id (Lambek, one direction)
--
-- Proof: unfoldS (sem-CoIn F x) = coerce-ν-in F x (by definition)
--        sem-CoOut wf (sem-CoIn F x) = coerce-ν-out wf (unfoldS (sem-CoIn F x))
--                                    = coerce-ν-out wf (coerce-ν-in F x)
--                                    = x  (by round-trip)
--
sem-CoOut-CoIn : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦ F ⟧F (⟦ν⟧ F))
               → sem-CoOut wf (sem-CoIn F x) ≡ x
sem-CoOut-CoIn {F} wf x = coerce-μ-round-trip wf (⟦ν⟧ F) x


-- | Anamorphism: given coalgebra A → F(A), unfold A → νF
--
-- D062: guardedness-CHECKED corecursion (global --guardedness) — the mutual
-- `sfmapSemAna` places the corecursive `sem-ana` calls structurally at SId, so
-- Agda sees the guard. Bridged to `sfmap` by `sfmapSemAna-is-sfmap`.
mutual
  sem-ana : ∀ (F : Functor) {A : Set} → (A → ⟦ F ⟧F A) → A → ⟦ν⟧ F
  unfoldS (sem-ana F {A} coalg a) =
    sfmapSemAna F (translateF IntRep F) coalg (coerce-ν-in F A (coalg a))

  sfmapSemAna : ∀ (F : Functor) (H : SFunctor) {A : Set}
              → (A → ⟦ F ⟧F A) → ⟦ H ⟧SF A → ⟦ H ⟧SF (⟦ν⟧ F)
  sfmapSemAna F (SK B)     coalg x        = x
  sfmapSemAna F SId        coalg a        = sem-ana F coalg a
  sfmapSemAna F (H₁ S⊕ H₂) coalg (inj₁ x) = inj₁ (sfmapSemAna F H₁ coalg x)
  sfmapSemAna F (H₁ S⊕ H₂) coalg (inj₂ y) = inj₂ (sfmapSemAna F H₂ coalg y)
  sfmapSemAna F (H₁ S⊗ H₂) coalg (x , y)  = (sfmapSemAna F H₁ coalg x , sfmapSemAna F H₂ coalg y)

-- | The mutual `sfmapSemAna` IS `sfmap` of the corecursor (D062): structural
-- induction on the functor code, refl at the leaves. `F` explicit (non-injective
-- `⟦ F ⟧F` in coalg).
sfmapSemAna-is-sfmap : ∀ (F : Functor) (H : SFunctor) {A : Set}
                       (coalg : A → ⟦ F ⟧F A) (x : ⟦ H ⟧SF A)
                     → sfmapSemAna F H coalg x ≡ sfmap H (sem-ana F coalg) x
sfmapSemAna-is-sfmap F (SK B)     coalg x        = refl
sfmapSemAna-is-sfmap F SId        coalg a        = refl
sfmapSemAna-is-sfmap F (H₁ S⊕ H₂) coalg (inj₁ x) = cong inj₁ (sfmapSemAna-is-sfmap F H₁ coalg x)
sfmapSemAna-is-sfmap F (H₁ S⊕ H₂) coalg (inj₂ y) = cong inj₂ (sfmapSemAna-is-sfmap F H₂ coalg y)
sfmapSemAna-is-sfmap F (H₁ S⊗ H₂) coalg (x , y)  =
  cong₂ _,_ (sfmapSemAna-is-sfmap F H₁ coalg x) (sfmapSemAna-is-sfmap F H₂ coalg y)

-- | Structured Fusion: μ-anchored hylomorphism (correct by construction)
--
-- OCP-0003: Unlike Hylo where termination is a CONTRACT (coalgebra must
-- destruct the μ-component), Fuse guarantees termination STRUCTURALLY:
-- - Input1 is μG (well-founded inductive type)
-- - Transform receives pre-destructed G-layer via out-μ
-- - Transform produces F-layer with same μG values (rearranged)
-- - Recursion is structural on the μG subterms
--
-- The TERMINATING pragma on fuseS is JUSTIFIED (unlike sem-hylo) because:
-- - Transform is an IR morphism (total, cannot synthesize values)
-- - Therefore μG values in output came from input (subterms)
-- - This is a valid structural recursion that Agda cannot see
--
-- Equivalence: fuse alg transform = cata (alg ∘ fmap fuse ∘ transform)
-- But computed directly for deforestation (no intermediate structure).
--
-- | Natural Transformation Fusion (TERMINATING-free)
--
-- OCP-0003: When the transform is a NATURAL TRANSFORMATION (parametric in
-- the recursive position), fusion is cataS's structural recursion.
--
-- A natural transform `∀ {A} → ⟦ G ⟧F A → ⟦ F ⟧F A` cannot inspect the A values,
-- so it reduces to structural recursion: fuseNatS transform alg = cataS (alg ∘ transform)
--
-- This is the preferred version when the transform is known to be natural.
-- For transforms that inspect recursive positions, use sem-fuse instead.
--
-- Note: At the IR level, transforms are monomorphic (IR (⟦ G ⟧T X) (⟦ F ⟧T X)).
-- When such IR morphisms use only structural operations (no Cata/Ana/etc.),
-- they evaluate to natural transformations.
--
sem-fuseNat : ∀ (F G : Functor) → WellFormedF F → WellFormedF G → {B : Set}
            → (∀ {A} → ⟦ G ⟧F A → ⟦ F ⟧F A)   -- natural transform: G → F
            → (⟦ F ⟧F B → B)                   -- algebra: F(B) → B
            → ⟦μ⟧ G → B
sem-fuseNat F G wfF wfG {B} transform alg =
  fuseNatS {translateF IntRep F} {translateF IntRep G} {B}
    (coerce-μ-in F _ ∘ transform ∘ coerce-μ-out wfG _)
    (alg ∘ coerce-μ-out wfF B)

-- | Congruence for `sem-fuseNat`: pointwise-equal natural transforms and
-- pointwise-equal algebras give equal folds. (D062: lets the optimizer/escape/
-- fusion correctness proofs lift `appNatTr-F (map-nt t) ≡ appNatTr-F t` and the
-- algebra correctness through the `Fuse`/`Hylo` meaning.) Reduces to
-- `cataS-cong` since `sem-fuseNat … = cataS (alg ∘ transform ∘ coercions)`.
sem-fuseNat-cong : ∀ (F G : Functor) (wfF : WellFormedF F) (wfG : WellFormedF G) {B : Set}
                 → (φ ψ : ∀ {A} → ⟦ G ⟧F A → ⟦ F ⟧F A)
                 → (alg₁ alg₂ : ⟦ F ⟧F B → B)
                 → (∀ {A} (g : ⟦ G ⟧F A) → φ g ≡ ψ g)
                 → (∀ y → alg₁ y ≡ alg₂ y)
                 → (x : ⟦μ⟧ G)
                 → sem-fuseNat F G wfF wfG φ alg₁ x ≡ sem-fuseNat F G wfF wfG ψ alg₂ x
sem-fuseNat-cong F G wfF wfG {B} φ ψ alg₁ alg₂ φψ-eq alg-eq x =
  cataS-cong Φ-eq x
  where
    Φ-eq : ∀ (z : ⟦ translateF IntRep G ⟧SF B)
         → alg₁ (coerce-μ-out wfF B (coerce-μ-in F B (φ (coerce-μ-out wfG B z))))
         ≡ alg₂ (coerce-μ-out wfF B (coerce-μ-in F B (ψ (coerce-μ-out wfG B z))))
    Φ-eq z =
      trans (cong (λ w → alg₁ (coerce-μ-out wfF B (coerce-μ-in F B w)))
                  (φψ-eq (coerce-μ-out wfG B z)))
            (alg-eq (coerce-μ-out wfF B (coerce-μ-in F B (ψ (coerce-μ-out wfG B z)))))

-- | Monoid-accumulating natural fusion (the `fuseNatW` wrapper, D062). The
-- trace counterpart of `sem-fuseNat`: same coercions, but the algebra returns
-- a `(monoid , value)` pair threaded by `fuseNatW` in fused depth-first order
-- (children, then algebra post). The transform is a NATURAL transformation, so
-- it realizes no effects and contributes the monoid unit `ε` per layer — all
-- accumulation comes from the algebra. With `M = List SigOpEvent` this is the
-- SigOp trace of the (structural, total) fused hylomorphism. Pragma-free:
-- `fuseNatW` is `cataS`-derived. Replaces the `fuseW`-based `sem-fuse-events`.
sem-fuseNat-events : ∀ {M : Set} (_·_ : M → M → M) (ε : M)
                     (F G : Functor) → WellFormedF F → WellFormedF G → {B : Set}
                   → (∀ {A} → ⟦ G ⟧F A → ⟦ F ⟧F A)   -- natural transform: G ⇒ F
                   → (⟦ F ⟧F B → M × B)               -- algebra: F(B) → (M , B)
                   → ⟦μ⟧ G → M × B
sem-fuseNat-events {M} _·_ ε F G wfF wfG {B} transform alg =
  fuseNatW {translateF IntRep F} {translateF IntRep G} {B} {M} _·_ ε
    (λ {A} sg → (ε , coerce-μ-in F A (transform (coerce-μ-out wfG A sg))))
    (λ sfb → alg (coerce-μ-out wfF B sfb))

------------------------------------------------------------------------
-- μ-Coercion Round-Trip Properties (OCP-0003)
--
-- The coercions between ⟦ F ⟧F and ⟦ translateF F ⟧SF are inverses.
-- This is proven by structural induction on F, using the type-level
-- round-trip lemmas for the K case.
------------------------------------------------------------------------

-- | Round-trip: coerce-μ-out ∘ coerce-μ-in ≡ id
-- | coerce-μ-round-trip: Requires WellFormedF (see coerce-wf-μ-round-trip above)
-- | coerce-μ⁻¹-round-trip: Requires WellFormedF (see coerce-wf-μ⁻¹-round-trip above)

------------------------------------------------------------------------
-- Recursion Scheme Laws (OCP-0003: Proven for Well-Formed Functors)
--
-- These capture the key properties of initial algebras and final
-- coalgebras. Proven for well-formed functors.
------------------------------------------------------------------------

-- | In and Out are inverses (Lambek's Lemma, one direction)
--
-- OCP-0003: Proven using coerce-μ-round-trip.
--
sem-Out-In : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦ F ⟧F (⟦μ⟧ F)) → sem-Out wf (sem-In F x) ≡ x
sem-Out-In wf x = coerce-μ-round-trip wf _ x

-- | In and Out are inverses (Lambek's Lemma, other direction)
--
-- OCP-0003: Proven using coerce-μ⁻¹-round-trip.
--
sem-In-Out : ∀ {F : Functor} → (wf : WellFormedF F) → (x : ⟦μ⟧ F) → sem-In F (sem-Out wf x) ≡ x
sem-In-Out wf ⟨ y ⟩ = cong ⟨_⟩ (coerce-μ⁻¹-round-trip wf _ y)

------------------------------------------------------------------------
-- Fmap-Coercion Coherence for μ (OCP-0003)
--
-- This relates sem-fmap (working on ⟦ F ⟧F) to sfmap (working on ⟦ translateF F ⟧SF)
-- through the coercions.
------------------------------------------------------------------------

-- | sem-fmap through coercions equals sfmap
--
-- coerce-μ-in F ∘ sem-fmap F f ≡ sfmap (translateF F) f ∘ coerce-μ-in F
--
fmap-coerce-μ-coherence : ∀ F {X Y : Set} (f : X → Y) (x : ⟦ F ⟧F X)
                        → coerce-μ-in F Y (sem-fmap F f x) ≡ sfmap (translateF IntRep F) f (coerce-μ-in F X x)
fmap-coerce-μ-coherence (K A) f x = refl
fmap-coerce-μ-coherence Id f x = refl
fmap-coerce-μ-coherence (F ⊕ G) f (inj₁ x) = cong inj₁ (fmap-coerce-μ-coherence F f x)
fmap-coerce-μ-coherence (F ⊕ G) f (inj₂ y) = cong inj₂ (fmap-coerce-μ-coherence G f y)
fmap-coerce-μ-coherence (F ⊗ G) f (x , y) = cong₂ _,_ (fmap-coerce-μ-coherence F f x) (fmap-coerce-μ-coherence G f y)

-- | The inverse direction: sfmap through coercions equals sem-fmap
--
-- coerce-μ-out wf ∘ sfmap (translateF F) f ≡ sem-fmap F f ∘ coerce-μ-out wf
--
fmap-coerce-μ-coherence′ : ∀ {F} (wf : WellFormedF F) {X Y : Set} (f : X → Y) (x : ⟦ translateF IntRep F ⟧SF X)
                         → coerce-μ-out wf Y (sfmap (translateF IntRep F) f x) ≡ sem-fmap F f (coerce-μ-out wf X x)
fmap-coerce-μ-coherence′ (wf-K pA) f x = refl
fmap-coerce-μ-coherence′ wf-Id f x = refl
fmap-coerce-μ-coherence′ (wf-Sum wfF wfG) f (inj₁ x) = cong inj₁ (fmap-coerce-μ-coherence′ wfF f x)
fmap-coerce-μ-coherence′ (wf-Sum wfF wfG) f (inj₂ y) = cong inj₂ (fmap-coerce-μ-coherence′ wfG f y)
fmap-coerce-μ-coherence′ (wf-Prod wfF wfG) f (x , y) = cong₂ _,_ (fmap-coerce-μ-coherence′ wfF f x) (fmap-coerce-μ-coherence′ wfG f y)

------------------------------------------------------------------------
-- Catamorphism Laws (OCP-0003: Proven)
------------------------------------------------------------------------

-- | Catamorphism computation law (PROVEN)
--
-- OCP-0003: Proven using SPF's cataS-computation and coercion coherence.
--
-- Proof:
--   sem-cata wf alg (sem-In F x)
--   = cataS (alg ∘ coerce-μ-out wf) ⟨ coerce-μ-in F x ⟩
--   = (alg ∘ coerce-μ-out wf) (sfmapCata (translateF F) ... (coerce-μ-in F x))
--   By cataS-computation and coherence properties.
--
sem-cata-compute : ∀ {F : Functor} → (wf : WellFormedF F) → ∀ {A : Set} (alg : ⟦ F ⟧F A → A) (x : ⟦ F ⟧F (⟦μ⟧ F))
                 → sem-cata wf alg (sem-In F x) ≡ alg (sem-fmap F (sem-cata wf alg) x)
sem-cata-compute {F} wf {A} alg x =
  let TF = translateF IntRep F
      alg′ = λ y → alg (coerce-μ-out wf A y)
      step1 : cataS {TF} alg′ ⟨ coerce-μ-in F (⟦μ⟧ F) x ⟩ ≡ alg′ (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x))
      step1 = cataS-computation TF alg′ (coerce-μ-in F (⟦μ⟧ F) x)
      step2 : alg′ (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x))
            ≡ alg (coerce-μ-out wf A (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x)))
      step2 = refl
      step3 : coerce-μ-out wf A (sfmap TF (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x))
            ≡ sem-fmap F (cataS alg′) (coerce-μ-out wf (⟦μ⟧ F) (coerce-μ-in F (⟦μ⟧ F) x))
      step3 = fmap-coerce-μ-coherence′ wf (cataS alg′) (coerce-μ-in F (⟦μ⟧ F) x)
      step4 : coerce-μ-out wf (⟦μ⟧ F) (coerce-μ-in F (⟦μ⟧ F) x) ≡ x
      step4 = coerce-μ-round-trip wf (⟦μ⟧ F) x
      step5 : sem-fmap F (cataS alg′) x ≡ sem-fmap F (sem-cata wf alg) x
      step5 = refl
  in trans step1 (trans step2 (cong alg (trans step3 (cong (sem-fmap F (sem-cata wf alg)) step4))))



------------------------------------------------------------------------
-- Hylomorphism Laws (OCP-0003 Phase 10)
--
-- D062: `sem-hylo`/`sem-fuse` (the `fuseW`-based folds) are GONE; `Fuse`/
-- `Hylo` now carry a natural transformation (`NatTr`) and denote via the
-- total `sem-fuseNat`/`sem-fuseNat-events`. By `fuse ≡ hylo` the two schemes
-- coincide definitionally (both fold `cataS (alg ∘ transform)`), so the old
-- `sem-hylo-is-fuse` bridge is vacuous and has been removed.
------------------------------------------------------------------------