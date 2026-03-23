-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors


------------------------------------------------------------------------
-- Once.Category.Laws
--
-- Proofs of the categorical laws for Once's IR.
-- These establish that IR forms a category.
------------------------------------------------------------------------

module Once.Category.Laws where


open import Once.Type
open import Once.CCC.IR
open import Once.Semantics.IR using (⟦_⟧; eval′)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import Function using (_∘′_)

------------------------------------------------------------------------
-- Category Laws
------------------------------------------------------------------------

-- | Left identity: id ∘ f ≡ f (semantically)
--
-- For any morphism f : A → B, composing with identity on the left
-- gives back f.
--
eval-id-left : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
             → eval′ (id ∘ f) x ≡ eval′ f x
eval-id-left f x = refl

-- | Right identity: f ∘ id ≡ f (semantically)
--
-- For any morphism f : A → B, composing with identity on the right
-- gives back f.
--
eval-id-right : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
              → eval′ (f ∘ id) x ≡ eval′ f x
eval-id-right f x = refl

-- | Associativity: (f ∘ g) ∘ h ≡ f ∘ (g ∘ h) (semantically)
--
-- Composition is associative.
--
eval-assoc : ∀ {A B C D} (f : IR C D) (g : IR B C) (h : IR A B) (x : ⟦ A ⟧)
           → eval′ ((f ∘ g) ∘ h) x ≡ eval′ (f ∘ (g ∘ h)) x
eval-assoc f g h x = refl

------------------------------------------------------------------------
-- Product Laws (Beta)
------------------------------------------------------------------------

-- | fst ∘ ⟨ f , g ⟩ ≡ f
--
-- Projecting the first component of a pair gives the first morphism.
--
eval-fst-pair : ∀ {A B C} (f : IR C A) (g : IR C B) (m : AllocMode) (x : ⟦ C ⟧)
              → eval′ (fst ∘ ⟨ f , g ⟩ m) x ≡ eval′ f x
eval-fst-pair f g m x = refl

-- | snd ∘ ⟨ f , g ⟩ ≡ g
--
-- Projecting the second component of a pair gives the second morphism.
--
eval-snd-pair : ∀ {A B C} (f : IR C A) (g : IR C B) (m : AllocMode) (x : ⟦ C ⟧)
              → eval′ (snd ∘ ⟨ f , g ⟩ m) x ≡ eval′ g x
eval-snd-pair f g m x = refl

------------------------------------------------------------------------
-- Product Laws (Eta/Uniqueness)
------------------------------------------------------------------------

-- | ⟨ fst , snd ⟩ ≡ id (semantically)
--
-- Pairing the projections gives back the identity on products.
--
eval-pair-eta : ∀ {A B} (m : AllocMode) (x : ⟦ A * B ⟧)
              → eval′ (⟨ fst , snd ⟩ m) x ≡ x
eval-pair-eta m (a , b) = refl

-- | Product uniqueness: ⟨ fst ∘ h , snd ∘ h ⟩ ≡ h (semantically)
--
-- Any morphism into a product is uniquely determined by its projections.
-- This is the universal property of products.
--
eval-pair-unique : ∀ {A B C} (h : IR C (A * B)) (m : AllocMode) (x : ⟦ C ⟧)
                 → eval′ (⟨ fst ∘ h , snd ∘ h ⟩ m) x ≡ eval′ h x
eval-pair-unique h m x with eval′ h x
... | (a , b) = refl

------------------------------------------------------------------------
-- Coproduct Laws (Beta)
------------------------------------------------------------------------

-- | (case f g) ∘ inl ≡ f
--
-- Case analysis on a left injection gives the left branch.
--
eval-case-inl : ∀ {A B C} (f : IR A C) (g : IR B C) (m : AllocMode) (x : ⟦ A ⟧)
              → eval′ ((case f g) ∘ inl m) x ≡ eval′ f x
eval-case-inl f g m x = refl

-- | (case f g) ∘ inr ≡ g
--
-- Case analysis on a right injection gives the right branch.
--
eval-case-inr : ∀ {A B C} (f : IR A C) (g : IR B C) (m : AllocMode) (x : ⟦ B ⟧)
              → eval′ ((case f g) ∘ inr m) x ≡ eval′ g x
eval-case-inr f g m x = refl

------------------------------------------------------------------------
-- Coproduct Laws (Eta/Uniqueness)
------------------------------------------------------------------------

-- | (case inl inr) ≡ id (semantically)
--
-- Case analysis that re-injects gives back identity on coproducts.
--
eval-case-eta : ∀ {A B} (m : AllocMode) (x : ⟦ A + B ⟧)
              → eval′ (case (inl m) (inr m)) x ≡ x
eval-case-eta m (inj₁ a) = refl
eval-case-eta m (inj₂ b) = refl

-- | Coproduct uniqueness: [ h ∘ inl , h ∘ inr ] ≡ h (semantically)
--
-- Any morphism from a coproduct is uniquely determined by its restrictions.
-- This is the universal property of coproducts.
--
eval-case-unique : ∀ {A B C} (h : IR (A + B) C) (m : AllocMode) (x : ⟦ A + B ⟧)
                 → eval′ (case (h ∘ inl m) (h ∘ inr m)) x ≡ eval′ h x
eval-case-unique h m (inj₁ a) = refl
eval-case-unique h m (inj₂ b) = refl

------------------------------------------------------------------------
-- Terminal Object Laws
------------------------------------------------------------------------

-- | Any two morphisms to Unit are equal (semantically)
--
-- Unit is terminal: there's a unique morphism from any object to Unit.
--
eval-terminal-unique : ∀ {A} (f : IR A Unit) (x : ⟦ A ⟧)
                     → eval′ f x ≡ eval′ terminal x
eval-terminal-unique f x with eval′ f x
... | tt = refl

------------------------------------------------------------------------
-- Initial Object Laws
------------------------------------------------------------------------

-- | Any two morphisms from Void are equal (semantically)
--
-- Void is initial: there's a unique morphism from Void to any object.
-- This is vacuously true since Void is empty.
--
eval-initial-unique : ∀ {A} (f : IR Void A) (x : ⟦ Void ⟧)
                    → eval′ f x ≡ eval′ initial x
eval-initial-unique f ()

------------------------------------------------------------------------
-- Exponential Laws (Curry/Apply adjunction)
------------------------------------------------------------------------

-- | apply ∘ ⟨ curry f ∘ fst , snd ⟩ ≡ f (semantically)
--
-- This is the beta law for exponentials.
-- The quantity {q} is phantom; the law holds for any quantity.
--
eval-curry-apply : ∀ {A B C q} (f : IR (A * B) C) (m₁ m₂ : AllocMode) (x : ⟦ A * B ⟧)
                 → eval′ (apply {q = q} ∘ ⟨ curry {q = q} f m₁ ∘ fst , snd ⟩ m₂) x ≡ eval′ f x
eval-curry-apply f m₁ m₂ (a , b) = refl

-- | curry (apply ∘ ⟨ g ∘ fst , snd ⟩) ≡ g (semantically, for functions)
--
-- This is the eta law for exponentials.
-- Note: This requires function extensionality for full generality,
-- but we can prove it pointwise.
--
-- With plain functions, application is direct function application.
-- The quantity {q} is phantom; the law holds for any quantity.
eval-curry-eta : ∀ {A B C q} (g : IR A (B ⇒[ q ] C)) (m₁ m₂ : AllocMode) (a : ⟦ A ⟧) (b : ⟦ B ⟧)
               → eval′ (curry {q = q} (apply {q = q} ∘ ⟨ g ∘ fst , snd ⟩ m₁) m₂) a b ≡ eval′ g a b
eval-curry-eta g m₁ m₂ a b = refl

------------------------------------------------------------------------
-- Distributivity Laws
------------------------------------------------------------------------

-- Distributivity of products over coproducts (C × (A + B) ≅ (C × A) + (C × B))
-- See Once.Surface.Correct (distribute-inl and distribute-inr).

------------------------------------------------------------------------
-- Functoriality of Product and Coproduct
------------------------------------------------------------------------

-- | bimap f g = ⟨ f ∘ fst , g ∘ snd ⟩ preserves identity
--
eval-bimap-id : ∀ {A B} (m : AllocMode) (x : ⟦ A * B ⟧)
              → eval′ (⟨ id ∘ fst , id ∘ snd ⟩ m) x ≡ x
eval-bimap-id m (a , b) = refl

-- | bimap preserves composition
--
eval-bimap-compose : ∀ {A B C D E F}
                     (f : IR B C) (g : IR A B) (h : IR E F) (i : IR D E)
                     (m₁ m₂ : AllocMode) (x : ⟦ A * D ⟧)
                   → eval′ (⟨ (f ∘ g) ∘ fst , (h ∘ i) ∘ snd ⟩ m₁) x
                     ≡ eval′ (⟨ f ∘ fst , h ∘ snd ⟩ m₁ ∘ ⟨ g ∘ fst , i ∘ snd ⟩ m₂) x
eval-bimap-compose f g h i m₁ m₂ (a , d) = refl

-- | bicase f g = [ inl ∘ f , inr ∘ g ] preserves identity
--
eval-bicase-id : ∀ {A B} (m : AllocMode) (x : ⟦ A + B ⟧)
               → eval′ (case (inl m ∘ id) (inr m ∘ id)) x ≡ x
eval-bicase-id m (inj₁ a) = refl
eval-bicase-id m (inj₂ b) = refl

------------------------------------------------------------------------
-- Recursion Scheme Laws (OCP-0003)
------------------------------------------------------------------------
--
-- The old fold/unfold laws have been replaced by structured recursion
-- schemes: In/Cata for initial algebras, Out/Ana for final coalgebras.
--
-- Identity laws (semantic):
--   Cata (In m) ≡ id   -- Identity catamorphism
--   Ana Out ≡ id       -- Identity anamorphism
--
-- Fusion laws (conceptual):
--   h ∘ cata alg = cata alg'   (if h ∘ alg = alg' ∘ fmap h)
--   ana coalg ∘ h = ana coalg' (if coalg ∘ h = fmap h ∘ coalg')
--
-- Hylomorphism deforestation:
--   cata alg ∘ ana coalg = hylo alg coalg
--
-- Full proofs require functor fmap operations and universal properties.
-- See SPF.agda for the semantic foundations.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Arrow Laws (D032: Effect System)
------------------------------------------------------------------------
--
-- The arr combinator lifts pure functions to effectful morphisms.
-- arr : (A ⇒ B) → Eff A B
--
-- At runtime, Eff A B is represented the same as A ⇒ B (a function).
-- The distinction is purely for effect tracking at the type level.
--
-- Arrow axioms (from Hughes' "Generalising Monads to Arrows"):
-- In the context of Once, arr is essentially identity on function values.
--
------------------------------------------------------------------------

-- | arr is semantically identity
--
-- Lifting a pure function just returns it unchanged, since Eff A B
-- is semantically the same as A ⇒ B.
--
eval-arr-identity : ∀ {A B} (f : ⟦ A ⇒ B ⟧)
                  → eval′ (arr {q = Many}) f ≡ f
eval-arr-identity f = refl

-- | arr ∘ curry ≡ curry with effectful codomain (conceptually)
--
-- This captures that currying followed by arr produces an effectful
-- curried function. The semantics are the same because effects are
-- purely a type-level distinction.
--
-- Note: The exact formulation depends on how effectful composition
-- is defined. For Once's simple model where Eff = function at runtime,
-- this is trivially true.

------------------------------------------------------------------------
-- OCP-0003: Recursion Scheme Laws (Initial Algebras / Final Coalgebras)
------------------------------------------------------------------------
--
-- These laws establish the properties of the recursion scheme
-- constructors In, Cata, Out, Ana, and Hylo.
--
-- Key theorems:
-- 1. Lambek's Lemma: In and Out are inverses (μF ≅ F(μF))
-- 2. Catamorphism computation: how cata unfolds through In
-- 3. Anamorphism observation: how ana builds through Out
-- 4. Hylo fusion: cata ∘ ana = hylo (deforestation)
------------------------------------------------------------------------

open import Once.Semantics.Machine
  using (sem-In; sem-Out; sem-cata; sem-CoOut; sem-ana; sem-hylo;
         sem-Out-In; sem-In-Out; sem-cata-compute; sem-fmap;
         coerce-functor; coerce-functor⁻¹; ⟦_⟧F)

------------------------------------------------------------------------
-- Lambek's Lemma (Semantic Level)
--
-- At the semantic level, μF ≅ F(μF) via sem-In and sem-Out.
-- This is postulated in Semantics/Core.agda (sem-In-Out, sem-Out-In).
--
-- At the IR level:
--   - In constructs μ-type values
--   - Cata folds μ-type values with an algebra
--   - Out destructs ν-type values (NOT μ-type!)
--   - Ana unfolds to build ν-type values
--
-- The key IR-level law is that Cata with the In algebra is identity.
------------------------------------------------------------------------

-- | Cata In ≡ id (identity catamorphism)
--
-- Folding with the constructor algebra gives back the original value.
-- This is the canonical way to express that μF ≅ F(μF) at the IR level.
--
-- Conceptually: cata In (In x) = In (fmap (cata In) x) = In x (when fmap id = id)
--
postulate
  eval-cata-In-id : ∀ (F : Functor) (m : AllocMode) (x : ⟦ μ-type F ⟧)
                  → eval′ (Cata {F} (In {F} m)) x ≡ x

------------------------------------------------------------------------
-- Catamorphism Laws
--
-- The catamorphism is the unique homomorphism from an initial algebra.
------------------------------------------------------------------------

-- | Functorial map at the Type level
--
-- This applies a function through the functor structure, working with
-- Type-level functor application (⟦ F ⟧T) rather than Set-level (⟦ F ⟧F).
--
fmap-Type : ∀ F {X Y : Type} → (⟦ X ⟧ → ⟦ Y ⟧) → ⟦ ⟦ F ⟧T X ⟧ → ⟦ ⟦ F ⟧T Y ⟧
fmap-Type (K A) f x = x
fmap-Type Id f x = f x
fmap-Type (F ⊕ G) f (inj₁ x) = inj₁ (fmap-Type F f x)
fmap-Type (F ⊕ G) f (inj₂ y) = inj₂ (fmap-Type G f y)
fmap-Type (F ⊗ G) f (x , y) = (fmap-Type F f x , fmap-Type G f y)

-- | Catamorphism computation law
--
-- cata alg (In x) ≡ alg (fmap (cata alg) x)
--
-- This is the defining equation for catamorphisms: to fold a structure,
-- first recursively fold all substructures, then apply the algebra.
--
-- The proof requires careful handling of coercions between Type-level
-- and Set-level functor applications, so it is postulated here.
-- The semantic foundation is sem-cata-compute in Semantics/Core.
--
postulate
  eval-cata-In : ∀ (F : Functor) {A : Type} (alg : IR (⟦ F ⟧T A) A) (m : AllocMode)
                 (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧)
               → eval′ (Cata {F} alg ∘ In {F} m) x ≡
                 eval′ alg (fmap-Type F (eval′ (Cata {F} alg)) x)

------------------------------------------------------------------------
-- Hylomorphism Laws
--
-- The hylomorphism combines an algebra and coalgebra into a single
-- recursive computation without building intermediate structure.
--
-- Note: Unlike in Haskell where Fix = μ = ν, Once distinguishes
-- μ-type (inductive) from ν-type (coinductive). Therefore the
-- composition Cata ∘ Ana doesn't type-check directly.
--
-- The hylo is the primitive operation; cata and ana are special cases.
------------------------------------------------------------------------

-- | Hylo semantics: recursive application of algebra after coalgebra
--
-- hylo alg coalg x = alg (fmap (hylo alg coalg) (coalg x))
--
-- This is the defining equation for hylomorphisms.
--
postulate
  eval-hylo-unfold : ∀ (F : Functor) {A B : Type}
                     (alg : IR (⟦ F ⟧T B) B) (coalg : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧)
                   → eval′ (Hylo {F} alg coalg) x ≡
                     eval′ alg (fmap-Type F (eval′ (Hylo {F} alg coalg)) (eval′ coalg x))

------------------------------------------------------------------------
-- Ana-Out Identity Law (Coinductive)
--
-- The anamorphism with Out coalgebra is identity on ν-type.
------------------------------------------------------------------------

-- | Ana Out ≡ id (identity anamorphism)
--
-- Unfolding with the destructor coalgebra gives back the original value.
--
postulate
  eval-ana-Out-id : ∀ (F : Functor) (x : ⟦ ν-type F ⟧)
                  → eval′ (Ana {F} (Out {F})) x ≡ x