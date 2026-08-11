-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.SPF
--
-- Strictly Positive Functors (Polynomial Functors)
--
-- This module provides implementations for polynomial functor fixed points
-- with proven properties, used by the semantic coherence layer.
--
-- KEY INSIGHT: The S1 semantic gap exists because Fix F : Type → Type
-- has no way to express where recursive occurrences appear. Polynomial
-- functors solve this by having an explicit "Id" constructor for the
-- recursive position.
--
-- Example: Nat = Fix (Unit + X) becomes Fix (K Unit ⊕ Id)
-- where Id marks the recursive occurrence.
--
-- MATHEMATICAL FOUNDATION:
-- Polynomial functors form the free cartesian category on one generator.
-- This aligns with Once's CCC foundation. Initial algebras of polynomial
-- functors always exist in Set.
--
-- OCP-0003 Phase 6: This module now uses Once.Type.Functor instead of
-- defining its own, enabling the semantic coherence layer.
--
------------------------------------------------------------------------

module Once.SPF where

open import Once.Type using (Type; Functor; K; Id; _⊕_; _⊗_)
open import Once.Semantics.Machine using (⟦_⟧; ⟦_⟧F)
-- OCP-0003 Phase 6: Import base functor for coherence
open import Once.Semantics.Functor as Base using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; νS; sfmap)
open import Once.Functor.Translate using (translateF; μ-sem; ν-sem)
open import Data.Integer using (ℤ)

open import Level using (Level; 0ℓ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

------------------------------------------------------------------------
-- OCP-0003: Functor Codes imported from Once.Type
--
-- Previously defined here; now imported for semantic coherence.
-- Functor codes: K (constant), Id (recursive), ⊕ (sum), ⊗ (product)
------------------------------------------------------------------------

-- Re-export for backwards compatibility
-- (Functor, K, Id, _⊕_, _⊗_ imported from Once.Type above)

------------------------------------------------------------------------
-- OCP-0003: Functor Interpretation imported from Once.Semantics.IR
--
-- Previously defined here; now imported for semantic coherence.
-- ⟦_⟧F : Functor → Set → Set
------------------------------------------------------------------------

-- Re-export for backwards compatibility
-- (⟦_⟧F imported from Once.Semantics.IR above)

------------------------------------------------------------------------
-- Fixed Point (Initial Algebra)
--
-- μ F is the initial algebra of functor F.
-- It satisfies μ F ≅ F (μ F).
------------------------------------------------------------------------

-- | Initial algebra of a polynomial functor
--
-- This is the proper recursive type: μ F ≅ F (μ F)
-- The ⟨_⟩ constructor witnesses F (μ F) → μ F.
-- The inverse is given by out below.
--
data μ (F : Functor) : Set where
  ⟨_⟩ : ⟦ F ⟧F (μ F) → μ F

-- | Destructor (inverse of ⟨_⟩)
out : ∀ (F : Functor) → μ F → ⟦ F ⟧F (μ F)
out F ⟨ x ⟩ = x

------------------------------------------------------------------------
-- Functorial Map (fmap)
--
-- Every polynomial functor has a canonical fmap that respects
-- the functor structure.
------------------------------------------------------------------------

-- | Functorial map
--
-- Applies a function to every recursive position.
--
fmap : ∀ F → {X Y : Set} → (X → Y) → ⟦ F ⟧F X → ⟦ F ⟧F Y
fmap (K A) f x = x                           -- Constants unchanged
fmap Id f x = f x                            -- Apply at recursive position
fmap (F ⊕ G) f (inj₁ x) = inj₁ (fmap F f x)  -- Map into left
fmap (F ⊕ G) f (inj₂ y) = inj₂ (fmap G f y)  -- Map into right
fmap (F ⊗ G) f (x , y) = (fmap F f x , fmap G f y)  -- Map into both

------------------------------------------------------------------------
-- Functor Laws
--
-- fmap preserves identity and composition.
------------------------------------------------------------------------

-- | fmap preserves identity
fmap-id : ∀ F {X : Set} (x : ⟦ F ⟧F X) → fmap F (λ z → z) x ≡ x
fmap-id (K A) x = refl
fmap-id Id x = refl
fmap-id (F ⊕ G) (inj₁ x) = cong inj₁ (fmap-id F x)
fmap-id (F ⊕ G) (inj₂ y) = cong inj₂ (fmap-id G y)
fmap-id (F ⊗ G) (x , y) = cong₂ _,_ (fmap-id F x) (fmap-id G y)
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B}
          → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    cong₂ f refl refl = refl

-- | fmap preserves composition
fmap-comp : ∀ F {X Y Z : Set} (f : X → Y) (g : Y → Z) (x : ⟦ F ⟧F X)
          → fmap F (λ z → g (f z)) x ≡ fmap F g (fmap F f x)
fmap-comp (K A) f g x = refl
fmap-comp Id f g x = refl
fmap-comp (F ⊕ G) f g (inj₁ x) = cong inj₁ (fmap-comp F f g x)
fmap-comp (F ⊕ G) f g (inj₂ y) = cong inj₂ (fmap-comp G f g y)
fmap-comp (F ⊗ G) f g (x , y) = cong₂ _,_ (fmap-comp F f g x) (fmap-comp G f g y)
  where
    cong₂ : ∀ {A B C : Set} (h : A → B → C) {x x' : A} {y y' : B}
          → x ≡ x' → y ≡ y' → h x y ≡ h x' y'
    cong₂ h refl refl = refl

------------------------------------------------------------------------
-- Catamorphism (Fold)
--
-- The universal property of initial algebras: there is a unique
-- morphism from μ F to any F-algebra.
------------------------------------------------------------------------

-- | Catamorphism (fold)
--
-- Given an F-algebra (A, alg : F A → A), there is a unique
-- homomorphism cata alg : μ F → A such that:
--
--   cata alg ∘ ⟨_⟩ = alg ∘ fmap F (cata alg)
--
-- Implementation note: We use mutual recursion with fmapCata to
-- convince Agda's termination checker that this terminates.
-- The key insight is that fmapCata G descends into the functor
-- structure while cata descends into μ F.
--
mutual
  cata : ∀ {F} {A : Set} → (⟦ F ⟧F A → A) → μ F → A
  cata {F} alg ⟨ x ⟩ = alg (fmapCata F alg x)

  -- Helper: apply cata to all recursive positions
  fmapCata : ∀ F {G} {A : Set} → (⟦ G ⟧F A → A) → ⟦ F ⟧F (μ G) → ⟦ F ⟧F A
  fmapCata (K A) alg x = x
  fmapCata Id alg x = cata alg x
  fmapCata (F ⊕ G) alg (inj₁ x) = inj₁ (fmapCata F alg x)
  fmapCata (F ⊕ G) alg (inj₂ y) = inj₂ (fmapCata G alg y)
  fmapCata (F ⊗ G) alg (x , y) = (fmapCata F alg x , fmapCata G alg y)

------------------------------------------------------------------------
-- Catamorphism Laws (OCP-0003 Phase 6)
--
-- These laws establish key properties of cata:
-- 1. fmapCata ≡ fmap ∘ cata (fmapCata is fmap with cata)
-- 2. Computation law: cata alg ⟨ x ⟩ ≡ alg (fmap (cata alg) x)
-- 3. Identity: cata ⟨_⟩ ≡ id
------------------------------------------------------------------------

-- | fmapCata is equivalent to fmap composed with cata
--
-- This is the key lemma relating the mutual recursion helper
-- to the standard fmap operation.
--
mutual
  fmapCata-is-fmap : ∀ F {G} {A : Set} (alg : ⟦ G ⟧F A → A) (x : ⟦ F ⟧F (μ G))
                   → fmapCata F alg x ≡ fmap F (cata alg) x
  fmapCata-is-fmap (K B) alg x = refl
  fmapCata-is-fmap Id alg x = refl
  fmapCata-is-fmap (F ⊕ G) alg (inj₁ x) = cong inj₁ (fmapCata-is-fmap F alg x)
  fmapCata-is-fmap (F ⊕ G) alg (inj₂ y) = cong inj₂ (fmapCata-is-fmap G alg y)
  fmapCata-is-fmap (F ⊗ G) alg (x , y) =
    cong₂ _,_ (fmapCata-is-fmap F alg x) (fmapCata-is-fmap G alg y)
    where
      cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B}
            → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
      cong₂ f refl refl = refl

-- | Catamorphism computation law
--
-- cata alg ⟨ x ⟩ ≡ alg (fmap F (cata alg) x)
--
-- This follows directly from the definition and fmapCata-is-fmap.
--
cata-computation : ∀ (F : Functor) {A : Set} (alg : ⟦ F ⟧F A → A) (x : ⟦ F ⟧F (μ F))
                 → cata {F} alg ⟨ x ⟩ ≡ alg (fmap F (cata {F} alg) x)
cata-computation F {A} alg x = cong alg (fmapCata-is-fmap F {F} {A} alg x)

-- | Identity catamorphism: cata ⟨_⟩ ≡ id
--
-- When the algebra is the constructor ⟨_⟩, cata gives back the original value.
-- Proof by induction on μ F.
--
mutual
  cata-In-id : ∀ {F} (x : μ F) → cata ⟨_⟩ x ≡ x
  cata-In-id {F} ⟨ x ⟩ = cong ⟨_⟩ (fmapCata-In-id F x)

  -- Helper: fmapCata with ⟨_⟩ is identity on the functor structure
  fmapCata-In-id : ∀ F {G} (x : ⟦ F ⟧F (μ G)) → fmapCata F ⟨_⟩ x ≡ x
  fmapCata-In-id (K B) x = refl
  fmapCata-In-id Id x = cata-In-id x
  fmapCata-In-id (F ⊕ G) (inj₁ x) = cong inj₁ (fmapCata-In-id F x)
  fmapCata-In-id (F ⊕ G) (inj₂ y) = cong inj₂ (fmapCata-In-id G y)
  fmapCata-In-id (F ⊗ G) (x , y) =
    cong₂ _,_ (fmapCata-In-id F x) (fmapCata-In-id G y)
    where
      cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B}
            → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
      cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Greatest Fixed Point (Final Coalgebra)
--
-- ν F is the greatest fixed point of functor F.
-- It satisfies ν F ≅ F (ν F), just like μ F, but is coinductive.
--
-- Key difference:
--   μ F (least fixed point) - inductive, finite, consumed by cata
--   ν F (greatest fixed point) - coinductive, potentially infinite, produced by ana
--
-- For strictly positive functors over Set, μ F ≅ ν F for finite data.
------------------------------------------------------------------------

-- | Greatest fixed point of a polynomial functor (coinductive)
--
-- Uses Agda's coinductive records with copatterns.
-- The 'unfold' field gives F (ν F) from ν F.
--
-- Productivity of operations on ν F is genuine — each unfold produces one
-- F-layer before recursive calls — and asserted by the TERMINATING pragmas
-- below. Per D062 the sound replacement is `--guardedness`-checked corecursion
-- (deferred); the sized-types proof is deleted (the flag is unsound-flagged).
--
record ν (F : Functor) : Set where
  coinductive
  field
    unfold : ⟦ F ⟧F (ν F)

open ν public

------------------------------------------------------------------------
-- Anamorphism (Unfold)
--
-- The dual of cata: builds a ν F from a coalgebra.
------------------------------------------------------------------------

-- | Anamorphism (unfold) - builds ν F from a coalgebra
--
-- Given an F-coalgebra (A, coalg : A → F A), builds a ν F.
--
-- TERMINATING justification: The recursive call (ana coalg) appears inside
-- fmap F, which only applies it to recursive positions of F. This is
-- productive because each unfold produces one F-layer before recursive calls.
-- (D062: TERMINATING here is an honest productivity assertion; the sound
-- replacement is `--guardedness` — deferred, see the anaS note in Functor.Base.)
--
{-# TERMINATING #-}
ana : ∀ {F} {A : Set} → (A → ⟦ F ⟧F A) → A → ν F
unfold (ana {F} coalg a) = fmap F (ana coalg) (coalg a)

-- | Anamorphism specification
--
-- unfold (ana coalg a) = fmap F (ana coalg) (coalg a)
--
-- This is definitionally true by the copattern definition above.
--
ana-unfold : ∀ (F : Functor) {A : Set} (coalg : A → ⟦ F ⟧F A) (a : A)
           → unfold (ana {F} coalg a) ≡ fmap F (ana coalg) (coalg a)
ana-unfold F coalg a = refl

------------------------------------------------------------------------
-- Bisimulation for Coinductive Types
--
-- To prove properties of coinductive values, we need bisimulation rather
-- than induction. Two ν F values are bisimilar if they produce the same
-- observations at every level.
------------------------------------------------------------------------

-- | Relational interpretation of functors
--
-- Lifts a relation R : A → B → Set through functor structure.
-- Two F-structures are related if corresponding parts are related.
--
⟦_⟧F-rel : (F : Functor) {A B : Set} (R : A → B → Set) → ⟦ F ⟧F A → ⟦ F ⟧F B → Set
⟦ K _ ⟧F-rel R x y = x ≡ y
⟦ Id ⟧F-rel R x y = R x y
⟦ F ⊕ G ⟧F-rel R (inj₁ x) (inj₁ y) = ⟦ F ⟧F-rel R x y
⟦ F ⊕ G ⟧F-rel R (inj₁ x) (inj₂ y) = ⊥
⟦ F ⊕ G ⟧F-rel R (inj₂ x) (inj₁ y) = ⊥
⟦ F ⊕ G ⟧F-rel R (inj₂ x) (inj₂ y) = ⟦ G ⟧F-rel R x y
⟦ F ⊗ G ⟧F-rel R (x₁ , x₂) (y₁ , y₂) = ⟦ F ⟧F-rel R x₁ y₁ × ⟦ G ⟧F-rel R x₂ y₂

-- | Bisimulation relation on ν F (coinductive)
--
-- Two coinductive values are bisimilar if their unfoldings are related
-- through the relational interpretation, with bisimilarity at recursive positions.
--
-- Productivity is genuine (one F-layer per unfold); see the D062 note above.
--
record _∼_ {F : Functor} (x y : ν F) : Set where
  coinductive
  field
    unfold-∼ : ⟦ F ⟧F-rel (_∼_ {F}) (unfold x) (unfold y)

open _∼_

-- | Bisimulation implies equality (coalgebraic extensionality)
--
-- This is a standard principle in coalgebra theory: bisimilar values are equal.
-- In Cubical Agda this can be proven; in standard Agda we postulate it.
--
-- This is a more principled postulate than ana-Out-id directly, as it
-- captures a general mathematical fact rather than a specific property.
--
postulate
  bisim-to-eq : ∀ {F : Functor} (x y : ν F) → x ∼ y → x ≡ y

-- | fmap preserves relational structure
--
-- If R relates recursive positions, then fmap lifts R through F.
--
fmap-rel : ∀ F {A B : Set} {R : A → B → Set} {f : A → A} {g : B → B}
         → (∀ a b → R a b → R (f a) (g b))
         → ∀ x y → ⟦ F ⟧F-rel R x y → ⟦ F ⟧F-rel R (fmap F f x) (fmap F g y)
fmap-rel (K _) pres x y r = r
fmap-rel Id pres x y r = pres x y r
fmap-rel (F ⊕ G) pres (inj₁ x) (inj₁ y) r = fmap-rel F pres x y r
fmap-rel (F ⊕ G) pres (inj₂ x) (inj₂ y) r = fmap-rel G pres x y r
fmap-rel (F ⊗ G) pres (x₁ , x₂) (y₁ , y₂) (r₁ , r₂) =
  fmap-rel F pres x₁ y₁ r₁ , fmap-rel G pres x₂ y₂ r₂

-- | fmap f relates to identity when f relates to identity
--
-- If (f a) R a for all a, then (fmap F f x) R-lifted x.
-- This is the key lemma for proving ana unfold ∼ id.
--
fmap-f-rel : ∀ F {A : Set} {R : A → A → Set} {f : A → A}
           → (∀ a → R (f a) a)
           → ∀ x → ⟦ F ⟧F-rel R (fmap F f x) x
fmap-f-rel (K _) hyp x = refl
fmap-f-rel Id hyp x = hyp x
fmap-f-rel (F ⊕ G) hyp (inj₁ x) = fmap-f-rel F hyp x
fmap-f-rel (F ⊕ G) hyp (inj₂ x) = fmap-f-rel G hyp x
fmap-f-rel (F ⊗ G) hyp (x₁ , x₂) = fmap-f-rel F hyp x₁ , fmap-f-rel G hyp x₂

------------------------------------------------------------------------
-- Anamorphism Laws
--
-- These laws establish key properties of ana, dual to cata laws.
------------------------------------------------------------------------

-- | ana unfold is bisimilar to id (coinductive proof)
--
-- Proof by coinduction:
--   unfold (ana unfold x) = fmap F (ana unfold) (unfold x)  [by ana def]
--   We need: ⟦ F ⟧F-rel _∼_ (fmap F (ana unfold) (unfold x)) (unfold x)
--   By fmap-f-rel with coinductive hypothesis (ana unfold y ∼ y), this holds.
--
-- TERMINATING justification: Same as ana - recursive calls are guarded by fmap.
-- (D062: honest productivity assertion; sound replacement is `--guardedness`.)
--
{-# TERMINATING #-}
ana-unfold-bisim : ∀ (F : Functor) (x : ν F) → ana {F} unfold x ∼ x
unfold-∼ (ana-unfold-bisim F x) = fmap-f-rel F (ana-unfold-bisim F) (unfold x)

-- | Identity anamorphism: ana unfold ≡ id (PROVEN via bisimulation)
--
-- When the coalgebra is the destructor (unfold), ana gives back the original value.
--
-- Proof: ana unfold x ∼ x (by coinduction), then bisim-to-eq gives equality.
--
ana-Out-id : ∀ (F : Functor) (x : ν F) → ana {F} unfold x ≡ x
ana-Out-id F x = bisim-to-eq (ana unfold x) x (ana-unfold-bisim F x)

------------------------------------------------------------------------
-- Embedding μ into ν (finite data is also coinductive)
--
-- For finite data, the least and greatest fixed points coincide.
------------------------------------------------------------------------

-- | Every inductive μ F can be viewed as coinductive ν F
--
-- Uses cata to fold μ F into ν F.
--
μ-to-ν : ∀ {F} → μ F → ν F
μ-to-ν {F} = cata {F} {ν F} (λ x → record { unfold = x })

------------------------------------------------------------------------
-- Anamorphism for μ F (when coalgebra terminates)
--
-- For coalgebras that produce finite data, we can build μ F directly.
-- This requires a well-founded termination argument.
------------------------------------------------------------------------

-- | Anamorphism with explicit termination (fuel-based)
--
-- Given a fuel bound, unfolds at most n levels.
-- Returns nothing if fuel runs out.
--
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; map)

mutual
  ana-fuel : ∀ {F} {A : Set} → ℕ → (A → ⟦ F ⟧F A) → A → Maybe (μ F)
  ana-fuel zero coalg a = nothing
  ana-fuel {F} (suc n) coalg a = map ⟨_⟩ (fmapAna-fuel F n coalg (coalg a))

  fmapAna-fuel : ∀ G {F} {A : Set} → ℕ → (A → ⟦ F ⟧F A) → ⟦ G ⟧F A → Maybe (⟦ G ⟧F (μ F))
  fmapAna-fuel (K B) n coalg x = just x
  fmapAna-fuel Id n coalg x = ana-fuel n coalg x
  fmapAna-fuel (G₁ ⊕ G₂) n coalg (inj₁ x) = map inj₁ (fmapAna-fuel G₁ n coalg x)
  fmapAna-fuel (G₁ ⊕ G₂) n coalg (inj₂ y) = map inj₂ (fmapAna-fuel G₂ n coalg y)
  fmapAna-fuel (G₁ ⊗ G₂) n coalg (x , y) with fmapAna-fuel G₁ n coalg x | fmapAna-fuel G₂ n coalg y
  ... | just x' | just y' = just (x' , y')
  ... | _ | _ = nothing

------------------------------------------------------------------------
-- Fixed Point Isomorphism
--
-- The key property: μ F ≅ F (μ F)
-- ⟨_⟩ : F (μ F) → μ F
-- out : μ F → F (μ F)
-- These are inverses.
------------------------------------------------------------------------

-- | ⟨_⟩ and out are inverses (one direction)
fold-unfold : ∀ (F : Functor) (x : ⟦ F ⟧F (μ F)) → out F ⟨ x ⟩ ≡ x
fold-unfold F x = refl

-- | ⟨_⟩ and out are inverses (other direction)
unfold-fold : ∀ (F : Functor) (x : μ F) → ⟨ out F x ⟩ ≡ x
unfold-fold F ⟨ x ⟩ = refl

------------------------------------------------------------------------
-- Common Type Patterns
--
-- Standard data types expressed as polynomial functors.
------------------------------------------------------------------------

-- | Unit functor (terminal coalgebra carrier)
UnitF : Functor
UnitF = K Once.Type.Unit

-- | Natural numbers: Nat = Fix (Unit + X) = μ (K Unit ⊕ Id)
NatF : Functor
NatF = K Once.Type.Unit ⊕ Id

Nat : Set
Nat = μ NatF

zeroNat : Nat
zeroNat = ⟨ inj₁ tt ⟩

sucNat : Nat → Nat
sucNat n = ⟨ inj₂ n ⟩

-- | Maybe A = Fix (Unit + A) = μ (K Unit ⊕ K A)
-- Note: Maybe is NOT recursive, but can still be expressed
MaybeF : Type → Functor
MaybeF A = K Once.Type.Unit ⊕ K A

-- | List A = Fix (Unit + A * X) = μ (K Unit ⊕ K A ⊗ Id)
ListF : Type → Functor
ListF A = K Once.Type.Unit ⊕ (K A ⊗ Id)

List : Type → Set
List A = μ (ListF A)

nil : ∀ {A} → List A
nil = ⟨ inj₁ tt ⟩

cons : ∀ {A} → ⟦ A ⟧ → List A → List A
cons x xs = ⟨ inj₂ (x , xs) ⟩

-- | Binary tree: Tree A = Fix (A + X * X) = μ (K A ⊕ Id ⊗ Id)
TreeF : Type → Functor
TreeF A = K A ⊕ (Id ⊗ Id)

Tree : Type → Set
Tree A = μ (TreeF A)

leaf : ∀ {A} → ⟦ A ⟧ → Tree A
leaf a = ⟨ inj₁ a ⟩

branch : ∀ {A} → Tree A → Tree A → Tree A
branch l r = ⟨ inj₂ (l , r) ⟩

------------------------------------------------------------------------
-- Induction Principle
--
-- Every polynomial functor gives rise to an induction principle.
-- This is the dependent version of cata.
------------------------------------------------------------------------

-- | Induction principle for μ F
--
-- To prove P x for all x : μ F, it suffices to prove:
-- for all y : F (μ F), if P holds for all recursive positions in y,
-- then P (⟨ y ⟩).
--
-- This is the fundamental theorem for reasoning about recursive types.

-- Helper: All recursive positions in an F-structure satisfy P
All : ∀ F → {X : Set} → (X → Set) → ⟦ F ⟧F X → Set
All (K A) P x = ⊤                              -- No recursive positions
All Id P x = P x                               -- Single recursive position
All (F ⊕ G) P (inj₁ x) = All F P x             -- In left
All (F ⊕ G) P (inj₂ y) = All G P y             -- In right
All (F ⊗ G) P (x , y) = All F P x × All G P y  -- In both

-- | Induction for μ F
--
-- Uses mutual recursion for termination.
--
mutual
  ind : ∀ {F} (P : μ F → Set)
      → (step : (y : ⟦ F ⟧F (μ F)) → All F P y → P ⟨ y ⟩)
      → (x : μ F) → P x
  ind {F} P step ⟨ y ⟩ = step y (all-ind F F P step y)

  -- Build All proof recursively
  all-ind : ∀ G F (P : μ F → Set)
          → (step : (y : ⟦ F ⟧F (μ F)) → All F P y → P ⟨ y ⟩)
          → (z : ⟦ G ⟧F (μ F)) → All G P z
  all-ind (K A) F P step x = tt
  all-ind Id F P step x = ind P step x
  all-ind (G₁ ⊕ G₂) F P step (inj₁ x) = all-ind G₁ F P step x
  all-ind (G₁ ⊕ G₂) F P step (inj₂ y) = all-ind G₂ F P step y
  all-ind (G₁ ⊗ G₂) F P step (x , y) = (all-ind G₁ F P step x , all-ind G₂ F P step y)

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- This module provides:
--
-- Functor codes: K, Id, ⊕, ⊗
-- Interpretation: ⟦_⟧F : Functor → Set → Set
-- Fixed point: μ : Functor → Set
-- Constructors: ⟨_⟩ (fold), out (unfold)
-- Recursion: cata, ana
-- Functor map: fmap with laws fmap-id, fmap-comp
-- Isomorphism: fold-unfold, unfold-fold
-- Induction: ind
--
-- Standard types: NatF, ListF, TreeF with constructors
--
-- The proper semantics for Fix F is now:
--   ⟦ Fix F ⟧ = μ F   where F : Functor
--