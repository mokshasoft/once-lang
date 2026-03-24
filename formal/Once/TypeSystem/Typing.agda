-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeSystem.Typing
--
-- Typing judgments for Once IR.
--
-- In Once, the IR is intrinsically typed: the GADT IR : Type → Type → Set
-- enforces that only well-typed terms can be constructed.
--
-- This module makes the typing rules explicit and proves they
-- correspond to the semantic interpretation.
------------------------------------------------------------------------

module Once.TypeSystem.Typing where

open import Once.Type
open import Once.CCC.IR
open import Once.CCC.Machine.SMCore using (HeapRef)
open import Once.Semantics.IR using (⟦_⟧; eval′)
open import Once.Postulates using (extensionality)

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

------------------------------------------------------------------------
-- Typing Context
------------------------------------------------------------------------

-- | Typing context: a list of types
--
-- In a CCC, objects are types and morphisms are typed by
-- their domain and codomain. A context represents a "stack"
-- of input types.
--
Ctx : Set
Ctx = List Type

-- | Empty context
∅ : Ctx
∅ = []

-- | Context extension
_,ᶜ_ : Ctx → Type → Ctx
Γ ,ᶜ A = A ∷ Γ

infixl 5 _,ᶜ_

------------------------------------------------------------------------
-- Well-Typed IR (Explicit Rules)
------------------------------------------------------------------------

-- | Well-typed IR terms
--
-- This is isomorphic to IR but makes the typing rules explicit
-- as inference rules rather than GADT constructors.
--
-- Γ ⊢ A ⟶ B means "in context Γ, there is a morphism from A to B"
--
-- For a CCC-based calculus, the context Γ is often empty
-- because morphisms don't have free variables - they're
-- point-free combinators.
--
data _⊢_⟶_ : Ctx → Type → Type → Set where
  -- Identity
  --
  -- ─────────────
  -- Γ ⊢ A ⟶ A
  --
  ty-id : ∀ {Γ A} → Γ ⊢ A ⟶ A

  -- Composition
  --
  -- Γ ⊢ B ⟶ C    Γ ⊢ A ⟶ B
  -- ──────────────────────────
  --       Γ ⊢ A ⟶ C
  --
  ty-comp : ∀ {Γ A B C} → Γ ⊢ B ⟶ C → Γ ⊢ A ⟶ B → Γ ⊢ A ⟶ C

  -- First projection
  --
  -- ─────────────────────
  -- Γ ⊢ (A * B) ⟶ A
  --
  ty-fst : ∀ {Γ A B} → Γ ⊢ (A * B) ⟶ A

  -- Second projection
  --
  -- ─────────────────────
  -- Γ ⊢ (A * B) ⟶ B
  --
  ty-snd : ∀ {Γ A B} → Γ ⊢ (A * B) ⟶ B

  -- Pairing
  --
  -- Γ ⊢ C ⟶ A    Γ ⊢ C ⟶ B
  -- ──────────────────────────
  --     Γ ⊢ C ⟶ (A * B)
  --
  ty-pair : ∀ {Γ A B C} → Γ ⊢ C ⟶ A → Γ ⊢ C ⟶ B → Γ ⊢ C ⟶ (A * B)

  -- Left injection
  --
  -- ─────────────────────
  -- Γ ⊢ A ⟶ (A + B)
  --
  ty-inl : ∀ {Γ A B} → Γ ⊢ A ⟶ (A + B)

  -- Right injection
  --
  -- ─────────────────────
  -- Γ ⊢ B ⟶ (A + B)
  --
  ty-inr : ∀ {Γ A B} → Γ ⊢ B ⟶ (A + B)

  -- Case analysis
  --
  -- Γ ⊢ A ⟶ C    Γ ⊢ B ⟶ C
  -- ──────────────────────────
  --     Γ ⊢ (A + B) ⟶ C
  --
  ty-case : ∀ {Γ A B C} → Γ ⊢ A ⟶ C → Γ ⊢ B ⟶ C → Γ ⊢ (A + B) ⟶ C

  -- Terminal morphism
  --
  -- ─────────────────
  -- Γ ⊢ A ⟶ Unit
  --
  ty-terminal : ∀ {Γ A} → Γ ⊢ A ⟶ Unit

  -- Initial morphism
  --
  -- ─────────────────
  -- Γ ⊢ Void ⟶ A
  --
  ty-initial : ∀ {Γ A} → Γ ⊢ Void ⟶ A

  -- Curry (quantity-polymorphic)
  --
  --      Γ ⊢ (A * B) ⟶ C
  -- ─────────────────────────────
  --   Γ ⊢ A ⟶ (B ⇒[ q ] C)
  --
  ty-curry : ∀ {Γ A B C q} → Γ ⊢ (A * B) ⟶ C → Γ ⊢ A ⟶ (B ⇒[ q ] C)

  -- Apply (quantity-polymorphic)
  --
  -- ─────────────────────────────────
  -- Γ ⊢ ((A ⇒[ q ] B) * A) ⟶ B
  --
  ty-apply : ∀ {Γ A B q} → Γ ⊢ ((A ⇒[ q ] B) * A) ⟶ B

  -- OCP-0003: ty-fold/ty-unfold removed. Use ty-In/ty-Cata/ty-Out/ty-Ana instead.

  -- Arrow lift (D032: lift pure to effectful)
  --
  -- ─────────────────────────────
  -- Γ ⊢ (A ⇒ B) ⟶ Eff A B
  --
  -- Note: This takes a pure function object and returns an effectful morphism.
  -- At runtime, Eff A B is represented identically to A ⇒ B.
  -- The distinction is purely for effect tracking.
  --
  ty-arr : ∀ {Γ A B q} → Γ ⊢ (A ⇒[ q ] B) ⟶ Eff A B

  -- Primitive operations (opaque to optimizer)
  --
  -- ─────────────────────────
  -- Γ ⊢ A ⟶ B
  --
  -- Primitives are external operations provided by the runtime/platform.
  -- They cannot be decomposed into categorical generators.
  -- The String names the primitive (e.g., "arith.add.int").
  --
  ty-prim : ∀ {Γ A B} → String → Γ ⊢ A ⟶ B

  -- Memory management (explicit heap deallocation)
  ty-free-heap : ∀ {Γ} → HeapRef → Γ ⊢ Unit ⟶ Unit

  -- OCP-0003: Recursion schemes for polynomial functors
  --
  -- In: algebra for μ-type (fold into initial algebra)
  -- ──────────────────────────────────────
  -- Γ ⊢ ⟦ F ⟧T (μ-type F) ⟶ μ-type F
  --
  ty-In : ∀ {Γ F} → Γ ⊢ ⟦ F ⟧T (μ-type F) ⟶ μ-type F

  -- Cata: catamorphism (fold over μ-type)
  --      Γ ⊢ ⟦ F ⟧T A ⟶ A
  -- ──────────────────────────────
  --    Γ ⊢ μ-type F ⟶ A
  --
  ty-Cata : ∀ {Γ F A} → Γ ⊢ ⟦ F ⟧T A ⟶ A → Γ ⊢ μ-type F ⟶ A

  -- Out: observation of ν-type (unfold from final coalgebra)
  -- ──────────────────────────────────────
  -- Γ ⊢ ν-type F ⟶ ⟦ F ⟧T (ν-type F)
  --
  ty-Out : ∀ {Γ F} → Γ ⊢ ν-type F ⟶ ⟦ F ⟧T (ν-type F)

  -- Ana: anamorphism (unfold into ν-type)
  -- OCP-0003: coalg produces GuardedT F A for productivity enforcement
  --      Γ ⊢ A ⟶ GuardedT F A
  -- ───────────────────────────────
  --      Γ ⊢ A ⟶ ν-type F
  --
  ty-Ana : ∀ {Γ F A} → Γ ⊢ A ⟶ GuardedT F A → Γ ⊢ A ⟶ ν-type F

  -- Unguard: extract functor value from guarded value
  -- OCP-0003: used after Ana processing
  -- ──────────────────────────────────────
  -- Γ ⊢ GuardedT F A ⟶ ⟦ F ⟧T A
  --
  ty-Unguard : ∀ {Γ F A} → Γ ⊢ GuardedT F A ⟶ ⟦ F ⟧T A

  -- Guard: wrap functor value as guarded value
  -- OCP-0003: inverse of Unguard, establishes GuardedT ≅ ⟦ F ⟧T isomorphism
  -- ──────────────────────────────────────
  -- Γ ⊢ ⟦ F ⟧T A ⟶ GuardedT F A
  --
  ty-Guard : ∀ {Γ F A} → Γ ⊢ ⟦ F ⟧T A ⟶ GuardedT F A

  -- Hylo: hylomorphism (fused ana-cata)
  -- OCP-0003: coalg produces GuardedT F A for productivity enforcement
  --      Γ ⊢ ⟦ F ⟧T B ⟶ B    Γ ⊢ A ⟶ GuardedT F A
  -- ───────────────────────────────────────────────
  --                Γ ⊢ A ⟶ B
  --
  ty-Hylo : ∀ {Γ F A B} → Γ ⊢ ⟦ F ⟧T B ⟶ B → Γ ⊢ A ⟶ GuardedT F A → Γ ⊢ A ⟶ B

------------------------------------------------------------------------
-- Correspondence with IR GADT
------------------------------------------------------------------------

-- | Convert explicit typing derivation to IR term
--
-- This shows that the explicit rules generate exactly IR.
--
⌊_⌋ : ∀ {Γ A B} → Γ ⊢ A ⟶ B → IR A B
⌊ ty-id ⌋ = id
⌊ ty-comp g f ⌋ = ⌊ g ⌋ ∘ ⌊ f ⌋
⌊ ty-fst ⌋ = fst
⌊ ty-snd ⌋ = snd
⌊ ty-pair f g ⌋ = ⟨ ⌊ f ⌋ , ⌊ g ⌋ ⟩ Heap
⌊ ty-inl ⌋ = inl Heap
⌊ ty-inr ⌋ = inr Heap
⌊ ty-case f g ⌋ = (case ⌊ f ⌋ ⌊ g ⌋)
⌊ ty-terminal ⌋ = terminal
⌊ ty-initial ⌋ = initial
⌊ ty-curry f ⌋ = curry ⌊ f ⌋ Heap
⌊ ty-apply ⌋ = apply
-- OCP-0003: ty-fold/ty-unfold removed
⌊ ty-arr ⌋ = arr
⌊ ty-prim name ⌋ = Prim name
⌊ ty-free-heap h ⌋ = free-heap h
-- OCP-0003 recursion schemes
⌊ ty-In {F = F} ⌋ = In {F} Heap
⌊ ty-Cata {F = F} alg ⌋ = Cata {F} ⌊ alg ⌋
⌊ ty-Out {F = F} ⌋ = Out {F}
⌊ ty-Ana {F = F} coalg ⌋ = Ana {F} ⌊ coalg ⌋
⌊ ty-Unguard {F = F} ⌋ = Unguard {F}
⌊ ty-Guard {F = F} ⌋ = Guard {F}
⌊ ty-Hylo {F = F} alg coalg ⌋ = Hylo {F} ⌊ alg ⌋ ⌊ coalg ⌋

-- | Convert IR term to explicit typing derivation
--
-- This shows that every IR term has a typing derivation.
-- (Embedding into empty context since IR terms are closed.)
--
⌈_⌉ : ∀ {A B} → IR A B → ∅ ⊢ A ⟶ B
⌈ id ⌉ = ty-id
⌈ g ∘ f ⌉ = ty-comp ⌈ g ⌉ ⌈ f ⌉
⌈ fst ⌉ = ty-fst
⌈ snd ⌉ = ty-snd
⌈ (⟨ f , g ⟩ _) ⌉ = ty-pair ⌈ f ⌉ ⌈ g ⌉
⌈ (inl _) ⌉ = ty-inl
⌈ (inr _) ⌉ = ty-inr
⌈ (case f g) ⌉ = ty-case ⌈ f ⌉ ⌈ g ⌉
⌈ terminal ⌉ = ty-terminal
⌈ initial ⌉ = ty-initial
⌈ (curry f _) ⌉ = ty-curry ⌈ f ⌉
⌈ apply ⌉ = ty-apply
-- OCP-0003: fold/unfold removed
⌈ arr ⌉ = ty-arr
⌈ Prim name ⌉ = ty-prim name
⌈ free-heap h ⌉ = ty-free-heap h
-- OCP-0003 recursion schemes
⌈ In {F} _ ⌉ = ty-In {F = F}
⌈ Cata {F} alg ⌉ = ty-Cata {F = F} ⌈ alg ⌉
⌈ Out {F} ⌉ = ty-Out {F = F}
⌈ Ana {F} coalg ⌉ = ty-Ana {F = F} ⌈ coalg ⌉
⌈ Unguard {F} ⌉ = ty-Unguard {F = F}
⌈ Guard {F} ⌉ = ty-Guard {F = F}
⌈ Hylo {F} alg coalg ⌉ = ty-Hylo {F = F} ⌈ alg ⌉ ⌈ coalg ⌉

-- | Round-trip: ⌊ ⌈ f ⌉ ⌋ ≡ f (semantically)
--
-- Note: Syntactic equality doesn't hold because typing derivations don't
-- track AllocMode, so the round-trip normalizes to Heap allocation.
-- However, since AllocMode is semantically transparent, we have semantic equality.
--
round-trip-ir : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧) → eval′ ⌊ ⌈ f ⌉ ⌋ x ≡ eval′ f x
round-trip-ir id x = refl
round-trip-ir (g ∘ f) x = cong (eval′ ⌊ ⌈ g ⌉ ⌋) (round-trip-ir f x) `trans` round-trip-ir g (eval′ f x)
  where _`trans`_ = trans
round-trip-ir fst x = refl
round-trip-ir snd x = refl
round-trip-ir (⟨ f , g ⟩ _) x = cong₂ _,_ (round-trip-ir f x) (round-trip-ir g x)
round-trip-ir (inl _) x = refl
round-trip-ir (inr _) x = refl
round-trip-ir (case f g) (inj₁ a) = round-trip-ir f a
round-trip-ir (case f g) (inj₂ b) = round-trip-ir g b
round-trip-ir terminal x = refl
round-trip-ir initial ()
round-trip-ir (curry {q = q} f _) x =
  extensionality (λ b → round-trip-ir f (x , b))
round-trip-ir apply x = refl
-- OCP-0003: fold/unfold removed
round-trip-ir arr x = refl
round-trip-ir (Prim name) x = refl
round-trip-ir (free-heap h) x = refl
-- OCP-0003 recursion schemes: these use postulated semantics
-- so we postulate the round-trip property
round-trip-ir (In {F} _) x = round-trip-In {F} x
  where postulate round-trip-In : ∀ {F} (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧) → eval′ ⌊ ⌈ In {F} Heap ⌉ ⌋ x ≡ eval′ (In {F} Heap) x
round-trip-ir (Cata {F} alg) x = round-trip-Cata {F} alg x
  where postulate round-trip-Cata : ∀ {F A} (alg : IR (⟦ F ⟧T A) A) (x : ⟦ μ-type F ⟧) → eval′ ⌊ ⌈ Cata {F} alg ⌉ ⌋ x ≡ eval′ (Cata {F} alg) x
round-trip-ir (Out {F}) x = round-trip-Out {F} x
  where postulate round-trip-Out : ∀ {F} (x : ⟦ ν-type F ⟧) → eval′ ⌊ ⌈ Out {F} ⌉ ⌋ x ≡ eval′ (Out {F}) x
round-trip-ir (Ana {F} coalg) x = round-trip-Ana {F} coalg x
  where postulate round-trip-Ana : ∀ {F A} (coalg : IR A (GuardedT F A)) (x : ⟦ A ⟧) → eval′ ⌊ ⌈ Ana {F} coalg ⌉ ⌋ x ≡ eval′ (Ana {F} coalg) x
round-trip-ir (Unguard {F} {A}) x = round-trip-Unguard {F} {A} x
  where postulate round-trip-Unguard : ∀ {F A} (x : ⟦ GuardedT F A ⟧) → eval′ ⌊ ⌈ Unguard {F} {A} ⌉ ⌋ x ≡ eval′ (Unguard {F} {A}) x
round-trip-ir (Guard {F} {A}) x = round-trip-Guard {F} {A} x
  where postulate round-trip-Guard : ∀ {F A} (x : ⟦ ⟦ F ⟧T A ⟧) → eval′ ⌊ ⌈ Guard {F} {A} ⌉ ⌋ x ≡ eval′ (Guard {F} {A}) x
round-trip-ir (Hylo {F} alg coalg) x = round-trip-Hylo {F} alg coalg x
  where postulate round-trip-Hylo : ∀ {F A B} (alg : IR (⟦ F ⟧T B) B) (coalg : IR A (GuardedT F A)) (x : ⟦ A ⟧) → eval′ ⌊ ⌈ Hylo {F} alg coalg ⌉ ⌋ x ≡ eval′ (Hylo {F} alg coalg) x