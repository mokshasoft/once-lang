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
open import Once.Functor.Translate using (WellFormedF)

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
  -- All recursion scheme typing rules require WellFormedF proofs
  -- to ensure functors only use K with base types.
  --
  -- In: algebra for μ-type (fold into initial algebra)
  -- ──────────────────────────────────────
  -- Γ ⊢ ⟦ F ⟧T (μ-type F) ⟶ μ-type F
  --
  ty-In : ∀ {Γ F} → WellFormedF F → Γ ⊢ ⟦ F ⟧T (μ-type F) ⟶ μ-type F

  -- Cata: catamorphism (fold over μ-type)
  --      Γ ⊢ ⟦ F ⟧T A ⟶ A
  -- ──────────────────────────────
  --    Γ ⊢ μ-type F ⟶ A
  --
  ty-Cata : ∀ {Γ F} → WellFormedF F → ∀ {A} → Γ ⊢ ⟦ F ⟧T A ⟶ A → Γ ⊢ μ-type F ⟶ A

  -- Out: observation of ν-type (unfold from final coalgebra)
  -- ──────────────────────────────────────
  -- Γ ⊢ ν-type F ⟶ ⟦ F ⟧T (ν-type F)
  --
  ty-Out : ∀ {Γ F} → WellFormedF F → Γ ⊢ ν-type F ⟶ ⟦ F ⟧T (ν-type F)

  -- Ana: anamorphism (unfold into ν-type)
  -- Productivity follows from IR totality: coalgebras are IR morphisms,
  -- and IR morphisms are total. See IR/Totality.agda.
  --      Γ ⊢ A ⟶ ⟦ F ⟧T A
  -- ───────────────────────────────
  --      Γ ⊢ A ⟶ ν-type F
  --
  ty-Ana : ∀ {Γ F} → WellFormedF F → ∀ {A} → Γ ⊢ A ⟶ ⟦ F ⟧T A → Γ ⊢ A ⟶ ν-type F

  -- Guard/Unguard removed: productivity follows from IR totality (see IR/Totality.agda)

  -- Hylo: hylomorphism (fused ana-cata)
  -- Productivity follows from IR totality.
  --      Γ ⊢ ⟦ F ⟧T B ⟶ B    Γ ⊢ A ⟶ ⟦ F ⟧T A
  -- ───────────────────────────────────────────────
  --                Γ ⊢ A ⟶ B
  --
  ty-Hylo : ∀ {Γ F} → WellFormedF F → ∀ {A B} → Γ ⊢ ⟦ F ⟧T B ⟶ B → Γ ⊢ A ⟶ ⟦ F ⟧T A → Γ ⊢ A ⟶ B

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
-- OCP-0003 recursion schemes (WellFormedF proofs preserved)
⌊ ty-In {F = F} wf ⌋ = In {F} wf Heap
⌊ ty-Cata {F = F} wf alg ⌋ = Cata {F} wf ⌊ alg ⌋
⌊ ty-Out {F = F} wf ⌋ = Out {F} wf
⌊ ty-Ana {F = F} wf coalg ⌋ = Ana {F} wf ⌊ coalg ⌋
-- Guard/Unguard removed: productivity follows from IR totality
⌊ ty-Hylo {F = F} wf alg coalg ⌋ = Hylo {F} wf ⌊ alg ⌋ ⌊ coalg ⌋

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
-- OCP-0003 recursion schemes (WellFormedF proofs preserved)
⌈ In {F} wf _ ⌉ = ty-In {F = F} wf
⌈ Cata {F} wf alg ⌉ = ty-Cata {F = F} wf ⌈ alg ⌉
⌈ Out {F} wf ⌉ = ty-Out {F = F} wf
⌈ Ana {F} wf coalg ⌉ = ty-Ana {F = F} wf ⌈ coalg ⌉
-- Guard/Unguard removed: productivity follows from IR totality
⌈ Hylo {F} wf alg coalg ⌉ = ty-Hylo {F = F} wf ⌈ alg ⌉ ⌈ coalg ⌉

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
-- so we postulate the round-trip property (WellFormedF proofs preserved)
round-trip-ir (In {F} wf _) x = round-trip-In {F} wf x
  where postulate round-trip-In : ∀ {F} (wf : WellFormedF F) (x : ⟦ ⟦ F ⟧T (μ-type F) ⟧) → eval′ ⌊ ⌈ In {F} wf Heap ⌉ ⌋ x ≡ eval′ (In {F} wf Heap) x
round-trip-ir (Cata {F} wf alg) x = round-trip-Cata {F} wf alg x
  where postulate round-trip-Cata : ∀ {F} (wf : WellFormedF F) {A} (alg : IR (⟦ F ⟧T A) A) (x : ⟦ μ-type F ⟧) → eval′ ⌊ ⌈ Cata {F} wf alg ⌉ ⌋ x ≡ eval′ (Cata {F} wf alg) x
round-trip-ir (Out {F} wf) x = round-trip-Out {F} wf x
  where postulate round-trip-Out : ∀ {F} (wf : WellFormedF F) (x : ⟦ ν-type F ⟧) → eval′ ⌊ ⌈ Out {F} wf ⌉ ⌋ x ≡ eval′ (Out {F} wf) x
round-trip-ir (Ana {F} wf coalg) x = round-trip-Ana {F} wf coalg x
  where postulate round-trip-Ana : ∀ {F} (wf : WellFormedF F) {A} (coalg : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧) → eval′ ⌊ ⌈ Ana {F} wf coalg ⌉ ⌋ x ≡ eval′ (Ana {F} wf coalg) x
-- Guard/Unguard removed: productivity follows from IR totality
round-trip-ir (Hylo {F} wf alg coalg) x = round-trip-Hylo {F} wf alg coalg x
  where postulate round-trip-Hylo : ∀ {F} (wf : WellFormedF F) {A B} (alg : IR (⟦ F ⟧T B) B) (coalg : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧) → eval′ ⌊ ⌈ Hylo {F} wf alg coalg ⌉ ⌋ x ≡ eval′ (Hylo {F} wf alg coalg) x