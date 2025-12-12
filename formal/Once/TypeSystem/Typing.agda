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
open import Once.IR
open import Once.Semantics

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

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

  -- Curry
  --
  --    Γ ⊢ (A * B) ⟶ C
  -- ─────────────────────
  --   Γ ⊢ A ⟶ (B ⇒ C)
  --
  ty-curry : ∀ {Γ A B C} → Γ ⊢ (A * B) ⟶ C → Γ ⊢ A ⟶ (B ⇒ C)

  -- Apply
  --
  -- ───────────────────────────
  -- Γ ⊢ ((A ⇒ B) * A) ⟶ B
  --
  ty-apply : ∀ {Γ A B} → Γ ⊢ ((A ⇒ B) * A) ⟶ B

  -- Fold (constructor for recursive types)
  --
  -- ─────────────────────────
  -- Γ ⊢ F ⟶ Fix F
  --
  ty-fold : ∀ {Γ F} → Γ ⊢ F ⟶ Fix F

  -- Unfold (destructor for recursive types)
  --
  -- ─────────────────────────
  -- Γ ⊢ Fix F ⟶ F
  --
  ty-unfold : ∀ {Γ F} → Γ ⊢ Fix F ⟶ F

  -- Arrow lift (D032: lift pure to effectful)
  --
  -- ─────────────────────────────
  -- Γ ⊢ (A ⇒ B) ⟶ Eff A B
  --
  -- Note: This takes a pure function object and returns an effectful morphism.
  -- At runtime, Eff A B is represented identically to A ⇒ B.
  -- The distinction is purely for effect tracking.
  --
  ty-arr : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) ⟶ Eff A B

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
⌊ ty-pair f g ⌋ = ⟨ ⌊ f ⌋ , ⌊ g ⌋ ⟩
⌊ ty-inl ⌋ = inl
⌊ ty-inr ⌋ = inr
⌊ ty-case f g ⌋ = [ ⌊ f ⌋ , ⌊ g ⌋ ]
⌊ ty-terminal ⌋ = terminal
⌊ ty-initial ⌋ = initial
⌊ ty-curry f ⌋ = curry ⌊ f ⌋
⌊ ty-apply ⌋ = apply
⌊ ty-fold ⌋ = fold
⌊ ty-unfold ⌋ = unfold
⌊ ty-arr ⌋ = arr

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
⌈ ⟨ f , g ⟩ ⌉ = ty-pair ⌈ f ⌉ ⌈ g ⌉
⌈ inl ⌉ = ty-inl
⌈ inr ⌉ = ty-inr
⌈ [ f , g ] ⌉ = ty-case ⌈ f ⌉ ⌈ g ⌉
⌈ terminal ⌉ = ty-terminal
⌈ initial ⌉ = ty-initial
⌈ curry f ⌉ = ty-curry ⌈ f ⌉
⌈ apply ⌉ = ty-apply
⌈ fold ⌉ = ty-fold
⌈ unfold ⌉ = ty-unfold
⌈ arr ⌉ = ty-arr

-- | Round-trip: ⌊ ⌈ f ⌉ ⌋ ≡ f
--
round-trip-ir : ∀ {A B} (f : IR A B) → ⌊ ⌈ f ⌉ ⌋ ≡ f
round-trip-ir id = refl
round-trip-ir (g ∘ f) = cong₂ _∘_ (round-trip-ir g) (round-trip-ir f)
  where
    cong₂ : ∀ {A : Set} {B : Set} {C : Set}
            (f : A → B → C) {x y : A} {u v : B}
          → x ≡ y → u ≡ v → f x u ≡ f y v
    cong₂ f refl refl = refl
round-trip-ir fst = refl
round-trip-ir snd = refl
round-trip-ir ⟨ f , g ⟩ = cong₂ ⟨_,_⟩ (round-trip-ir f) (round-trip-ir g)
  where
    cong₂ : ∀ {A : Set} {B : Set} {C : Set}
            (f : A → B → C) {x y : A} {u v : B}
          → x ≡ y → u ≡ v → f x u ≡ f y v
    cong₂ f refl refl = refl
round-trip-ir inl = refl
round-trip-ir inr = refl
round-trip-ir [ f , g ] = cong₂ [_,_] (round-trip-ir f) (round-trip-ir g)
  where
    cong₂ : ∀ {A : Set} {B : Set} {C : Set}
            (f : A → B → C) {x y : A} {u v : B}
          → x ≡ y → u ≡ v → f x u ≡ f y v
    cong₂ f refl refl = refl
round-trip-ir terminal = refl
round-trip-ir initial = refl
round-trip-ir (curry f) = cong curry (round-trip-ir f)
round-trip-ir apply = refl
round-trip-ir fold = refl
round-trip-ir unfold = refl
round-trip-ir arr = refl
