------------------------------------------------------------------------
-- Encoding: Concrete Self-Representation for MinimalCCC
--
-- This module defines the encoding ⌜_⌝ that represents terms as data.
-- The encoding is the foundation for the fixpoint correctness theorem:
--
--   If N(⌜N⌝) = ⌜N⌝, then N correctly computes normal forms.
--
-- We define:
--   1. TyFuncCode - encoding of types and functors (mutually recursive)
--   2. TermCode' - encoding of terms with type annotations
--   3. ⌜_⌝Ty, ⌜_⌝Func, ⌜_⌝ - the encoding functions
------------------------------------------------------------------------

module normalizer.Foundations.Encoding where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC

------------------------------------------------------------------------
-- Part 1: Encoding Types and Functors
------------------------------------------------------------------------

-- Types and Functors are mutually recursive, so we encode them together.
-- We use a sum type with tags to distinguish:
--   - Types: Unit, A * B, A + B, μ F
--   - Functors: Id, K A, F ⊕ G, F ⊗ G
--
-- Encoding scheme (8 alternatives):
--   0: Unit type      (K Unit)
--   1: Product type   (Id ⊗ Id) - two type codes
--   2: Sum type       (Id ⊗ Id) - two type codes
--   3: Mu type        (Id)      - one functor code
--   4: Id functor     (K Unit)
--   5: K functor      (Id)      - one type code
--   6: Sum functor    (Id ⊗ Id) - two functor codes
--   7: Product functor(Id ⊗ Id) - two functor codes

TyFuncF : Func
TyFuncF = K Unit          -- 0: Unit type
        ⊕ (Id ⊗ Id)       -- 1: A * B
        ⊕ (Id ⊗ Id)       -- 2: A + B
        ⊕ Id              -- 3: μ F
        ⊕ K Unit          -- 4: Id functor
        ⊕ Id              -- 5: K A
        ⊕ (Id ⊗ Id)       -- 6: F ⊕ G
        ⊕ (Id ⊗ Id)       -- 7: F ⊗ G

TyFuncCode : Ty
TyFuncCode = μ TyFuncF

-- Injection helpers for building codes
-- We need to navigate the nested sum structure.

-- The functor applied to TyFuncCode:
-- ⟦ TyFuncF ⟧F TyFuncCode =
--   Unit + (TyFuncCode * TyFuncCode) + (TyFuncCode * TyFuncCode) + TyFuncCode
--   + Unit + TyFuncCode + (TyFuncCode * TyFuncCode) + (TyFuncCode * TyFuncCode)

-- Helper: inject into position n of an 8-way sum
-- We'll build specific injections for each constructor.

-- Type encoding injections:

-- 0: Unit type
inj-unit-ty : Term Unit (⟦ TyFuncF ⟧F TyFuncCode)
inj-unit-ty = inl ∘ terminal

-- 1: Product type A * B
inj-prod-ty : Term (TyFuncCode * TyFuncCode) (⟦ TyFuncF ⟧F TyFuncCode)
inj-prod-ty = inr ∘ inl

-- 2: Sum type A + B
inj-sum-ty : Term (TyFuncCode * TyFuncCode) (⟦ TyFuncF ⟧F TyFuncCode)
inj-sum-ty = inr ∘ inr ∘ inl

-- 3: Mu type μ F
inj-mu-ty : Term TyFuncCode (⟦ TyFuncF ⟧F TyFuncCode)
inj-mu-ty = inr ∘ inr ∘ inr ∘ inl

-- Functor encoding injections:

-- 4: Id functor
inj-id-func : Term Unit (⟦ TyFuncF ⟧F TyFuncCode)
inj-id-func = inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ terminal

-- 5: K functor
inj-k-func : Term TyFuncCode (⟦ TyFuncF ⟧F TyFuncCode)
inj-k-func = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- 6: Sum functor F ⊕ G
inj-oplus-func : Term (TyFuncCode * TyFuncCode) (⟦ TyFuncF ⟧F TyFuncCode)
inj-oplus-func = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- 7: Product functor F ⊗ G
inj-otimes-func : Term (TyFuncCode * TyFuncCode) (⟦ TyFuncF ⟧F TyFuncCode)
inj-otimes-func = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr

------------------------------------------------------------------------
-- Part 2: Type and Functor Encoding Functions
------------------------------------------------------------------------

-- Mutually recursive encoding of types and functors
-- We inline the injection helpers directly for explicit composition structure.
-- This makes the ∘-injective chain depth predictable for injectivity proofs.
⌜_⌝Ty : Ty → Term Unit TyFuncCode
⌜_⌝Func : Func → Term Unit TyFuncCode

-- Unit: In ∘ inl ∘ terminal (2 compositions)
⌜ Unit ⌝Ty = In ∘ inl ∘ terminal

-- Product: In ∘ inr ∘ inl ∘ ⟨...⟩ (3 compositions before pair)
⌜ A * B ⌝Ty = In ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

-- Sum: In ∘ inr ∘ inr ∘ inl ∘ ⟨...⟩ (4 compositions before pair)
⌜ A + B ⌝Ty = In ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

-- Mu: In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜F⌝ (5 compositions before subterm)
⌜ μ F ⌝Ty = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func

-- Id functor: In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ terminal (6 compositions)
⌜ Id ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ terminal

-- K functor: In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜A⌝ (7 compositions)
⌜ K A ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty

-- ⊕ functor: In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨...⟩ (8 compositions)
⌜ F ⊕ G ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ F ⌝Func , ⌜ G ⌝Func ⟩

-- ⊗ functor: In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨...⟩ (8 compositions, no inl)
⌜ F ⊗ G ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜ F ⌝Func , ⌜ G ⌝Func ⟩

------------------------------------------------------------------------
-- Part 3: Term Code Definition
------------------------------------------------------------------------

-- Terms have 11 constructors:
--   0: id         (no subterms, but has type A)
--   1: f ∘ g      (two subterms)
--   2: fst        (has types A, B)
--   3: snd        (has types A, B)
--   4: ⟨f, g⟩     (two subterms)
--   5: inl        (has types A, B)
--   6: inr        (has types A, B)
--   7: [f, g]     (two subterms)
--   8: terminal   (has type A)
--   9: In         (has functor F)
--  10: cata F alg (functor F, one subterm)
--
-- For a faithful encoding, we include type annotations.
-- This makes the encoding larger but ensures injectivity.

-- Term code functor:
-- Each constructor stores its subterms (if any) and type info.
TermF : Func
TermF = (K TyFuncCode)                              -- 0: id A
      ⊕ (Id ⊗ Id)                                   -- 1: f ∘ g
      ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 2: fst A B
      ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 3: snd A B
      ⊕ (Id ⊗ Id)                                   -- 4: ⟨f, g⟩
      ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl A B
      ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr A B
      ⊕ (Id ⊗ Id)                                   -- 7: [f, g]
      ⊕ (K TyFuncCode)                              -- 8: terminal A
      ⊕ (K TyFuncCode)                              -- 9: In F (store functor code)
      ⊕ (K TyFuncCode ⊗ Id)                        -- 10: cata F alg (functor + algebra)

TermCode' : Ty
TermCode' = μ TermF

-- The unfolded type of TermF at TermCode':
-- ⟦ TermF ⟧F TermCode' =
--   TyFuncCode                                    -- id
--   + (TermCode' * TermCode')                    -- compose
--   + (TyFuncCode * TyFuncCode)                  -- fst
--   + (TyFuncCode * TyFuncCode)                  -- snd
--   + (TermCode' * TermCode')                    -- pair
--   + (TyFuncCode * TyFuncCode)                  -- inl
--   + (TyFuncCode * TyFuncCode)                  -- inr
--   + (TermCode' * TermCode')                    -- case
--   + TyFuncCode                                  -- terminal
--   + TyFuncCode                                  -- In
--   + (TyFuncCode * TermCode')                   -- cata

------------------------------------------------------------------------
-- Part 4: Term Code Injections
------------------------------------------------------------------------

-- Helper type alias for the unfolded term code
UnfoldedTermCode : Ty
UnfoldedTermCode = ⟦ TermF ⟧F TermCode'

-- Injection for id
inj-id : Term TyFuncCode UnfoldedTermCode
inj-id = inl

-- Injection for compose
inj-comp : Term (TermCode' * TermCode') UnfoldedTermCode
inj-comp = inr ∘ inl

-- Injection for fst
inj-fst : Term (TyFuncCode * TyFuncCode) UnfoldedTermCode
inj-fst = inr ∘ inr ∘ inl

-- Injection for snd
inj-snd : Term (TyFuncCode * TyFuncCode) UnfoldedTermCode
inj-snd = inr ∘ inr ∘ inr ∘ inl

-- Injection for pair
inj-pair : Term (TermCode' * TermCode') UnfoldedTermCode
inj-pair = inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for inl
inj-inl : Term (TyFuncCode * TyFuncCode) UnfoldedTermCode
inj-inl = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for inr
inj-inr : Term (TyFuncCode * TyFuncCode) UnfoldedTermCode
inj-inr = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for case
inj-case : Term (TermCode' * TermCode') UnfoldedTermCode
inj-case = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for terminal
inj-terminal : Term TyFuncCode UnfoldedTermCode
inj-terminal = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for In
inj-In : Term TyFuncCode UnfoldedTermCode
inj-In = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for cata
inj-cata : Term (TyFuncCode * TermCode') UnfoldedTermCode
inj-cata = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr

------------------------------------------------------------------------
-- Part 5: The Term Encoding Function
------------------------------------------------------------------------

-- Encode a term as data
-- encode : ∀ {A B} → Term A B → Term Unit TermCode'
--
-- The encoding includes type information to ensure injectivity.
-- We use 'encode' to avoid clashing with the postulated ⌜_⌝ in MinimalCCC.

encode : ∀ {A B} → Term A B → Term Unit TermCode'

-- Inlined injection structure for explicit composition depth
-- (using right-associative _∘_ means we count inrs before inl)
-- 0: id         - inl (0 inrs)
-- 1: compose    - inr ∘ inl (1 inr)
-- 2: fst        - inr ∘ inr ∘ inl (2 inrs)
-- 3: snd        - inr ∘ inr ∘ inr ∘ inl (3 inrs)
-- 4: pair       - inr ∘ inr ∘ inr ∘ inr ∘ inl (4 inrs)
-- 5: inl        - inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl (5 inrs)
-- 6: inr        - inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl (6 inrs)
-- 7: case       - inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl (7 inrs)
-- 8: terminal   - inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl (8 inrs)
-- 9: In         - inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl (9 inrs)
-- 10: cata      - inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr (10 inrs, no inl)

encode (id {A}) = In ∘ inl ∘ ⌜ A ⌝Ty

encode (f ∘ g) = In ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩

encode (fst {A} {B}) = In ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

encode (snd {A} {B}) = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

encode ⟨ f , g ⟩ = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩

encode (inl {A} {B}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

encode (inr {A} {B}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

encode [ f , g ] = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩

encode (terminal {A}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty

encode (In {F}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func

encode (cata F alg) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜ F ⌝Func , encode alg ⟩

------------------------------------------------------------------------
-- Part 6: Properties of the Encoding
------------------------------------------------------------------------

-- The encoding is injective: different terms produce different codes.
-- This follows from the faithful representation of all constructor
-- arguments, including type information.

------------------------------------------------------------------------
-- 6a: Composition Injectivity Lemmas
------------------------------------------------------------------------

-- Composition is injective in both arguments
-- These follow from constructor injectivity of the Term datatype.

∘-injective-left : ∀ {A B C} {f g : Term B C} {h : Term A B} →
                   (f ∘ h) ≡ (g ∘ h) → f ≡ g
∘-injective-left refl = refl

∘-injective-right : ∀ {A B C} {f : Term B C} {g h : Term A B} →
                    (f ∘ g) ≡ (f ∘ h) → g ≡ h
∘-injective-right refl = refl

∘-injective : ∀ {A B C} {f₁ f₂ : Term B C} {g₁ g₂ : Term A B} →
              (f₁ ∘ g₁) ≡ (f₂ ∘ g₂) → (f₁ ≡ f₂) × (g₁ ≡ g₂)
∘-injective refl = refl , refl

-- Pairing is injective
⟨⟩-injective : ∀ {A B C} {f₁ f₂ : Term A B} {g₁ g₂ : Term A C} →
               ⟨ f₁ , g₁ ⟩ ≡ ⟨ f₂ , g₂ ⟩ → (f₁ ≡ f₂) × (g₁ ≡ g₂)
⟨⟩-injective refl = refl , refl

-- In is injective
In-injective : ∀ {F} {f g : Term (⟦ F ⟧F (μ F)) (⟦ TyFuncF ⟧F TyFuncCode)} →
               _≡_ {A = Term (⟦ F ⟧F (μ F)) TyFuncCode} (In ∘ f) (In ∘ g) → f ≡ g
In-injective refl = refl

------------------------------------------------------------------------
-- 6b: Type Discrimination
------------------------------------------------------------------------

-- Different type constructors produce different types.
-- We use these to derive contradictions when encodings of different
-- constructors are assumed equal.

-- The key insight: if ⌜ A ⌝Ty ≡ ⌜ B ⌝Ty where A and B have different
-- constructors, then by ∘-injective we get intermediate types that
-- must be equal, but they're structurally different.

-- Helper: extract the "injection depth" - how many inr's before inl
-- This distinguishes the 8 cases in TyFuncF.

-- For Unit:     In ∘ inl ∘ terminal           (0 inr's)
-- For A * B:    In ∘ inr ∘ inl ∘ ⟨...⟩        (1 inr)
-- For A + B:    In ∘ inr ∘ inr ∘ inl ∘ ⟨...⟩  (2 inr's)
-- For μ F:      In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ...  (3 inr's)
-- For Id:       In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ...  (4 inr's)
-- etc.

-- The intermediate type after the In tells us which constructor was used.
-- If two encodings are equal, their intermediate types must match.

------------------------------------------------------------------------
-- 6c: Type and Functor Encoding Injectivity (Mutual)
------------------------------------------------------------------------

-- We prove injectivity by mutual induction on the structure.
-- The proof uses the fact that different constructors produce
-- different injection patterns (different number of inr's before inl).

-- Due to Agda's limitations with mutual recursion and with-patterns,
-- we structure this carefully.

-- First, prove that the outer structure determines the constructor.
-- Then use induction for subterms.

-- Lemma: compositions with different outer structures are not equal
-- (This follows from constructor injectivity plus type structure)

-- For the type encoding, the structure is:
--   ⌜ Unit ⌝Ty    = In ∘ inl ∘ terminal
--   ⌜ A * B ⌝Ty   = In ∘ inr ∘ inl ∘ ⟨ ... ⟩
--   ⌜ A + B ⌝Ty   = In ∘ inr ∘ inr ∘ inl ∘ ⟨ ... ⟩
--   ⌜ μ F ⌝Ty     = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ...

-- Key type equalities that would be required for cross-constructor equality:
--   Unit ≡ TyFuncCode * TyFuncCode  (Unit vs Product encoding)
--   etc.
-- These are all provably false.

-- Type inequality witnesses
Unit≢Prod : ∀ {A B : Ty} → _≡_ {Ty} Unit (A * B) → ⊥
Unit≢Prod ()

Unit≢Sum : ∀ {A B : Ty} → _≡_ {Ty} Unit (A + B) → ⊥
Unit≢Sum ()

Unit≢Mu : ∀ {F : Func} → _≡_ {Ty} Unit (μ F) → ⊥
Unit≢Mu ()

Prod≢Sum : ∀ {A B C D : Ty} → _≡_ {Ty} (A * B) (C + D) → ⊥
Prod≢Sum ()

Prod≢Mu : ∀ {A B : Ty} {F : Func} → _≡_ {Ty} (A * B) (μ F) → ⊥
Prod≢Mu ()

Sum≢Mu : ∀ {A B : Ty} {F : Func} → _≡_ {Ty} (A + B) (μ F) → ⊥
Sum≢Mu ()

-- Functor inequality witnesses
Id≢K : ∀ {A : Ty} → _≡_ {Func} Id (K A) → ⊥
Id≢K ()

Id≢Oplus : ∀ {F G : Func} → _≡_ {Func} Id (F ⊕ G) → ⊥
Id≢Oplus ()

Id≢Otimes : ∀ {F G : Func} → _≡_ {Func} Id (F ⊗ G) → ⊥
Id≢Otimes ()

K≢Oplus : ∀ {A : Ty} {F G : Func} → _≡_ {Func} (K A) (F ⊕ G) → ⊥
K≢Oplus ()

K≢Otimes : ∀ {A : Ty} {F G : Func} → _≡_ {Func} (K A) (F ⊗ G) → ⊥
K≢Otimes ()

Oplus≢Otimes : ∀ {F₁ G₁ F₂ G₂ : Func} → _≡_ {Func} (F₁ ⊕ G₁) (F₂ ⊗ G₂) → ⊥
Oplus≢Otimes ()

-- Constructor injectivity for Ty
*-injective : ∀ {A B C D : Ty} → _≡_ {Ty} (A * B) (C * D) → (A ≡ C) × (B ≡ D)
*-injective refl = refl , refl

+-injective : ∀ {A B C D : Ty} → _≡_ {Ty} (A + B) (C + D) → (A ≡ C) × (B ≡ D)
+-injective refl = refl , refl

μ-injective : ∀ {F G : Func} → _≡_ {Ty} (μ F) (μ G) → F ≡ G
μ-injective refl = refl

-- Constructor injectivity for Func
K-injective : ∀ {A B : Ty} → _≡_ {Func} (K A) (K B) → A ≡ B
K-injective refl = refl

⊕-injective : ∀ {F₁ G₁ F₂ G₂ : Func} → _≡_ {Func} (F₁ ⊕ G₁) (F₂ ⊕ G₂) → (F₁ ≡ F₂) × (G₁ ≡ G₂)
⊕-injective refl = refl , refl

⊗-injective : ∀ {F₁ G₁ F₂ G₂ : Func} → _≡_ {Func} (F₁ ⊗ G₁) (F₂ ⊗ G₂) → (F₁ ≡ F₂) × (G₁ ≡ G₂)
⊗-injective refl = refl , refl

------------------------------------------------------------------------
-- 6d: Maybe (defined in terms of existing constructs)
------------------------------------------------------------------------

-- Maybe A ≅ ⊤ ⊎ A (no new primitives!)
Maybe : Set → Set
Maybe A = ⊤ ⊎ A

nothing : ∀ {A : Set} → Maybe A
nothing = inj₁ tt

just : ∀ {A : Set} → A → Maybe A
just x = inj₂ x

-- just is injective
just-inj : ∀ {A : Set} {x y : A} → _≡_ {Maybe A} (just x) (just y) → x ≡ y
just-inj refl = refl

-- nothing ≢ just
nothing≢just : ∀ {A : Set} {x : A} → _≡_ {Maybe A} nothing (just x) → ⊥
nothing≢just ()

------------------------------------------------------------------------
-- 6e: Decode Functions (inverse of encoding)
------------------------------------------------------------------------

-- The decode approach: define functions that extract types/functors
-- from their encodings, then prove decode ∘ encode = just.
-- Injectivity follows: if encode A ≡ encode B, then
-- decode (encode A) ≡ decode (encode B), so just A ≡ just B, so A ≡ B.

-- Decode requires matching on the specific encoding patterns.
-- We define mutual decode functions for types and functors.

-- The encoding patterns (for reference):
--   ⌜ Unit ⌝Ty    = In ∘ inl ∘ terminal
--   ⌜ A * B ⌝Ty   = In ∘ inr ∘ inl ∘ ⟨ ⌜A⌝, ⌜B⌝ ⟩
--   ⌜ A + B ⌝Ty   = In ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜A⌝, ⌜B⌝ ⟩
--   ⌜ μ F ⌝Ty     = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜F⌝
--   ⌜ Id ⌝Func    = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ terminal
--   ⌜ K A ⌝Func   = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜A⌝
--   ⌜ F ⊕ G ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜F⌝, ⌜G⌝ ⟩
--   ⌜ F ⊗ G ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜F⌝, ⌜G⌝ ⟩

-- Due to Agda's pattern matching limitations with deeply nested compositions,
-- we use a staged approach: first match the outer structure, then recurse.

-- Helper: match the "injection tag" (how many inr's before inl/terminal)
-- This is tricky because the patterns overlap with general compositions.

-- For now, we observe that the decode approach requires the same deep
-- pattern matching that caused issues in the progress proof. The fundamental
-- issue is that Agda's coverage checker struggles with patterns like
-- (In ∘ (inr ∘ (inl ∘ ⟨ f , g ⟩))) because it can't determine exhaustiveness
-- without knowing all possible term shapes.

-- ALTERNATIVE PROOF: Direct structural induction
-- Instead of decode, we prove injectivity directly by case analysis.
-- The key lemma is ∘-domain-eq: equal compositions have equal intermediate types.

------------------------------------------------------------------------
-- 6f: Main Injectivity Proofs (via domain type discrimination)
------------------------------------------------------------------------

-- The key insight: each encoding constructor produces a composition where
-- the INTERMEDIATE TYPE differs. When encodings are equal, the intermediate
-- types must match (by ∘-domain-eq). Different constructors produce
-- incompatible intermediate types, giving us contradictions.

-- Helper: extract domain type equality from composition equality
∘-domain-eq : ∀ {A B B' C} {f : Term B C} {f' : Term B' C}
              {g : Term A B} {g' : Term A B'} →
              _≡_ {Term A C} (f ∘ g) (f' ∘ g') → B ≡ B'
∘-domain-eq refl = refl

-- The encoding intermediate types (the domain of the second part after In):
--   ⌜ Unit ⌝Ty    = In ∘ (inl ∘ terminal)        -- inl domain: Unit
--   ⌜ A * B ⌝Ty   = In ∘ (inr ∘ ...)             -- inr domain: TC*TC + ...
--   ⌜ A + B ⌝Ty   = In ∘ (inr ∘ ...)             -- inr domain: TC*TC + ...
--   ⌜ μ F ⌝Ty     = In ∘ (inr ∘ ...)             -- inr domain: TC*TC + ...
--
-- For Unit vs others: the second-level domains differ (Unit vs larger sum).
-- For * vs + vs μ: we need to look deeper to distinguish.

-- Type aliases for the intermediate types in the encoding
-- These help clarify what types we're comparing.

-- Level 1: after In, we have term of type ⟦TyFuncF⟧F TyFuncCode
-- Level 2: that's a composition (inl or inr) ∘ something

-- The key contradiction: Unit ≢ (TyFuncCode * TyFuncCode) + Rest
-- This distinguishes Unit from the other type constructors.

-- For distinguishing *, +, μ from each other, we look at level 3.

-- Mutual injectivity proofs (using domain type discrimination)
⌜⌝Ty-injective : ∀ {A B : Ty} → ⌜ A ⌝Ty ≡ ⌜ B ⌝Ty → A ≡ B
⌜⌝Func-injective : ∀ {F G : Func} → ⌜ F ⌝Func ≡ ⌜ G ⌝Func → F ≡ G

-- For the proof, we use the fact that different constructors produce
-- structurally different compositions. The ∘-injective lemma extracts
-- the component equalities, and when structures differ, we get type
-- mismatches that are impossible.

-- Type injectivity by case analysis
-- The key insight: each encoding has a unique structural form.
-- For same constructors, we extract subterm equalities and recurse.
-- For different constructors, the structural mismatch leads to contradictions
-- that Agda can detect during unification when pattern matching on refl.

⌜⌝Ty-injective {Unit} {Unit} _ = refl
-- For Unit vs others: the inner compositions have incompatible structures.
-- Agda detects this during unification and rules out the refl pattern.
⌜⌝Ty-injective {Unit} {_ * _} ()
⌜⌝Ty-injective {Unit} {_ + _} ()
⌜⌝Ty-injective {Unit} {μ _} ()

⌜⌝Ty-injective {_ * _} {Unit} ()
-- _∘_ is RIGHT-associative (infixr 9), so:
--   ⌜ A * B ⌝Ty = In ∘ inr ∘ inl ∘ ⟨...⟩ = In ∘ (inr ∘ (inl ∘ ⟨...⟩))
-- We need 3 ∘-injective applications to reach the pair.
⌜⌝Ty-injective {A * B} {C * D} eq =
  let (_ , eq2) = ∘-injective eq          -- In ≡ In, rest ≡ rest
      (_ , eq3) = ∘-injective eq2         -- inr ≡ inr, rest ≡ rest
      (_ , eq-pair) = ∘-injective eq3     -- inl ≡ inl, ⟨...⟩ ≡ ⟨...⟩
      (eqA , eqB) = ⟨⟩-injective eq-pair
  in cong₂ _*_ (⌜⌝Ty-injective eqA) (⌜⌝Ty-injective eqB)
⌜⌝Ty-injective {_ * _} {_ + _} ()
⌜⌝Ty-injective {_ * _} {μ _} ()

⌜⌝Ty-injective {_ + _} {Unit} ()
⌜⌝Ty-injective {_ + _} {_ * _} ()
-- ⌜ A + B ⌝Ty = In ∘ inr ∘ inr ∘ inl ∘ ⟨...⟩ = In ∘ (inr ∘ (inr ∘ (inl ∘ ⟨...⟩)))
-- 4 ∘-injective applications to reach the pair.
⌜⌝Ty-injective {A + B} {C + D} eq =
  let (_ , eq2) = ∘-injective eq
      (_ , eq3) = ∘-injective eq2
      (_ , eq4) = ∘-injective eq3
      (_ , eq-pair) = ∘-injective eq4
      (eqA , eqB) = ⟨⟩-injective eq-pair
  in cong₂ _+_ (⌜⌝Ty-injective eqA) (⌜⌝Ty-injective eqB)
⌜⌝Ty-injective {_ + _} {μ _} ()

⌜⌝Ty-injective {μ _} {Unit} ()
⌜⌝Ty-injective {μ _} {_ * _} ()
⌜⌝Ty-injective {μ _} {_ + _} ()
-- ⌜ μ F ⌝Ty = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜F⌝
-- = In ∘ (inr ∘ (inr ∘ (inr ∘ (inl ∘ ⌜F⌝))))
-- 5 ∘-injective applications to reach the subterm.
⌜⌝Ty-injective {μ F} {μ G} eq =
  let (_ , eq2) = ∘-injective eq
      (_ , eq3) = ∘-injective eq2
      (_ , eq4) = ∘-injective eq3
      (_ , eq5) = ∘-injective eq4
      (_ , eq-sub) = ∘-injective eq5
  in cong μ_ (⌜⌝Func-injective eq-sub)

-- Functor injectivity (similar structure with absurd patterns for cross-cases)
-- _∘_ is RIGHT-associative (infixr 9), so we need to count correctly:
-- - K A: In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜A⌝ (7 compositions)
-- - F ⊕ G: In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨...⟩ (8 compositions)
-- - F ⊗ G: In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨...⟩ (8 compositions)
⌜⌝Func-injective {Id} {Id} _ = refl
⌜⌝Func-injective {Id} {K _} ()
⌜⌝Func-injective {Id} {_ ⊕ _} ()
⌜⌝Func-injective {Id} {_ ⊗ _} ()

⌜⌝Func-injective {K _} {Id} ()
-- K A: 7 ∘-injective applications
⌜⌝Func-injective {K A} {K B} eq =
  let (_ , eq2) = ∘-injective eq
      (_ , eq3) = ∘-injective eq2
      (_ , eq4) = ∘-injective eq3
      (_ , eq5) = ∘-injective eq4
      (_ , eq6) = ∘-injective eq5
      (_ , eq7) = ∘-injective eq6
      (_ , eq-sub) = ∘-injective eq7
  in cong K (⌜⌝Ty-injective eq-sub)
⌜⌝Func-injective {K _} {_ ⊕ _} ()
⌜⌝Func-injective {K _} {_ ⊗ _} ()

⌜⌝Func-injective {_ ⊕ _} {Id} ()
⌜⌝Func-injective {_ ⊕ _} {K _} ()
-- F ⊕ G: 8 ∘-injective applications, then ⟨⟩-injective
⌜⌝Func-injective {F₁ ⊕ G₁} {F₂ ⊕ G₂} eq =
  let (_ , eq2) = ∘-injective eq
      (_ , eq3) = ∘-injective eq2
      (_ , eq4) = ∘-injective eq3
      (_ , eq5) = ∘-injective eq4
      (_ , eq6) = ∘-injective eq5
      (_ , eq7) = ∘-injective eq6
      (_ , eq8) = ∘-injective eq7
      (_ , eq-pair) = ∘-injective eq8
      (eqF , eqG) = ⟨⟩-injective eq-pair
  in cong₂ _⊕_ (⌜⌝Func-injective eqF) (⌜⌝Func-injective eqG)
⌜⌝Func-injective {_ ⊕ _} {_ ⊗ _} ()

⌜⌝Func-injective {_ ⊗ _} {Id} ()
⌜⌝Func-injective {_ ⊗ _} {K _} ()
⌜⌝Func-injective {_ ⊗ _} {_ ⊕ _} ()
-- F ⊗ G: 8 ∘-injective applications, then ⟨⟩-injective
⌜⌝Func-injective {F₁ ⊗ G₁} {F₂ ⊗ G₂} eq =
  let (_ , eq2) = ∘-injective eq
      (_ , eq3) = ∘-injective eq2
      (_ , eq4) = ∘-injective eq3
      (_ , eq5) = ∘-injective eq4
      (_ , eq6) = ∘-injective eq5
      (_ , eq7) = ∘-injective eq6
      (_ , eq8) = ∘-injective eq7
      (_ , eq-pair) = ∘-injective eq8
      (eqF , eqG) = ⟨⟩-injective eq-pair
  in cong₂ _⊗_ (⌜⌝Func-injective eqF) (⌜⌝Func-injective eqG)

------------------------------------------------------------------------
-- 6e: Term Encoding Injectivity
------------------------------------------------------------------------

-- Term encoding injectivity follows the same pattern but with 11 cases.
-- The proof is more complex due to dependent types in constructors like cata,
-- and the fact that composition has an intermediate type that needs to be proven equal.
--
-- For now, we keep this as a postulate. The key injectivity results
-- (type and functor encoding) are fully proven above.
--
-- The proof would follow the same pattern:
-- 1. Different constructors: absurd patterns (different injection depth)
-- 2. Same constructors: peel through ∘-injective and recurse

postulate
  encode-injective : ∀ {A B} {t u : Term A B} → encode t ≡ encode u → t ≡ u

-- NOTE: To complete this proof, we would need to:
-- 1. Handle type constraints on constructors (id requires A=B, fst requires A=A'*B', etc.)
-- 2. Prove that equal encodings of compositions have equal intermediate types
-- 3. Handle the dependent case for cata (algebra type depends on functor)
-- The structure is mechanical but requires careful handling of dependent types.

------------------------------------------------------------------------
-- Part 7: Connection to MinimalCCC.TermCode
------------------------------------------------------------------------

-- MinimalCCC defines a simpler TermCode without type annotations.
-- Our TermCode' is more complete but compatible.
--
-- For the fixpoint theorem, we use TermCode' because:
-- 1. It's injective (different terms → different codes)
-- 2. It's self-contained (no external type info needed)
-- 3. A normalizer can pattern match on the structure
--
-- The normalizer type becomes:
--   Normalizer' = Term TermCode' TermCode'

Normalizer'' : Set
Normalizer'' = Term TermCode' TermCode'

-- Apply normalizer to encoded term
apply-norm' : Normalizer'' → Term Unit TermCode' → Term Unit TermCode'
apply-norm' N code = N ∘ code

-- Fixpoint condition with our encoding
IsFixpoint'' : Normalizer'' → Set
IsFixpoint'' N = apply-norm' N (encode N) ≡ encode N

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- We have defined:
--   TyFuncCode  : Ty                        -- type for type/functor codes
--   TermCode'   : Ty                        -- type for term codes
--   ⌜_⌝Ty      : Ty → Term Unit TyFuncCode
--   ⌜_⌝Func    : Func → Term Unit TyFuncCode
--   encode     : Term A B → Term Unit TermCode'
--
-- The encoding is:
--   - Complete: all term constructors are represented
--   - Faithful: type information is preserved
--   - Injective: different terms produce different codes (postulated)
--
-- This encoding is the foundation for the fixpoint correctness theorem.
-- A normalizer N : Term TermCode' TermCode' can process these codes,
-- and if N(encode N) = encode N, then N correctly computes normal forms.
------------------------------------------------------------------------
