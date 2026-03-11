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

module Encoding where

open import Types
open import MinimalCCC

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
⌜_⌝Ty : Ty → Term Unit TyFuncCode
⌜_⌝Func : Func → Term Unit TyFuncCode

⌜ Unit ⌝Ty = In ∘ inj-unit-ty
⌜ A * B ⌝Ty = In ∘ inj-prod-ty ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
⌜ A + B ⌝Ty = In ∘ inj-sum-ty ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩
⌜ μ F ⌝Ty = In ∘ inj-mu-ty ∘ ⌜ F ⌝Func

⌜ Id ⌝Func = In ∘ inj-id-func
⌜ K A ⌝Func = In ∘ inj-k-func ∘ ⌜ A ⌝Ty
⌜ F ⊕ G ⌝Func = In ∘ inj-oplus-func ∘ ⟨ ⌜ F ⌝Func , ⌜ G ⌝Func ⟩
⌜ F ⊗ G ⌝Func = In ∘ inj-otimes-func ∘ ⟨ ⌜ F ⌝Func , ⌜ G ⌝Func ⟩

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

encode (id {A}) = In ∘ inj-id ∘ ⌜ A ⌝Ty

encode (f ∘ g) = In ∘ inj-comp ∘ ⟨ encode f , encode g ⟩

encode (fst {A} {B}) = In ∘ inj-fst ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

encode (snd {A} {B}) = In ∘ inj-snd ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

encode ⟨ f , g ⟩ = In ∘ inj-pair ∘ ⟨ encode f , encode g ⟩

encode (inl {A} {B}) = In ∘ inj-inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

encode (inr {A} {B}) = In ∘ inj-inr ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

encode [ f , g ] = In ∘ inj-case ∘ ⟨ encode f , encode g ⟩

encode (terminal {A}) = In ∘ inj-terminal ∘ ⌜ A ⌝Ty

encode (In {F}) = In ∘ inj-In ∘ ⌜ F ⌝Func

encode (cata F alg) = In ∘ inj-cata ∘ ⟨ ⌜ F ⌝Func , encode alg ⟩

------------------------------------------------------------------------
-- Part 6: Properties of the Encoding
------------------------------------------------------------------------

-- The encoding is injective: different terms produce different codes.
-- This follows from the faithful representation of all constructor
-- arguments, including type information.

-- Injectivity of type encoding
postulate
  ⌜⌝Ty-injective : ∀ {A B : Ty} → ⌜ A ⌝Ty ≡ ⌜ B ⌝Ty → A ≡ B

-- Injectivity of functor encoding
postulate
  ⌜⌝Func-injective : ∀ {F G : Func} → ⌜ F ⌝Func ≡ ⌜ G ⌝Func → F ≡ G

-- Injectivity of term encoding
-- Note: This is stated for terms at the same type. Cross-type
-- injectivity follows from type information in the encoding.
postulate
  encode-injective : ∀ {A B} {t u : Term A B} → encode t ≡ encode u → t ≡ u

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
