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
      ⊕ (K TyFuncCode)                              -- 10: Out F (store functor code)
      ⊕ (K TyFuncCode ⊗ Id)                        -- 11: cata F alg (functor + algebra)

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

-- Injection for Out
inj-Out : Term TyFuncCode UnfoldedTermCode
inj-Out = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for cata
inj-cata : Term (TyFuncCode * TermCode') UnfoldedTermCode
inj-cata = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr

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
-- 9: In         - inr^9 ∘ inl (9 inrs)
-- 10: Out       - inr^10 ∘ inl (10 inrs)
-- 11: cata      - inr^11 (11 inrs, no inl)

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

encode (Out {F}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func

encode (cata F alg) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜ F ⌝Func , encode alg ⟩


-- End of minimal Encoding for Level0V2
