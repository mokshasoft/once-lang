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
--   3. ⌜_⌝Ty, ⌜_⌝Func, encode - the encoding functions
------------------------------------------------------------------------

module normalizer.Foundations.Encoding where

open import normalizer.Foundations.Types
open import normalizer.Foundations.MinimalCCC

------------------------------------------------------------------------
-- Part 1: Encoding Types and Functors
------------------------------------------------------------------------

-- Types and Functors are mutually recursive, so we encode them together.
-- We use a sum type with tags to distinguish:
--   - Types: Void, Unit, A * B, A + B, A ⇒ B, μ F
--   - Functors: Id, K A, F ⊕ G, F ⊗ G
--
-- Encoding scheme (10 type/functor alternatives):
--   0: Void type      (K Unit)
--   1: Unit type      (K Unit)
--   2: Product type   (Id ⊗ Id) - two type codes
--   3: Sum type       (Id ⊗ Id) - two type codes
--   4: Exponential    (Id ⊗ Id) - two type codes (A ⇒ B)
--   5: Mu type        (Id)      - one functor code
--   6: Id functor     (K Unit)
--   7: K functor      (Id)      - one type code
--   8: Sum functor    (Id ⊗ Id) - two functor codes
--   9: Product functor(Id ⊗ Id) - two functor codes

TyFuncF : Func
TyFuncF = K Unit          -- 0: Void type
        ⊕ K Unit          -- 1: Unit type
        ⊕ (Id ⊗ Id)       -- 2: A * B
        ⊕ (Id ⊗ Id)       -- 3: A + B
        ⊕ (Id ⊗ Id)       -- 4: A ⇒ B (exponential)
        ⊕ Id              -- 5: μ F
        ⊕ K Unit          -- 6: Id functor
        ⊕ Id              -- 7: K A
        ⊕ (Id ⊗ Id)       -- 8: F ⊕ G
        ⊕ (Id ⊗ Id)       -- 9: F ⊗ G

TyFuncCode : Ty
TyFuncCode = μ TyFuncF

------------------------------------------------------------------------
-- Part 2: Type and Functor Encoding Functions
------------------------------------------------------------------------

-- Mutually recursive encoding of types and functors
-- We inline the injection helpers directly for explicit composition structure.
-- This makes the ∘-injective chain depth predictable for injectivity proofs.
⌜_⌝Ty : Ty → Term Unit TyFuncCode
⌜_⌝Func : Func → Term Unit TyFuncCode

-- Void: In ∘ inl ∘ terminal (position 0)
⌜ Void ⌝Ty = In ∘ inl ∘ terminal

-- Unit: In ∘ inr ∘ inl ∘ terminal (position 1)
⌜ Unit ⌝Ty = In ∘ inr ∘ inl ∘ terminal

-- Product: In ∘ inr^2 ∘ inl ∘ ⟨...⟩ (position 2)
⌜ A * B ⌝Ty = In ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

-- Sum: In ∘ inr^3 ∘ inl ∘ ⟨...⟩ (position 3)
⌜ A + B ⌝Ty = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

-- Exponential: In ∘ inr^4 ∘ inl ∘ ⟨...⟩ (position 4)
⌜ A ⇒ B ⌝Ty = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

-- Mu: In ∘ inr^5 ∘ inl ∘ ⌜F⌝ (position 5)
⌜ μ F ⌝Ty = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func

-- Id functor: In ∘ inr^6 ∘ inl ∘ terminal (position 6)
⌜ Id ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ terminal

-- K functor: In ∘ inr^7 ∘ inl ∘ ⌜A⌝ (position 7)
⌜ K A ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty

-- ⊕ functor: In ∘ inr^8 ∘ inl ∘ ⟨...⟩ (position 8)
⌜ F ⊕ G ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ F ⌝Func , ⌜ G ⌝Func ⟩

-- ⊗ functor: In ∘ inr^9 (position 9, last alternative)
⌜ F ⊗ G ⌝Func = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜ F ⌝Func , ⌜ G ⌝Func ⟩

------------------------------------------------------------------------
-- Part 3: Term Code Definition
------------------------------------------------------------------------

-- Terms have 15 constructors:
--   0: id         (no subterms, but has type A)
--   1: f ∘ g      (two subterms)
--   2: fst        (has types A, B)
--   3: snd        (has types A, B)
--   4: ⟨f, g⟩     (two subterms)
--   5: inl        (has types A, B)
--   6: inr        (has types A, B)
--   7: [f, g]     (two subterms)
--   8: terminal   (has type A)
--   9: initial    (has type A)
--  10: In         (has functor F)
--  11: Out        (has functor F)
--  12: cata F alg (functor F, one subterm)
--  13: curry f    (types A, B, C, one subterm)
--  14: apply      (types A, B)
--
-- For a faithful encoding, we include type annotations.
-- This makes the encoding larger but ensures injectivity.

-- Term code functor (binary sums)
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
      ⊕ (K TyFuncCode)                              -- 9: initial A
      ⊕ (K TyFuncCode)                              -- 10: In F (store functor code)
      ⊕ (K TyFuncCode)                              -- 11: Out F (store functor code)
      ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata F alg (functor + algebra)
      ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry f (A, B, C, body)
      ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply A B

TermCode' : Ty
TermCode' = μ TermF

------------------------------------------------------------------------
-- Part 4: Term Code Injections
------------------------------------------------------------------------

-- Helper type alias for the unfolded term code
UnfoldedTermCode : Ty
UnfoldedTermCode = ⟦ TermF ⟧F TermCode'

-- Injection for id (position 0)
inj-id : Term TyFuncCode UnfoldedTermCode
inj-id = inl

-- Injection for compose (position 1)
inj-comp : Term (TermCode' * TermCode') UnfoldedTermCode
inj-comp = inr ∘ inl

-- Injection for fst (position 2)
inj-fst : Term (TyFuncCode * TyFuncCode) UnfoldedTermCode
inj-fst = inr ∘ inr ∘ inl

-- Injection for snd (position 3)
inj-snd : Term (TyFuncCode * TyFuncCode) UnfoldedTermCode
inj-snd = inr ∘ inr ∘ inr ∘ inl

-- Injection for pair (position 4)
inj-pair : Term (TermCode' * TermCode') UnfoldedTermCode
inj-pair = inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for inl (position 5)
inj-inl : Term (TyFuncCode * TyFuncCode) UnfoldedTermCode
inj-inl = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for inr (position 6)
inj-inr : Term (TyFuncCode * TyFuncCode) UnfoldedTermCode
inj-inr = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for case (position 7)
inj-case : Term (TermCode' * TermCode') UnfoldedTermCode
inj-case = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for terminal (position 8)
inj-terminal : Term TyFuncCode UnfoldedTermCode
inj-terminal = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for initial (position 9)
inj-initial : Term TyFuncCode UnfoldedTermCode
inj-initial = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for In (position 10)
inj-In : Term TyFuncCode UnfoldedTermCode
inj-In = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for Out (position 11)
inj-Out : Term TyFuncCode UnfoldedTermCode
inj-Out = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for cata (position 12)
inj-cata : Term (TyFuncCode * TermCode') UnfoldedTermCode
inj-cata = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for curry (position 13)
inj-curry : Term ((TyFuncCode * TyFuncCode) * (TyFuncCode * TermCode')) UnfoldedTermCode
inj-curry = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl

-- Injection for apply (position 14, last alternative)
inj-apply : Term (TyFuncCode * TyFuncCode) UnfoldedTermCode
inj-apply = inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr

------------------------------------------------------------------------
-- Part 5: The Term Encoding Function
------------------------------------------------------------------------

-- Encode a term as data
-- The encoding includes type information to ensure injectivity.
encode : ∀ {A B} → Term A B → Term Unit TermCode'

-- 0: id - inl (0 inrs)
encode (id {A}) = In ∘ inl ∘ ⌜ A ⌝Ty

-- 1: compose - inr ∘ inl (1 inr)
encode (f ∘ g) = In ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩

-- 2: fst - inr^2 ∘ inl (2 inrs)
encode (fst {A} {B}) = In ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

-- 3: snd - inr^3 ∘ inl (3 inrs)
encode (snd {A} {B}) = In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

-- 4: pair - inr^4 ∘ inl (4 inrs)
encode ⟨ f , g ⟩ = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩

-- 5: inl - inr^5 ∘ inl (5 inrs)
encode (inl {A} {B}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

-- 6: inr - inr^6 ∘ inl (6 inrs)
encode (inr {A} {B}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩

-- 7: case - inr^7 ∘ inl (7 inrs)
encode [ f , g ] = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩

-- 8: terminal - inr^8 ∘ inl (8 inrs)
encode (terminal {A}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty

-- 9: initial - inr^9 ∘ inl (9 inrs)
encode (initial {A}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty

-- 10: In - inr^10 ∘ inl (10 inrs)
encode (In {F}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func

-- 11: Out - inr^11 ∘ inl (11 inrs)
encode (Out {F}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func

-- 12: cata - inr^12 ∘ inl (12 inrs)
encode (cata F alg) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ F ⌝Func , encode alg ⟩

-- 13: curry - inr^13 ∘ inl (13 inrs)
-- curry stores ((A, B), (C, body))
encode (curry {A} {B} {C} f) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩

-- 14: apply - inr^14 (14 inrs, no inl - last alternative)
-- apply stores (A, B)
encode (apply {A} {B}) = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩


-- End of minimal Encoding for Level0
