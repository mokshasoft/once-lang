------------------------------------------------------------------------
-- AlgebraSpec: Full specification for a fixpoint-achieving algebra
--
-- An algebra achieves fixpoint if it "acts like In" at each position.
-- This module defines the per-position conditions and derives the
-- fixpoint theorem generically from structural induction.
------------------------------------------------------------------------

module normalizer.Correctness.AlgebraSpec where

open import normalizer.Foundations.Catamorphisms
open import normalizer.Foundations.TermFunctor
open import normalizer.Foundations.Encoding
  using (encode; TermCode'; TermF; TyFuncCode; ⌜_⌝Ty; ⌜_⌝Func)
open import normalizer.Foundations.NoRedex
  using (NoRedex; NotIdStruct)

------------------------------------------------------------------------
-- Per-position algebra conditions
--
-- For each position N, the algebra must satisfy:
--   alg ∘ inj-N ⟶* In ∘ inj-N
--
-- This means: when given data at position N, the algebra produces
-- the same result as just wrapping with In.
--
-- For trivial positions: this is immediate from handler definitions
-- For composition: this requires proving is-id returns inr on NoRedex
------------------------------------------------------------------------

-- Injection chains for each position (right-associated)
-- Position 0: inl
-- Position 1: inr ∘ inl
-- Position 2: inr ∘ inr ∘ inl
-- etc.

record AlgebraSpec (alg : Term (⟦ TermF ⟧F TermCode') TermCode') : Set₁ where
  field
    -- Position 0 (id): alg ∘ inl ⟶* In ∘ inl
    alg-at-id : ∀ {A} →
      (alg ∘ (inl ∘ ⌜ A ⌝Ty)) ⟶* (In {TermF} ∘ (inl ∘ ⌜ A ⌝Ty))

    -- Position 1 (comp): The non-trivial case
    -- For NoRedex f, g where neither is id-shaped:
    alg-at-comp : ∀ {A B C} {f : Term B C} {g : Term A B} →
      NoRedex f → NoRedex g → NotIdStruct f → NotIdStruct g →
      (alg ∘ (inr ∘ inl ∘ ⟨ encode f , encode g ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inl ∘ ⟨ encode f , encode g ⟩))

    -- Position 2 (fst): alg ∘ inr ∘ inr ∘ inl ⟶* In ∘ inr ∘ inr ∘ inl
    alg-at-fst : ∀ {A B} →
      (alg ∘ (inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))

    -- Position 3 (snd)
    alg-at-snd : ∀ {A B} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))

    -- Position 4 (pair): Has recursive subterms, but handler is trivial
    alg-at-pair : ∀ {C A B} {f : Term C A} {g : Term C B} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩))

    -- Position 5 (inl)
    alg-at-inl : ∀ {A B} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))

    -- Position 6 (inr)
    alg-at-inr : ∀ {A B} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))

    -- Position 7 (case): Has recursive subterms
    alg-at-case : ∀ {A B C} {f : Term A C} {g : Term B C} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ encode f , encode g ⟩))

    -- Position 8 (terminal)
    alg-at-terminal : ∀ {A} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty))

    -- Position 9 (initial)
    alg-at-initial : ∀ {A} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ A ⌝Ty))

    -- Position 10 (In)
    alg-at-In : ∀ {F} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func))

    -- Position 11 (Out)
    alg-at-Out : ∀ {F} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⌜ F ⌝Func))

    -- Position 12 (cata): Has recursive subterm (alg)
    alg-at-cata : ∀ {F A} {a : Term (⟦ F ⟧F A) A} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ F ⌝Func , encode a ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨ ⌜ F ⌝Func , encode a ⟩))

    -- Position 13 (curry): Has recursive subterm (body)
    alg-at-curry : ∀ {A B C} {f : Term (A * B) C} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘
              ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl ∘
              ⟨ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩ , ⟨ ⌜ C ⌝Ty , encode f ⟩ ⟩))

    -- Position 14 (apply)
    alg-at-apply : ∀ {A B} →
      (alg ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩)) ⟶*
      (In {TermF} ∘ (inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr ∘ ⟨ ⌜ A ⌝Ty , ⌜ B ⌝Ty ⟩))

  -- The normalizer built from this algebra
  N : Term TermCode' TermCode'
  N = cata TermF alg

------------------------------------------------------------------------
-- Note: The fixpoint theorem will be derived in SpecDerivedFixpoint.agda
-- using structural induction on NoRedex, composing:
--   1. cata-β-right (unfold catamorphism)
--   2. fmap navigation (from TermFunctor.agda)
--   3. alg-at-* conditions (from this spec)
--   4. IH on recursive subterms
------------------------------------------------------------------------
