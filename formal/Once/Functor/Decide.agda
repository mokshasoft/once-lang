-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Functor.Decide
--
-- Structural deciders for `IsBaseType` and `WellFormedF`. These let the
-- elaborator turn a *parsed* functor (`Once.Type.Functor`, e.g. the body
-- of a `Mu F` type) into the `WellFormedF F` witness that the CCC
-- recursion-scheme IR constructors (`In` / `Cata` / `out-μ`) require.
--
-- Both return `Maybe` (a `nothing` means the functor is not well-formed,
-- e.g. a `K` holding a function/μ/ν type) — exactly the partiality the
-- elaborator surfaces as a type error.
------------------------------------------------------------------------

module Once.Functor.Decide where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer;
                             _*_; _+_; _⇒[_]_; μ-type; ν-type;
                             Functor; K; Id; _⊕_; _⊗_)
open import Once.Functor.Translate
  using (IsBaseType; base-Unit; base-Void; base-Int; base-Float;
         base-Str; base-Buffer; base-Prod; base-Sum;
         IsConcrete; con-base; con-fun;
         WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)

-- | Decide whether a type is a base type (no functions / μ / ν).
isBaseType? : (A : Type) → Maybe (IsBaseType A)
isBaseType? Unit   = just base-Unit
isBaseType? Void   = just base-Void
isBaseType? Int    = just base-Int
isBaseType? Float  = just base-Float
isBaseType? Str    = just base-Str
isBaseType? Buffer = just base-Buffer
isBaseType? (A * B) with isBaseType? A | isBaseType? B
... | just bA | just bB = just (base-Prod bA bB)
... | _       | _       = nothing
isBaseType? (A + B) with isBaseType? A | isBaseType? B
... | just bA | just bB = just (base-Sum bA bB)
... | _       | _       = nothing
isBaseType? (_ ⇒[ _ ] _) = nothing
isBaseType? (μ-type _) = nothing
isBaseType? (ν-type _) = nothing

-- | Decide whether a type is CONCRETE / FFI-representable (Plan 0.58): a base
-- type, or a first-order function pointer (base argument, concrete result).
isConcrete? : (A : Type) → Maybe (IsConcrete A)
isConcrete? (A ⇒[ _ ] B) with isBaseType? A | isConcrete? B
... | just bA | just cB = just (con-fun bA cB)
... | _       | _       = nothing
isConcrete? A with isBaseType? A
... | just bA = just (con-base bA)
... | nothing = nothing

-- | Completeness: a genuine `IsBaseType`/`IsConcrete` witness means the decider
-- returns `just` (Plan 0.58 — needed to reduce the elaborator's new
-- concreteness-guarded branches in Completeness/fallback proofs).
isBaseType?-complete : ∀ {A} → IsBaseType A → ∃[ b ] isBaseType? A ≡ just b
isBaseType?-complete base-Unit   = base-Unit , refl
isBaseType?-complete base-Void   = base-Void , refl
isBaseType?-complete base-Int    = base-Int , refl
isBaseType?-complete base-Float  = base-Float , refl
isBaseType?-complete base-Str    = base-Str , refl
isBaseType?-complete base-Buffer = base-Buffer , refl
isBaseType?-complete (base-Prod bA bB)
  with isBaseType?-complete bA | isBaseType?-complete bB
... | (a , eqA) | (b , eqB) rewrite eqA | eqB = base-Prod a b , refl
isBaseType?-complete (base-Sum bA bB)
  with isBaseType?-complete bA | isBaseType?-complete bB
... | (a , eqA) | (b , eqB) rewrite eqA | eqB = base-Sum a b , refl

isConcrete?-complete : ∀ {A} → IsConcrete A → ∃[ c ] isConcrete? A ≡ just c
isConcrete?-complete (con-base base-Unit)   = con-base base-Unit , refl
isConcrete?-complete (con-base base-Void)   = con-base base-Void , refl
isConcrete?-complete (con-base base-Int)    = con-base base-Int , refl
isConcrete?-complete (con-base base-Float)  = con-base base-Float , refl
isConcrete?-complete (con-base base-Str)    = con-base base-Str , refl
isConcrete?-complete (con-base base-Buffer) = con-base base-Buffer , refl
isConcrete?-complete (con-base (base-Prod bA bB))
  with isBaseType?-complete (base-Prod bA bB)
... | (b , eq) rewrite eq = con-base b , refl
isConcrete?-complete (con-base (base-Sum bA bB))
  with isBaseType?-complete (base-Sum bA bB)
... | (b , eq) rewrite eq = con-base b , refl
isConcrete?-complete (con-fun bA cB)
  with isBaseType?-complete bA | isConcrete?-complete cB
... | (b , eqB) | (c , eqC) rewrite eqB | eqC = con-fun b c , refl

-- | Decide whether a functor is well-formed (K positions are base types).
wellFormedF? : (F : Functor) → Maybe (WellFormedF F)
wellFormedF? (K A) with isBaseType? A
... | just bA = just (wf-K bA)
... | nothing = nothing
wellFormedF? Id = just wf-Id
wellFormedF? (F ⊕ G) with wellFormedF? F | wellFormedF? G
... | just wF | just wG = just (wf-Sum wF wG)
... | _       | _       = nothing
wellFormedF? (F ⊗ G) with wellFormedF? F | wellFormedF? G
... | just wF | just wG = just (wf-Prod wF wG)
... | _       | _       = nothing
