-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Functor.Decide
--
-- Structural deciders for `Base ∅ₖ` and `WFFun ∅ₖ`. These let the
-- elaborator turn a *parsed* functor (`Once.Type.Functor`, e.g. the body
-- of a `Mu F` type) into the `WFFun ∅ₖ F` witness that the CCC
-- recursion-scheme IR constructors (`In` / `Cata` / `out-μ`) require.
--
-- Both return `Maybe` (a `nothing` means the functor is not well-formed,
-- e.g. a `K` holding a function/μ/ν type) — exactly the partiality the
-- elaborator surfaces as a type error.
------------------------------------------------------------------------

module Once.Functor.Decide where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Type using (Ty; Fun; WFFun; wf-⊕; wf-⊗; KCtx; Kind; base; any; Base; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; var; μ; ν; Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; K; Id; _⊕_; _⊗_)

open import Once.Spec.Type using (Fun; μ; ν)
open import Once.Spec.Type using (wf-K; wf-Id)
open import Once.Internal.Type.WellFormed using (IsConcrete; con-base; con-fun)
open import Once.Spec.Type using (Base; WFFun; b-*; b-+; b-Float; b-Int; b-Unit; b-Void; wf-⊕; wf-⊗; ∅ₖ)

-- | Decide whether a type is a base type (no functions / μ / ν).
isBaseType? : (A : Type) → Maybe (Base ∅ₖ A)
isBaseType? Unit   = just b-Unit
isBaseType? Void   = just b-Void
isBaseType? Int    = just b-Int
isBaseType? Float  = just b-Float
isBaseType? (A * B) with isBaseType? A | isBaseType? B
... | just bA | just bB = just (b-* bA bB)
{-# CATCHALL #-}
... | _       | _       = nothing
isBaseType? (A + B) with isBaseType? A | isBaseType? B
... | just bA | just bB = just (b-+ bA bB)
{-# CATCHALL #-}
... | _       | _       = nothing
isBaseType? (_ ⇒[ _ ] _) = nothing
isBaseType? (μ _) = nothing
isBaseType? (ν _ _) = nothing

-- | Decide whether a type is CONCRETE / FFI-representable (Plan 0.58): a base
-- type, or a first-order function pointer (base argument, base result: the
-- ABI returns a register value, never a closure — plan 0.105).
isConcrete? : (A : Type) → Maybe (IsConcrete A)
isConcrete? (A ⇒[ _ ] B) with isBaseType? A | isBaseType? B
... | just bA | just bB = just (con-fun bA bB)
{-# CATCHALL #-}
... | _       | _       = nothing
{-# CATCHALL #-}
isConcrete? A with isBaseType? A
... | just bA = just (con-base bA)
... | nothing = nothing

-- | Completeness: a genuine `Base ∅ₖ`/`IsConcrete` witness means the decider
-- returns `just` (Plan 0.58 — needed to reduce the elaborator's new
-- concreteness-guarded branches in Completeness/fallback proofs).
isBaseType?-complete : ∀ {A} → Base ∅ₖ A → ∃[ b ] isBaseType? A ≡ just b
isBaseType?-complete b-Unit   = b-Unit , refl
isBaseType?-complete b-Void   = b-Void , refl
isBaseType?-complete b-Int    = b-Int , refl
isBaseType?-complete b-Float  = b-Float , refl
isBaseType?-complete (b-* bA bB)
  with isBaseType?-complete bA | isBaseType?-complete bB
... | (a , eqA) | (b , eqB) rewrite eqA | eqB = b-* a b , refl
isBaseType?-complete (b-+ bA bB)
  with isBaseType?-complete bA | isBaseType?-complete bB
... | (a , eqA) | (b , eqB) rewrite eqA | eqB = b-+ a b , refl

isConcrete?-complete : ∀ {A} → IsConcrete A → ∃[ c ] isConcrete? A ≡ just c
isConcrete?-complete (con-base b-Unit)   = con-base b-Unit , refl
isConcrete?-complete (con-base b-Void)   = con-base b-Void , refl
isConcrete?-complete (con-base b-Int)    = con-base b-Int , refl
isConcrete?-complete (con-base b-Float)  = con-base b-Float , refl
isConcrete?-complete (con-base (b-* bA bB))
  with isBaseType?-complete (b-* bA bB)
... | (b , eq) rewrite eq = con-base b , refl
isConcrete?-complete (con-base (b-+ bA bB))
  with isBaseType?-complete (b-+ bA bB)
... | (b , eq) rewrite eq = con-base b , refl
isConcrete?-complete (con-fun bA bB)
  with isBaseType?-complete bA | isBaseType?-complete bB
... | (b , eqB) | (c , eqC) rewrite eqB | eqC = con-fun b c , refl

-- | Decide whether a functor is well-formed (K positions are base types).
wellFormedF? : (F : Fun 0) → Maybe (WFFun ∅ₖ F)
wellFormedF? (K A) with isBaseType? A
... | just bA = just (wf-K bA)
... | nothing = nothing
wellFormedF? Id = just wf-Id
wellFormedF? (F ⊕ G) with wellFormedF? F | wellFormedF? G
... | just wF | just wG = just (wf-⊕ wF wG)
{-# CATCHALL #-}
... | _       | _       = nothing
wellFormedF? (F ⊗ G) with wellFormedF? F | wellFormedF? G
... | just wF | just wG = just (wf-⊗ wF wG)
{-# CATCHALL #-}
... | _       | _       = nothing

------------------------------------------------------------------------
-- Base types over type variables of kinds `Δ` (a polymorphic body): a
-- variable is base when its kind is.
------------------------------------------------------------------------

base-var? : ∀ {m} (Δ : KCtx m) (i : Fin m) (k : Kind) → Δ i ≡ k → Maybe (Base Δ (var i))
base-var? Δ i base e = just (b-var e)
base-var? Δ i any  _ = nothing

base? : ∀ {m} (Δ : KCtx m) (A : Ty m) → Maybe (Base Δ A)
base? Δ (var i) = base-var? Δ i (Δ i) refl
base? Δ Unit   = just b-Unit
base? Δ Void   = just b-Void
base? Δ Int    = just b-Int
base? Δ Float  = just b-Float
base? Δ (A * B) with base? Δ A | base? Δ B
... | just bA | just bB = just (b-* bA bB)
{-# CATCHALL #-}
... | _       | _       = nothing
base? Δ (A + B) with base? Δ A | base? Δ B
... | just bA | just bB = just (b-+ bA bB)
{-# CATCHALL #-}
... | _       | _       = nothing
base? Δ (_ ⇒[ _ ] _) = nothing
base? Δ (μ _) = nothing
base? Δ (ν _ _) = nothing

base?-complete : ∀ {m} {Δ : KCtx m} {A} → Base Δ A → ∃[ b ] base? Δ A ≡ just b
base?-complete {Δ = Δ} (b-var {i} e) = go (Δ i) refl e
  where
    go : ∀ k (e′ : Δ i ≡ k) → k ≡ base → ∃[ b ] base-var? Δ i k e′ ≡ just b
    go base e′ refl = b-var e′ , refl
base?-complete b-Unit   = b-Unit , refl
base?-complete b-Void   = b-Void , refl
base?-complete b-Int    = b-Int , refl
base?-complete b-Float  = b-Float , refl
base?-complete (b-* bA bB)
  with base?-complete bA | base?-complete bB
... | (a , eqA) | (b , eqB) rewrite eqA | eqB = b-* a b , refl
base?-complete (b-+ bA bB)
  with base?-complete bA | base?-complete bB
... | (a , eqA) | (b , eqB) rewrite eqA | eqB = b-+ a b , refl

-- Well-formed functors over type variables of kinds `Δ`.
wfFun? : ∀ {m} (Δ : KCtx m) (F : Fun m) → Maybe (WFFun Δ F)
wfFun? Δ (K A) with base? Δ A
... | just b  = just (wf-K b)
... | nothing = nothing
wfFun? Δ Id = just wf-Id
wfFun? Δ (F ⊕ G) with wfFun? Δ F | wfFun? Δ G
... | just f | just g = just (wf-⊕ f g)
{-# CATCHALL #-}
... | _      | _      = nothing
wfFun? Δ (F ⊗ G) with wfFun? Δ F | wfFun? Δ G
... | just f | just g = just (wf-⊗ f g)
{-# CATCHALL #-}
... | _      | _      = nothing
