-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Eval
--
-- Semantic evaluation of IR terms.
--
-- Provides:
--   - PrimSem: Record for primitive semantics provider
--   - eval: Evaluator for IR parameterized by PrimSem
------------------------------------------------------------------------

module Once.CCC.Eval where

open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)

open import Once.Type
open import Once.CCC.IR

-- Import semantic interpretation of types from Once.Sem
open import Once.Semantics.Machine
  using (⟦_⟧; sem-pair; sem-fst; sem-snd; sem-inl; sem-inr; sem-case;
         -- OCP-0003: fold/unfold removed. Use recursion scheme semantics:
         sem-In; sem-cata; sem-CoOut;
         -- OCP-0003: Guarded operations for productive corecursion:
         sem-unguard; sem-guard; sem-ana-guarded; sem-hylo-guarded;
         coerce-functor; coerce-functor⁻¹)

-- Re-export ⟦_⟧ for convenience
open import Once.Semantics.Machine public using (⟦_⟧)

------------------------------------------------------------------------
-- Primitive Semantics Provider
--
-- Any module that wants to evaluate IR must provide semantics for
-- primitive operations via this record.
------------------------------------------------------------------------

record PrimSem : Set₁ where
  field
    evalPrim : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

open PrimSem public

------------------------------------------------------------------------
-- Semantic Evaluation
--
-- Evaluates IR terms given a primitive semantics provider.
-- AllocMode is ignored in semantics (it's a compilation concern).
------------------------------------------------------------------------

eval : PrimSem → ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
eval ps id x = x
eval ps (g ∘ f) x = eval ps g (eval ps f x)
eval ps (⟨ f , g ⟩ _) x = sem-pair (eval ps f x) (eval ps g x)
eval ps fst x = sem-fst x
eval ps snd x = sem-snd x
eval ps (inl _) x = sem-inl x
eval ps (inr _) x = sem-inr x
eval ps (case f g) x = sem-case (eval ps f) (eval ps g) x
eval ps terminal x = tt
eval ps initial ()
eval ps (curry f _) x = λ y → eval ps f (sem-pair x y)
eval ps apply (closure , arg) = closure arg
eval ps arr f = f
-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.
eval ps (free-heap _) x = x
eval ps (Prim name) x = evalPrim ps name x
-- OCP-0003: Recursion scheme evaluation (WellFormedF proofs from IR constructors)
-- In: wrap value into μ-type (initial algebra constructor)
eval ps (In {F} _ _) x = sem-In F (coerce-functor F (μ-type F) x)
-- Cata: fold with algebra over μ-type
eval ps (Cata {F} wf alg) x = sem-cata wf (λ fa → eval ps alg (coerce-functor⁻¹ F _ fa)) x
-- Out: observe ν-type (final coalgebra destructor)
eval ps (Out {F} wf) x = coerce-functor⁻¹ F (ν-type F) (sem-CoOut wf x)
-- Ana: unfold with GUARDED coalgebra to build ν-type (OCP-0003 productivity)
-- The coalgebra produces GuardedT F A, ensuring productivity by construction.
eval ps (Ana {F} wf coalg) x = sem-ana-guarded wf (λ a → eval ps coalg a) x
-- Unguard: extract functor value from guarded value
eval ps (Unguard {F} wf) x = coerce-functor⁻¹ F _ (sem-unguard wf x)
-- Guard: wrap functor value as guarded value
eval ps (Guard {F} _ {A}) x = sem-guard F (coerce-functor F A x)
-- Hylo: fused cata ∘ ana with GUARDED coalgebra (OCP-0003 productivity)
eval ps (Hylo {F} wf alg coalg) x =
  sem-hylo-guarded wf
    (λ fb → eval ps alg (coerce-functor⁻¹ F _ fb))
    (λ a → eval ps coalg a)
    x