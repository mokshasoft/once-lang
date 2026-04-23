-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Eval
--
-- Semantic evaluation of IR terms.
--
-- Provides:
--   - SigOpSem: Record for primitive semantics provider
--   - eval: Evaluator for IR parameterized by SigOpSem
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
         sem-In; sem-Out; sem-cata; sem-para; sem-CoOut; sem-CoIn; sem-ana; sem-hylo;
         -- OCP-0003: Structured fusion (correct by construction)
         sem-fuse;
         coerce-functor; coerce-functor⁻¹)

-- Re-export ⟦_⟧ for convenience
open import Once.Semantics.Machine public using (⟦_⟧)

------------------------------------------------------------------------
-- Primitive Semantics Provider
--
-- Any module that wants to evaluate IR must provide semantics for
-- primitive operations via this record.
------------------------------------------------------------------------

record SigOpSem : Set₁ where
  field
    evalSigOp : ∀ {A B} → String → ⟦ A ⟧ → ⟦ B ⟧

open SigOpSem public

------------------------------------------------------------------------
-- Semantic Evaluation
--
-- Evaluates IR terms given a primitive semantics provider.
-- AllocMode is ignored in semantics (it's a compilation concern).
------------------------------------------------------------------------

eval : SigOpSem → ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
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
eval ps (SigOp name) x = evalSigOp ps name x
-- OCP-0003: Recursion scheme evaluation (WellFormedF proofs from IR constructors)
-- In: wrap value into μ-type (initial algebra constructor)
eval ps (In {F} _ _) x = sem-In F (coerce-functor F (μ-type F) x)
-- out-μ: destruct μ-type (inverse of In, by Lambek's Lemma)
eval ps (out-μ {F} wf) x = coerce-functor⁻¹ F (μ-type F) (sem-Out wf x)
-- Cata: fold with algebra over μ-type
eval ps (Cata {F} wf alg) x = sem-cata wf (λ fa → eval ps alg (coerce-functor⁻¹ F _ fa)) x
-- Para: paramorphism - fold with access to original substructure
eval ps (Para {F} wf alg) x = sem-para wf (λ fx → eval ps alg (coerce-functor⁻¹ F _ fx)) x
-- Out: observe ν-type (final coalgebra destructor)
eval ps (Out {F} wf) x = coerce-functor⁻¹ F (ν-type F) (sem-CoOut wf x)
-- in-ν: construct ν-type (inverse of Out, by Lambek's Lemma)
eval ps (in-ν {F} _ _) x = sem-CoIn F (coerce-functor F (ν-type F) x)
-- Ana: unfold with coalgebra to build ν-type (OCP-0003 productivity)
-- Productivity follows from IR totality - no GuardedT needed.
eval ps (Ana {F} wf coalg) x = sem-ana F (λ a → coerce-functor F _ (eval ps coalg a)) x
-- Guard/Unguard removed: productivity follows from IR totality
-- Hylo: fused cata ∘ ana (OCP-0003: based on Fuse, structurally terminating)
-- Termination is guaranteed by requiring μG as input - no contract needed.
eval ps (Hylo {F} {G} wfF wfG alg coalg) x =
  sem-hylo F G wfF wfG
    (λ fb → eval ps alg (coerce-functor⁻¹ F _ fb))
    (λ μg → coerce-functor F (μ-type G) (eval ps coalg μg))
    x
-- Fuse: μ-anchored fusion (OCP-0003: correct by construction)
-- Termination is structural on μG - no contract needed, no escape hatch.
eval ps (Fuse {F} {G} wfF wfG alg transform) x =
  sem-fuse F G wfF wfG
    (λ fb → eval ps alg (coerce-functor⁻¹ F _ fb))
    (λ gx → coerce-functor F _ (eval ps transform (coerce-functor⁻¹ G _ gx)))
    x