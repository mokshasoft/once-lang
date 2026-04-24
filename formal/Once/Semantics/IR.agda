-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Semantics.IR
--
-- IR-level denotational semantics for Once.
-- Interprets types as Agda Sets and IR morphisms as Agda functions.
--
-- Uses ℤ for Int (mathematical integers for arithmetic proofs).
-- Functions are plain Agda functions (not Closure records).
--
-- For machine-level semantics (with ℕ), use Once.Semantics.Machine.
------------------------------------------------------------------------

module Once.Semantics.IR where

open import Data.Integer using (ℤ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)

open import Once.Type
open import Once.CCC.IR

-- Instantiate Core with ℤ for integers and re-export
open import Once.Semantics.Core ℤ public

------------------------------------------------------------------------
-- Primitive Semantics (Parameterized)
------------------------------------------------------------------------

-- SigOpSem record removed (plan 0.2.4.1 Phase A).
-- The semantic function for each signature operation now lives on
-- its `SigOpInfo` (the `semI` field for frontend semantics), so
-- eval is direct: `eval (SigOp si) x = semI si x`.
-- No external parameter threads through evaluation.

------------------------------------------------------------------------
-- Evaluation of IR morphisms
------------------------------------------------------------------------

-- | Evaluation of IR morphisms.
--
-- Maps IR morphisms to Agda functions. The morphism mapping of a
-- functor from Once's CCC to Set.
--
-- After plan 0.2.4.1 Phase A: `SigOp` carries a `SigOpInfo` that
-- embeds the semantic function, so evaluation is direct — no more
-- `SigOpSem` parameter or `defaultEvalSigOp` postulate.
--
eval′ : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧

-- Category structure
eval′ id x              = x
eval′ (g ∘ f) x         = eval′ g (eval′ f x)

-- Products (AllocMode ignored in semantics)
eval′ fst (a , b)       = a
eval′ snd (a , b)       = b
eval′ (⟨ f , g ⟩ _) x   = (eval′ f x , eval′ g x)

-- Coproducts (AllocMode ignored in semantics)
eval′ (inl _) a         = inj₁ a
eval′ (inr _) b         = inj₂ b
eval′ (case f g) (inj₁ a) = eval′ f a
eval′ (case f g) (inj₂ b) = eval′ g b

-- Terminal
eval′ terminal _        = tt

-- Initial
eval′ initial ()

-- Exponential (plain functions, no Closure record)
-- curry f : IR A (B ⇒ C) creates a function capturing the input
eval′ (curry f _) a     = λ b → eval′ f (a , b)
-- apply : IR ((A ⇒ B) * A) B extracts and applies the function
eval′ apply (f , a)     = f a

-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana.

-- Recursion schemes (OCP-0003: total/productive)
eval′ (In {F} _ _) x = sem-In F (coerce-functor F (μ-type F) x)
eval′ (out-μ {F} wf) x = coerce-functor⁻¹ F (μ-type F) (sem-Out wf x)
eval′ (Cata {F} wf alg) x =
  sem-cata wf (λ fa → eval′ alg (coerce-functor⁻¹ F _ fa)) x
eval′ (Para {F} wf alg) x =
  sem-para wf (λ fx → eval′ alg (coerce-functor⁻¹ F _ fx)) x
eval′ (Out {F} wf) x = coerce-functor⁻¹ F (ν-type F) (sem-CoOut wf x)
eval′ (in-ν {F} _ _) x = sem-CoIn F (coerce-functor F (ν-type F) x)
eval′ (Ana {F} wf {A} coalg) x =
  sem-ana F (λ a → coerce-functor F A (eval′ coalg a)) x
eval′ (Hylo {F} {G} wfF wfG alg coalg) x =
  let alg-set = λ fb → eval′ alg (coerce-functor⁻¹ F _ fb)
      coalg-set = λ μg → coerce-functor F (μ-type G) (eval′ coalg μg)
  in sem-hylo F G wfF wfG alg-set coalg-set x
eval′ (Fuse {F} {G} wfF wfG alg transform) x =
  sem-fuse F G wfF wfG
    (λ fb → eval′ alg (coerce-functor⁻¹ F _ fb))
    (λ gx → coerce-functor F _ (eval′ transform (coerce-functor⁻¹ G _ gx)))
    x

-- Effect lifting (D032): arr is the identity at runtime; semantics
-- is too.
eval′ arr f             = f

-- Memory management (no-op in semantics)
eval′ (free-heap _) x   = x

-- Signature operations: the `SigOpInfo` carries the semantic
-- function (`semI` for the frontend-level semantics used here).
eval′ (SigOp si) x      = semI si x

------------------------------------------------------------------------
-- OCP-0003: Recursion Scheme Semantics
------------------------------------------------------------------------
--
-- With OCP-0003, recursive types use polynomial functors:
--
--   μ-type F : inductive/finite data (consumed via Cata)
--   ν-type F : coinductive/infinite codata (produced via Ana)
--
-- where F : Functor is a strictly positive polynomial functor.
-- This provides proper fixed point semantics via SPF.agda.
--
-- Example: Nat = μ-type (K Unit ⊕ Id) satisfies:
--   ⟦ Nat ⟧ = ⟦μ⟧ (K Unit ⊕ Id) ≅ ⊤ ⊎ ⟦ Nat ⟧
--
------------------------------------------------------------------------