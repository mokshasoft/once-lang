-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Eval
--
-- Machine-level semantic evaluation of IR terms.
--
-- After plan 0.2.4.1 Phase A: `SigOp` carries a `SigOpInfo` that
-- embeds the semantic function. `eval` is direct — no more
-- `SigOpSem` parameter or external provider threading.
--
-- For the frontend/proof-level semantics (Int ≡ ℤ), see
-- `Once.Semantics.IR`.
------------------------------------------------------------------------

module Once.CCC.Eval where

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
-- Semantic Evaluation (machine-level)
--
-- Direct evaluator: every `SigOp` node carries its own `SigOpInfo`,
-- and `semM` is the machine-level semantic function. AllocMode is
-- ignored in semantics (it's a compilation concern).
------------------------------------------------------------------------

eval : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
eval id x = x
eval (g ∘ f) x = eval g (eval f x)
eval (⟨ f , g ⟩ _) x = sem-pair (eval f x) (eval g x)
eval fst x = sem-fst x
eval snd x = sem-snd x
eval (inl _) x = sem-inl x
eval (inr _) x = sem-inr x
eval (case f g) x = sem-case (eval f) (eval g) x
eval terminal x = tt
eval initial ()
eval (curry f _) x = λ y → eval f (sem-pair x y)
eval apply (closure , arg) = closure arg
eval arr f = f
eval (free-heap _) x = x
-- Signature operations: the `SigOpInfo` carries the machine-level
-- semantic function (`semM`).
eval (SigOp si) x = semM si x
-- Recursion schemes (OCP-0003)
eval (In {F} _ _) x = sem-In F (coerce-functor F (μ-type F) x)
eval (out-μ {F} wf) x = coerce-functor⁻¹ F (μ-type F) (sem-Out wf x)
eval (Cata {F} wf alg) x = sem-cata wf (λ fa → eval alg (coerce-functor⁻¹ F _ fa)) x
eval (Para {F} wf alg) x = sem-para wf (λ fx → eval alg (coerce-functor⁻¹ F _ fx)) x
eval (Out {F} wf) x = coerce-functor⁻¹ F (ν-type F) (sem-CoOut wf x)
eval (in-ν {F} _ _) x = sem-CoIn F (coerce-functor F (ν-type F) x)
eval (Ana {F} wf coalg) x = sem-ana F (λ a → coerce-functor F _ (eval coalg a)) x
eval (Hylo {F} {G} wfF wfG alg coalg) x =
  sem-hylo F G wfF wfG
    (λ fb → eval alg (coerce-functor⁻¹ F _ fb))
    (λ μg → coerce-functor F (μ-type G) (eval coalg μg))
    x
eval (Fuse {F} {G} wfF wfG alg transform) x =
  sem-fuse F G wfF wfG
    (λ fb → eval alg (coerce-functor⁻¹ F _ fb))
    (λ gx → coerce-functor F _ (eval transform (coerce-functor⁻¹ G _ gx)))
    x
