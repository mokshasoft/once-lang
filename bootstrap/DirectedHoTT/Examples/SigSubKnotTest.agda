-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ `Examples/SigCore`'s SUBSTITUTION AT THE KNOT,
-- against the kernel's own `subTm`, through the Knot's quotation.
--
-- ⚠ No binder here: under one, the kit's `WK` is itself a `#trav`, and the
--   test evaluator (`Algorithm/Eval`: applicative order, δ unfolded
--   eagerly) normalises the generic traversal inlined inside the generic
--   traversal — the type checker OOMs at the cgroup's cap (2026-10-05).
--   Substitution UNDER a binder is tested on the λ-calculus
--   (`Examples/SigTravTest.sub-λ-bind`), by the same signature-generic code.
--   Each `refl` was checked against a deliberately wrong right-hand side.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.SigSubKnotTest where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( ε; _∙; vz; vs )
import DirectedHoTT.Spec.Syntax as R
import DirectedHoTT.Spec.Typing as Ty
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.Sugar using ( tag )
open import DirectedHoTT.Examples.Knot.Terms using ( quoteTm )
open import DirectedHoTT.Examples.SigCore
open import DirectedHoTT.Examples.SigCoreEval

private
  -- the single substitution [u/x₀] at depth 1 → 0, as an environment
  single : R.RTm ε → R.RTm ε
  single u = R.lam (R.fcase (R.var vz) (R.renTm (λ ()) u) (R.fcase0 (R.var vz)))

  subKn : R.RTm ε → R.RTm ε → R.RTm ε
  subKn u t = ⟪ #trav ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫
                          ∷ ⟪ #sVF ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ [])
                          ∷ ⟪ #sWK ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ ⟪ #rNK ⟫ ∷ [])
                          ∷ ⟪ #sV0 ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ ⟪ #rNK ⟫ ∷ [])
                          ∷ ⟪ #sN ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ [])
                          ∷ tag 1 ∷ num 1 ∷ t ∷ num 0 ∷ single u ∷ [])

  -- `(x₀ x₀) (nsuc x₀)` at depth 1
  tS : R.RTm (ε R.∙)
  tS = R.app (R.app (R.var vz) (R.var vz)) (R.nsuc (R.var vz))

-- ★★ substituting into the quotation IS quoting the substitution
sub-knot : nfOf (subKn (quoteTm (R.nzero {ε})) (quoteTm tS)) ≡ quoteTm (R.subTm (Ty.single R.nzero) tS)
sub-knot = refl
