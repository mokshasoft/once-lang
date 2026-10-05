-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ `Examples/SigCore`'s SUBSTITUTION AT THE KNOT,
-- against the kernel's own `subTm`, through the Knot's quotation.
--
-- ★ UNDER A BINDER too (`sub-knot-bind`): there the kit's `WK` is itself a
--   `#trav`, nested inside the traversal.  Negative controls are decided
--   inequalities at the end.
-- ★ RUN BY THE ENVIRONMENT EVALUATOR (`Algorithm/NbE`, PLAN-EVAL E0).
--   By the substitution evaluator these OOMed the type checker even at fuel
--   40 (they were parked in `Negative/`); by NbE the module checks in ~10 s.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.NbESigSubKnotTest where
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
open import DirectedHoTT.Examples.SigMeth using ( #trav; #rVF; #rWK; #rV0; #rNλ; #rNK; #sVF; #sWK; #sV0; #sN )
open import DirectedHoTT.Examples.SigCoreEval
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Algorithm.DecEq using ( _≟Tm_; yes; no )

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
sub-knot : nfᴺ (subKn (quoteTm (R.nzero {ε})) (quoteTm tS)) ≡ quoteTm (R.subTm (Ty.single R.nzero) tS)
sub-knot = refl

private
  -- under a BINDER: `λ. x₁ x₀` at depth 1 (the kit's WK is a nested traversal)
  tB : R.RTm (ε R.∙)
  tB = R.lam (R.app (R.var (vs vz)) (R.var vz))

sub-knot-bind : nfᴺ (subKn (quoteTm (R.nsuc (R.nzero {ε}))) (quoteTm tB)) ≡ quoteTm (R.subTm (Ty.single (R.nsuc R.nzero)) tB)
sub-knot-bind = refl

------------------------------------------------------------------------
-- ★ NEGATIVE CONTROLS, as decided inequalities (see NbESigTravTest)
------------------------------------------------------------------------

private
  differs : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ → Bool
  differs t u with t ≟Tm u
  ... | yes _ = false
  ... | no  _ = true

sub-knot✗ : differs (nfᴺ (subKn (quoteTm (R.nzero {ε})) (quoteTm tS))) (quoteTm (R.subTm (Ty.single (R.nsuc R.nzero)) tS)) ≡ true
sub-knot✗ = refl

sub-knot-bind✗ : differs (nfᴺ (subKn (quoteTm (R.nsuc (R.nzero {ε}))) (quoteTm tB))) (quoteTm (R.subTm (Ty.single R.nzero) tB)) ≡ true
sub-knot-bind✗ = refl
