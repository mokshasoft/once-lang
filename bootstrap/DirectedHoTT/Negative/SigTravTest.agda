-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ `Examples/SigCore`'s TRAVERSAL COMPUTES:
-- renaming and substitution, on the λ-calculus and — against the kernel's
-- own `renTm`/`subTm`, through the Knot's quotation — at the Knot.  Each
-- `refl` was checked against a deliberately wrong right-hand side.
------------------------------------------------------------------------

-- ⚠ PARKED (2026-10-05): with the Lib-form decoder these evaluations OOM
--   the type checker (cgroup cap) even at fuel 40 — Agda's evaluation of an
--   object-level interpreter shares no work across β's `subTm` towers.  They
--   PASSED with the select-then-map decoder (commit cb30cfb1a); see
--   PLAN-BIDI "S7b step 3", the evaluation question.

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.SigTravTest where
open import normalizer.Syntax.Types using ( _≡_; refl; _×_; _,_ )
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

------------------------------------------------------------------------
-- ★ RENAMING (the traversal at the renaming kit) COMPUTES.
------------------------------------------------------------------------

private
  -- the λ-calculus's nodes
  varK : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ
  varK x = R.con (R.pair R.fzero (R.pair x R.unit))
  lamK : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ
  lamK b = R.con (R.pair (R.fsuc R.fzero) (R.pair b R.unit))
  appK : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ → R.RTm Γ
  appK f a = R.con (R.pair (R.fsuc (R.fsuc R.fzero)) (R.pair f (R.pair a R.unit)))

  -- weakening `λ x. fsuc x`, depth d → d + 1, sort s
  wkλ : ℕ → R.RTm ε → R.RTm ε
  wkλ d t = ⟪ #trav ⟫ ⋆ (num 1 ∷ tag 0 ∷ ⟪ #lamΣ ⟫ ∷ ⟪ #rVF ⟫ ∷ ⟪ #rWK ⟫ ∷ ⟪ #rV0 ⟫ ∷ ⟪ #rNλ ⟫
                         ∷ tag 0 ∷ num d ∷ t ∷ num (suc d) ∷ R.lam (R.fsuc (R.var vz)) ∷ [])
  wkKn : ℕ → ℕ → R.RTm ε → R.RTm ε
  wkKn s d t = ⟪ #trav ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ ⟪ #rVF ⟫ ∷ ⟪ #rWK ⟫ ∷ ⟪ #rV0 ⟫ ∷ ⟪ #rNK ⟫
                            ∷ tag s ∷ num d ∷ t ∷ num (suc d) ∷ R.lam (R.fsuc (R.var vz)) ∷ [])

  -- the kernel term `λ. (x₀ x₁) (ref 0 0)` at depth 1
  tK : R.RTm (ε R.∙)
  tK = R.lam (R.app (R.app (R.var vz) (R.var (vs vz))) (R.ref 0 R.nzero))

-- a free variable moves, the bound one stays (the environment is lifted)
ren-λ : nfOf (wkλ 1 (lamK (appK (varK R.fzero) (varK (R.fsuc R.fzero)))))
      ≡ lamK (appK (varK R.fzero) (varK (R.fsuc (R.fsuc R.fzero))))
ren-λ = refl

-- ★★ at the Knot, AGAINST THE KERNEL: renaming the quotation IS quoting
--   the renaming (a binder, a crossing variable, a ref's nat and cls)
ren-knot : nfOf (wkKn 1 1 (quoteTm tK)) ≡ quoteTm (R.renTm vs tK)
ren-knot = refl

------------------------------------------------------------------------
-- ★ SUBSTITUTION (the traversal at the substitution kit) COMPUTES.
------------------------------------------------------------------------

private
  -- the substitution kit at a signature (n , vs , sg , its renaming node)
  subKit : ℕ → ℕ → ℕ → ℕ → List (R.RTm ε)
  subKit n v sg rN = ⟪ #sVF ⟫ ⋆ (num n ∷ tag v ∷ ⟪ sg ⟫ ∷ [])
                   ∷ ⟪ #sWK ⟫ ⋆ (num n ∷ tag v ∷ ⟪ sg ⟫ ∷ ⟪ rN ⟫ ∷ [])
                   ∷ ⟪ #sV0 ⟫ ⋆ (num n ∷ tag v ∷ ⟪ sg ⟫ ∷ ⟪ rN ⟫ ∷ [])
                   ∷ ⟪ #sN ⟫ ⋆ (num n ∷ tag v ∷ ⟪ sg ⟫ ∷ []) ∷ []

  _++_ : {A : Set} → List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
  infixr 5 _++_

  -- the single substitution [u/x₀] at depth 1 → 0, as an environment
  single : R.RTm ε → R.RTm ε
  single u = R.lam (R.fcase (R.var vz) (R.renTm (λ ()) u) (R.fcase0 (R.var vz)))

  subλ : R.RTm ε → R.RTm ε → R.RTm ε
  subλ u t = ⟪ #trav ⟫ ⋆ ((num 1 ∷ tag 0 ∷ ⟪ #lamΣ ⟫ ∷ []) ++ subKit 1 0 #lamΣ #rNλ
                          ++ (tag 0 ∷ num 1 ∷ t ∷ num 0 ∷ single u ∷ []))

  subKn : R.RTm ε → R.RTm ε → R.RTm ε
  subKn u t = ⟪ #trav ⟫ ⋆ ((num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ []) ++ subKit 2 1 #KΣ #rNK
                          ++ (tag 1 ∷ num 1 ∷ t ∷ num 0 ∷ single u ∷ []))

  uλ : R.RTm ε                                -- λ x. x
  uλ = lamK (varK R.fzero)

-- (x₀ x₀)[u/x₀] = u u
sub-λ : nfOf (subλ uλ (appK (varK R.fzero) (varK R.fzero))) ≡ appK uλ uλ
sub-λ = refl

-- under a binder: λ.(x₀ x₁)[u] = λ.(x₀ u) — the bound variable stays,
--   the substituted term is weakened (the kit's WK: renaming)
sub-λ-bind : nfOf (subλ uλ (lamK (appK (varK R.fzero) (varK (R.fsuc R.fzero))))) ≡ lamK (appK (varK R.fzero) uλ)
sub-λ-bind = refl
