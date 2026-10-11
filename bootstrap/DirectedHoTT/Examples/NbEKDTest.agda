-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ the WHOLE Knot description by the environment
-- evaluator: the core decoder at `⌜KSig⌝` has the Lib's `KD` normal form
-- (52 constructors, both sorts).  By `normLazy` this OOMed the type
-- checker (4.7 min at the cgroup cap, 2026-10-05; `SigCoreTest` tests it
-- per constructor instead).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.NbEKDTest where
open import normalizer.Syntax.Types using ( _≡_; refl; sym )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( ε; ∅ᴷ )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Examples.Sig0 using ( wf₀; ok₀ )
-- the Lib's terms carry no references: read at the empty signature
open import DirectedHoTT.Lib.NatNum ∅ᴷ 0 using ( num )
open import DirectedHoTT.Lib.Sugar ∅ᴷ 0 ok₀ using ( tag )
open import DirectedHoTT.Lib.Syn ∅ᴷ 0 ok₀ using ( SD )
open import DirectedHoTT.Algorithm.DecEq using ( _≟Tm_; yes; no )
open import DirectedHoTT.Examples.Knot.Sig ∅ᴷ wf₀ using ( KD )
open import DirectedHoTT.Examples.SigCore
open import DirectedHoTT.Examples.SigCoreEval

-- (`KD` is the opaque `SD KSig`: evaluating it needs its constructors)
opaque
  unfolding SD
  kd-whole : nfᴺ {ε} (⟪ #SD ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ [])) ≡ nfᴺ KD
  kd-whole = refl

-- negative control: the λ-calculus's description is not the Knot's
private
  differs : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ → Bool
  differs t u with t ≟Tm u
  ... | yes _ = false
  ... | no  _ = true

kd-whole✗ : differs (nfᴺ {ε} (⟪ #SD ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ []))) (nfᴺ (⟪ #SD ⟫ ⋆ (num 1 ∷ tag 0 ∷ ⟪ #lamΣ ⟫ ∷ []))) ≡ true
kd-whole✗ = refl

------------------------------------------------------------------------
-- ★ CERTIFIED: the core decoder at ⌜KSig⌝ is CONVERTIBLE with the Lib's
--   whole `KD` — by the evaluator's soundness (`Algorithm/NbESound`):
--   t ≅ nbe t ≡ nbe u ≅ u.  (The substitution evaluator OOMed computing
--   either normal form.)
------------------------------------------------------------------------

open import DirectedHoTT.Spec.Signature using ( kernel )
-- at the signature `SigCoreEval` evaluates in (SigMeth extends SigCore)
import DirectedHoTT.Examples.SigMeth as M
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Algorithm.NbETable using ( mkTbl; mkTbl-ok )
open import DirectedHoTT.Spec.Typing (kernel M.S) (Defs.size (kernel M.S)) using ( _≅_; ctrn; csym )
open import DirectedHoTT.Algorithm.NbESound (kernel M.S) (mkTbl (kernel M.S)) (mkTbl-ok (kernel M.S)) using ( nbe-sound )
open import normalizer.Syntax.Types using ( subst )

-- generic in the terms: `nbe-sound`'s evaluator and `nfᴺ` are two
--   instances of `Algorithm/NbE`, matched here on VARIABLES (one unfolding
--   each); joined at the concrete `KD`, Agda evaluated both sides (OOM)
byNbE : {Γ : R.Cx} (t u : R.RTm Γ) → nfᴺ t ≡ nfᴺ u → t ≅ u
byNbE t u e = ctrn (nbe-sound 100000 t) (subst (λ z → z ≅ u) (sym e) (csym (nbe-sound 100000 u)))

kd-conv : (⟪ #SD ⟫ ⋆ (num 2 ∷ tag 1 ∷ ⟪ #KΣ ⟫ ∷ [])) ≅ KD {ε}
kd-conv = byNbE _ KD kd-whole
