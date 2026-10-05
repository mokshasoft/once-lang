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
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( ε )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.Sugar using ( tag )
open import DirectedHoTT.Algorithm.DecEq using ( _≟Tm_; yes; no )
open import DirectedHoTT.Examples.Knot.Sig using ( KD )
open import DirectedHoTT.Examples.SigCore
open import DirectedHoTT.Examples.SigCoreEval

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
