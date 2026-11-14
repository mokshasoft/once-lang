-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.StepCov — plan 0.146 B1.5: EVERY IMAGE STEP IS COVERED by the
-- word layer's step theorem (`StepKinds.CoveredC` of its code); a primitive
-- an op (D426) or a local one, by its term's head. Its split on a step lives
-- here, in a module of its own.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.StepCov
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Machine fmt ans bw using (Sh)
open import Once.LinCore.Image fmt ans bw using (Codeᴵ)
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.StepKinds fmt ans bw using (CoveredC; PrimCov; pc-op; pc-loc)

-- a primitive: an op, or not
prim-cov : ∀ {Γ A B} (g : LTm Γ A B) → PrimCov g
prim-cov (lop s) = pc-op
prim-cov lid = pc-loc tt
prim-cov (_ ∘l _) = pc-loc tt
prim-cov (_ ⊗l _) = pc-loc tt
prim-cov ρl = pc-loc tt
prim-cov ρl⁻ = pc-loc tt
prim-cov lul = pc-loc tt
prim-cov lul⁻ = pc-loc tt
prim-cov lassoc = pc-loc tt
prim-cov lassoc⁻ = pc-loc tt
prim-cov lswap = pc-loc tt
prim-cov dup = pc-loc tt
prim-cov drop = pc-loc tt
prim-cov linl = pc-loc tt
prim-cov linr = pc-loc tt
prim-cov (lcase _ _) = pc-loc tt
prim-cov lzero = pc-loc tt
prim-cov lIn = pc-loc tt
prim-cov lOutμ = pc-loc tt
prim-cov (lcata _ _) = pc-loc tt
prim-cov (lclo _ _) = pc-loc tt
prim-cov (lapp _) = pc-loc tt
prim-cov (lend _) = pc-loc tt
prim-cov (blift _) = pc-loc tt
prim-cov bcopy = pc-loc tt
prim-cov (llam _ _) = pc-loc tt
prim-cov (llamω _ _) = pc-loc tt
prim-cov lev = pc-loc tt
prim-cov lunf = pc-loc tt
prim-cov lout = pc-loc tt
prim-cov (lconst _) = pc-loc tt
prim-cov (liter _ _) = pc-loc tt

step-covered : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
             → StepI c r m n t c′ r′ m′ n′ → CoveredC c
step-covered (i-prim {g = g} _) = prim-cov g
step-covered (i-opend _) = pc-op
step-covered i-unpair = tt
step-covered i-pair = tt
step-covered i-swap = tt
step-covered i-unit = tt
step-covered i-untag = tt
step-covered i-untag₁ = tt
step-covered i-tag₁ = tt
step-covered i-case₁ = tt
step-covered i-case₂ = tt
step-covered i-elend = tt
step-covered i-eunlend = tt
step-covered i-elift = tt
step-covered i-epop = tt
step-covered i-call = tt
step-covered i-ret = tt
step-covered i-reti = tt
step-covered i-loop = tt
step-covered i-icall = tt
step-covered i-iobs = tt
step-covered i-cfree = tt
step-covered i-nfree = tt
step-covered i-open1 = tt
step-covered i-nopen = tt
step-covered i-fopen = tt
step-covered i-fopenν = tt
step-covered (i-efst _) = tt
step-covered (i-esnd _) = tt
step-covered (i-eout _) = tt
step-covered (i-eoutq _) = tt
step-covered (i-ecase₁ _) = tt
step-covered (i-ecase₂ _) = tt
step-covered (i-eapp _) = tt
step-covered (i-eword _) = tt
step-covered (i-icallω _) = tt
step-covered (i-ccopy _) = tt
step-covered (i-ncopy _) = tt
step-covered (i-openω _) = tt
step-covered (i-copen _) = tt
step-covered (i-copenν _) = tt
step-covered (i-reclose _) = tt
step-covered (i-recloseν _) = tt
