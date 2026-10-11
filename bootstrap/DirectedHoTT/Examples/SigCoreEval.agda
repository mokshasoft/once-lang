-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — evaluating `Examples/SigCore`'s entries: normal
-- forms (with the guard that they were REACHED), kernel references to the
-- entries, application to a list.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.SigCoreEval where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax using ( ε; _∙; vz; vs )
open import DirectedHoTT.Spec.Signature using ( Sig; kernel )
import DirectedHoTT.Spec.Syntax as R
open import normalizer.Syntax.Types using ( _,_ )
open import DirectedHoTT.Examples.SigMeth using ( S )
-- the evaluators at the signature's kernel, one instance each
open import DirectedHoTT.Algorithm.NbETable using ( mkTbl )
open import DirectedHoTT.Algorithm.Eval (kernel S) using ( eval; nfd; out )
open import DirectedHoTT.Algorithm.ConvLazy (kernel S) using ( normLazy )
open import DirectedHoTT.Algorithm.NbE (mkTbl (kernel S)) using ( nbe )

-- ★ the NORMAL-ORDER reduct (`Algorithm/ConvLazy.normLazy`): weak-head
--   first, so an unapplied generic definition is never normalised; a
--   reduct of the input (its chain is the evidence a `refl` test rests on)
nfOf : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ
nfOf t with normLazy 100000 t
... | u , _ = u

-- ★ the ENVIRONMENT evaluator's normal form (`Algorithm/NbE`, PLAN-EVAL
--   E0): untrusted — a test that uses it checks the evaluator as much as
--   the program, so each `refl` keeps its negative control
nfᴺ : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ
nfᴺ = nbe 100000

normal? : {Γ : R.Cx} → R.RTm Γ → Bool
normal? t with eval 100000 t
... | nfd _ _ _ = true
... | out _ _   = false

-- an entry, as a kernel reference
⟪_⟫ : {Γ : R.Cx} → ℕ → R.RTm Γ
⟪ d ⟫ = R.ref d

_⋆_ : {Γ : R.Cx} → R.RTm Γ → List (R.RTm Γ) → R.RTm Γ
f ⋆ []       = f
f ⋆ (x ∷ xs) = R.app f x ⋆ xs
infixl 9 _⋆_
