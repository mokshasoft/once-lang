-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the hand-written `⊢` pieces the generated rows (`JudgeRowsGen`) use: the payload-field views.
--
-- A rule whose conclusion TYPE is a constructor pattern is a NESTED CASE
-- on the convoy's type (`Lib/SynPat`): the pattern's variables are the
-- type's payload, the case's convoy is `(Γ , term payload)`
-- (`JudgeTmIx`).  A computed conclusion type Fords (`⌜Id⌝` field).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeRowsTm where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; Lt; lt-z; lt-s; []ᵈ; _∷ᵈ_; v₁; _,ₚ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢recFst; ⊢recSnd; ⊢atDepthSK; ⊢natFst )
open import DirectedHoTT.Lib.NatCode using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Examples.Knot.JudgeCase
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( rows; ⊢rows )
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeTmIx
open import DirectedHoTT.Examples.Knot.JudgeFib using ( RowOK; f0; r1 )
open import DirectedHoTT.Examples.Knot.Lookup using ( toTy; hereTy; I∋; ⊢I∋; I∋-sub; ix∋; ⊢ix∋; D∋; ⊢D∋ )
open import DirectedHoTT.Examples.Knot.LookupCon using ( D∋-sub )
open import DirectedHoTT.Lib.NatCode using ( toI; fromI )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-⌜IMu⌝ⁱ; ⟶*-⌜Fin⌝ )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0; ⊢sub0; sub0-sub )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )

private
  variable
    Δ Θ : Cx

-- a TERM payload's field (index `(1 , j)`), its depth read off
g0 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
     Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) ((tag 1) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ K s (nsucs k j)
g0 {j = j} s k sh dp = ⊢atDepthSK {sg = KSig} {a = tag 1} {j = j} {s = s} {k = k} (⊢recFst {s = s} {k = k} {sh = sh} dp)

-- a variable payload's field, at the depth
⊢varOf : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} → Ξ ⊢ p ∷ PayV sh-kvar ((tag 1) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ Fin j
⊢varOf {j = j} dp = ⊢conv (⊢fst dp) (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-⌜Fin⌝ (step (βsnd (tag 1) j) done)))) (credᵀ El-⌜Fin⌝))
