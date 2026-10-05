-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the typing judgement's ROW MACHINERY at the Knot: the
-- fibred family's index and convoy before any row (`Fib₀`), a payload's
-- fields at sort 0, and the empty row's typing.  Every `⊢ty`/`⊢` row is
-- generated (`JudgeRowsGen`, `tools/gen-judge.py`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeFib where


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Lib.NatCode using ( fromI )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimⁱ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-snd; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; Lt; lt-z; lt-s; subC; selF-sub; []ᵈ; _∷ᵈ_; _,ₚ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; payV-red; ⊢recFst; ⊢recSnd; ⊢atDepthSK )
open import DirectedHoTT.Lib.NatCode using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Ren using ( wk; wk-sub; ⊢wkS )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Sorted using ( ⊢sortOf )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row; module Fib; ⊢conRow )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( ⌜Ctx⌝; rows; ⊢rows )

open import DirectedHoTT.Lib.SynFib using ( module Fib₀ )
open import DirectedHoTT.Examples.Knot.JudgeIx

private
  variable
    Δ Θ : Cx

open Fib₀ KOK JT JT-sub ⊢JT CT CT-sub ⊢CT public

-- a payload's fields at sort 0, the shape EXPLICIT (`PayV` computes on it)
f0 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
     Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) ((tag 0) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ K s (nsucs k j)
f0 {j = j} s k sh dp = ⊢atDepthSK {sg = KSig} {a = tag 0} {j = j} {s = s} {k = k} (⊢recFst {s = s} {k = k} {sh = sh} dp)

r1 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
     Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) ((tag 0) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ snd p ∷ PayV sh ((tag 0) ,ₚ j) (SI 2) (SD KSig)
r1 s k sh dp = ⊢recSnd {s = s} {k = k} {sh = sh} dp

okNone : (s : ℕ) (sh : Shape) → RowOK s sh rNone
okNone s sh dj dp dc = ⊢rows {I = JT} {Cs = []} ⊢JT []ᵈ
