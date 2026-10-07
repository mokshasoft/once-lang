-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the typing judgement's ROW MACHINERY at the Knot: the
-- fibred family's index and convoy before any row (`Fib₀`), a payload's
-- fields at sort 0, and the empty row's typing.  Every `⊢ty`/`⊢` row is
-- generated (`JudgeRowsGen`, `tools/gen-judge.py`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.JudgeFib (𝒮 : Defs) (wf : WfK 𝒮) where




open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
import DirectedHoTT.Lib.NatCode 𝒮 (Defs.size 𝒮) as ᴵNatCode
open ᴵNatCode using ( fromI )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic 𝒮 using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimⁱ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-snd; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Cons; []; _∷_; conₗ; tag; Lt; lt-z; lt-s; subC; selF-sub; []ᵈ; _∷ᵈ_; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV; payV-red; ⊢recFst; ⊢recSnd; ⊢atDepthSK )
open ᴵNatCode using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( wk; wk-sub; ⊢wkS )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Sorted 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( ⊢sortOf )
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
import DirectedHoTT.Lib.SynFib 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) as ᴵSynFib
open ᴵSynFib using ( Row; module Fib; ⊢conRow )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( ⌜Ctx⌝; rows; ⊢rows )

open ᴵSynFib using ( module Fib₀ )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜TSig⌝; ⌜TSig⌝-sub; ⊢⌜TSig⌝ )

private
  variable
    Δ Θ : Cx

-- ★ PLAN-REF: the typing judgement is over the signature and the bound
open Fib₀ KOK ⌜TSig⌝ ⌜TSig⌝-sub ⊢⌜TSig⌝ JT JT-sub ⊢JT CT CT-sub ⊢CT public

-- a payload's fields at sort 0, the shape EXPLICIT (`PayV` computes on it)
f0 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
     Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) ((tag 0) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ fst p ∷ K s (nsucs k j)
f0 {j = j} s k sh dp = ⊢atDepthSK {sg = KSig} {a = tag 0} {j = j} {s = s} {k = k} (⊢recFst {s = s} {k = k} {sh = sh} dp)

r1 : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} (s k : ℕ) (sh : Shape) →
     Ξ ⊢ p ∷ PayV (rec s k ∷ʰ sh) ((tag 0) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ snd p ∷ PayV sh ((tag 0) ,ₚ j) (SI 2) (SD KSig)
r1 s k sh dp = ⊢recSnd {s = s} {k = k} {sh = sh} dp

okNone : (s : ℕ) (sh : Shape) → RowOK s sh rNone
okNone s sh dq dj dp dc = ⊢rows {I = JT} {Cs = []} ⊢JT []ᵈ
