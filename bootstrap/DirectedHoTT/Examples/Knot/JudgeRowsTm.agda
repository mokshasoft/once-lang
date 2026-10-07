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
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.JudgeRowsTm (𝒮 : Defs) (wf : WfK 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Cons; []; _∷_; tag; Lt; lt-z; lt-s; []ᵈ; _∷ᵈ_; v₁; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV; ⊢recFst; ⊢recSnd; ⊢atDepthSK; ⊢natFst )
import DirectedHoTT.Lib.NatCode 𝒮 (Defs.size 𝒮) as ᴵNatCode
open ᴵNatCode using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors 𝒮 wf
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.SynFib 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Row )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf as ᴵLookup
open ᴵLookup using ( rows; ⊢rows )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.JudgeTmIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.JudgeFib 𝒮 wf using ( RowOK; f0; r1 )
open ᴵLookup using ( toTy; hereTy; I∋; ⊢I∋; I∋-sub; ix∋; ⊢ix∋; D∋; ⊢D∋ )
open import DirectedHoTT.Examples.Knot.LookupCon 𝒮 wf using ( D∋-sub )
open ᴵNatCode using ( toI; fromI )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-⌜IMu⌝ⁱ; ⟶*-⌜Fin⌝ )
open import DirectedHoTT.Examples.Knot.Sub 𝒮 wf using ( sub0; ⊢sub0; sub0-sub )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using () renaming ( wk-sub to wkS )

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
