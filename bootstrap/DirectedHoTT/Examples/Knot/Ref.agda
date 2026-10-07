-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ DEFINITIONS, the reduction rule about `kref`.
--                      (PLAN-BIDI §2-ter, option 3: the Knot encodes the
--                       kernel's definitions; written by hand, not generated)
--
--   δ     a definition steps to its body, weakened to the depth:
--             kref n b  ⟶  εwkK 1 j b
--   (the typing rule `⊢ref` is `Knot/RefJudge`)
--
-- A row is its telescope (`Lib/Tel`): the premises (`tρ`), the
-- existentials (`tσ`), and the Ford equation on the convoy (`⌜Id⌝`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.Ref (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( cong; cong₂ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( []; _∷_; tag; lt-z; lt-s; AllD; []ᵈ; _∷ᵈ_; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 𝓃 ok using ( PayV; ⊢natSnd; ⊢clsFst )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynFib 𝒮 𝓃 ok using ( Row )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( ⊢rows )
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( εwkK; ⊢εwkK; εwkK-sub )
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf using ( module Redₘ; ⊢tgt )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( TelLaw; defRow; ⌜Tm⌝; ⌜Tm⌝-sub; ⊢⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( toTm )

private
  variable
    Δ Θ : Cx

-- the body of a `kref` payload `(n , (b , unit))`
bodyOf : RTm Δ → RTm Δ
bodyOf p = fst (snd p)

⊢bodyOf : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} →
          Ξ ⊢ p ∷ PayV sh-kref ((tag 1) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ bodyOf p ∷ K 1 nzero
⊢bodyOf {j = j} {p = p} dp =
  ⊢IMu→SK {sg = KSig} {s = 1} {d = nzero}
    (⊢clsFst {i = (tag 1) ,ₚ j} {I = SI 2} {D = SD KSig} {p = snd p} {s = 1} {sh = []ʰ}
      (⊢natSnd {i = (tag 1) ,ₚ j} {I = SI 2} {D = SD KSig} {p = p} {sh = cls 1 ∷ʰ []ʰ} dp))

------------------------------------------------------------------------
-- δ — the reduction family's row at `kref`.
------------------------------------------------------------------------

Tδ : RTm Δ → RTm Δ → RTm Δ → Tel Δ
Tδ j p c = tσ (⌜Id⌝ (⌜Tm⌝ j) c (εwkK 1 j (bodyOf p))) tι

Tδ-law : TelLaw Tδ
Tδ-law σ j p c =
  cong (λ X → ⌜ tσ X tι ⌝ᵗ)
       (cong₂ (λ T E → ⌜Id⌝ T (subTm σ c) E) (⌜Tm⌝-sub σ j) (εwkK-sub σ 1 j (bodyOf p)))

rδ : Row
rδ = defRow Tδ Tδ-law

okTδ : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ bodyOf p ∷ K 1 nzero → Ξ ⊢ c ∷ K 1 j →
       TelOK Ξ Redₘ.J (Tδ j p c)
okTδ dj db dc = ok-σ (⊢⌜Id⌝ (⊢⌜Tm⌝ dj) (toTm dc) (toTm (⊢εwkK (lt-s lt-z) dj db))) ok-ι

allδ : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ bodyOf p ∷ K 1 nzero → Ξ ⊢ c ∷ K 1 j →
       AllD Ξ Redₘ.J (⌜ Tδ j p c ⌝ᵗ ∷ [])
allδ {j = j} {p} {c} dj db dc = ⊢tel {T = Tδ j p c} Redₘ.⊢J (okTδ dj db dc) ∷ᵈ []ᵈ

okδ : Redₘ.RowOK 1 sh-kref rδ
okδ {Ξ} {j} {p} {c} dj dp dc =
  ⊢rows {Cs = ⌜ Tδ j p c ⌝ᵗ ∷ []} Redₘ.⊢J (allδ {j = j} {p} {c} dj (⊢bodyOf {j = j} {p = p} dp) (⊢tgt {s = 1} dc))
