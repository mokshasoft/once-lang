-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ DEFINITIONS, the reduction rule about `kref`.
--                      (PLAN-REF K4, D082: a reference is a PROJECTION)
--
--   δ     a name below the quoted signature's size steps to its body,
--         read off the signature `q` (the family's parameter) and weakened
--         to the depth:
--             n < sizeQ q   ⟹   kref n  ⟶  εwkK 1 j (bodiesQ q n)
--         (`Spec/Reduction.δref`: `d <ˢ size 𝒮 → ref d ⟶ εwkTm (body 𝒮 d)`;
--          the side condition is the kernel's order, `Hom Nat`)
--   (the typing rule `⊢ref` is `Knot/RefJudge`)
--
-- A row is its telescope (`Lib/Tel`): the existentials (`tσ`) — the
-- side condition, then the Ford equation on the convoy (`⌜Id⌝`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.Ref (𝒮 : Defs) (wf : WfK 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; trans; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( []; _∷_; tag; lt-z; lt-s; AllD; []ᵈ; _∷ᵈ_; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV; ⊢natFst )
open import DirectedHoTT.Lib.NatCode 𝒮 (Defs.size 𝒮) using ( ⊢isuc )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.SynFib 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Row )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( ⊢rows )
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( εwkK; ⊢εwkK; εwkK-sub )
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf using ( module Redₘ; ⊢tgt )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( TelLaw; defRow; ⌜Tm⌝; ⌜Tm⌝-sub; ⊢⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( toTm; w1; w1-sub; wkN; wkK )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜QSig⌝; sizeQ; bodiesQ; ⊢sizeQ; ⊢bodiesQ; wkQ )

private
  variable
    Δ Θ : Cx

-- the name of a `kref` payload `(n , unit)`
nameOf : RTm Δ → RTm Δ
nameOf p = fst p

⊢nameOf : {Ξ : Ctx} {j p : RTm ⌊ Ξ ⌋} →
          Ξ ⊢ p ∷ PayV sh-kref ((tag 1) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ nameOf p ∷ El ⌜Nat⌝
⊢nameOf {j = j} dp = ⊢natFst {i = (tag 1) ,ₚ j} {I = SI 2} {D = SD KSig} {sh = []ʰ} dp

------------------------------------------------------------------------
-- δ — the reduction family's row at `kref`.
------------------------------------------------------------------------

-- the Ford equation (the tail after the side condition), at variables
TδT : RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
TδT Q J N C = tσ (⌜Id⌝ (⌜Tm⌝ J) C (εwkK 1 J (bodiesQ Q N))) tι

TδT-sub : (σ : Sub Δ Θ) (Q J N C : RTm Δ) →
          subTm σ ⌜ TδT Q J N C ⌝ᵗ ≡ ⌜ TδT (subTm σ Q) (subTm σ J) (subTm σ N) (subTm σ C) ⌝ᵗ
TδT-sub σ Q J N C =
  cong (λ Z → ⌜ tσ Z tι ⌝ᵗ)
       (cong₂ (λ T E → ⌜Id⌝ T (subTm σ C) E) (⌜Tm⌝-sub σ J) (εwkK-sub σ 1 J (bodiesQ Q N)))

-- the side condition `N < sizeQ Q`, then the Ford equation — at variables
Tδ' : RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
Tδ' Q J N C = tσ (⌜Hom⌝ ⌜Nat⌝ (nsuc N) (sizeQ Q)) (TδT (w1 Q) (w1 J) (w1 N) (w1 C))

Tδ'-sub : (σ : Sub Δ Θ) (Q J N C : RTm Δ) →
          subTm σ ⌜ Tδ' Q J N C ⌝ᵗ ≡ ⌜ Tδ' (subTm σ Q) (subTm σ J) (subTm σ N) (subTm σ C) ⌝ᵗ
Tδ'-sub σ Q J N C =
  cong (λ Z → dσ (⌜Hom⌝ ⌜Nat⌝ (nsuc (subTm σ N)) (sizeQ (subTm σ Q))) (lam Z))
       (trans (TδT-sub (extS σ) (w1 Q) (w1 J) (w1 N) (w1 C))
              (cong₄ (λ a b c d → ⌜ TδT a b c d ⌝ᵗ) (w1-sub σ Q) (w1-sub σ J) (w1-sub σ N) (w1-sub σ C)))

-- the row, at the fibre's sources: the name out of the payload
Tδ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
Tδ q j p c = Tδ' q j (nameOf p) c

Tδ-law : TelLaw Tδ
Tδ-law σ q j p c = Tδ'-sub σ q j (nameOf p) c

rδ : Row
rδ = defRow Tδ Tδ-law

okTδT : {Ξ : Ctx} {Q J N C : RTm ⌊ Ξ ⌋} → Ξ ⊢ Q ∷ El ⌜QSig⌝ → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ N ∷ El ⌜Nat⌝ →
        Ξ ⊢ C ∷ K 1 J → TelOK Ξ Redₘ.J (TδT Q J N C)
okTδT dQ dJ dN dC =
  Redₘ.okσ (⊢⌜Id⌝ (⊢⌜Tm⌝ dJ) (toTm dC) (toTm (⊢εwkK (lt-s lt-z) dJ (⊢bodiesQ dQ dN)))) ok-ι

okTδ' : {Ξ : Ctx} {Q J N C : RTm ⌊ Ξ ⌋} → Ξ ⊢ Q ∷ El ⌜QSig⌝ → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ N ∷ El ⌜Nat⌝ →
        Ξ ⊢ C ∷ K 1 J → TelOK Ξ Redₘ.J (Tδ' Q J N C)
okTδ' dQ dJ dN dC =
  Redₘ.okσ (⊢⌜Hom⌝ ⊢⌜Nat⌝ (⊢isuc dN) (⊢sizeQ dQ)) (okTδT (wkQ dQ) (wkN dJ) (wkN dN) (wkK dC))

okδ : Redₘ.RowOK 1 sh-kref rδ
okδ {Ξ} {q} {j} {p} {c} dq dj dp dc =
  ⊢rows {Cs = ⌜ Tδ q j p c ⌝ᵗ ∷ []} Redₘ.⊢J
        (⊢tel {T = Tδ q j p c} Redₘ.⊢J (okTδ' dq dj (⊢nameOf {j = j} dp) (⊢tgt {s = 1} dc)) ∷ᵈ []ᵈ)
