-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ DEFINITIONS, the typing rule about `kref`
--                      (PLAN-REF K4, D082: a reference is a PROJECTION).
--
--   ⊢ref  a name below the BOUND has its declared type, read off the
--         signature and weakened to the depth — no premise:
--             n < boundT q   ⟹   Γ ⊢ kref n ∷ εwkK 0 j (typesQ (sigT q) n)
--         (`Spec/Typing.⊢ref : d <ˢ n → Γ ⊢ ref d ∷ εwkTy (type 𝒮 d)`;
--          the typing family's parameter `q` is the signature and the
--          bound, `Knot/QSig.⌜TSig⌝`)
--
-- Apart from `Knot/Ref` (δ) because the typing family's rows sit above the
-- reduction family: a head's row carries its conversion row (`TCVat`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
module DirectedHoTT.Examples.Knot.RefJudge (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( []; _∷_; tag; lt-z; lt-s; AllD; []ᵈ; _∷ᵈ_; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV )
open import DirectedHoTT.Lib.NatCode 𝒮 (Defs.size 𝒮) using ( toI; ⊢isuc )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.SynFib 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Row )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( ⌜Ty⌝; ⌜Ty⌝-sub; ⊢⌜Ty⌝; cε; ⊢cε )
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( rows; ⊢rows; toTy; hereTy )
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( εwkK; ⊢εwkK; εwkK-sub )
open import DirectedHoTT.Examples.Knot.Ref 𝒮 wf using ( nameOf; ⊢nameOf )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜TSig⌝; sigT; boundT; typesQ; ⊢sigT; ⊢boundT; ⊢typesQ; wkT )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; ⊢JT; TelLaw; rows-sub'; CTat; tmIx; ⊢tmIx; ⊢tyOf )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( w1; w1-sub; wkN; wkK; okσJ )
open import DirectedHoTT.Examples.Knot.JudgeFib 𝒮 wf using ( RowOK )
open import DirectedHoTT.Examples.Knot.JudgeConv 𝒮 wf core using ( TCVat; TCVat-law; okTCVat )

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- ⊢ref — the typing family's row at `kref`: the side condition, and the
--   conclusion's type the declared one, weakened.
------------------------------------------------------------------------

-- the Ford equation on the conclusion's type (the tail), at variables
T⊢refT : RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
T⊢refT Q J N C = tσ (⌜Id⌝ (⌜Ty⌝ J) C (εwkK 0 J (typesQ (sigT Q) N))) tι

T⊢refT-sub : (σ : Sub Δ Θ) (Q J N C : RTm Δ) →
             subTm σ ⌜ T⊢refT Q J N C ⌝ᵗ ≡ ⌜ T⊢refT (subTm σ Q) (subTm σ J) (subTm σ N) (subTm σ C) ⌝ᵗ
T⊢refT-sub σ Q J N C =
  cong (λ Z → ⌜ tσ Z tι ⌝ᵗ)
       (cong₂ (λ T E → ⌜Id⌝ T (subTm σ C) E) (⌜Ty⌝-sub σ J) (εwkK-sub σ 0 J (typesQ (sigT Q) N)))

-- the side condition `N < boundT Q`, then the Ford equation — at variables
T⊢ref' : RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
T⊢ref' Q J N C = tσ (⌜Hom⌝ ⌜Nat⌝ (nsuc N) (boundT Q)) (T⊢refT (w1 Q) (w1 J) (w1 N) (w1 C))

T⊢ref'-sub : (σ : Sub Δ Θ) (Q J N C : RTm Δ) →
             subTm σ ⌜ T⊢ref' Q J N C ⌝ᵗ ≡ ⌜ T⊢ref' (subTm σ Q) (subTm σ J) (subTm σ N) (subTm σ C) ⌝ᵗ
T⊢ref'-sub σ Q J N C =
  cong (λ Z → dσ (⌜Hom⌝ ⌜Nat⌝ (nsuc (subTm σ N)) (boundT (subTm σ Q))) (lam Z))
       (trans (T⊢refT-sub (extS σ) (w1 Q) (w1 J) (w1 N) (w1 C))
              (cong₄ (λ a b c d → ⌜ T⊢refT a b c d ⌝ᵗ) (w1-sub σ Q) (w1-sub σ J) (w1-sub σ N) (w1-sub σ C)))

-- the row, at the fibre's sources: the name out of the payload, the type
--   out of the convoy
T⊢ref : RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
T⊢ref q j p c = T⊢ref' q j (nameOf p) (snd c)

T⊢ref-law : TelLaw T⊢ref
T⊢ref-law σ q j p c = T⊢ref'-sub σ q j (nameOf p) (snd c)

-- the row at `kref` is the rule and the head's conversion row (`TCVat`),
-- as at every other head
r⊢ref : Row
r⊢ref = record
  { R     = λ q j p c → rows (⌜ T⊢ref q j p c ⌝ᵗ ∷ ⌜ TCVat 38 q j p c ⌝ᵗ ∷ [])
  ; R-sub = λ σ q j p c → trans (rows-sub' σ (⌜ T⊢ref q j p c ⌝ᵗ ∷ ⌜ TCVat 38 q j p c ⌝ᵗ ∷ []))
                                (cong₂ (λ a b → rows (a ∷ b ∷ [])) (T⊢ref-law σ q j p c) (TCVat-law 38 σ q j p c)) }

okT⊢refT : {Ξ : Ctx} {Q J N C : RTm ⌊ Ξ ⌋} → Ξ ⊢ Q ∷ El ⌜TSig⌝ → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ N ∷ El ⌜Nat⌝ →
           Ξ ⊢ C ∷ K 0 J → TelOK Ξ JT (T⊢refT Q J N C)
okT⊢refT dQ dJ dN dC =
  okσJ (⊢⌜Id⌝ (⊢⌜Ty⌝ dJ) (toTy dC) (toTy (⊢εwkK lt-z dJ (⊢typesQ (⊢sigT dQ) dN)))) ok-ι

okT⊢ref' : {Ξ : Ctx} {Q J N C : RTm ⌊ Ξ ⌋} → Ξ ⊢ Q ∷ El ⌜TSig⌝ → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ N ∷ El ⌜Nat⌝ →
           Ξ ⊢ C ∷ K 0 J → TelOK Ξ JT (T⊢ref' Q J N C)
okT⊢ref' dQ dJ dN dC =
  okσJ (⊢⌜Hom⌝ ⊢⌜Nat⌝ (⊢isuc dN) (⊢boundT dQ)) (okT⊢refT (wkT dQ) (wkN dJ) (wkN dN) (wkK dC))

all⊢ref : {Ξ : Ctx} {q j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜TSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ →
          Ξ ⊢ p ∷ PayV sh-kref ((tag 1) ,ₚ j) (SI 2) (SD KSig) →
          Ξ ⊢ c ∷ El (CTat ((tag 1) ,ₚ j)) → AllD Ξ JT (⌜ T⊢ref q j p c ⌝ᵗ ∷ ⌜ TCVat 38 q j p c ⌝ᵗ ∷ [])
all⊢ref {q = q} {j} {p} {c} dq dj dp dc =
  ⊢tel {T = T⊢ref q j p c} ⊢JT (okT⊢ref' dq dj (⊢nameOf {j = j} dp) (⊢tyOf dc))
  ∷ᵈ ⊢tel {T = TCVat 38 q j p c} ⊢JT (okTCVat (atᵍ 1) (atʰ 38) dq dj dp dc)
  ∷ᵈ []ᵈ

ok⊢ref : RowOK 1 sh-kref r⊢ref
ok⊢ref {Ξ} {q} {j} {p} {c} dq dj dp dc =
  ⊢rows {Cs = ⌜ T⊢ref q j p c ⌝ᵗ ∷ ⌜ TCVat 38 q j p c ⌝ᵗ ∷ []} ⊢JT (all⊢ref {q = q} {j} {p} {c} dq dj dp dc)
