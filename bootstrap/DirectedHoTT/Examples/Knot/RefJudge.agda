-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ DEFINITIONS, the typing rule about `kref`
--                      (PLAN-BIDI §2-ter, option 3; written by hand).
--
--   ⊢ref  a definition has its body's type, weakened to the depth,
--         when its body is typed in the EMPTY context:
--             ◇ ⊢ b ∷ A   ⇒   Γ ⊢ kref n b ∷ εwkK 0 j A
--
-- Apart from `Knot/Ref` (δ) because the typing family's rows sit above the
-- reduction family: a head's row carries its conversion row (`TCVat`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.RefJudge (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong₂ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( []; _∷_; tag; lt-z; lt-s; AllD; []ᵈ; _∷ᵈ_; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 𝓃 ok using ( PayV )
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃 using ( toI )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynFib 𝒮 𝓃 ok using ( Row )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( ⌜Ty⌝; ⌜Ty⌝-sub; ⊢⌜Ty⌝; cε; ⊢cε )
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( rows; ⊢rows; toTy; hereTy )
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( εwkK; ⊢εwkK; εwkK-sub )
open import DirectedHoTT.Examples.Knot.Ref 𝒮 wf using ( bodyOf; ⊢bodyOf )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; ⊢JT; TelLaw; rows-sub'; CTat; tmIx; ⊢tmIx; ⊢tyOf )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( w1; w1-sub; wkN; wkK; okσJ )
open import DirectedHoTT.Examples.Knot.JudgeFib 𝒮 wf using ( RowOK )
open import DirectedHoTT.Examples.Knot.JudgeConv 𝒮 wf using ( TCVat; TCVat-law; okTCVat )

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- ⊢ref — the typing family's row at `kref`: some type `A` at depth 0, the
--   body typed at it in the empty context, and the conclusion's type the
--   weakening of `A`.
------------------------------------------------------------------------

-- the tail after `A`, at variables: `B` the body, `C` the conclusion's type
T⊢ref⁽1⁾ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
T⊢ref⁽1⁾ J B C A = tρ (tmIx nzero cε B A) (tσ (⌜Id⌝ (⌜Ty⌝ J) C (εwkK 0 J A)) tι)

T⊢ref⁽1⁾-sub : (σ : Sub Δ Θ) (J B C A : RTm Δ) →
               subTm σ ⌜ T⊢ref⁽1⁾ J B C A ⌝ᵗ ≡ ⌜ T⊢ref⁽1⁾ (subTm σ J) (subTm σ B) (subTm σ C) (subTm σ A) ⌝ᵗ
T⊢ref⁽1⁾-sub σ J B C A =
  cong₂ (λ X Y → ⌜ tρ (tmIx nzero cε (subTm σ B) (subTm σ A)) (tσ (⌜Id⌝ X (subTm σ C) Y) tι) ⌝ᵗ)
        (⌜Ty⌝-sub σ J) (εwkK-sub σ 0 J A)

okT⊢ref⁽1⁾ : {Ξ : Ctx} {J B C A : RTm ⌊ Ξ ⌋} → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ B ∷ K 1 nzero → Ξ ⊢ C ∷ K 0 J →
             Ξ ⊢ A ∷ K 0 nzero → TelOK Ξ JT (T⊢ref⁽1⁾ J B C A)
okT⊢ref⁽1⁾ dJ dB dC dA =
  ok-ρ (⊢tmIx (toI ⊢nzero) ⊢cε dB dA)
       (okσJ (⊢⌜Id⌝ (⊢⌜Ty⌝ dJ) (toTy dC) (toTy (⊢εwkK lt-z dJ dA))) ok-ι)

T⊢ref : RTm Δ → RTm Δ → RTm Δ → Tel Δ
T⊢ref j p c = tσ (⌜Ty⌝ nzero) (T⊢ref⁽1⁾ (w1 j) (w1 (bodyOf p)) (w1 (snd c)) v₀)

T⊢ref-law : TelLaw T⊢ref
T⊢ref-law σ j p c =
  cong₂ (λ X Y → dσ X (lam Y)) (⌜Ty⌝-sub σ nzero)
        (trans (T⊢ref⁽1⁾-sub (extS σ) (w1 j) (w1 (bodyOf p)) (w1 (snd c)) v₀)
               (cong₃' (λ J B C → ⌜ T⊢ref⁽1⁾ J B C v₀ ⌝ᵗ) (w1-sub σ j) (w1-sub σ (bodyOf p)) (w1-sub σ (snd c))))
  where
    cong₃' : {A B C D : Set} (f : A → B → C → D) {a a' : A} {b b' : B} {x x' : C} →
             a ≡ a' → b ≡ b' → x ≡ x' → f a b x ≡ f a' b' x'
    cong₃' f refl refl refl = refl

-- the row at `kref` is the rule and the head's conversion row (`TCVat`),
-- as at every other head
r⊢ref : Row
r⊢ref = record
  { R     = λ j p c → rows (⌜ T⊢ref j p c ⌝ᵗ ∷ ⌜ TCVat 38 j p c ⌝ᵗ ∷ [])
  ; R-sub = λ σ j p c → trans (rows-sub' σ (⌜ T⊢ref j p c ⌝ᵗ ∷ ⌜ TCVat 38 j p c ⌝ᵗ ∷ []))
                              (cong₂ (λ a b → rows (a ∷ b ∷ [])) (T⊢ref-law σ j p c) (TCVat-law 38 σ j p c)) }

okT⊢ref : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ bodyOf p ∷ K 1 nzero → Ξ ⊢ snd c ∷ K 0 j →
          TelOK Ξ JT (T⊢ref j p c)
okT⊢ref dj db dA = okσJ (⊢⌜Ty⌝ (toI ⊢nzero)) (okT⊢ref⁽1⁾ (wkN dj) (wkK db) (wkK dA) (hereTy {m = nzero}))

all⊢ref : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ p ∷ PayV sh-kref ((tag 1) ,ₚ j) (SI 2) (SD KSig) →
          Ξ ⊢ c ∷ El (CTat ((tag 1) ,ₚ j)) → AllD Ξ JT (⌜ T⊢ref j p c ⌝ᵗ ∷ ⌜ TCVat 38 j p c ⌝ᵗ ∷ [])
all⊢ref {j = j} {p} {c} dj dp dc =
  ⊢tel {T = T⊢ref j p c} ⊢JT (okT⊢ref dj (⊢bodyOf {j = j} {p = p} dp) (⊢tyOf dc))
  ∷ᵈ ⊢tel {T = TCVat 38 j p c} ⊢JT (okTCVat (atᵍ 1) (atʰ 38) dj dp dc)
  ∷ᵈ []ᵈ

ok⊢ref : RowOK 1 sh-kref r⊢ref
ok⊢ref {Ξ} {j} {p} {c} dj dp dc =
  ⊢rows {Cs = ⌜ T⊢ref j p c ⌝ᵗ ∷ ⌜ TCVat 38 j p c ⌝ᵗ ∷ []} ⊢JT (all⊢ref {j = j} {p} {c} dj dp dc)
