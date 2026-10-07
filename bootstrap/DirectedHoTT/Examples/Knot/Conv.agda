-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the CONVERSIONS `t ≅ u` and `A ≅ᵀ B` as families
-- (D077): their four rules have a bare-variable subject, so every fibre
-- is the same four rows at the subject `conₗ k p` — ONE parametric fibre,
-- typed once, at every head.
--
--     cred  : t ⟶ u → t ≅ u            (a σ-field of the lower stratum ⟶)
--     crfl  : t ≅ t                    (the target Forded: u ≡ t)
--     csym  : u ≅ t → t ≅ u
--     ctrn  : t ≅ v → v ≅ u → t ≅ u    (v a σ-field)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
module DirectedHoTT.Examples.Knot.Conv (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Cons; []; _∷_; tag; conₗ; tag-sub; []ᵈ; _∷ᵈ_; AllD; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV; ⊢conP )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.SynFib 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( Row )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( rows; ⊢rows; toTy; hereTy )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( rows-sub'; ⌜Tm⌝; ⌜Tm⌝-sub; ⊢⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase 𝒮 wf using ( w1; w1-sub; hereTm; toTm; wkN; wkK; dσ¹-cong )
open import DirectedHoTT.Examples.Knot.GenHelpers 𝒮 wf using ( ∷-cong4 )
open import DirectedHoTT.Examples.Knot.RedIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Red 𝒮 wf core using ( ⌜⟶⌝; ⊢⌜⟶⌝; ⌜⟶⌝-sub )
open import DirectedHoTT.Examples.Knot.RedT 𝒮 wf core using ( ⌜⟶ᵀ⌝; ⊢⌜⟶ᵀ⌝; ⌜⟶ᵀ⌝-sub )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜QSig⌝ )

private
  variable
    Δ Θ : Cx

  conₗ-sub : (σ : Sub Δ Θ) (k : ℕ) (p : RTm Δ) → subTm σ (conₗ k p) ≡ conₗ k (subTm σ p)
  conₗ-sub σ k p = cong (λ t → con (t ,ₚ (subTm σ p))) (tag-sub σ k)

  -- ctrn's two premises, the middle a σ-bound variable
  tr-cong : {Δ : Cx} (ix : RTm (Δ ∙) → RTm (Δ ∙) → RTm (Δ ∙) → RTm (Δ ∙)) (J J' T T' X X' : RTm (Δ ∙)) →
            J ≡ J' → T ≡ T' → X ≡ X' →
            dρ (ix J T v₀) (dρ (ix J v₀ X) dι) ≡ dρ (ix J' T' v₀) (dρ (ix J' v₀ X') dι)
  tr-cong ix J J' T T' X X' refl refl refl = refl

------------------------------------------------------------------------
-- 1. t ≅ u
------------------------------------------------------------------------

C≅ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
C≅ Q J T X = rows (dσ (⌜⟶⌝ Q J T X) (lam dι)
               ∷ dσ (⌜Id⌝ (⌜Tm⌝ J) T X) (lam dι)
               ∷ dρ (ix≅ J X T) dι
               ∷ dσ (⌜Tm⌝ J) (lam (dρ (ix≅ (w1 J) (w1 T) v₀) (dρ (ix≅ (w1 J) v₀ (w1 X)) dι)))
               ∷ [])

C≅-sub : (σ : Sub Δ Θ) (Q J T X : RTm Δ) → subTm σ (C≅ Q J T X) ≡ C≅ (subTm σ Q) (subTm σ J) (subTm σ T) (subTm σ X)
C≅-sub σ Q J T X =
  trans (rows-sub' σ (dσ (⌜⟶⌝ Q J T X) (lam dι)
               ∷ dσ (⌜Id⌝ (⌜Tm⌝ J) T X) (lam dι)
               ∷ dρ (ix≅ J X T) dι
               ∷ dσ (⌜Tm⌝ J) (lam (dρ (ix≅ (w1 J) (w1 T) v₀) (dρ (ix≅ (w1 J) v₀ (w1 X)) dι)))
               ∷ []))
        (cong rows (∷-cong4 _ _ (cong (λ Z → dσ Z (lam dι)) (⌜⟶⌝-sub σ Q J T X))
                            _ _ (cong (λ Z → dσ (⌜Id⌝ Z (subTm σ T) (subTm σ X)) (lam dι)) (⌜Tm⌝-sub σ J))
                            _ _ refl
                            _ _ (dσ¹-cong _ _ _ _ (⌜Tm⌝-sub σ J)
                                   (tr-cong ix≅ _ _ _ _ _ _ (w1-sub σ J) (w1-sub σ T) (w1-sub σ X)))))

-- the four rows' typings (what a constructor cites)
allC≅ : {Ξ : Ctx} {Q J T X : RTm ⌊ Ξ ⌋} → Ξ ⊢ Q ∷ El ⌜QSig⌝ → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ T ∷ K 1 J → Ξ ⊢ X ∷ K 1 J →
        AllD Ξ Convₘ.J (dσ (⌜⟶⌝ Q J T X) (lam dι) ∷ dσ (⌜Id⌝ (⌜Tm⌝ J) T X) (lam dι) ∷ dρ (ix≅ J X T) dι ∷ dσ (⌜Tm⌝ J) (lam (dρ (ix≅ (w1 J) (w1 T) v₀) (dρ (ix≅ (w1 J) v₀ (w1 X)) dι))) ∷ [])
allC≅ {Ξ} {Q} {J} {T} {X} dQ dJ dT dX =
    ⊢tel Convₘ.⊢J (ok-σ (⊢⌜⟶⌝ dQ dJ dT dX) ok-ι)
     ∷ᵈ ⊢tel Convₘ.⊢J (ok-σ (⊢⌜Id⌝ (⊢⌜Tm⌝ dJ) (toTm dT) (toTm dX)) ok-ι)
     ∷ᵈ ⊢tel Convₘ.⊢J (ok-ρ (⊢ix≅ dJ dX dT) ok-ι)
     ∷ᵈ ⊢tel Convₘ.⊢J (Convₘ.okσ (⊢⌜Tm⌝ dJ)
          (ok-ρ (⊢ix≅ (wkN dJ) (wkK dT) (hereTm {m = J})) (ok-ρ (⊢ix≅ (wkN dJ) (hereTm {m = J}) (wkK dX)) ok-ι)))
     ∷ᵈ []ᵈ

⊢C≅ : {Ξ : Ctx} {Q J T X : RTm ⌊ Ξ ⌋} → Ξ ⊢ Q ∷ El ⌜QSig⌝ → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ T ∷ K 1 J → Ξ ⊢ X ∷ K 1 J → Ξ ⊢ C≅ Q J T X ∷ Desc Convₘ.J
⊢C≅ dQ dJ dT dX = ⊢rows Convₘ.⊢J (allC≅ dQ dJ dT dX)

row≅ᵏ : ℕ → Row
row≅ᵏ k = record { R = λ q j p c → C≅ q j (conₗ k p) c
                 ; R-sub = λ σ q j p c → trans (C≅-sub σ q j (conₗ k p) c) (cong (λ z → C≅ (subTm σ q) (subTm σ j) z (subTm σ c)) (conₗ-sub σ k p)) }

none≅ : Row
none≅ = record { R = λ q j p c → rows [] ; R-sub = λ σ q j p c → refl }

row≅ : ℕ → ℕ → Row
row≅ (suc zero) k = row≅ᵏ k
row≅ _ _ = none≅

rowOK≅ : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG KSig s shs → NthSh shs k sh → Convₘ.RowOK s sh (row≅ s k)
rowOK≅ nthᵍ-z nh dq dj dp dc = ⊢rows {I = Convₘ.J} {Cs = []} Convₘ.⊢J []ᵈ
rowOK≅ (nthᵍ-s nthᵍ-z) nh dq dj dp dc = ⊢C≅ dq dj (⊢conP KOK (nthᵍ-s nthᵍ-z) nh dj dp) (⊢tgt dc)

module ≅F = Convₘ.Family row≅ rowOK≅

K≅ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTy Δ
K≅ q d t u = ≅F.KF q (ix≅ d t u)

------------------------------------------------------------------------
-- 2. A ≅ᵀ B
------------------------------------------------------------------------

C≅ᵀ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
C≅ᵀ Q J T X = rows (dσ (⌜⟶ᵀ⌝ Q J T X) (lam dι)
                ∷ dσ (⌜Id⌝ (⌜Ty⌝ J) T X) (lam dι)
                ∷ dρ (ix≅ᵀ J X T) dι
                ∷ dσ (⌜Ty⌝ J) (lam (dρ (ix≅ᵀ (w1 J) (w1 T) v₀) (dρ (ix≅ᵀ (w1 J) v₀ (w1 X)) dι)))
                ∷ [])

C≅ᵀ-sub : (σ : Sub Δ Θ) (Q J T X : RTm Δ) → subTm σ (C≅ᵀ Q J T X) ≡ C≅ᵀ (subTm σ Q) (subTm σ J) (subTm σ T) (subTm σ X)
C≅ᵀ-sub σ Q J T X =
  trans (rows-sub' σ (dσ (⌜⟶ᵀ⌝ Q J T X) (lam dι)
                ∷ dσ (⌜Id⌝ (⌜Ty⌝ J) T X) (lam dι)
                ∷ dρ (ix≅ᵀ J X T) dι
                ∷ dσ (⌜Ty⌝ J) (lam (dρ (ix≅ᵀ (w1 J) (w1 T) v₀) (dρ (ix≅ᵀ (w1 J) v₀ (w1 X)) dι)))
                ∷ []))
        (cong rows (∷-cong4 _ _ (cong (λ Z → dσ Z (lam dι)) (⌜⟶ᵀ⌝-sub σ Q J T X))
                            _ _ (cong (λ Z → dσ (⌜Id⌝ Z (subTm σ T) (subTm σ X)) (lam dι)) (⌜Ty⌝-sub σ J))
                            _ _ refl
                            _ _ (dσ¹-cong _ _ _ _ (⌜Ty⌝-sub σ J)
                                   (tr-cong ix≅ᵀ _ _ _ _ _ _ (w1-sub σ J) (w1-sub σ T) (w1-sub σ X)))))

-- the four rows' typings (what a constructor cites)
allC≅ᵀ : {Ξ : Ctx} {Q J T X : RTm ⌊ Ξ ⌋} → Ξ ⊢ Q ∷ El ⌜QSig⌝ → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ T ∷ K 0 J → Ξ ⊢ X ∷ K 0 J →
        AllD Ξ ConvTₘ.J (dσ (⌜⟶ᵀ⌝ Q J T X) (lam dι) ∷ dσ (⌜Id⌝ (⌜Ty⌝ J) T X) (lam dι) ∷ dρ (ix≅ᵀ J X T) dι ∷ dσ (⌜Ty⌝ J) (lam (dρ (ix≅ᵀ (w1 J) (w1 T) v₀) (dρ (ix≅ᵀ (w1 J) v₀ (w1 X)) dι))) ∷ [])
allC≅ᵀ {Ξ} {Q} {J} {T} {X} dQ dJ dT dX =
    ⊢tel ConvTₘ.⊢J (ok-σ (⊢⌜⟶ᵀ⌝ dQ dJ dT dX) ok-ι)
     ∷ᵈ ⊢tel ConvTₘ.⊢J (ok-σ (⊢⌜Id⌝ (⊢⌜Ty⌝ dJ) (toTy dT) (toTy dX)) ok-ι)
     ∷ᵈ ⊢tel ConvTₘ.⊢J (ok-ρ (⊢ix≅ᵀ dJ dX dT) ok-ι)
     ∷ᵈ ⊢tel ConvTₘ.⊢J (ConvTₘ.okσ (⊢⌜Ty⌝ dJ)
          (ok-ρ (⊢ix≅ᵀ (wkN dJ) (wkK dT) (hereTy {m = J})) (ok-ρ (⊢ix≅ᵀ (wkN dJ) (hereTy {m = J}) (wkK dX)) ok-ι)))
     ∷ᵈ []ᵈ

⊢C≅ᵀ : {Ξ : Ctx} {Q J T X : RTm ⌊ Ξ ⌋} → Ξ ⊢ Q ∷ El ⌜QSig⌝ → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ T ∷ K 0 J → Ξ ⊢ X ∷ K 0 J → Ξ ⊢ C≅ᵀ Q J T X ∷ Desc ConvTₘ.J
⊢C≅ᵀ dQ dJ dT dX = ⊢rows ConvTₘ.⊢J (allC≅ᵀ dQ dJ dT dX)

row≅ᵀᵏ : ℕ → Row
row≅ᵀᵏ k = record { R = λ q j p c → C≅ᵀ q j (conₗ k p) c
                  ; R-sub = λ σ q j p c → trans (C≅ᵀ-sub σ q j (conₗ k p) c) (cong (λ z → C≅ᵀ (subTm σ q) (subTm σ j) z (subTm σ c)) (conₗ-sub σ k p)) }

row≅ᵀ : ℕ → ℕ → Row
row≅ᵀ zero k = row≅ᵀᵏ k
row≅ᵀ _ _ = none≅

rowOK≅ᵀ : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG KSig s shs → NthSh shs k sh → ConvTₘ.RowOK s sh (row≅ᵀ s k)
rowOK≅ᵀ nthᵍ-z nh dq dj dp dc = ⊢C≅ᵀ dq dj (⊢conP KOK nthᵍ-z nh dj dp) (⊢tgt dc)
rowOK≅ᵀ (nthᵍ-s nthᵍ-z) nh dq dj dp dc = ⊢rows {I = ConvTₘ.J} {Cs = []} ConvTₘ.⊢J []ᵈ

module ≅ᵀF = ConvTₘ.Family row≅ᵀ rowOK≅ᵀ

K≅ᵀ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTy Δ
K≅ᵀ q d A B = ≅ᵀF.KF q (ix≅ᵀ d A B)

------------------------------------------------------------------------
-- 3. ★ As CODES (`⊢conv` cites `≅ᵀ` through a σ-field), OPAQUE.
------------------------------------------------------------------------

opaque
  ⌜≅ᵀ⌝ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
  ⌜≅ᵀ⌝ q d A B = ⌜IMu⌝ ConvTₘ.J (≅ᵀF.DF q) (ix≅ᵀ d A B)

  ⊢⌜≅ᵀ⌝ : {Ξ : Ctx} {q d A B : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜QSig⌝ → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ A ∷ K 0 d → Ξ ⊢ B ∷ K 0 d → Ξ ⊢ ⌜≅ᵀ⌝ q d A B ∷ U
  ⊢⌜≅ᵀ⌝ dq dd dA dB = ⊢⌜IMu⌝ ConvTₘ.⊢J (≅ᵀF.⊢DF dq) (⊢ix≅ᵀ dd dA dB)

  ⌜≅ᵀ⌝-sub : (σ : Sub Δ Θ) (q d A B : RTm Δ) → subTm σ (⌜≅ᵀ⌝ q d A B) ≡ ⌜≅ᵀ⌝ (subTm σ q) (subTm σ d) (subTm σ A) (subTm σ B)
  ⌜≅ᵀ⌝-sub σ q d A B = cong₂ (λ I D → ⌜IMu⌝ I D (ix≅ᵀ (subTm σ d) (subTm σ A) (subTm σ B))) (ConvTₘ.J-sub σ) (≅ᵀF.DF-sub σ q)

  El-⌜≅ᵀ⌝ : {q d A B : RTm Δ} → El (⌜≅ᵀ⌝ q d A B) ≅ᵀ K≅ᵀ q d A B
  El-⌜≅ᵀ⌝ = credᵀ El-⌜IMu⌝

  ⌜≅⌝ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
  ⌜≅⌝ q d t u = ⌜IMu⌝ Convₘ.J (≅F.DF q) (ix≅ d t u)

  ⊢⌜≅⌝ : {Ξ : Ctx} {q d t u : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜QSig⌝ → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 d → Ξ ⊢ u ∷ K 1 d → Ξ ⊢ ⌜≅⌝ q d t u ∷ U
  ⊢⌜≅⌝ dq dd dt du = ⊢⌜IMu⌝ Convₘ.⊢J (≅F.⊢DF dq) (⊢ix≅ dd dt du)

  ⌜≅⌝-sub : (σ : Sub Δ Θ) (q d t u : RTm Δ) → subTm σ (⌜≅⌝ q d t u) ≡ ⌜≅⌝ (subTm σ q) (subTm σ d) (subTm σ t) (subTm σ u)
  ⌜≅⌝-sub σ q d t u = cong₂ (λ I D → ⌜IMu⌝ I D (ix≅ (subTm σ d) (subTm σ t) (subTm σ u))) (Convₘ.J-sub σ) (≅F.DF-sub σ q)
