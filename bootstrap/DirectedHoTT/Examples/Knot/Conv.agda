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
module DirectedHoTT.Examples.Knot.Conv where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; conₗ; tag-sub; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢conP )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( rows; ⊢rows; toTy; hereTy )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( rows-sub'; ⌜Tm⌝; ⌜Tm⌝-sub; ⊢⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w1-sub; hereTm; toTm; wkN; wkK; dσ¹-cong )
open import DirectedHoTT.Examples.Knot.GenHelpers using ( ∷-cong4 )
open import DirectedHoTT.Examples.Knot.RedIx
open import DirectedHoTT.Examples.Knot.Red using ( ⌜⟶⌝; ⊢⌜⟶⌝; ⌜⟶⌝-sub )
open import DirectedHoTT.Examples.Knot.RedT using ( ⌜⟶ᵀ⌝; ⊢⌜⟶ᵀ⌝; ⌜⟶ᵀ⌝-sub )

private
  variable
    Δ Θ : Cx

  conₗ-sub : (σ : Sub Δ Θ) (k : ℕ) (p : RTm Δ) → subTm σ (conₗ k p) ≡ conₗ k (subTm σ p)
  conₗ-sub σ k p = cong (λ t → con (pair t (subTm σ p))) (tag-sub σ k)

  -- ctrn's two premises, the middle a σ-bound variable
  tr-cong : {Δ : Cx} (ix : RTm (Δ ∙) → RTm (Δ ∙) → RTm (Δ ∙) → RTm (Δ ∙)) (J J' T T' X X' : RTm (Δ ∙)) →
            J ≡ J' → T ≡ T' → X ≡ X' →
            dρ (ix J T (var vz)) (dρ (ix J (var vz) X) dι) ≡ dρ (ix J' T' (var vz)) (dρ (ix J' (var vz) X') dι)
  tr-cong ix J J' T T' X X' refl refl refl = refl

------------------------------------------------------------------------
-- 1. t ≅ u
------------------------------------------------------------------------

C≅ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
C≅ J T X = rows (dσ (⌜⟶⌝ J T X) (lam dι)
               ∷ dσ (⌜Id⌝ (⌜Tm⌝ J) T X) (lam dι)
               ∷ dρ (ix≅ J X T) dι
               ∷ dσ (⌜Tm⌝ J) (lam (dρ (ix≅ (w1 J) (w1 T) (var vz)) (dρ (ix≅ (w1 J) (var vz) (w1 X)) dι)))
               ∷ [])

C≅-sub : (σ : Sub Δ Θ) (J T X : RTm Δ) → subTm σ (C≅ J T X) ≡ C≅ (subTm σ J) (subTm σ T) (subTm σ X)
C≅-sub σ J T X =
  trans (rows-sub' σ (dσ (⌜⟶⌝ J T X) (lam dι)
               ∷ dσ (⌜Id⌝ (⌜Tm⌝ J) T X) (lam dι)
               ∷ dρ (ix≅ J X T) dι
               ∷ dσ (⌜Tm⌝ J) (lam (dρ (ix≅ (w1 J) (w1 T) (var vz)) (dρ (ix≅ (w1 J) (var vz) (w1 X)) dι)))
               ∷ []))
        (cong rows (∷-cong4 _ _ (cong (λ Z → dσ Z (lam dι)) (⌜⟶⌝-sub σ J T X))
                            _ _ (cong (λ Z → dσ (⌜Id⌝ Z (subTm σ T) (subTm σ X)) (lam dι)) (⌜Tm⌝-sub σ J))
                            _ _ refl
                            _ _ (dσ¹-cong _ _ _ _ (⌜Tm⌝-sub σ J)
                                   (tr-cong ix≅ _ _ _ _ _ _ (w1-sub σ J) (w1-sub σ T) (w1-sub σ X)))))

⊢C≅ : {Ξ : Ctx} {J T X : RTm ⌊ Ξ ⌋} → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ T ∷ K 1 J → Ξ ⊢ X ∷ K 1 J → Ξ ⊢ C≅ J T X ∷ Desc Convₘ.J
⊢C≅ {Ξ} {J} {T} {X} dJ dT dX =
  ⊢rows Convₘ.⊢J
    (⊢tel Convₘ.⊢J (ok-σ (⊢⌜⟶⌝ dJ dT dX) ok-ι)
     ∷ᵈ ⊢tel Convₘ.⊢J (ok-σ (⊢⌜Id⌝ (⊢⌜Tm⌝ dJ) (toTm dT) (toTm dX)) ok-ι)
     ∷ᵈ ⊢tel Convₘ.⊢J (ok-ρ (⊢ix≅ dJ dX dT) ok-ι)
     ∷ᵈ ⊢tel Convₘ.⊢J (Convₘ.okσ (⊢⌜Tm⌝ dJ)
          (ok-ρ (⊢ix≅ (wkN dJ) (wkK dT) (hereTm {m = J})) (ok-ρ (⊢ix≅ (wkN dJ) (hereTm {m = J}) (wkK dX)) ok-ι)))
     ∷ᵈ []ᵈ)

row≅ᵏ : ℕ → Row
row≅ᵏ k = record { R = λ j p c → C≅ j (conₗ k p) c
                 ; R-sub = λ σ j p c → trans (C≅-sub σ j (conₗ k p) c) (cong (λ z → C≅ (subTm σ j) z (subTm σ c)) (conₗ-sub σ k p)) }

none≅ : Row
none≅ = record { R = λ j p c → rows [] ; R-sub = λ σ j p c → refl }

row≅ : ℕ → ℕ → Row
row≅ (suc zero) k = row≅ᵏ k
row≅ _ _ = none≅

rowOK≅ : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG KSig s shs → NthSh shs k sh → Convₘ.RowOK s sh (row≅ s k)
rowOK≅ nthᵍ-z nh dj dp dc = ⊢rows {I = Convₘ.J} {Cs = []} Convₘ.⊢J []ᵈ
rowOK≅ (nthᵍ-s nthᵍ-z) nh dj dp dc = ⊢C≅ dj (⊢conP KOK (nthᵍ-s nthᵍ-z) nh dj dp) (⊢tgt dc)

module ≅F = Convₘ.Family row≅ rowOK≅

K≅ : RTm Δ → RTm Δ → RTm Δ → RTy Δ
K≅ d t u = ≅F.KF (ix≅ d t u)

------------------------------------------------------------------------
-- 2. A ≅ᵀ B
------------------------------------------------------------------------

C≅ᵀ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
C≅ᵀ J T X = rows (dσ (⌜⟶ᵀ⌝ J T X) (lam dι)
                ∷ dσ (⌜Id⌝ (⌜Ty⌝ J) T X) (lam dι)
                ∷ dρ (ix≅ᵀ J X T) dι
                ∷ dσ (⌜Ty⌝ J) (lam (dρ (ix≅ᵀ (w1 J) (w1 T) (var vz)) (dρ (ix≅ᵀ (w1 J) (var vz) (w1 X)) dι)))
                ∷ [])

C≅ᵀ-sub : (σ : Sub Δ Θ) (J T X : RTm Δ) → subTm σ (C≅ᵀ J T X) ≡ C≅ᵀ (subTm σ J) (subTm σ T) (subTm σ X)
C≅ᵀ-sub σ J T X =
  trans (rows-sub' σ (dσ (⌜⟶ᵀ⌝ J T X) (lam dι)
                ∷ dσ (⌜Id⌝ (⌜Ty⌝ J) T X) (lam dι)
                ∷ dρ (ix≅ᵀ J X T) dι
                ∷ dσ (⌜Ty⌝ J) (lam (dρ (ix≅ᵀ (w1 J) (w1 T) (var vz)) (dρ (ix≅ᵀ (w1 J) (var vz) (w1 X)) dι)))
                ∷ []))
        (cong rows (∷-cong4 _ _ (cong (λ Z → dσ Z (lam dι)) (⌜⟶ᵀ⌝-sub σ J T X))
                            _ _ (cong (λ Z → dσ (⌜Id⌝ Z (subTm σ T) (subTm σ X)) (lam dι)) (⌜Ty⌝-sub σ J))
                            _ _ refl
                            _ _ (dσ¹-cong _ _ _ _ (⌜Ty⌝-sub σ J)
                                   (tr-cong ix≅ᵀ _ _ _ _ _ _ (w1-sub σ J) (w1-sub σ T) (w1-sub σ X)))))

⊢C≅ᵀ : {Ξ : Ctx} {J T X : RTm ⌊ Ξ ⌋} → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ T ∷ K 0 J → Ξ ⊢ X ∷ K 0 J → Ξ ⊢ C≅ᵀ J T X ∷ Desc ConvTₘ.J
⊢C≅ᵀ {Ξ} {J} {T} {X} dJ dT dX =
  ⊢rows ConvTₘ.⊢J
    (⊢tel ConvTₘ.⊢J (ok-σ (⊢⌜⟶ᵀ⌝ dJ dT dX) ok-ι)
     ∷ᵈ ⊢tel ConvTₘ.⊢J (ok-σ (⊢⌜Id⌝ (⊢⌜Ty⌝ dJ) (toTy dT) (toTy dX)) ok-ι)
     ∷ᵈ ⊢tel ConvTₘ.⊢J (ok-ρ (⊢ix≅ᵀ dJ dX dT) ok-ι)
     ∷ᵈ ⊢tel ConvTₘ.⊢J (ConvTₘ.okσ (⊢⌜Ty⌝ dJ)
          (ok-ρ (⊢ix≅ᵀ (wkN dJ) (wkK dT) (hereTy {m = J})) (ok-ρ (⊢ix≅ᵀ (wkN dJ) (hereTy {m = J}) (wkK dX)) ok-ι)))
     ∷ᵈ []ᵈ)

row≅ᵀᵏ : ℕ → Row
row≅ᵀᵏ k = record { R = λ j p c → C≅ᵀ j (conₗ k p) c
                  ; R-sub = λ σ j p c → trans (C≅ᵀ-sub σ j (conₗ k p) c) (cong (λ z → C≅ᵀ (subTm σ j) z (subTm σ c)) (conₗ-sub σ k p)) }

row≅ᵀ : ℕ → ℕ → Row
row≅ᵀ zero k = row≅ᵀᵏ k
row≅ᵀ _ _ = none≅

rowOK≅ᵀ : {s c k : ℕ} {shs : Shapes c} {sh : Shape} → NthG KSig s shs → NthSh shs k sh → ConvTₘ.RowOK s sh (row≅ᵀ s k)
rowOK≅ᵀ nthᵍ-z nh dj dp dc = ⊢C≅ᵀ dj (⊢conP KOK nthᵍ-z nh dj dp) (⊢tgt dc)
rowOK≅ᵀ (nthᵍ-s nthᵍ-z) nh dj dp dc = ⊢rows {I = ConvTₘ.J} {Cs = []} ConvTₘ.⊢J []ᵈ

module ≅ᵀF = ConvTₘ.Family row≅ᵀ rowOK≅ᵀ

K≅ᵀ : RTm Δ → RTm Δ → RTm Δ → RTy Δ
K≅ᵀ d A B = ≅ᵀF.KF (ix≅ᵀ d A B)

------------------------------------------------------------------------
-- 3. ★ As CODES (`⊢conv` cites `≅ᵀ` through a σ-field), OPAQUE.
------------------------------------------------------------------------

opaque
  ⌜≅ᵀ⌝ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
  ⌜≅ᵀ⌝ d A B = ⌜IMu⌝ ConvTₘ.J ≅ᵀF.DF (ix≅ᵀ d A B)

  ⊢⌜≅ᵀ⌝ : {Ξ : Ctx} {d A B : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ A ∷ K 0 d → Ξ ⊢ B ∷ K 0 d → Ξ ⊢ ⌜≅ᵀ⌝ d A B ∷ U
  ⊢⌜≅ᵀ⌝ dd dA dB = ⊢⌜IMu⌝ ConvTₘ.⊢J ≅ᵀF.⊢DF (⊢ix≅ᵀ dd dA dB)

  ⌜≅ᵀ⌝-sub : (σ : Sub Δ Θ) (d A B : RTm Δ) → subTm σ (⌜≅ᵀ⌝ d A B) ≡ ⌜≅ᵀ⌝ (subTm σ d) (subTm σ A) (subTm σ B)
  ⌜≅ᵀ⌝-sub σ d A B = cong₂ (λ I D → ⌜IMu⌝ I D (ix≅ᵀ (subTm σ d) (subTm σ A) (subTm σ B))) (ConvTₘ.J-sub σ) (≅ᵀF.DF-sub σ)

  El-⌜≅ᵀ⌝ : {d A B : RTm Δ} → El (⌜≅ᵀ⌝ d A B) ≅ᵀ K≅ᵀ d A B
  El-⌜≅ᵀ⌝ = credᵀ El-⌜IMu⌝

  ⌜≅⌝ : RTm Δ → RTm Δ → RTm Δ → RTm Δ
  ⌜≅⌝ d t u = ⌜IMu⌝ Convₘ.J ≅F.DF (ix≅ d t u)

  ⊢⌜≅⌝ : {Ξ : Ctx} {d t u : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ K 1 d → Ξ ⊢ u ∷ K 1 d → Ξ ⊢ ⌜≅⌝ d t u ∷ U
  ⊢⌜≅⌝ dd dt du = ⊢⌜IMu⌝ Convₘ.⊢J ≅F.⊢DF (⊢ix≅ dd dt du)

  ⌜≅⌝-sub : (σ : Sub Δ Θ) (d t u : RTm Δ) → subTm σ (⌜≅⌝ d t u) ≡ ⌜≅⌝ (subTm σ d) (subTm σ t) (subTm σ u)
  ⌜≅⌝-sub σ d t u = cong₂ (λ I D → ⌜IMu⌝ I D (ix≅ (subTm σ d) (subTm σ t) (subTm σ u))) (Convₘ.J-sub σ) (≅F.DF-sub σ)
