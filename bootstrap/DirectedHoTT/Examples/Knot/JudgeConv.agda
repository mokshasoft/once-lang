------------------------------------------------------------------------
-- OCP-0009 · KNOT — `⊢conv : Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B`, the `⊢`
-- rule with a bare-variable subject: one row in EVERY term fibre (D077),
-- parametric in the subject, typed once.  `A` is a σ-field, `A ≅ᵀ B` a
-- σ-field of the lower stratum's code (`Knot/Conv`).  And the `∋` premise
-- of `⊢var` as an opaque code.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeConv where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( tag; conₗ; tag-sub )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢conP )
open import DirectedHoTT.Lib.FinFam using ( FinI )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( hereTy; I∋; ⊢I∋; I∋-sub; D∋; ⊢D∋; ix∋; ⊢ix∋; K∋ )
open import DirectedHoTT.Examples.Knot.LookupCon using ( D∋-sub )
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w1-sub; okσJ; wkN; wkK; wkG )
open import DirectedHoTT.Examples.Knot.Conv using ( ⌜≅ᵀ⌝; ⊢⌜≅ᵀ⌝; ⌜≅ᵀ⌝-sub )

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- ⊢conv
------------------------------------------------------------------------

TCV : RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
TCV J G T X = tσ (⌜Ty⌝ J) (tρ (tmIx (w1 J) (w1 G) (w1 T) (var vz)) (tσ (⌜≅ᵀ⌝ (w1 J) (var vz) (w1 X)) tι))

private
  cv-cong : (a a' : RTm Δ) (J J' G G' T T' X X' : RTm (Δ ∙)) → a ≡ a' → J ≡ J' → G ≡ G' → T ≡ T' → X ≡ X' →
            (b b' : RTm (Δ ∙)) → b ≡ b' →
            dσ a (lam (dρ (tmIx J G T (var vz)) (dσ b (lam dι)))) ≡ dσ a' (lam (dρ (tmIx J' G' T' (var vz)) (dσ b' (lam dι))))
  cv-cong a a' J J' G G' T T' X X' refl refl refl refl refl b b' refl = refl

TCV-sub : (σ : Sub Δ Θ) (J G T X : RTm Δ) → subTm σ ⌜ TCV J G T X ⌝ᵗ ≡ ⌜ TCV (subTm σ J) (subTm σ G) (subTm σ T) (subTm σ X) ⌝ᵗ
TCV-sub σ J G T X =
  cv-cong _ _ _ _ _ _ _ _ _ _ (⌜Ty⌝-sub σ J) (w1-sub σ J) (w1-sub σ G) (w1-sub σ T) (w1-sub σ X) _ _
          (trans (⌜≅ᵀ⌝-sub (extS σ) (w1 J) (var vz) (w1 X))
                 (cong₂ (λ a b → ⌜≅ᵀ⌝ a (var vz) b) (w1-sub σ J) (w1-sub σ X)))

okTCV : {Ξ : Ctx} {J G T X : RTm ⌊ Ξ ⌋} → Ξ ⊢ J ∷ El ⌜Nat⌝ → Ξ ⊢ G ∷ KCtx J → Ξ ⊢ T ∷ K 1 J → Ξ ⊢ X ∷ K 0 J →
        TelOK Ξ JT (TCV J G T X)
okTCV {J = J} dJ dG dT dX =
  okσJ (⊢⌜Ty⌝ dJ)
    (ok-ρ (⊢tmIx (wkN dJ) (wkG dG) (wkK dT) (hereTy {m = J}))
          (okσJ (⊢⌜≅ᵀ⌝ (wkN dJ) (hereTy {m = J}) (wkK dX)) ok-ι))

-- at head `k`: the subject is `conₗ k p`, the convoy `(Γ , B)`
TCVat : ℕ → RTm Δ → RTm Δ → RTm Δ → Tel Δ
TCVat k j p c = TCV j (fst c) (conₗ k p) (snd c)

TCVat-law : (k : ℕ) → TelLaw (TCVat k)
TCVat-law k σ j p c =
  trans (TCV-sub σ j (fst c) (conₗ k p) (snd c))
        (cong (λ z → ⌜ TCV (subTm σ j) (fst (subTm σ c)) z (snd (subTm σ c)) ⌝ᵗ)
              {x = subTm σ (conₗ k p)} {y = conₗ k (subTm σ p)}
              (cong (λ t → con (pair t (subTm σ p))) (tag-sub σ k)))

okTCVat : {c₀ k : ℕ} {shs : Shapes c₀} {sh : Shape} → NthG KSig 1 shs → NthSh shs k sh →
          {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ →
          Ξ ⊢ p ∷ PayV sh (pair (tag 1) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat (pair (tag 1) j)) →
          TelOK Ξ JT (TCVat k j p c)
okTCVat ng nh dj dp dc = okTCV dj (⊢ctxOf dc) (⊢conP KOK ng nh dj dp) (⊢tyOf dc)

------------------------------------------------------------------------
-- the `∋` premise, as a CODE (opaque)
------------------------------------------------------------------------

opaque
  ⌜∋⌝ : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
  ⌜∋⌝ d g x a = ⌜IMu⌝ I∋ D∋ (ix∋ d g x a)

  ⊢⌜∋⌝ : {Ξ : Ctx} {d g x a : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx d → Ξ ⊢ x ∷ FinI d → Ξ ⊢ a ∷ K 0 d →
         Ξ ⊢ ⌜∋⌝ d g x a ∷ U
  ⊢⌜∋⌝ dd dg dx da = ⊢⌜IMu⌝ ⊢I∋ ⊢D∋ (⊢ix∋ dd dg dx da)

  ⌜∋⌝-sub : (σ : Sub Δ Θ) (d g x a : RTm Δ) → subTm σ (⌜∋⌝ d g x a) ≡ ⌜∋⌝ (subTm σ d) (subTm σ g) (subTm σ x) (subTm σ a)
  ⌜∋⌝-sub σ d g x a = cong₂ (λ I D → ⌜IMu⌝ I D (ix∋ (subTm σ d) (subTm σ g) (subTm σ x) (subTm σ a))) (I∋-sub σ) (D∋-sub σ)

  El-⌜∋⌝ : {d g x a : RTm Δ} → El (⌜∋⌝ d g x a) ⟶ᵀ K∋ (ix∋ d g x a)
  El-⌜∋⌝ = El-⌜IMu⌝
