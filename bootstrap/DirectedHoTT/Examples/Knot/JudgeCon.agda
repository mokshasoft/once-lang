------------------------------------------------------------------------
-- OCP-0009 · KNOT — the CONSTRUCTORS of the typing judgement: a rule's derivation as a Knot term, typed via the fibre computation (`fibK`) and the row's typing.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeCon where


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimⁱ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-snd; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; Lt; lt-z; lt-s; subC; selF-sub; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; payV-red; ⊢recFst; ⊢recSnd; ⊢atDepth )
open import DirectedHoTT.Lib.FinFam using ( FinI; ffz; ⊢ffz; ⊢isuc )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Ren using ( wk; wk-sub; ⊢wkS )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Sorted using ( ⊢sortOf )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row; module Fib; ⊢conRow )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( ⌜Ctx⌝; rows; ⊢rows )

open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeRowsTy
open import DirectedHoTT.Examples.Knot.Judge

private
  variable
    Δ Θ : Cx

-- ★ `ty-base : Γ ⊢ty base`
⊢ty-base : {Ξ : Ctx} {j g : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
           Ξ ⊢ conₗ 0 unit ∷ K⊢ (tyIx j g kbase)
⊢ty-base {Ξ} {j} {g} dj dg =
  ⊢conRow {Ξ} {JT} {D⊢} {tyIx j g kbase} {dι} {unit} ⊢JT ⊢D⊢ (⊢tyIx dj dg (⊢kbase dj))
          (fibK {s = 0} {k = 0} {j = j} {p = unit} {c = pair g unit} nthᵍ-z nthʰ-z)
          (⊢dι ⊢JT) (⊢payι {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {unit} ⊢unit)

-- ★ `ty-Π : Γ ⊢ty A → (Γ ▹ A) ⊢ty B → Γ ⊢ty Π A B`
⊢ty-Π : {Ξ : Ctx} {j g A B r₁ r₂ : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
        Ξ ⊢ A ∷ K 0 j → Ξ ⊢ B ∷ K 0 (nsuc j) →
        Ξ ⊢ r₁ ∷ K⊢ (tyIx j g A) → Ξ ⊢ r₂ ∷ K⊢ (tyIx (nsuc j) (cext g A) B) →
        Ξ ⊢ conₗ 0 (pair r₁ (pair r₂ unit)) ∷ K⊢ (tyIx j g (kPi A B))
⊢ty-Π {Ξ} {j} {g} {A} {B} {r₁} {r₂} dj dg dA dB dr₁ dr₂ =
  ⊢conRow {Ξ} {JT} {D⊢} {tyIx j g (kPi A B)} {⌜ TPi j p c ⌝ᵗ} {pair r₁ (pair r₂ unit)} ⊢JT ⊢D⊢
          (⊢tyIx dj dg (⊢kPi dj dA dB))
          (fibK {s = 0} {k = 2} {j = j} {p = p} {c = c} nthᵍ-z (nthʰ-s (nthʰ-s nthʰ-z)))
          (⊢tel {Ξ} {JT} {TPi j p c} ⊢JT ok)
          (⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J1} {r₁} {pair r₂ unit} {tρ J2 tι} ok
                 (⊢conv dr₁ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix1))))
                 (⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J2} {r₂} {unit} {tι} (okRest ok)
                        (⊢conv dr₂ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix2))))
                        (⊢payι {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {unit} ⊢unit)))
  where
    p c : RTm ⌊ Ξ ⌋
    p = pair A (pair B unit)
    c = pair g unit
    J1 J2 : RTm ⌊ Ξ ⌋
    J1 = tyIx j (fst c) (fst p)
    J2 = tyIx (nsuc j) (cext (fst c) (fst p)) (fst (snd p))
    ok : TelOK Ξ JT (TPi j p c)
    ok = okPiT dj (⊢payK lt-z ok-kPi dj (a-rec dA (a-rec dB a[]))) (⊢cTy dj dg)
    okRest : {J : RTm ⌊ Ξ ⌋} {T : Tel ⌊ Ξ ⌋} → TelOK Ξ JT (tρ J T) → TelOK Ξ JT T
    okRest (ok-ρ _ o) = o
    -- the row's indices, their projections reduced
    rix1 : J1 ⟶* tyIx j g A
    rix1 = ⟶*-pairʳ (⟶*-trans {t = pair (fst p) (pair (fst c) unit)} {u = pair A (pair (fst c) unit)} {v = pair A (pair g unit)}
                     (⟶*-pairˡ (step (βfst A (pair B unit)) done)) (⟶*-pairʳ (⟶*-pairˡ (step (βfst g unit) done))))
    rix2 : J2 ⟶* tyIx (nsuc j) (cext g A) B
    rix2 = ⟶*-pairʳ (⟶*-trans {t = pair (fst (snd p)) (pair (cext (fst c) (fst p)) unit)}
                              {u = pair B (pair (cext (fst c) (fst p)) unit)} {v = pair B (pair (cext g A) unit)}
                     (⟶*-pairˡ (⟶*-trans {t = fst (snd p)} {u = fst (pair B unit)} {v = B}
                                  (⟶*-fst (step (βsnd A (pair B unit)) done)) (step (βfst B unit) done)))
                     (⟶*-pairʳ (⟶*-pairˡ (⟶*-con (⟶*-pairʳ (⟶*-trans {t = pair (fst c) (pair (fst p) unit)}
                                  {u = pair g (pair (fst p) unit)} {v = pair g (pair A unit)}
                                  (⟶*-pairˡ (step (βfst g unit) done))
                                  (⟶*-pairʳ (⟶*-pairˡ (step (βfst A (pair B unit)) done)))))))))

