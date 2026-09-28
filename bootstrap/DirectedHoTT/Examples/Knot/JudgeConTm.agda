------------------------------------------------------------------------
-- OCP-0009 · KNOT — the CONSTRUCTORS of the `⊢` rows: a rule's derivation
-- as a Knot term, typed via the fibre computation (`fibK`), the nested
-- case's computation (`case-β`) and the row's typing.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeConTm where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶*-dpayᶜ; ⟶ᵀ*-El; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.Sugar using ( tag; conₗ; lt-z; lt-s )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( ⊢conRow )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeTmIx
open import DirectedHoTT.Examples.Knot.JudgeRowsTm
open import DirectedHoTT.Examples.Knot.Judge

-- ★ `⊢lam : Γ ⊢ty A → (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Π A B`
⊢tm-lam : {Ξ : Ctx} {j g A B t r₁ r₂ : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
          Ξ ⊢ A ∷ K 0 j → Ξ ⊢ B ∷ K 0 (nsuc j) → Ξ ⊢ t ∷ K 1 (nsuc j) →
          Ξ ⊢ r₁ ∷ K⊢ (tyIx j g A) → Ξ ⊢ r₂ ∷ K⊢ (tmIx (nsuc j) (cext g A) t B) →
          Ξ ⊢ conₗ 0 (pair r₁ (pair r₂ unit)) ∷ K⊢ (tmIx j g (klam t) (kPi A B))
⊢tm-lam {Ξ} {j} {g} {A} {B} {t} {r₁} {r₂} dj dg dA dB dt dr₁ dr₂ =
  ⊢conRow {Ξ} {JT} {D⊢} {tmIx j g (klam t) (kPi A B)} {CLam j p c} {pair r₁ (pair r₂ unit)} ⊢JT ⊢D⊢
          (⊢tmIx dj dg (⊢klam dj dt) (⊢kPi dj dA dB))
          (fibK {s = 1} {k = 1} {j = j} {p = p} {c = c} (nthᵍ-s nthᵍ-z) (nthʰ-s nthʰ-z))
          (⊢CLam dj dp dc)
          (⊢conv payT (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ redC)))))
  where
    p c q c' : RTm ⌊ Ξ ⌋
    p = pair t unit
    c = pair g (kPi A B)
    q = pair A (pair B unit)
    c' = pair g p
    dp = ⊢payK (lt-s lt-z) ok-klam dj (a-rec dt a[])
    dc = ⊢cTm dj dg (⊢kPi dj dA dB)
    -- the outer row's one rule: the case on `Π A B`
    redC : CLam j p c ⟶* ⌜ TLam j q c' ⌝ᵗ
    redC = ⟶*-trans {t = CLam j p c} {u = PLam.CASE j (kPi A B) (pair (fst c) p)} {v = ⌜ TLam j q c' ⌝ᵗ}
             (⟶*-appˡ (⟶*-ielimᵗ (step (βsnd g (kPi A B)) done)))
             (⟶*-trans {t = PLam.CASE j (kPi A B) (pair (fst c) p)} {u = PLam.CASE j (kPi A B) c'} {v = ⌜ TLam j q c' ⌝ᵗ}
                (⟶*-appʳ (⟶*-pairˡ (step (βfst g (kPi A B)) done)))
                (PLam.case-β {j = j} {q = q} {c = c'} nthᵍ-z (nthʰ-s (nthʰ-s nthʰ-z))))
    J1 J2 : RTm ⌊ Ξ ⌋
    J1 = tyIx j (fst c') (fst q)
    J2 = tmIx (nsuc j) (cext (fst c') (fst q)) (fst (snd c')) (fst (snd q))
    ok : TelOK Ξ JT (TLam j q c')
    ok = okLamT dj (⊢payK lt-z ok-kPi dj (a-rec dA (a-rec dB a[]))) (⊢cI sh-klam ok-klam dj dg dp)
    okRest : {J : RTm ⌊ Ξ ⌋} {T : Tel ⌊ Ξ ⌋} → TelOK Ξ JT (tρ J T) → TelOK Ξ JT T
    okRest (ok-ρ _ o) = o
    fA : fst q ⟶* A
    fA = step (βfst A (pair B unit)) done
    fg : fst c' ⟶* g
    fg = step (βfst g p) done
    rix1 : J1 ⟶* tyIx j g A
    rix1 = ⟶*-pairʳ (⟶*-trans {t = pair (fst q) (pair (fst c') unit)} {u = pair A (pair (fst c') unit)} {v = pair A (pair g unit)}
                     (⟶*-pairˡ fA) (⟶*-pairʳ (⟶*-pairˡ fg)))
    rix2 : J2 ⟶* tmIx (nsuc j) (cext g A) t B
    rix2 = ⟶*-pairʳ (⟶*-trans {t = pair (fst (snd c')) (pair (cext (fst c') (fst q)) (fst (snd q)))}
                              {u = pair t (pair (cext (fst c') (fst q)) (fst (snd q)))} {v = pair t (pair (cext g A) B)}
                     (⟶*-pairˡ (⟶*-trans {t = fst (snd c')} {u = fst p} {v = t}
                                  (⟶*-fst (step (βsnd g p) done)) (step (βfst t unit) done)))
                     (⟶*-pairʳ (⟶*-trans {t = pair (cext (fst c') (fst q)) (fst (snd q))} {u = pair (cext g A) (fst (snd q))}
                               {v = pair (cext g A) B}
                        (⟶*-pairˡ (⟶*-con (⟶*-pairʳ (⟶*-trans {t = pair (fst c') (pair (fst q) unit)}
                                     {u = pair g (pair (fst q) unit)} {v = pair g (pair A unit)}
                                     (⟶*-pairˡ fg) (⟶*-pairʳ (⟶*-pairˡ fA))))))
                        (⟶*-pairʳ (⟶*-trans {t = fst (snd q)} {u = fst (pair B unit)} {v = B}
                                     (⟶*-fst (step (βsnd A (pair B unit)) done)) (step (βfst B unit) done))))))
    payT : Ξ ⊢ pair r₁ (pair r₂ unit) ∷ El (dpay JT D⊢ ⌜ TLam j q c' ⌝ᵗ)
    payT = ⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J1} {r₁} {pair r₂ unit} {tρ J2 tι} ok
                 (⊢conv dr₁ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix1))))
                 (⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J2} {r₂} {unit} {tι} (okRest ok)
                        (⊢conv dr₂ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix2))))
                        (⊢payι {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {unit} ⊢unit))
