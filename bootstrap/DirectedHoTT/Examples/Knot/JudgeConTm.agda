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
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-ielimᵗ; ⟶*-fst; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶*-dpayᶜ; ⟶ᵀ*-El; ⟶ᵀ*-IMu; ⟶ᵀ*-trans; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; stepᵀ; doneᵀ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Lib.SynView using ( ⊢recSnd )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Examples.Knot.Lookup using ( toTy; hereTy; K∋; I∋; D∋; ix∋ )
open import DirectedHoTT.Lib.FinFam using ( FinI )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0; ⊢sub0; ⟶*-sub0ᵘ )
open import DirectedHoTT.Lib.Sugar using ( tag; conₗ; lt-z; lt-s; nth-z; []; _∷_; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( ⊢conRowₖ )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeTmIx
open import DirectedHoTT.Examples.Knot.JudgeRowsGen
open import DirectedHoTT.Examples.Knot.JudgeRowsTm using ( g0 )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w2; okσJ; wkN; wkG; wkK; dσ¹-cong )
open import DirectedHoTT.Examples.Knot.JudgeConv using ( TCVat; okTCVat; El-⌜∋⌝ )
open import DirectedHoTT.Examples.Knot.Judge

-- ★ `⊢lam : Γ ⊢ty A → (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Π A B`
⊢tm-lam : {Ξ : Ctx} {j g A B t r₁ r₂ : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
          Ξ ⊢ A ∷ K 0 j → Ξ ⊢ B ∷ K 0 (nsuc j) → Ξ ⊢ t ∷ K 1 (nsuc j) →
          Ξ ⊢ r₁ ∷ K⊢ (tyIx j g A) → Ξ ⊢ r₂ ∷ K⊢ (tmIx (nsuc j) (cext g A) t B) →
          Ξ ⊢ conₗ 0 (pair r₁ (pair r₂ unit)) ∷ K⊢ (tmIx j g (klam t) (kPi A B))
⊢tm-lam {Ξ} {j} {g} {A} {B} {t} {r₁} {r₂} dj dg dA dB dt dr₁ dr₂ =
  ⊢conRowₖ {Ξ} {2} {0} {JT} {D⊢} {tmIx j g (klam t) (kPi A B)} {PT⊢lam.CX j p c} {pair r₁ (pair r₂ unit)}
           {PT⊢lam.CX j p c ∷ ⌜ TCVat 1 j p c ⌝ᵗ ∷ []} nth-z ⊢JT ⊢D⊢
          (⊢tmIx dj dg (⊢klam dj dt) (⊢kPi dj dA dB))
          (fibK {s = 1} {k = 1} {j = j} {p = p} {c = c} (nthᵍ-s nthᵍ-z) (nthʰ-s nthʰ-z))
          (PT⊢lam.⊢CX okC⊢lamI {Ξ} {j} {p} {c} dj dp dc
             ∷ᵈ ⊢tel {Ξ} {JT} {TCVat 1 j p c} ⊢JT (okTCVat (nthᵍ-s nthᵍ-z) (nthʰ-s nthʰ-z) dj dp dc) ∷ᵈ []ᵈ)
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
    redC : PT⊢lam.CX j p c ⟶* ⌜ T⊢lam j q c' ⌝ᵗ
    redC = ⟶*-trans {t = PT⊢lam.CX j p c} {u = PT⊢lam.CASE j (kPi A B) (pair (fst c) p)} {v = ⌜ T⊢lam j q c' ⌝ᵗ}
             (PT⊢lam.CASE-⟶ᵃ (step (βsnd g (kPi A B)) done))
             (⟶*-trans {t = PT⊢lam.CASE j (kPi A B) (pair (fst c) p)} {u = PT⊢lam.CASE j (kPi A B) c'} {v = ⌜ T⊢lam j q c' ⌝ᵗ}
                (PT⊢lam.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g (kPi A B)) done)))
                (PT⊢lam.case-β {j = j} {q = q} {c = c'} nthᵍ-z (nthʰ-s (nthʰ-s nthʰ-z))))
    J1 J2 : RTm ⌊ Ξ ⌋
    J1 = tyIx j (fst c') (fst q)
    J2 = tmIx (nsuc j) (cext (fst c') (fst q)) (fst (snd c')) (fst (snd q))
    ok : TelOK Ξ JT (T⊢lam j q c')
    ok = okT⊢lam dj (⊢payK lt-z ok-kPi dj (a-rec dA (a-rec dB a[]))) (⊢cI sh-klam ok-klam dj dg dp)
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
    payT : Ξ ⊢ pair r₁ (pair r₂ unit) ∷ El (dpay JT D⊢ ⌜ T⊢lam j q c' ⌝ᵗ)
    payT = ⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J1} {r₁} {pair r₂ unit} {tρ J2 tι} ok
                 (⊢conv dr₁ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix1))))
                 (⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J2} {r₂} {unit} {tι} (okRest ok)
                        (⊢conv dr₂ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix2))))
                        (⊢payι {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {unit} ⊢unit))

------------------------------------------------------------------------
-- ★ `⊢app : Γ ⊢ t ∷ Π A B → Γ ⊢ u ∷ A → Γ ⊢ app t u ∷ B[u]`
--   the σ-fields instantiated one at a time (`TAppI-sub` + cancellation),
--   the Ford field is `idrefl`
------------------------------------------------------------------------

private
  -- a weakening under one binder, cancelled by the next instantiation
  kc1 : {Δ : Cx} (u t : RTm Δ) → subTm (extS (single u)) (w2 t) ≡ w1 t
  kc1 u t = trans (wkS (single u) (w1 t)) (cong w1 (wk-cancel-tm u t))

  dσ-cong : {Δ : Cx} (X X' : RTm Δ) (Z Z' : RTm (Δ ∙)) → X ≡ X' → Z ≡ Z' → dσ X (lam Z) ≡ dσ X' (lam Z')
  dσ-cong X X' Z Z' refl refl = refl

⊢tm-app : {Ξ : Ctx} {j g A B t u r₁ r₂ : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
          Ξ ⊢ A ∷ K 0 j → Ξ ⊢ B ∷ K 0 (nsuc j) → Ξ ⊢ t ∷ K 1 j → Ξ ⊢ u ∷ K 1 j →
          Ξ ⊢ r₁ ∷ K⊢ (tmIx j g t (kPi A B)) → Ξ ⊢ r₂ ∷ K⊢ (tmIx j g u A) →
          Ξ ⊢ conₗ 0 (pair A (pair B (pair r₁ (pair r₂ (pair (idrefl (⌜Ty⌝ j) (sub0 0 j B u)) unit)))))
            ∷ K⊢ (tmIx j g (kapp t u) (sub0 0 j B u))
⊢tm-app {Ξ} {j} {g} {A} {B} {t} {u} {r₁} {r₂} dj dg dA dB dt du dr₁ dr₂ =
  ⊢conRowₖ {Ξ} {2} {0} {JT} {D⊢} {tmIx j g (kapp t u) X} {⌜ T⊢app j p c ⌝ᵗ} {pay}
           {⌜ T⊢app j p c ⌝ᵗ ∷ ⌜ TCVat 2 j p c ⌝ᵗ ∷ []} nth-z ⊢JT ⊢D⊢
          (⊢tmIx dj dg (⊢kapp dj dt du) dX)
          (fibK {s = 1} {k = 2} {j = j} {p = p} {c = c} (nthᵍ-s nthᵍ-z) (nthʰ-s (nthʰ-s nthʰ-z)))
          (⊢tel {Ξ} {JT} {T⊢app j p c} ⊢JT ok0
             ∷ᵈ ⊢tel {Ξ} {JT} {TCVat 2 j p c} ⊢JT (okTCVat (nthᵍ-s nthᵍ-z) (nthʰ-s (nthʰ-s nthʰ-z)) dj dp dc) ∷ᵈ []ᵈ)
          (⊢payσ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {C⊢app_0I j} {A} {pay1} {T0} ok0 (toTy dA)
            (⊢-cast {Ξ} {pay1} {El (dpay JT D⊢ ⌜ T1 ⌝ᵗ)} {El (dpay JT D⊢ (subTm (single A) ⌜ T0 ⌝ᵗ))}
                    (cong (λ Z → El (dpay JT D⊢ Z)) (sym e1))
              (⊢payσ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {C⊢app_1I j} {B} {pay2} {T1'} ok1 (toTy dB)
                (⊢-cast {Ξ} {pay2} {El (dpay JT D⊢ ⌜ T2 ⌝ᵗ)} {El (dpay JT D⊢ (subTm (single B) ⌜ T1' ⌝ᵗ))}
                        (cong (λ Z → El (dpay JT D⊢ Z)) (sym e2))
                  (⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J1} {r₁} {pair r₂ (pair e unit)} {tρ J2 TE} ok2
                         (⊢conv dr₁ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix1))))
                    (⊢payρ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {J2} {r₂} {pair e unit} {TE} (okRest ok2)
                           (⊢conv dr₂ (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu rix2))))
                      (⊢payσ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {SE} {e} {unit} {tι} (okRest (okRest ok2)) dE
                             (⊢payι {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {unit} ⊢unit))))))))
  where
    X p c : RTm ⌊ Ξ ⌋
    X = sub0 0 j B u
    p = pair t (pair u unit)
    c = pair g X
    e = idrefl (⌜Ty⌝ j) X
    pay2 = pair r₁ (pair r₂ (pair e unit))
    pay1 = pair B pay2
    pay = pair A pay1
    dX : Ξ ⊢ X ∷ K 0 j
    dX = ⊢sub0 lt-z dj dB du
    dp = ⊢payK (lt-s lt-z) ok-kapp dj (a-rec dt (a-rec du a[]))
    dc = ⊢cTm dj dg dX
    ok0 : TelOK Ξ JT (T⊢app j p c)
    ok0 = okT⊢app dj dp dc
    -- the telescope after each σ-field
    T0 : Tel (⌊ Ξ ⌋ ∙)
    T0 = tσ (C⊢app_1I (w1 j)) (T⊢appI (w2 j) (w2 (fst c)) (w2 (snd c)) (w2 (fst p)) (w2 (fst (snd p))) (var (vs vz)) (var vz))
    T1' : Tel (⌊ Ξ ⌋ ∙)
    T1' = T⊢appI (w1 j) (w1 (fst c)) (w1 (snd c)) (w1 (fst p)) (w1 (fst (snd p))) (w1 A) (var vz)
    T1 : Tel ⌊ Ξ ⌋
    T1 = tσ (C⊢app_1I j) T1'
    T2 : Tel ⌊ Ξ ⌋
    T2 = T⊢appI j (fst c) (snd c) (fst p) (fst (snd p)) A B
    SE = ⌜Id⌝ (⌜Ty⌝ j) (snd c) (sub0 0 j B (fst (snd p)))
    TE : Tel ⌊ Ξ ⌋
    TE = tσ SE tι
    J1 J2 : RTm ⌊ Ξ ⌋
    J1 = tmIx j (fst c) (fst p) (kPi A B)
    J2 = tmIx j (fst c) (fst (snd p)) A
    e1 : subTm (single A) ⌜ T0 ⌝ᵗ ≡ ⌜ T1 ⌝ᵗ
    e1 = dσ-cong _ _ _ _
           (trans (C⊢app_1I-sub (single A) (w1 j)) (C⊢app_1I-cong _ _ (wk-cancel-tm A j)))
           (trans (T⊢appI-sub (extS (single A)) (w2 j) (w2 (fst c)) (w2 (snd c)) (w2 (fst p)) (w2 (fst (snd p))) (var (vs vz)) (var vz))
                  (T⊢appI-cong _ _ _ _ _ _ _ _ _ _ _ _ _ _ (kc1 A j) (kc1 A (fst c)) (kc1 A (snd c)) (kc1 A (fst p)) (kc1 A (fst (snd p))) refl refl))
    e2 : subTm (single B) ⌜ T1' ⌝ᵗ ≡ ⌜ T2 ⌝ᵗ
    e2 = trans (T⊢appI-sub (single B) (w1 j) (w1 (fst c)) (w1 (snd c)) (w1 (fst p)) (w1 (fst (snd p))) (w1 A) (var vz))
               (T⊢appI-cong _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wk-cancel-tm B j) (wk-cancel-tm B (fst c)) (wk-cancel-tm B (snd c))
                            (wk-cancel-tm B (fst p)) (wk-cancel-tm B (fst (snd p))) (wk-cancel-tm B A) refl)
    -- the projections' typings (as the row types them)
    dfc : Ξ ⊢ fst c ∷ KCtx j
    dfc = ⊢ctxOf dc
    dfp : Ξ ⊢ fst p ∷ K 1 j
    dfp = g0 1 0 (rec 1 0 ∷ʰ []ʰ) dp
    dfsp : Ξ ⊢ fst (snd p) ∷ K 1 j
    dfsp = g0 {j = j} {p = snd p} 1 0 []ʰ (⊢recSnd {s = 1} {k = 0} {sh = rec 1 0 ∷ʰ []ʰ} dp)
    ok1 : TelOK Ξ JT T1
    ok1 = okσJ (okC⊢app_1I dj)
            (okT⊢appI {_} {w1 j} {w1 (fst c)} {w1 (snd c)} {w1 (fst p)} {w1 (fst (snd p))} {w1 A} {var vz}
                      (wkN dj) (wkG dfc) (wkK (⊢tyOf dc)) (wkK dfp) (wkK dfsp) (wkK dA) (hereTy {m = nsuc j}))
    ok2 : TelOK Ξ JT T2
    ok2 = okT⊢appI {Ξ} {j} {fst c} {snd c} {fst p} {fst (snd p)} {A} {B} dj dfc (⊢tyOf dc) dfp dfsp dA dB
    okRest : {J : RTm ⌊ Ξ ⌋} {T : Tel ⌊ Ξ ⌋} → TelOK Ξ JT (tρ J T) → TelOK Ξ JT T
    okRest (ok-ρ _ o) = o
    fg : fst c ⟶* g
    fg = step (βfst g X) done
    ft : fst p ⟶* t
    ft = step (βfst t (pair u unit)) done
    fu : fst (snd p) ⟶* u
    fu = ⟶*-trans {t = fst (snd p)} {u = fst (pair u unit)} {v = u} (⟶*-fst (step (βsnd t (pair u unit)) done)) (step (βfst u unit) done)
    rix1 : J1 ⟶* tmIx j g t (kPi A B)
    rix1 = ⟶*-pairʳ (⟶*-trans {t = pair (fst p) (pair (fst c) (kPi A B))} {u = pair t (pair (fst c) (kPi A B))} {v = pair t (pair g (kPi A B))}
                     (⟶*-pairˡ ft) (⟶*-pairʳ (⟶*-pairˡ fg)))
    rix2 : J2 ⟶* tmIx j g u A
    rix2 = ⟶*-pairʳ (⟶*-trans {t = pair (fst (snd p)) (pair (fst c) A)} {u = pair u (pair (fst c) A)} {v = pair u (pair g A)}
                     (⟶*-pairˡ fu) (⟶*-pairʳ (⟶*-pairˡ fg)))
    dE : Ξ ⊢ e ∷ El SE
    dE = ⊢conv (⊢idrefl (⊢⌜Ty⌝ dj) (toTy dX))
               (csymᵀ (red→≅ᵀ (stepᵀ (El-⌜Id⌝ (⌜Ty⌝ j) (snd c) (sub0 0 j B (fst (snd p))))
                               (⟶ᵀ*-trans (⟶ᵀ*-Idˡ (step (βsnd g X) done)) (⟶ᵀ*-Idʳ (⟶*-sub0ᵘ fu))))))

------------------------------------------------------------------------
-- ★ `⊢var : Γ ∋ x ∷ A → Γ ⊢ var x ∷ A` — the ∋-derivation is the payload
------------------------------------------------------------------------

⊢tm-var : {Ξ : Ctx} {j g x A r : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j →
          Ξ ⊢ x ∷ FinI j → Ξ ⊢ A ∷ K 0 j → Ξ ⊢ r ∷ K∋ (ix∋ j g x A) →
          Ξ ⊢ conₗ 0 (pair r unit) ∷ K⊢ (tmIx j g (kvar x) A)
⊢tm-var {Ξ} {j} {g} {x} {A} {r} dj dg dx dA dr =
  ⊢conRowₖ {Ξ} {2} {0} {JT} {D⊢} {tmIx j g (kvar x) A} {⌜ T⊢var j p c ⌝ᵗ} {pair r unit}
           {⌜ T⊢var j p c ⌝ᵗ ∷ ⌜ TCVat 0 j p c ⌝ᵗ ∷ []} nth-z ⊢JT ⊢D⊢
          (⊢tmIx dj dg (⊢kvar dj dx) dA)
          (fibK {s = 1} {k = 0} {j = j} {p = p} {c = c} (nthᵍ-s nthᵍ-z) nthʰ-z)
          (⊢tel {Ξ} {JT} {T⊢var j p c} ⊢JT ok
             ∷ᵈ ⊢tel {Ξ} {JT} {TCVat 0 j p c} ⊢JT (okTCVat (nthᵍ-s nthᵍ-z) nthʰ-z dj dp dc) ∷ᵈ []ᵈ)
          (⊢payσ {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {C⊢var_0I j (fst c) (snd c) (fst p)} {r} {unit} {T⊢varI} ok
                 (⊢conv dr (csymᵀ (ctrnᵀ (credᵀ El-⌜∋⌝) (red→≅ᵀ (⟶ᵀ*-IMu rix)))))
                 (⊢payι {Ξ} {JT} {D⊢} ⊢JT ⊢D⊢ {unit} ⊢unit))
  where
    p c ix : RTm ⌊ Ξ ⌋
    p = pair x unit
    c = pair g A
    ix = ix∋ j (fst c) (fst p) (snd c)
    dp = ⊢payK (lt-s lt-z) ok-kvar dj (a-v dx)
    dc = ⊢cTm dj dg dA
    ok : TelOK Ξ JT (T⊢var j p c)
    ok = okT⊢var dj dp dc
    rix : ix ⟶* ix∋ j g x A
    rix = ⟶*-pairʳ (⟶*-trans {t = pair (fst c) (pair (fst p) (snd c))} {u = pair g (pair (fst p) (snd c))} {v = pair g (pair x A)}
                     (⟶*-pairˡ (step (βfst g A) done))
                     (⟶*-pairʳ (⟶*-trans {t = pair (fst p) (snd c)} {u = pair x (snd c)} {v = pair x A}
                        (⟶*-pairˡ (step (βfst x unit) done)) (⟶*-pairʳ (step (βsnd g A) done)))))
