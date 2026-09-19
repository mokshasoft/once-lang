------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `iihTyK` AGREES WITH `iihTy`.
--
-- ⚠⚠ THE MOST EXPENSIVE MODULE IN THE TREE: 3482 s (58 min), MEASURED.
--   The `iρ` row's cast nests `nat7 iinstK` inside `cong₂ Ty-SgK` beside
--   `nat7₂ wkTyK`, and `iinstK` itself unfolds to FOUR nested programs
--   (`subTyAtK` twice, `extNK`, `singleK` twice).  Seven `trans`/`cong`
--   layers over that is an enormous elaborated term.
--   ★ INLINE IT DID NOT FINISH IN 40 MINUTES; `where`-binding the three
--     lifts (`eIinst`, `eWk`, `eApp`) is what made it terminate at all.
--     `agda-cost-is-elaborated-term-size`, at the CAST rather than at a
--     datatype.
--   ⬜ OWED: move the cast equalities into their own module so they are
--     `Def`-backed ACROSS a module boundary and elaborated once —
--     `Knot/IhTyRho`/`IhTyKap` are split for exactly this reason and the
--     split is measured there too.  Not done; the entry is proved and
--     the restructuring is separable.
--
--   iihTy D I σ iι       q M = Unit
--   iihTy D I σ (iρ j C) q M =
--     Σ' (iinst (subTm σ j) (fst q) M)
--        (renTy vs (iihTy D I (iext σ (fst q)) C (snd q) M))
--   iihTy D I σ (iκ κ C) q M = iihTy D I (iext σ (fst q)) C (snd q) M
--
-- ★★★ EVERY INGREDIENT IS ALREADY DISCHARGED, and three of them by this
--   session's own earlier entries:
--     iinst-agree      ✅ Knot/IExtAgree
--     iext-Represents  ✅ Knot/IExtRep      ← the recursion uses `iext`,
--                                             NOT `extS` as `ipayTy` did
--     sub-agree        ✅ Knot/SubAgreeTie
--     wkTyK-agree      ✅ Knot/TyAgree      (the meta carries `renTy vs`)
--
-- ★ AND BOTH REAL ROWS SHARE ONE SPINE (`IhITyRows.ihApp`), so the `iκ`
--   row IS the `iρ` row's second component.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhITyAgree where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; IDesc; ICon; iι; iρ; iκ; Sub; subTm; extS
        ; app; ielim; pair; fst; snd; var; vz; vs; nsuc; iihs; isingle
        ; ilookupD; idrefl; ⌜Nat⌝; unit; iext; renTy; lam )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; βfst; βsnd; wk-single; single; iihTy; iinst )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.Wk
  using ( towerJ; towerJ⁵; sub-w²-single; cong₃; cong₄; cong₅ )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.IMeths
  using ( cdTake; methsFrom-sel; methsFrom-past; sel-here; sel-there; inCD; tt )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ
        ; ⟶*-ielimⁱ; ⟶*-fst; ⟶*-nsuc; ⟶*-lam; ⟶*-ren )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans )
open import DirectedHoTT.Examples.Knot.Sorts using ( len; sICon; sTy )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enTy; enTm; enICon )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagICon-i; tagICon-rho; tagICon-kap )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-SgK; Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.IhITy using ( iihTyMethsK; iihTyK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK; subTyAtK )
open import DirectedHoTT.Examples.Knot.Single using ( singleK )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK )
open import DirectedHoTT.Examples.Knot.SubNat using ( extNK-sub )
open import DirectedHoTT.Examples.Knot.IExt using ( iextK; iinstK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK )
open import DirectedHoTT.Examples.Knot.SubAgree using ( Represents; single-Represents )
open import DirectedHoTT.Examples.Knot.SubAgreeTie using ( sub-agree )
open import DirectedHoTT.Examples.Knot.TyAgree using ( wkTyK-agree )
open import DirectedHoTT.Examples.Knot.IExtAgree using ( iinst-agree )
open import DirectedHoTT.Examples.Knot.IExtRep
  using ( iext-Represents; iextK-sub; singleK-sub; subTmAtK-sub
        ; ⟶*-subTmAtK; ⟶*-subTmAtKᵈ )
open import DirectedHoTT.Examples.Knot.PayTyAgree
  using ( wkTyK-sub; ⟶*-wkTyKᵃ )
open import DirectedHoTT.Examples.Knot.IhTyAgree
  using ( subTyAtK-sub; ⟶*-subTyAtKᵃ; ⟶*-singleKᵛ )
open import DirectedHoTT.Examples.Knot.IPayTyAgree using ( nat7₃; inSgL; inSgR )
open import DirectedHoTT.Examples.Knot.IihsAgree using ( nat7; tower⁶; tower⁷ )
open import DirectedHoTT.Examples.Knot.DepthCong using ( ⟶*-subAtˢ )

------------------------------------------------------------------------
-- ★ REACHING `iinstK`'s INDEX ARGUMENT.
--
--   iinstK n i t M = subTyAtK (nsuc n) n (singleK n t)
--                      (subTyAtK (nsuc (nsuc n)) (nsuc n)
--                                (extNK (nsuc n) n (singleK n i)) M)
--
--   so `i` sits under `singleK`'s `lam`, inside `extNK`'s σ slot, inside
--   the INNER `subTyAtK`'s σ slot, inside the outer one's scrutinee.
------------------------------------------------------------------------

⟶*-extNKˢ : {Γ : Cx} {d n σ σ' : RTm Γ} →
            σ ⟶* σ' → extNK d n σ ⟶* extNK d n σ'
⟶*-extNKˢ h = ⟶*-lam (⟶*-appʳ (⟶*-ren vs h))

⟶*-iinstKⁱ : {Γ : Cx} {n i i' t M : RTm Γ} →
             i ⟶* i' → iinstK n i t M ⟶* iinstK n i' t M
⟶*-iinstKⁱ h = ⟶*-subTyAtKᵃ (⟶*-subAtˢ (⟶*-extNKˢ (⟶*-singleKᵛ h)))

-- ★ and `iinstK`'s own naturality, for the cast.
iinstK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n i t M : RTm Γ) →
             subTm τ (iinstK n i t M)
             ≡ iinstK (subTm τ n) (subTm τ i) (subTm τ t) (subTm τ M)
iinstK-sub τ n i t M =
  trans (subTyAtK-sub τ (nsuc n) n (singleK n t)
                        (subTyAtK (nsuc (nsuc n)) (nsuc n)
                                  (extNK (nsuc n) n (singleK n i)) M))
        (cong₄ subTyAtK refl refl (singleK-sub τ n t)
               (trans (subTyAtK-sub τ (nsuc (nsuc n)) (nsuc n)
                                      (extNK (nsuc n) n (singleK n i)) M)
                      (cong₄ subTyAtK refl refl
                             (trans (extNK-sub τ (nsuc n) n (singleK n i))
                                    (cong₃ extNK refl refl (singleK-sub τ n i)))
                             refl)))

-- ★ the 2-ary seven-fold lift, for `wkTyK`.
nat7₂ : (F : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ) →
        ({Γ Δ : Cx} (τ : Sub Γ Δ) (a b : RTm Γ) →
           subTm τ (F a b) ≡ F (subTm τ a) (subTm τ b)) →
        {Γ0 Γ1 Γ2 Γ3 Γ4 Γ5 Γ6 Γ7 : Cx}
        (τ0 : Sub Γ1 Γ0) (τ1 : Sub Γ2 Γ1) (τ2 : Sub Γ3 Γ2) (τ3 : Sub Γ4 Γ3)
        (τ4 : Sub Γ5 Γ4) (τ5 : Sub Γ6 Γ5) (τ6 : Sub Γ7 Γ6) (a b : RTm Γ7) →
        subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 (F a b)))))))
        ≡ F (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 a)))))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 b)))))))
nat7₂ F hF τ0 τ1 τ2 τ3 τ4 τ5 τ6 a b =
  trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 z)))))) (hF τ6 a b))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 z))))) (hF τ5 _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 z)))) (hF τ4 _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 z))) (hF τ3 _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 z)) (hF τ2 _ _))
  (trans (cong (subTm τ0) (hF τ1 _ _)) (hF τ0 _ _))))))

iihTy-agree : {Γ Δ Θ : Cx} (D : IDesc) (I : RTy ε) {σ : Sub Δ Γ} {s : RTm Θ} →
              Represents σ s → (C : ICon Δ) (q : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
              app (app (app (app (ielim KnotD (pair sICon (num (len Δ)))
                                         iihTyMethsK (enICon C))
                                 (num (len Γ)))
                            s)
                       (enTm {Γ} {Θ} q))
                  (enTy {(Γ ∙) ∙} {Θ} M)
              ⟶* enTy {Γ} {Θ} (iihTy {Γ} D I σ C q M)
-- ★ ROW `iι` — tag 48, the junk method, body `Ty-UnitK` = `enTy Unit`.
iihTy-agree {Γ} {Δ} D I h iι       q M =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD iihTyMethsK tagICon-i (pair sICon (num (len Δ))) _
      (methsFrom-sel (cdTake 49 KnotD) tagICon-i
                     (inCD (cdTake 49 KnotD) tagICon-i tt))
      done))))  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
-- ★ ROW `iρ` — `Σ' (iinst (subTm σ j) (fst q) M) (renTy vs (…IH…))`.
--   ⚠ The meta carries `renTy vs`, so `wkTyK-agree` lands on the answer
--     and NO bridging cast is owed — `ihTy`'s situation, not `payTy`'s.
iihTy-agree {Γ} {Δ} {Θ} D I {σ = σ} {s = s} h (iρ j C) q M =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD iihTyMethsK tagICon-rho (pair sICon (num (len Δ))) _
      (methsFrom-past (cdTake 49 KnotD) 0 » sel-here _ _)
      done))))  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  -- ⚠ THE THREE LIFTS ARE `where`-BOUND, NOT INLINE.  Inline, this
  --   clause did not finish in FORTY MINUTES: each `nat7` expands to
  --   seven `trans`/`cong` layers over the whole seven-substitution
  --   stack, and nesting two of them inside a third multiplies the
  --   ELABORATED TERM.  Naming them gives Agda a `Def` to share.
  --   `agda-cost-is-elaborated-term-size`, at the cast rather than the
  --   datatype.
  » ⟶*-castₗ (cong₂ Ty-SgK eIinst eWk)
   (   inSgL (⟶*-iinstKⁱ (⟶*-subTmAtKᵈ (step (βsnd _ _) done)))
  » inSgL (⟶*-iinstKⁱ (⟶*-subTmAtK (step (βfst _ _) done)))
  » inSgL (⟶*-iinstKⁱ (sub-agree h j))
  » inSgL (iinst-agree (subTm σ j) (fst q) M)
  » inSgR (⟶*-wkTyKᵃ (       ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (step (βsnd _ _) done)))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done)))))
  » iihTy-agree D I (iext-Represents (snd IX) (fst q) h) C (snd q) M))
  » inSgR (wkTyK-agree {Γ} (iihTy {Γ} D I (iext σ (fst q)) C (snd q) M)))
  where
    IX : RTm Θ
    IX = pair sICon (num (len Δ))
    PAY : RTm Θ
    PAY = pair (enTm j) (pair (enICon C) (pair (idrefl ⌜Nat⌝ sICon) unit))
    IHS : RTm Θ
    IHS = iihs KnotD iihTyMethsK (isingle IX) (ilookupD KnotD tagICon-rho) PAY
    T0 : Sub (Θ ∙) Θ
    T0 = single (enTy {(Γ ∙) ∙} {Θ} M)
    T1 : Sub ((Θ ∙) ∙) (Θ ∙)
    T1 = extS (single (enTm {Γ} {Θ} q))
    T2 : Sub (((Θ ∙) ∙) ∙) ((Θ ∙) ∙)
    T2 = extS (extS (single s))
    T3 : Sub ((((Θ ∙) ∙) ∙) ∙) (((Θ ∙) ∙) ∙)
    T3 = extS (extS (extS (single (num (len Γ)))))
    T4 : Sub (((((Θ ∙) ∙) ∙) ∙) ∙) ((((Θ ∙) ∙) ∙) ∙)
    T4 = extS (extS (extS (extS (single IHS))))
    T5 : Sub ((((((Θ ∙) ∙) ∙) ∙) ∙) ∙) (((((Θ ∙) ∙) ∙) ∙) ∙)
    T5 = extS (extS (extS (extS (extS (single PAY)))))
    T6 : Sub (((((((Θ ∙) ∙) ∙) ∙) ∙) ∙) ∙) ((((((Θ ∙) ∙) ∙) ∙) ∙) ∙)
    T6 = extS (extS (extS (extS (extS (extS (single IX))))))
    tQ  = wk-single {v = enTy {(Γ ∙) ∙} {Θ} M} (enTm {Γ} {Θ} q)
    tSB = sub-w²-single {a = enTy {(Γ ∙) ∙} {Θ} M} {b = enTm {Γ} {Θ} q} s
    tN  = towerJ (enTy {(Γ ∙) ∙} {Θ} M) (enTm {Γ} {Θ} q) s (num (len Γ))
    tIH = towerJ⁵ (enTy {(Γ ∙) ∙} {Θ} M) (enTm {Γ} {Θ} q) s (num (len Γ)) IHS
    tPY = tower⁶ (enTy {(Γ ∙) ∙} {Θ} M) (enTm {Γ} {Θ} q) s (num (len Γ)) IHS PAY
    tIX = tower⁷ (enTy {(Γ ∙) ∙} {Θ} M) (enTm {Γ} {Θ} q) s (num (len Γ)) IHS PAY IX
    eIext = trans (nat7 iextK iextK-sub T0 T1 T2 T3 T4 T5 T6
                        (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                        (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                        (Tm-fstK (var (vs vz))))
                  (cong₄ iextK (cong snd tIX) tN tSB (cong Tm-fstK tQ))
    eApp = cong₄ (λ ihv nv ext qq →
                    app (app (app (app (fst (snd ihv)) nv) ext) (Tm-sndK qq))
                        (enTy {(Γ ∙) ∙} {Θ} M))
                 tIH tN eIext tQ
    eSub = trans (nat7 subTmAtK subTmAtK-sub T0 T1 T2 T3 T4 T5 T6
                       (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                       (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                       (fst (var (vs (vs (vs (vs (vs vz))))))))
                 (cong₄ subTmAtK (cong snd tIX) tN tSB (cong fst tPY))
    eIinst = trans (nat7 iinstK iinstK-sub T0 T1 T2 T3 T4 T5 T6
                         (var (vs (vs (vs vz))))
                         (subTmAtK (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                                   (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                                   (fst (var (vs (vs (vs (vs (vs vz))))))))
                         (Tm-fstK (var (vs vz))) (var vz))
                   (cong₄ iinstK tN eSub (cong Tm-fstK tQ) refl)
    eWk = trans (nat7₂ wkTyK wkTyK-sub T0 T1 T2 T3 T4 T5 T6
                       (var (vs (vs (vs vz))))
                       (app (app (app (app (fst (snd (var (vs (vs (vs (vs vz)))))))
                                           (var (vs (vs (vs vz)))))
                                      (iextK (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                                             (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                                             (Tm-fstK (var (vs vz)))))
                                 (Tm-sndK (var (vs vz))))
                            (var vz)))
                (cong₂ wkTyK tN eApp)
-- ★ ROW `iκ` — the body IS `ihApp`, so this row is the `iρ` row's
--   second component with no wrapper.
iihTy-agree {Γ} {Δ} {Θ} D I {σ = σ} {s = s} h (iκ κ C) q M =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD iihTyMethsK tagICon-kap (pair sICon (num (len Δ))) _
      (methsFrom-past (cdTake 49 KnotD) 1 » sel-there 0 _ _ (sel-here _ _))
      done))))  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  » ⟶*-castₗ eApp
   (          ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (step (βsnd _ _) done)))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done)))))
  » iihTy-agree D I (iext-Represents (snd IX) (fst q) h) C (snd q) M)
  where
    IX : RTm Θ
    IX = pair sICon (num (len Δ))
    PAY : RTm Θ
    PAY = pair (enTm κ) (pair (enICon C) (pair (idrefl ⌜Nat⌝ sICon) unit))
    IHS : RTm Θ
    IHS = iihs KnotD iihTyMethsK (isingle IX) (ilookupD KnotD tagICon-kap) PAY
    T0 : Sub (Θ ∙) Θ
    T0 = single (enTy {(Γ ∙) ∙} {Θ} M)
    T1 : Sub ((Θ ∙) ∙) (Θ ∙)
    T1 = extS (single (enTm {Γ} {Θ} q))
    T2 : Sub (((Θ ∙) ∙) ∙) ((Θ ∙) ∙)
    T2 = extS (extS (single s))
    T3 : Sub ((((Θ ∙) ∙) ∙) ∙) (((Θ ∙) ∙) ∙)
    T3 = extS (extS (extS (single (num (len Γ)))))
    T4 : Sub (((((Θ ∙) ∙) ∙) ∙) ∙) ((((Θ ∙) ∙) ∙) ∙)
    T4 = extS (extS (extS (extS (single IHS))))
    T5 : Sub ((((((Θ ∙) ∙) ∙) ∙) ∙) ∙) (((((Θ ∙) ∙) ∙) ∙) ∙)
    T5 = extS (extS (extS (extS (extS (single PAY)))))
    T6 : Sub (((((((Θ ∙) ∙) ∙) ∙) ∙) ∙) ∙) ((((((Θ ∙) ∙) ∙) ∙) ∙) ∙)
    T6 = extS (extS (extS (extS (extS (extS (single IX))))))
    tQ  = wk-single {v = enTy {(Γ ∙) ∙} {Θ} M} (enTm {Γ} {Θ} q)
    tSB = sub-w²-single {a = enTy {(Γ ∙) ∙} {Θ} M} {b = enTm {Γ} {Θ} q} s
    tN  = towerJ (enTy {(Γ ∙) ∙} {Θ} M) (enTm {Γ} {Θ} q) s (num (len Γ))
    tIH = towerJ⁵ (enTy {(Γ ∙) ∙} {Θ} M) (enTm {Γ} {Θ} q) s (num (len Γ)) IHS
    tPY = tower⁶ (enTy {(Γ ∙) ∙} {Θ} M) (enTm {Γ} {Θ} q) s (num (len Γ)) IHS PAY
    tIX = tower⁷ (enTy {(Γ ∙) ∙} {Θ} M) (enTm {Γ} {Θ} q) s (num (len Γ)) IHS PAY IX
    eIext = trans (nat7 iextK iextK-sub T0 T1 T2 T3 T4 T5 T6
                        (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                        (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                        (Tm-fstK (var (vs vz))))
                  (cong₄ iextK (cong snd tIX) tN tSB (cong Tm-fstK tQ))
    eApp = cong₄ (λ ihv nv ext qq →
                    app (app (app (app (fst (snd ihv)) nv) ext) (Tm-sndK qq))
                        (enTy {(Γ ∙) ∙} {Θ} M))
                 tIH tN eIext tQ

------------------------------------------------------------------------
-- ★★★ AT THE LEDGER'S NAME.
------------------------------------------------------------------------

iihTyK-agree : {Γ Δ Θ : Cx} (D : IDesc) (I : RTy ε) {σ : Sub Δ Γ} {s : RTm Θ} →
               Represents σ s → (C : ICon Δ) (q : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
               iihTyK (num (len Δ)) (enICon C) (num (len Γ)) s
                      (enTm {Γ} {Θ} q) (enTy {(Γ ∙) ∙} {Θ} M)
               ⟶* enTy {Γ} {Θ} (iihTy {Γ} D I σ C q M)
iihTyK-agree D I h C q M = iihTy-agree D I h C q M
