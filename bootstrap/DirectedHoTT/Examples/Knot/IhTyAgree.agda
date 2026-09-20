------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `ihTyK` AGREES WITH `ihTy`.
--
--   ihTy D dι       q M = Unit
--   ihTy D (dρ C)   q M = Σ' (subTy (single (fst q)) M)
--                            (renTy vs (ihTy D C (snd q) M))
--   ihTy D (dκ A C) q M = ihTy D C (snd q) M
--
-- ★★★ THE META CARRIES `renTy vs` ITSELF, so unlike `payTy` there is NO
--   gap between it and the object side's `wkTyK` — no bridging lemma is
--   owed.  ⇒ survey the kernel for what it already proves BEFORE
--   assuming a naturality debt: `payTy` needed `payTy-ren`, this needs
--   nothing, and `ipayTy` ships five lemmas.
--
-- ★ THREE ROWS — an ENCODED `DCon` — and row 43 is the junk, whose body
--   IS `Ty-UnitK`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhTyAgree where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; Desc; DCon; dι; dρ; dκ; app; ielim; pair
        ; fst; snd; var; vz; vs; Sub; subTm; extS; renTy; Σ'; Unit
        ; iihs; isingle; ilookupD; idrefl; ⌜Nat⌝; unit; nsuc )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; βfst; βsnd; wk-single; single; ihTy; subTy )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ; ⟶*-castᵣ )
open import DirectedHoTT.Lib.Wk using ( towerJ⁵; pw^; cong₃; cong₄; sub-w²-single )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.IMeths
  using ( cdTake; methsFrom-sel; methsFrom-past; sel-here; sel-there; inCD; tt )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ
        ; ⟶*-ielimⁱ; ⟶*-fst; ⟶*-lam; ⟶*-nsuc; ⟶*-ren )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans )
open import DirectedHoTT.Examples.Knot.Sorts using ( len; sDCon; sTy )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enTy; enTm; enDCon )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagDCon-i; tagDCon-rho; tagDCon-kap )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-SgK; Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.IhTy using ( ihTyMethsK; ihTyK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTyAtK )
open import DirectedHoTT.Examples.Knot.Single using ( singleK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK )
open import DirectedHoTT.Examples.Knot.TyAgree using ( wkTyK-agree; subTyAtK-agree )
open import DirectedHoTT.Examples.Knot.SubAgree using ( single-Represents )
open import DirectedHoTT.Examples.Knot.IExtRep using ( singleK-sub; subTmAtK-sub; subMethsK-sub )
open import DirectedHoTT.Examples.Knot.PayTyAgree
  using ( wkTyK-sub; ⟶*-wkTyKᵈ; ⟶*-wkTyKᵃ; nat4₂ )
open import DirectedHoTT.Examples.Knot.SubMot using ( subMethsK )
open import DirectedHoTT.Examples.Knot.SubNat using ( app₂-cong₃ )

-- ★ `subTyAtK`'s naturality — `subTmAtK-sub` at the OTHER sort.  Its
--   only non-structural part is the 53-row tuple.
subTyAtK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (dd m σ t : RTm Γ) →
               subTm τ (subTyAtK dd m σ t)
               ≡ subTyAtK (subTm τ dd) (subTm τ m) (subTm τ σ) (subTm τ t)
subTyAtK-sub τ dd m σ t =
  app₂-cong₃ (cong (λ z → ielim KnotD (pair sTy (subTm τ dd)) z (subTm τ t))
                   (subMethsK-sub τ))
             refl refl

-- ★ FIVE-FOLD, DERIVED FROM THE FOUR-FOLD — one `trans`, not a rewrite.
--   ⚠ `nat4₂` lives in `Knot/PayTyAgree`; the next count is always one
--     line over the previous, which is how this family should grow.
nat5₂' : (F : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ) →
         ({Γ Δ : Cx} (τ : Sub Γ Δ) (a b : RTm Γ) →
            subTm τ (F a b) ≡ F (subTm τ a) (subTm τ b)) →
         {Γ0 Γ1 Γ2 Γ3 Γ4 Γ5 : Cx}
         (τ0 : Sub Γ1 Γ0) (τ1 : Sub Γ2 Γ1) (τ2 : Sub Γ3 Γ2)
         (τ3 : Sub Γ4 Γ3) (τ4 : Sub Γ5 Γ4) (a b : RTm Γ5) →
         subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (F a b)))))
         ≡ F (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 a)))))
             (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 b)))))
nat5₂' F hF τ0 τ1 τ2 τ3 τ4 a b =
  trans (cong (subTm τ0) (nat4₂ F hF τ1 τ2 τ3 τ4 a b)) (hF τ0 _ _)

------------------------------------------------------------------------
-- ★ THE FIVE-FOLD LIFTS — `nat7`/`nat4₂` at five substitutions.
--   ⬜ FOURTH AND FIFTH instances of this shape.  It wants ONE `Lib`
--     lemma parameterised by arity and fold count; every customer so far
--     has written its own.
------------------------------------------------------------------------

-- ⚠⚠ `nat5₂` DELETED 2026-09-20 — it had the SAME TYPE as `nat5₂'`
--   twenty lines above, and was never used.  Found by
--   `tools/find-dup-lemmas.py nat5₂ 6`, which reported the pair at
--   ZERO HOLES: not "similar" — the identical statement, in the same
--   module, proved twice (one line via `nat4₂`, five lines longhand).
--   ★ The tool's premise in one hit.  This was not hidden across the
--     tree; it was TWENTY LINES APART, and it still survived every
--     reading of this module.

nat5₄ : (F : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ) →
        ({Γ Δ : Cx} (τ : Sub Γ Δ) (a b c d : RTm Γ) →
           subTm τ (F a b c d)
           ≡ F (subTm τ a) (subTm τ b) (subTm τ c) (subTm τ d)) →
        {Γ0 Γ1 Γ2 Γ3 Γ4 Γ5 : Cx}
        (τ0 : Sub Γ1 Γ0) (τ1 : Sub Γ2 Γ1) (τ2 : Sub Γ3 Γ2)
        (τ3 : Sub Γ4 Γ3) (τ4 : Sub Γ5 Γ4) (a b c d : RTm Γ5) →
        subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (F a b c d)))))
        ≡ F (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 a)))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 b)))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 c)))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 d)))))
nat5₄ F hF τ0 τ1 τ2 τ3 τ4 a b c d =
  trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 z)))) (hF τ4 a b c d))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 z))) (hF τ3 _ _ _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 z)) (hF τ2 _ _ _ _))
  (trans (cong (subTm τ0) (hF τ1 _ _ _ _)) (hF τ0 _ _ _ _))))

------------------------------------------------------------------------
-- ★ REDUCING THE DEPTH THROUGH `subTyAtK (nsuc d) d (singleK d u) t`.
--   THREE positions, and the third is under `singleK`'s own `lam`
--   (`singleK n u = lam (app (singleSK (pair sVar (nsuc (w n))) …) …)`).
--   ⇒ one lemma for the shape the row actually has, rather than three.
------------------------------------------------------------------------

⟶*-singleKᵈ : {Γ : Cx} {d d' u : RTm Γ} →
              d ⟶* d' → singleK d u ⟶* singleK d' u
⟶*-singleKᵈ h =
  ⟶*-lam (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (⟶*-ren vs h)))))

⟶*-subTyAtK-single :
  {Γ : Cx} {d d' u t : RTm Γ} → d ⟶* d' →
  subTyAtK (nsuc d) d (singleK d u) t ⟶* subTyAtK (nsuc d') d' (singleK d' u) t
⟶*-subTyAtK-single h =
    ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc h))))
  » ⟶*-appˡ (⟶*-appʳ h)
  » ⟶*-appʳ (⟶*-singleKᵈ h)

-- ★ and into `subTyAtK`'s SCRUTINEE, for the payload peel.
⟶*-subTyAtKᵃ : {Γ : Cx} {dd m σ t t' : RTm Γ} →
               t ⟶* t' → subTyAtK dd m σ t ⟶* subTyAtK dd m σ t'
⟶*-subTyAtKᵃ h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ h))

-- ★ …and into `singleK`'s VALUE, for `Tm-fstK q`.
⟶*-singleKᵛ : {Γ : Cx} {d u u' : RTm Γ} →
              u ⟶* u' → singleK d u ⟶* singleK d u'
⟶*-singleKᵛ h = ⟶*-lam (⟶*-appʳ (⟶*-ren vs h))

inSgL : {Γ : Cx} {a a' b : RTm Γ} → a ⟶* a' → Ty-SgK a b ⟶* Ty-SgK a' b
inSgL r = ⟶*-icon (⟶*-pairˡ r)

inSgR : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Ty-SgK a b ⟶* Ty-SgK a b'
inSgR r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

ihTy-agree : {Γ Θ : Cx} (D : Desc) (C : DCon) (q : RTm Γ) (M : RTy (Γ ∙)) →
             app (app (ielim KnotD (pair sDCon (num (len Γ))) ihTyMethsK
                             (enDCon {Θ} C))
                      (enTm {Γ} {Θ} q))
                 (enTy {Γ ∙} {Θ} M)
             ⟶* enTy {Γ} {Θ} (ihTy {Γ} D C q M)
ihTy-agree {Γ} {Θ} D dι       q M =
  ⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD ihTyMethsK tagDCon-i (pair sDCon (num (len Γ))) _
      (methsFrom-sel (cdTake 44 KnotD) tagDCon-i
                     (inCD (cdTake 44 KnotD) tagDCon-i tt))
      done))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
-- ★ ROW `dρ` — `Σ' (subTy (single (fst q)) M) (renTy vs (ihTy D C (snd q) M))`.
--
-- ★★★ NO BRIDGING CAST.  The META carries `renTy vs` itself, so
--   `wkTyK-agree` lands on the answer — unlike `payTy`, where the meta
--   had none and `payTy-ren` was needed.  ⇒ read the META before
--   assuming a naturality debt.
ihTy-agree {Γ} {Θ} D (dρ C)   q M =
  ⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD ihTyMethsK tagDCon-rho (pair sDCon (num (len Γ))) _
      (methsFrom-past (cdTake 44 KnotD) 0 » sel-here _ _)
      done))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  -- ⚠ THREE CALLS TO LIFT: `subTyAtK` (hides `subMethsK`), the `singleK`
  --   nested inside it, and `wkTyK` (hides `vsRenK`'s `lam`).
  » ⟶*-castₗ
      (cong₂ Ty-SgK
        (trans (nat5₄ subTyAtK subTyAtK-sub T0 T1 T2 T3 T4
                      (nsuc (snd (var (vs (vs (vs (vs vz)))))))
                      (snd (var (vs (vs (vs (vs vz))))))
                      (singleK (snd (var (vs (vs (vs (vs vz)))))) (Tm-fstK (var (vs vz))))
                      (var vz))
               (cong₄ subTyAtK (cong nsuc (cong snd tIX)) (cong snd tIX)
                      (trans (nat5₂' singleK singleK-sub T0 T1 T2 T3 T4
                                     (snd (var (vs (vs (vs (vs vz))))))
                                     (Tm-fstK (var (vs vz))))
                             (cong₂ singleK (cong snd tIX)
                                    (cong Tm-fstK (wk-single {v = enTy {Γ ∙} {Θ} M}
                                                             (enTm {Γ} {Θ} q)))))
                      refl))
        (trans (nat5₂' wkTyK wkTyK-sub T0 T1 T2 T3 T4
                       (snd (var (vs (vs (vs (vs vz))))))
                       (app (app (fst (var (vs (vs vz)))) (Tm-sndK (var (vs vz))))
                            (var vz)))
               (cong₂ wkTyK (cong snd tIX)
                      (cong₂ (λ ih qq → app (app (fst ih) (Tm-sndK qq))
                                            (enTy {Γ ∙} {Θ} M))
                             (sub-w²-single {a = enTy {Γ ∙} {Θ} M}
                                            {b = enTm {Γ} {Θ} q} IHS)
                             (wk-single {v = enTy {Γ ∙} {Θ} M} (enTm {Γ} {Θ} q))))))
   (   inSgL (⟶*-subTyAtK-single (step (βsnd _ _) done))
  » inSgL (subTyAtK-agree (single-Represents (num (len Γ))) M)
  » inSgR (⟶*-wkTyKᵈ (step (βsnd _ _) done))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done))))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done)))))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done))))))
  » inSgR (⟶*-wkTyKᵃ (ihTy-agree D C (snd q) M))
  » inSgR (wkTyK-agree (ihTy {Γ} D C (snd q) M)))
  where
    IX : RTm Θ
    IX = pair sDCon (num (len Γ))
    PAY : RTm Θ
    PAY = pair (enDCon {Θ} C) (pair (idrefl ⌜Nat⌝ sDCon) unit)
    IHS : RTm Θ
    IHS = iihs KnotD ihTyMethsK (isingle IX) (ilookupD KnotD tagDCon-rho) PAY
    T0 : Sub (Θ ∙) Θ
    T0 = single (enTy {Γ ∙} {Θ} M)
    T1 : Sub ((Θ ∙) ∙) (Θ ∙)
    T1 = extS (single (enTm {Γ} {Θ} q))
    T2 : Sub (((Θ ∙) ∙) ∙) ((Θ ∙) ∙)
    T2 = extS (extS (single IHS))
    T3 : Sub ((((Θ ∙) ∙) ∙) ∙) (((Θ ∙) ∙) ∙)
    T3 = extS (extS (extS (single PAY)))
    T4 : Sub (((((Θ ∙) ∙) ∙) ∙) ∙) ((((Θ ∙) ∙) ∙) ∙)
    T4 = extS (extS (extS (extS (single IX))))
    tIX : subTm T0 (subTm T1 (subTm T2 (subTm T3 (subTm T4
            (var (vs (vs (vs (vs vz)))))))))  ≡ IX
    tIX = towerJ⁵ (enTy {Γ ∙} {Θ} M) (enTm {Γ} {Θ} q) IHS PAY IX
-- ★ ROW `dκ` — the field is SKIPPED and the row IS its own IH, at the
--   payload's tail.  `cDCon-kap` has TWO `iρ` fields, so `fst (snd ih)`.
ihTy-agree {Γ} {Θ} D (dκ A C) q M =
  ⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD ihTyMethsK tagDCon-kap (pair sDCon (num (len Γ))) _
      (methsFrom-past (cdTake 44 KnotD) 1 » sel-there 0 _ _ (sel-here _ _))
      done))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  -- ★ FIVE βs: M 0 rungs, q 1, the IH 2, the payload 3, the index 4.
  » ⟶*-castₗ
      (cong₂ (λ ih qq → app (app (fst (snd ih)) (Tm-sndK qq)) (enTy {Γ ∙} {Θ} M))
             (sub-w²-single {a = enTy {Γ ∙} {Θ} M} {b = enTm {Γ} {Θ} q} IHS)
             (wk-single {v = enTy {Γ ∙} {Θ} M} (enTm {Γ} {Θ} q)))
   (   ⟶*-appˡ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done))))
  » ihTy-agree D C (snd q) M)
  where
    IX : RTm Θ
    IX = pair sDCon (num (len Γ))
    PAY : RTm Θ
    PAY = pair (enTy {ε} {Θ} A) (pair (enDCon {Θ} C) (pair (idrefl ⌜Nat⌝ sDCon) unit))
    IHS : RTm Θ
    IHS = iihs KnotD ihTyMethsK (isingle IX) (ilookupD KnotD tagDCon-kap) PAY
    T0 : Sub (Θ ∙) Θ
    T0 = single (enTy {Γ ∙} {Θ} M)
    T1 : Sub ((Θ ∙) ∙) (Θ ∙)
    T1 = extS (single (enTm {Γ} {Θ} q))
    T2 : Sub (((Θ ∙) ∙) ∙) ((Θ ∙) ∙)
    T2 = extS (extS (single IHS))
    T3 : Sub ((((Θ ∙) ∙) ∙) ∙) (((Θ ∙) ∙) ∙)
    T3 = extS (extS (extS (single PAY)))
    T4 : Sub (((((Θ ∙) ∙) ∙) ∙) ∙) ((((Θ ∙) ∙) ∙) ∙)
    T4 = extS (extS (extS (extS (single IX))))
    tIX : subTm T0 (subTm T1 (subTm T2 (subTm T3 (subTm T4
            (var (vs (vs (vs (vs vz)))))))))  ≡ IX
    tIX = towerJ⁵ (enTy {Γ ∙} {Θ} M) (enTm {Γ} {Θ} q) IHS PAY IX

------------------------------------------------------------------------
-- ★★★ AT THE LEDGER'S NAME.
------------------------------------------------------------------------

ihTyK-agree : {Γ Θ : Cx} (D : Desc) (C : DCon) (q : RTm Γ) (M : RTy (Γ ∙)) →
              ihTyK (num (len Γ)) (enDCon {Θ} C) (enTm {Γ} {Θ} q)
                    (enTy {Γ ∙} {Θ} M)
              ⟶* enTy {Γ} {Θ} (ihTy {Γ} D C q M)
ihTyK-agree D C q M = ihTy-agree D C q M
