------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `ipayTyK` AGREES WITH `ipayTy`.
--
--   ipayTy D I σ iι       = Unit
--   ipayTy D I σ (iρ j C) = Σ' (IMu D I (subTm σ j)) (ipayTy D I (extS σ) C)
--   ipayTy D I σ (iκ κ C) = Σ' (El (subTm σ κ))      (ipayTy D I (extS σ) C)
--
-- ★ THREE ROWS on an ENCODED `ICon`, with the substitution threaded —
--   `iihs-agree`'s shape.  ⚠ The recursion uses `extS σ` (NOT `iext`),
--   so the step is `Knot/SubExt.extS-Represents`, already discharged.
--
-- ★★ AND THE `IDesc` PASSENGER IS WEAKENED ON THE OBJECT SIDE ONLY
--   (`wkAtK sIDesc n ⌈D⌉`); `Knot/RenClosed.ren-IDesc-id` says renaming
--   a closed encoding is the identity, which is exactly the bridge.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IPayTyAgree where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )

open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; IDesc; ICon; iι; iρ; iκ; Sub; subTm; extS
        ; app; ielim; pair; ipayTy; Σ'; IMu; El; Unit )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts using ( len; sICon )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enTy; enTm; enIDesc; enICon )
open import DirectedHoTT.Examples.Knot.IPayTy using ( ipayTyMethsK )
open import DirectedHoTT.Examples.Knot.SubAgree using ( Represents )
open import DirectedHoTT.Spec.Typing
  using ( step; β; βfst; βsnd; wk-single; single )
open import DirectedHoTT.Spec.Syntax
  using ( fst; snd; var; vz; vs; nsuc; iihs; isingle; ilookupD; idrefl
        ; ⌜Nat⌝; unit; renTm )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ )
open import DirectedHoTT.Lib.Wk
  using ( towerJ; towerJ⁵; sub-w²-single; cong₃; cong₄; cong₅; cong₆ )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.IMeths
  using ( cdTake; methsFrom-sel; methsFrom-past; sel-here; sel-there; inCD; tt )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ
        ; ⟶*-ielimⁱ; ⟶*-fst; ⟶*-nsuc )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagICon-i; tagICon-rho; tagICon-kap )
open import DirectedHoTT.Examples.Knot.Sorts using ( sIDesc; sTy )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-SgK; Ty-IMuK; Ty-ElK )
open import DirectedHoTT.Examples.Knot.Desc using ( cICon-rho; cICon-kap )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK )
open import DirectedHoTT.Examples.Knot.SubNat using ( extNK-sub )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkAtK )
open import DirectedHoTT.Examples.Knot.RenTm using ( renTmAtK; vsRenK; renMethsK )
open import DirectedHoTT.Examples.Knot.SubSpec using ( renMethsK-sub; vsRenK-sub )
open import DirectedHoTT.Examples.Knot.SubExt using ( extS-Represents )
open import DirectedHoTT.Examples.Knot.SubAgreeTie using ( sub-agree )
open import DirectedHoTT.Examples.Knot.RenClosed using ( ren-IDesc-id )
open import DirectedHoTT.Examples.Knot.IExtRep
  using ( subTmAtK-sub; ⟶*-subTmAtK; ⟶*-subTmAtKᵈ )
open import DirectedHoTT.Examples.Knot.IihsAgree using ( nat7; tower⁶; tower⁷ )

------------------------------------------------------------------------
-- ★ `wkAtK`'s NATURALITY, GENERIC IN THE SORT.
--   `Knot/PayTyAgree.wkTyK-sub` is this at `sTy`; the `iρ`/`iκ` rows
--   weaken an `IDesc`, so the sort must be a parameter.
------------------------------------------------------------------------

wkAtK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (so n t : RTm Γ) →
            subTm τ (wkAtK so n t)
            ≡ wkAtK (subTm τ so) (subTm τ n) (subTm τ t)
wkAtK-sub τ so n t =
  cong₂ (λ ms rn → app (app (ielim KnotD (pair (subTm τ so) (subTm τ n)) ms
                                   (subTm τ t))
                            (nsuc (subTm τ n))) rn)
        (renMethsK-sub τ) (vsRenK-sub τ n)

-- ★ the 3-ary seven-fold lift — `Knot/IihsAgree.nat7` is the 4-ary one.
nat7₃ : (F : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ) →
        ({Γ Δ : Cx} (τ : Sub Γ Δ) (a b c : RTm Γ) →
           subTm τ (F a b c) ≡ F (subTm τ a) (subTm τ b) (subTm τ c)) →
        {Γ0 Γ1 Γ2 Γ3 Γ4 Γ5 Γ6 Γ7 : Cx}
        (τ0 : Sub Γ1 Γ0) (τ1 : Sub Γ2 Γ1) (τ2 : Sub Γ3 Γ2) (τ3 : Sub Γ4 Γ3)
        (τ4 : Sub Γ5 Γ4) (τ5 : Sub Γ6 Γ5) (τ6 : Sub Γ7 Γ6) (a b c : RTm Γ7) →
        subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 (F a b c)))))))
        ≡ F (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 a)))))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 b)))))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (subTm τ6 c)))))))
nat7₃ F hF τ0 τ1 τ2 τ3 τ4 τ5 τ6 a b c =
  trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 z)))))) (hF τ6 a b c))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 z))))) (hF τ5 _ _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 z)))) (hF τ4 _ _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 z))) (hF τ3 _ _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 z)) (hF τ2 _ _ _))
  (trans (cong (subTm τ0) (hF τ1 _ _ _)) (hF τ0 _ _ _))))))

inSgL : {Γ : Cx} {a a' b : RTm Γ} → a ⟶* a' → Ty-SgK a b ⟶* Ty-SgK a' b
inSgL r = ⟶*-icon (⟶*-pairˡ r)

inSgR : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Ty-SgK a b ⟶* Ty-SgK a b'
inSgR r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

-- ★ `Ty-IMuK a b c` — the THIRD slot is the index.
inIMu₂ : {Γ : Cx} {a b c c' : RTm Γ} →
         c ⟶* c' → Ty-IMuK a b c ⟶* Ty-IMuK a b c'
inIMu₂ r = ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ r)))

inEl : {Γ : Cx} {a a' : RTm Γ} → a ⟶* a' → Ty-ElK a ⟶* Ty-ElK a'
inEl r = ⟶*-icon (⟶*-pairˡ r)

ipayTy-agree : {Γ Δ Θ : Cx} (D : IDesc) (I : RTy ε) {σ : Sub Δ Γ} {s : RTm Θ} →
               Represents σ s → (C : ICon Δ) →
               app (app (app (app (ielim KnotD (pair sICon (num (len Δ)))
                                          ipayTyMethsK (enICon C))
                                  (num (len Γ)))
                             s)
                        (enIDesc {Θ} D))
                   (enTy {ε} {Θ} I)
               ⟶* enTy {Γ} {Θ} (ipayTy {Γ} D I σ C)
-- ★ ROW `iι` — tag 48 is inside `methsFrom`'s 49-row prefix, so the
--   JUNK method answers and its body IS `Ty-UnitK` = `enTy Unit`.
ipayTy-agree {Γ} {Δ} D I h iι       =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD ipayTyMethsK tagICon-i (pair sICon (num (len Δ))) _
      (methsFrom-sel (cdTake 49 KnotD) tagICon-i
                     (inCD (cdTake 49 KnotD) tagICon-i tt))
      done))))  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
-- ★ ROW `iρ` — `Σ' (IMu D I (subTm σ j)) (ipayTy D I (extS σ) C)`.
--   ⚠ THREE LIFTED CALLS: `subTmAtK` (hides `subMethsK`), `extNK` and
--     `wkAtK` (both build a `lam`).
ipayTy-agree {Γ} {Δ} {Θ} D I {σ = σ} {s = s} h (iρ j C) =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD ipayTyMethsK tagICon-rho (pair sICon (num (len Δ))) _
      (methsFrom-past (cdTake 49 KnotD) 0 » sel-here _ _)
      done))))  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  » ⟶*-castₗ
      (cong₆ (λ dv nv ihv sub extk wk →
                Ty-SgK (Ty-IMuK dv (enTy {ε} {Θ} I) sub)
                       (app (app (app (app (fst (snd ihv)) (nsuc nv)) extk) wk)
                            (enTy {ε} {Θ} I)))
             tD tN tIH eSub eExt eWk)
   (   inSgL (inIMu₂ (⟶*-subTmAtKᵈ (step (βsnd _ _) done)))
  » inSgL (inIMu₂ (⟶*-subTmAtK (step (βfst _ _) done)))
  » inSgL (inIMu₂ (sub-agree h j))
  »        inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done))))))
  » inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)))))
  » inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (step (βsnd _ _) done))))))))
  » inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done)))))))
  » inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))))))
  » inSgR (⟶*-appˡ (⟶*-appʳ (ren-IDesc-id (len Γ) (suc (len Γ)) _ D)))
  » inSgR (ipayTy-agree D I (extS-Represents (snd IX) h) C))
  where
    IX : RTm Θ
    IX = pair sICon (num (len Δ))
    PAY : RTm Θ
    PAY = pair (enTm j) (pair (enICon C) (pair (idrefl ⌜Nat⌝ sICon) unit))
    IHS : RTm Θ
    IHS = iihs KnotD ipayTyMethsK (isingle IX) (ilookupD KnotD tagICon-rho) PAY
    T0 : Sub (Θ ∙) Θ
    T0 = single (enTy {ε} {Θ} I)
    T1 : Sub ((Θ ∙) ∙) (Θ ∙)
    T1 = extS (single (enIDesc {Θ} D))
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
    tD  = wk-single {v = enTy {ε} {Θ} I} (enIDesc {Θ} D)
    tSB = sub-w²-single {a = enTy {ε} {Θ} I} {b = enIDesc {Θ} D} s
    tN  = towerJ (enTy {ε} {Θ} I) (enIDesc {Θ} D) s (num (len Γ))
    tIH = towerJ⁵ (enTy {ε} {Θ} I) (enIDesc {Θ} D) s (num (len Γ)) IHS
    tPY = tower⁶ (enTy {ε} {Θ} I) (enIDesc {Θ} D) s (num (len Γ)) IHS PAY
    tIX = tower⁷ (enTy {ε} {Θ} I) (enIDesc {Θ} D) s (num (len Γ)) IHS PAY IX
    eSub = trans (nat7 subTmAtK subTmAtK-sub T0 T1 T2 T3 T4 T5 T6
                       (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                       (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                       (fst (var (vs (vs (vs (vs (vs vz))))))))
                 (cong₄ subTmAtK (cong snd tIX) tN tSB (cong fst tPY))
    eExt = trans (nat7₃ extNK extNK-sub T0 T1 T2 T3 T4 T5 T6
                        (snd (var (vs (vs (vs (vs (vs (vs vz)))))))) 
                        (var (vs (vs (vs vz)))) (var (vs (vs vz))))
                 (cong₃ extNK (cong snd tIX) tN tSB)
    eWk  = trans (nat7₃ wkAtK wkAtK-sub T0 T1 T2 T3 T4 T5 T6
                        sIDesc (var (vs (vs (vs vz)))) (var (vs vz)))
                 (cong₃ wkAtK refl tN tD)
-- ★ ROW `iκ` — the same, with `El` in place of `IMu`.
ipayTy-agree {Γ} {Δ} {Θ} D I {σ = σ} {s = s} h (iκ κ C) =
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
    (ihead-red KnotD ipayTyMethsK tagICon-kap (pair sICon (num (len Δ))) _
      (methsFrom-past (cdTake 49 KnotD) 1 » sel-there 0 _ _ (sel-here _ _))
      done))))  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  » ⟶*-castₗ
      (cong₆ (λ dv nv ihv sub extk wk →
                Ty-SgK (Ty-ElK sub)
                       (app (app (app (app (fst (snd ihv)) (nsuc nv)) extk) wk)
                            (enTy {ε} {Θ} I)))
             tD tN tIH eSub eExt eWk)
   (   inSgL (inEl (⟶*-subTmAtKᵈ (step (βsnd _ _) done)))
  » inSgL (inEl (⟶*-subTmAtK (step (βfst _ _) done)))
  » inSgL (inEl (sub-agree h κ))
  »        inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done))))))
  » inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)))))
  » inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (step (βsnd _ _) done))))))))
  » inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
      (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done)))))))
  » inSgR (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))))))
  » inSgR (⟶*-appˡ (⟶*-appʳ (ren-IDesc-id (len Γ) (suc (len Γ)) _ D)))
  » inSgR (ipayTy-agree D I (extS-Represents (snd IX) h) C))
  where
    IX : RTm Θ
    IX = pair sICon (num (len Δ))
    PAY : RTm Θ
    PAY = pair (enTm κ) (pair (enICon C) (pair (idrefl ⌜Nat⌝ sICon) unit))
    IHS : RTm Θ
    IHS = iihs KnotD ipayTyMethsK (isingle IX) (ilookupD KnotD tagICon-kap) PAY
    T0 : Sub (Θ ∙) Θ
    T0 = single (enTy {ε} {Θ} I)
    T1 : Sub ((Θ ∙) ∙) (Θ ∙)
    T1 = extS (single (enIDesc {Θ} D))
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
    tD  = wk-single {v = enTy {ε} {Θ} I} (enIDesc {Θ} D)
    tSB = sub-w²-single {a = enTy {ε} {Θ} I} {b = enIDesc {Θ} D} s
    tN  = towerJ (enTy {ε} {Θ} I) (enIDesc {Θ} D) s (num (len Γ))
    tIH = towerJ⁵ (enTy {ε} {Θ} I) (enIDesc {Θ} D) s (num (len Γ)) IHS
    tPY = tower⁶ (enTy {ε} {Θ} I) (enIDesc {Θ} D) s (num (len Γ)) IHS PAY
    tIX = tower⁷ (enTy {ε} {Θ} I) (enIDesc {Θ} D) s (num (len Γ)) IHS PAY IX
    eSub = trans (nat7 subTmAtK subTmAtK-sub T0 T1 T2 T3 T4 T5 T6
                       (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                       (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                       (fst (var (vs (vs (vs (vs (vs vz))))))))
                 (cong₄ subTmAtK (cong snd tIX) tN tSB (cong fst tPY))
    eExt = trans (nat7₃ extNK extNK-sub T0 T1 T2 T3 T4 T5 T6
                        (snd (var (vs (vs (vs (vs (vs (vs vz)))))))) 
                        (var (vs (vs (vs vz)))) (var (vs (vs vz))))
                 (cong₃ extNK (cong snd tIX) tN tSB)
    eWk  = trans (nat7₃ wkAtK wkAtK-sub T0 T1 T2 T3 T4 T5 T6
                        sIDesc (var (vs (vs (vs vz)))) (var (vs vz)))
                 (cong₃ wkAtK refl tN tD)

------------------------------------------------------------------------
-- ★★★ AT THE LEDGER'S NAME.
------------------------------------------------------------------------

open import DirectedHoTT.Examples.Knot.IPayTy using ( ipayTyK )

ipayTyK-agree : {Γ Δ Θ : Cx} (D : IDesc) (I : RTy ε) {σ : Sub Δ Γ} {s : RTm Θ} →
                Represents σ s → (C : ICon Δ) →
                ipayTyK (num (len Δ)) (enICon C) (num (len Γ)) s
                        (enIDesc {Θ} D) (enTy {ε} {Θ} I)
                ⟶* enTy {Γ} {Θ} (ipayTy {Γ} D I σ C)
ipayTyK-agree D I h C = ipayTy-agree D I h C
