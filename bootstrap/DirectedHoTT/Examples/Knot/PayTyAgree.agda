------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `payTyK` AGREES WITH `payTy`.
--
--   payTy D dι       = Unit
--   payTy D (dρ C)   = Σ' (Mu D)    (payTy D C)
--   payTy D (dκ A C) = Σ' (εwkTy A) (payTy D C)
--
-- ★ THREE ROWS — it eliminates an ENCODED `DCon`.  Row 43 (`dι`) is the
--   JUNK method and its body IS `Ty-UnitK` = `enTy Unit`, so that row is
--   free, exactly as `lookupD`'s `dnil` was.
--
-- ★★ THE SECOND COMPONENT SITS UNDER `Σ'`'s BINDER, and the object side
--   weakens it EXPLICITLY (`wkAtK` = `wkTyK`).  The meta does not — but
--   `Spec/Typing.payTy-ren` says `renTy ρ (payTy D C) ≡ payTy D C`, so
--   the two agree after one cast.  ⇒ the kernel's own naturality lemma
--   is what closes the gap, not a new one.
--
-- ⚠ THE INDEX IS PINNED at `pair sDCon ⌈|Γ|⌉`: the rows READ it
--   (`snd ⟨i⟩` is the depth `wkAtK`/`εwkK` need), and `cDCon-rho`'s field
--   sits at the SAME depth, so one `βsnd` returns the child to the
--   pinned form.  `iihs-agree`'s rule — pin only what the child reduces
--   to.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PayTyAgree where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; Desc; DCon; dι; dρ; dκ; app; ielim; pair; payTy )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts using ( len; sDCon )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enTy; enDesc; enDCon )
open import DirectedHoTT.Examples.Knot.PayTy using ( payTyMethsK )
open import DirectedHoTT.Spec.Typing
  using ( step; β; βfst; βsnd; wk-single; single )
open import DirectedHoTT.Spec.Syntax
  using ( fst; snd; var; vz; vs; lam; renTm; iihs; isingle; ilookupD
        ; idrefl; ⌜Nat⌝; unit; nsuc; Mu; Unit; Σ'; εwkTy; RTy; payTy-ren )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ; ⟶*-castᵣ )
open import DirectedHoTT.Lib.Wk using ( towerJ; sub-w²-single; cong₃ )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.IMeths
  using ( cdTake; methsFrom-sel; methsFrom-past; sel-here; sel-there; inCD; tt )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-lam; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ
        ; ⟶*-ielimᵗ; ⟶*-ielimⁱ; ⟶*-nsuc; ⟶*-idreflᵃ; ⟶*-ren; ⟶*-fst )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagDCon-i; tagDCon-rho; tagDCon-kap )
open import DirectedHoTT.Examples.Knot.Sorts using ( sTy )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-SgK; Ty-MuK; Var-vsK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK; wkAtK )
open import DirectedHoTT.Examples.Knot.TyAgree using ( wkTyK-agree )
open import DirectedHoTT.Examples.Knot.SubAgreeTyTie using ( sub-agree-ty )
open import DirectedHoTT.Examples.Knot.EWk using ( εwkK )

-- ★ the congruence into `wkTyK`'s TERM argument (its depth needs the
--   four-way one above; its term needs only this).
⟶*-wkTyKᵃ : {Γ : Cx} {n A A' : RTm Γ} → A ⟶* A' → wkTyK n A ⟶* wkTyK n A'
⟶*-wkTyKᵃ h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ h))

-- ★ `Ty-SgK a b = icon tagTy-Sg (pair a (pair b (pair … unit)))`.
inSgL : {Γ : Cx} {a a' b : RTm Γ} → a ⟶* a' → Ty-SgK a b ⟶* Ty-SgK a' b
inSgL r = ⟶*-icon (⟶*-pairˡ r)

inSgR : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Ty-SgK a b ⟶* Ty-SgK a b'
inSgR r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

-- ★★ `εwkK`'s AGREEMENT, and the ledger's *"not owed — its argument is
--   CLOSED"* is why it is one line: `εwkTy = subTy εsub` and `εsub`'s
--   `Represents` is VACUOUS, `λ ()`, because `Var ε` is empty.
εwkK-agree : {Γ Θ : Cx} (A : RTy ε) →
             εwkK sTy (num (len Γ)) (enTy {ε} {Θ} A) ⟶* enTy {Γ} {Θ} (εwkTy A)
εwkK-agree {Γ} A = sub-agree-ty (λ ()) A

-- ★ …and its depth occurs ONCE (`subAtK`'s `m` slot is an `app`
--   argument), where `wkTyK`'s occurs four times.
⟶*-εwkKᵈ : {Γ : Cx} {s n n' t : RTm Γ} →
           n ⟶* n' → εwkK s n t ⟶* εwkK s n' t
⟶*-εwkKᵈ h = ⟶*-appˡ (⟶*-appʳ h)

⟶*-εwkKᵃ : {Γ : Cx} {s n t t' : RTm Γ} →
           t ⟶* t' → εwkK s n t ⟶* εwkK s n t'
⟶*-εwkKᵃ h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ h))

------------------------------------------------------------------------
-- ★★★ `wkTyK` AND `εwkK` ARE NATURAL, and their CALLERS need it.
--
-- ⚠ THE SAME WALL `iextK` HIT.  `wkTyK n A` contains `vsRenK n =
--   lam (Var-vsK (w n) (var vz))`, so `subTm` goes UNDER that binder and
--   the βs' four substitutions do not describe the slot.  ⇒ lift the
--   call out by its own naturality first.
--   ★ `Knot/SubSpec.wkTmK-sub` is the SAME lemma at `sTm`; this is it at
--     `sTy`, and `εwkK`'s is one `subMethsK-sub` (its `εsubK = lam
--     Tm-nzeroK` is closed constructors, hence `refl`).
------------------------------------------------------------------------

open import DirectedHoTT.Spec.Syntax using ( Sub; subTm; extS; ielim )
open import DirectedHoTT.Examples.Knot.SubSpec using ( renMethsK-sub; vsRenK-sub )
open import DirectedHoTT.Examples.Knot.IExtRep using ( subMethsK-sub )
open import DirectedHoTT.Examples.Knot.RenTm using ( renMethsK )
open import DirectedHoTT.Examples.Knot.EWk using ( εsubK )

wkTyK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n A : RTm Γ) →
            subTm τ (wkTyK n A) ≡ wkTyK (subTm τ n) (subTm τ A)
wkTyK-sub τ n A =
  cong₂ (λ ms rn → app (app (ielim KnotD (pair sTy (subTm τ n)) ms (subTm τ A))
                            (nsuc (subTm τ n))) rn)
        (renMethsK-sub τ) (vsRenK-sub τ n)

εwkKᵀ-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n t : RTm Γ) →
            subTm τ (εwkK sTy n t) ≡ εwkK sTy (subTm τ n) (subTm τ t)
εwkKᵀ-sub τ n t =
  cong (λ ms → app (app (ielim KnotD (pair sTy (num 0)) ms (subTm τ t))
                        (subTm τ n)) εsubK)
       (subMethsK-sub τ)

-- ★ THE FOUR-FOLD LIFT — `Knot/IihsAgree.nat7` at four substitutions and
--   a BINARY program.  ⬜ Third instance of this shape; it wants to live
--   in `Lib` with the arity and the fold count as parameters.
nat4₂ : (F : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ) →
        ({Γ Δ : Cx} (τ : Sub Γ Δ) (a b : RTm Γ) →
           subTm τ (F a b) ≡ F (subTm τ a) (subTm τ b)) →
        {Γ0 Γ1 Γ2 Γ3 Γ4 : Cx}
        (τ0 : Sub Γ1 Γ0) (τ1 : Sub Γ2 Γ1) (τ2 : Sub Γ3 Γ2) (τ3 : Sub Γ4 Γ3)
        (a b : RTm Γ4) →
        subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (F a b))))
        ≡ F (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 a))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 b))))
nat4₂ F hF τ0 τ1 τ2 τ3 a b =
  trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 z))) (hF τ3 a b))
  (trans (cong (λ z → subTm τ0 (subTm τ1 z)) (hF τ2 _ _))
  (trans (cong (subTm τ0) (hF τ1 _ _))
         (hF τ0 _ _)))

------------------------------------------------------------------------
-- ★ REDUCING `wkTyK`'s DEPTH — and it occurs FOUR times, not one.
--
--     wkTyK n A = app (app (renTmK (pair sTy n) A) (nsuc n)) (vsRenK n)
--     vsRenK n  = lam (Var-vsK (w n) (var vz))
--     Var-vsK a b mentions `a` TWICE — the level and the ford `nsuc a`.
--
-- ⚠ `conSSK`'s trap exactly (`maxtm-is-non-linear`'s cousin): `⟶*`
--   reduces ONE redex at a time, so a term mentioning the depth four
--   times costs four descents.  `subTmAtK` needed one, because its depth
--   occurs once.
------------------------------------------------------------------------

⟶*-wkTyKᵈ : {Γ : Cx} {n n' A : RTm Γ} →
            n ⟶* n' → wkTyK n A ⟶* wkTyK n' A
⟶*-wkTyKᵈ h =
    ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ h)))
  » ⟶*-appˡ (⟶*-appʳ (⟶*-nsuc h))
  » ⟶*-appʳ (⟶*-lam (⟶*-icon (⟶*-pairˡ (⟶*-ren vs h))))
  » ⟶*-appʳ (⟶*-lam (⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ
      (⟶*-pairˡ (⟶*-idreflᵃ (⟶*-nsuc (⟶*-ren vs h)))))))))

payTy-agree : {Γ Θ : Cx} (D : Desc) (C : DCon) →
              app (ielim KnotD (pair sDCon (num (len Γ))) payTyMethsK
                         (enDCon {Θ} C))
                  (enDesc {Θ} D)
              ⟶* enTy {Γ} {Θ} (payTy {Γ} D C)
payTy-agree D dι       =
  ⟶*-appˡ
    (ihead-red KnotD payTyMethsK tagDCon-i (pair sDCon (num (len _))) _
      (methsFrom-sel (cdTake 44 KnotD) tagDCon-i
                     (inCD (cdTake 44 KnotD) tagDCon-i tt))
      done)
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
payTy-agree {Γ} {Θ} D (dρ C)   =
  ⟶*-appˡ
    (ihead-red KnotD payTyMethsK tagDCon-rho (pair sDCon (num (len Γ))) _
      (methsFrom-past (cdTake 44 KnotD) 0 » sel-here _ _)
      done)
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  -- ★ FOUR βs, so the countdown is: the `Desc` passenger 0 rungs, the IH
  --   1 (`wk-single`), the payload 2, the ambient index 3 (`towerJ`).
  -- ★ FOUR βs: the `Desc` passenger 0 rungs, the IH 1, the payload 2,
  --   the ambient index 3.  ⚠ The `wkAtK` CALL is one slot, lifted out
  --   by `wkTyK-sub` first — its `vsRenK n` is a `lam`.
  » ⟶*-castₗ
      (cong (Ty-SgK (Ty-MuK (enDesc D)))
        (trans (nat4₂ wkTyK wkTyK-sub T0 T1 T2 T3
                      (snd (var (vs (vs (vs vz)))))
                      (app (fst (var (vs vz))) (var vz)))
               (cong₂ wkTyK (cong snd (towerJ (enDesc D) IHS PAY IX))
                            (cong (λ z → app (fst z) (enDesc D))
                                  (wk-single {v = enDesc D} IHS)))))
   (   inSgR (⟶*-wkTyKᵈ (step (βsnd _ _) done))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (step (βfst _ _) done)))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))))
  » inSgR (⟶*-wkTyKᵃ (payTy-agree D C))
  » inSgR (wkTyK-agree (payTy {Γ} D C))
  -- ★★ THE ONE CAST, and it is the KERNEL'S OWN LEMMA: the object side
  --   weakens explicitly (`wkAtK`) where the meta does not, and
  --   `Spec/Typing.payTy-ren` says `renTy ρ (payTy D C) ≡ payTy D C`.
  » ⟶*-castᵣ (cong (λ z → Ty-SgK (enTy {Γ} {Θ} (Mu D)) (enTy {Γ ∙} {Θ} z))
                   (payTy-ren vs D C))
             done)
  where
    IX : RTm Θ
    IX = pair sDCon (num (len Γ))
    PAY : RTm Θ
    PAY = pair (enDCon C) (pair (idrefl ⌜Nat⌝ sDCon) unit)
    IHS : RTm Θ
    IHS = iihs KnotD payTyMethsK (isingle IX) (ilookupD KnotD tagDCon-rho) PAY
    T0 : Sub (Θ ∙) Θ
    T0 = single (enDesc D)
    T1 : Sub ((Θ ∙) ∙) (Θ ∙)
    T1 = extS (single IHS)
    T2 : Sub (((Θ ∙) ∙) ∙) ((Θ ∙) ∙)
    T2 = extS (extS (single PAY))
    T3 : Sub ((((Θ ∙) ∙) ∙) ∙) (((Θ ∙) ∙) ∙)
    T3 = extS (extS (extS (single IX)))
payTy-agree {Γ} {Θ} D (dκ A C) =
  ⟶*-appˡ
    (ihead-red KnotD payTyMethsK tagDCon-kap (pair sDCon (num (len Γ))) _
      (methsFrom-past (cdTake 44 KnotD) 1 » sel-there 0 _ _ (sel-here _ _))
      done)
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  » ⟶*-castₗ
      (cong₂ Ty-SgK
        (trans (nat4₂ (εwkK sTy) εwkKᵀ-sub T0 T1 T2 T3
                      (snd (var (vs (vs (vs vz)))))
                      (fst (var (vs (vs vz)))))
               (cong₂ (εwkK sTy) (cong snd (towerJ (enDesc D) IHS PAY IX))
                                 (cong fst (sub-w²-single {a = enDesc D}
                                                          {b = IHS} PAY))))
        (trans (nat4₂ wkTyK wkTyK-sub T0 T1 T2 T3
                      (snd (var (vs (vs (vs vz)))))
                      (app (fst (snd (var (vs vz)))) (var vz)))
               (cong₂ wkTyK (cong snd (towerJ (enDesc D) IHS PAY IX))
                            (cong (λ z → app (fst (snd z)) (enDesc D))
                                  (wk-single {v = enDesc D} IHS)))))
   (   inSgL (⟶*-εwkKᵈ (step (βsnd _ _) done))
  » inSgL (⟶*-εwkKᵃ (step (βfst _ _) done))
  » inSgL (εwkK-agree {Γ} A)
  » inSgR (⟶*-wkTyKᵈ (step (βsnd _ _) done))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done))))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (step (βfst _ _) done)))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done)))))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))))
  » inSgR (⟶*-wkTyKᵃ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))))
  » inSgR (⟶*-wkTyKᵃ (payTy-agree D C))
  » inSgR (wkTyK-agree (payTy {Γ} D C))
  » ⟶*-castᵣ (cong (λ z → Ty-SgK (enTy {Γ} {Θ} (εwkTy A)) (enTy {Γ ∙} {Θ} z))
                   (payTy-ren vs D C))
             done)
  where
    IX : RTm Θ
    IX = pair sDCon (num (len Γ))
    PAY : RTm Θ
    PAY = pair (enTy A) (pair (enDCon C) (pair (idrefl ⌜Nat⌝ sDCon) unit))
    IHS : RTm Θ
    IHS = iihs KnotD payTyMethsK (isingle IX) (ilookupD KnotD tagDCon-kap) PAY
    T0 : Sub (Θ ∙) Θ
    T0 = single (enDesc D)
    T1 : Sub ((Θ ∙) ∙) (Θ ∙)
    T1 = extS (single IHS)
    T2 : Sub (((Θ ∙) ∙) ∙) ((Θ ∙) ∙)
    T2 = extS (extS (single PAY))
    T3 : Sub ((((Θ ∙) ∙) ∙) ∙) (((Θ ∙) ∙) ∙)
    T3 = extS (extS (extS (single IX)))

------------------------------------------------------------------------
-- ★★★ AT THE LEDGER'S NAME.  ⚠ `payTyK n C D` takes its `DCon` BEFORE
--   its `Desc` — the permutation `Knot/KAdapt.payTyKᵏ` exists to undo.
------------------------------------------------------------------------

open import DirectedHoTT.Examples.Knot.PayTy using ( payTyK )

payTyK-agree : {Γ Θ : Cx} (D : Desc) (C : DCon) →
               payTyK (num (len Γ)) (enDCon {Θ} C) (enDesc {Θ} D)
               ⟶* enTy {Γ} {Θ} (payTy {Γ} D C)
payTyK-agree D C = payTy-agree D C
