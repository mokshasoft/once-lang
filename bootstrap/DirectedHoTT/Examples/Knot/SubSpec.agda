------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ THE SUBSTITUTION-SIDE POINTWISE LAWS, and
-- `wkTmK`'s ADEQUACY.
--
-- `Knot/RenSpec` is the renaming side.  This is `extNK`'s `vz` law (its
-- `vs` law is next), plus the lemma that closes the arc this whole plan
-- opened with.
--
-- ★★★ `wkTmK-agree` IS ONE LINE, AND THAT IS THE POINT:
--
--     wkTmK n t = renTmAtK sTm n (nsuc n) (vsRenK n) t
--     wkTmK-agree t = ren-agree wk-Represents t
--
--   `wkTmK`'s adequacy is `ren-agree` at the renaming `vs`, whose
--   `RepresentsR` witness is `Knot/RenSpec.vsRenK-app` — THE FIRST LAW
--   STEP 2 PROVED, and the one `PLAN-RENAMING.md` §15.1 showed could not
--   even be STATED for `wkK`:
--
--     "there is no `app wkK x` to reduce: `wkK` is an `ielim`, and its
--      renaming exists only as the SHAPE of `Lib/IWk`'s 53 derived
--      methods.  ⇒ the defect was not that the law went unproved; it was
--      that the law was UNSTATABLE."
--
--   ⇒ the law that was unstatable for the WRONG weakening is exactly what
--     discharges the RIGHT one, in one line.  That is the plan's whole
--     thesis, reduced to a corollary.
--
-- ⚠ `constMethsFrom-past` is `Lib/IMeths.methsFrom-past`'s twin for
--   `Knot/SubMot`'s local builder — the second lemma that duplication has
--   cost (`constMethsFrom-sub` was the first).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubSpec where
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans; sym )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; app; pair; icon; ielim; iihs; isingle; ilookupD
        ; idrefl; ⌜Nat⌝; unit; fst; snd; var; vz; vs; renTm; IDesc; nsuc; sel )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; βfst; βsnd; ι-ielim; single; wk-single )
open import DirectedHoTT.Spec.Syntax using ( subTm; extS )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ; ⟶*-castₗ )
open import DirectedHoTT.Lib.Wk using ( w; pw^ )
open import DirectedHoTT.Lib.IMeths
  using ( CDesc; cd-stop; cd-cons; cdTake; cdLen; selCong )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz )
open import DirectedHoTT.Examples.Knot.Sorts using ( sVar; num )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-varK )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enVar )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTmK )
open import DirectedHoTT.Examples.Knot.RenTm using ( vsRenK )
open import DirectedHoTT.Examples.Knot.RenSpec using ( vsRenK-app )
open import DirectedHoTT.Examples.Knot.SubAgree using ( RepresentsR )
open import DirectedHoTT.Examples.Knot.RenAgreeTie using ( ren-agree )
open import DirectedHoTT.Examples.Knot.SubMot
  using ( extNK; extSK; extMethsK; extTail; constMethsFrom; constMeth; extVz )

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

-- ★ `Lib/IMeths.methsFrom-past`'s twin for `Knot/SubMot`'s local builder.
--   ⚠ Another consequence of `constMethsFrom` duplicating `methsFrom`:
--     every lemma about the one needs a copy for the other.
constMethsFrom-past : {Γ : Cx} {E : IDesc} (W : CDesc E) {tl : RTm Γ} (k : ℕ) →
                      sel (cdLen W + k) (constMethsFrom W tl) ⟶* sel k tl
constMethsFrom-past (cd-stop E) k = done
constMethsFrom-past (cd-cons W) k =
  step (selCong (cdLen W + k) (βsnd _ _)) (constMethsFrom-past W k)

-- ★ head reduction at row 51 (`vz`), which is the HEAD of `extTail`.
extSK-vz : {Γ : Cx} (i m : RTm Γ) →
           extSK i (Var-vzK m) ⟶*
             app (app (app extVz i)
                      (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                    (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
                 (iihs KnotD extMethsK (isingle i) (ilookupD KnotD 51)
                       (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                     (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
extSK-vz i m =
  step (ι-ielim KnotD i extMethsK tagVar-vz _)
       (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
         (constMethsFrom-past (cdTake 51 KnotD) zero » step (βfst _ _) done))))

-- ★ `extS σ vz = var vz`, object-level.  `extVz`'s body is
--   `Tm-varK (Var-vzK n)`, so the five βs land on the answer directly —
--   no projection, no jsub.  ⚠ Contrast `extVs` below.
extNK-vz : {Γ : Cx} (d n σ m : RTm Γ) →
           app (extNK d n σ) (Var-vzK m) ⟶* Tm-varK (Var-vzK n)
extNK-vz {Γ} d n σ m =
  step (β _ _)
    (⟶*-castₗ (cong₂ (λ a b → app (app (extSK (pair sVar (nsuc a)) (Var-vzK m)) b)
                                   (subTm (single (Var-vzK m)) (w σ)))
                     (wk-single {v = Var-vzK m} d) (wk-single {v = Var-vzK m} n))
      (⟶*-appˡ (⟶*-appˡ (extSK-vz _ _)) »
       ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))) »
       ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
       ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
       ⟶*-appˡ (step (β _ _) done) »
       step (β _ _) done »
       -- ★ `extVz`'s body is `Tm-varK (Var-vzK (var (vs vz)))`, and at five
       --   lams `var (vs vz)` is the TARGET DEPTH `n`.  Three of the five
       --   substitutions leave it alone; the fourth weakens and the fifth
       --   cancels — `pw^ 0`, i.e. one `wk-single`.
       ⟶*-castᵣ (cong (λ z → Tm-varK (Var-vzK z))
                      (pw^ {u = subTm (single (Var-vzK m)) (w σ)} 0 n))
                done))

------------------------------------------------------------------------
-- ★★★ AND `wkTmK` IS NOW A COROLLARY OF `ren-agree`.
--
--     wkTmK n t = renTmAtK sTm n (nsuc n) (vsRenK n) t
--
-- so its adequacy is `ren-agree` at the renaming `vs`, whose
-- `RepresentsR` witness is `Knot/RenSpec.vsRenK-app` — the very first law
-- step 2 proved, and the one that could not be stated for `wkK`
-- (`PLAN-RENAMING.md` §15.1).  ⇒ the arc closes: the law that was
-- UNSTATABLE for the wrong weakening is what discharges the right one.
------------------------------------------------------------------------

wk-Represents : {Γ Θ : Cx} → RepresentsR {Γ} {Γ ∙} {Θ} vs (vsRenK (num (len Γ)))
wk-Represents {Γ} x = vsRenK-app (num (len Γ)) (enVar x)

wkTmK-agree : {Γ Θ : Cx} (t : RTm Γ) →
              wkTmK (num (len Γ)) (enTm {Γ} {Θ} t) ⟶* enTm {Γ ∙} {Θ} (renTm vs t)
wkTmK-agree {Γ} t = ren-agree (wk-Represents {Γ}) t
