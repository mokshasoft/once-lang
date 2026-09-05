------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ THE FIVE ROWS `gen_renagree` DOES NOT EMIT.
--
-- `Knot/RenAgree` generates the 25 SAME-SORT `RTm` rows.  These are the
-- other five, and they are the interesting ones:
--
--   cTm-cMu   sDesc@D                       ← `Knot/RenClosed.ren-Desc-id`
--   cTm-elim  sDesc@D, sTm×2                ← ditto, plus ordinary IHs
--   cTm-ielim sIDesc@D, sTm×3               ← `ren-IDesc-id`
--   cTm-cIMu  sIDesc@D, sTy@lit(0), sTm     ← ★ and a PINNED slot
--   cTm-var   sVar@D                        ← ★★ a GIVEN row
--
-- ★ A CROSS-SORT SLOT IS AN ORDINARY DESCENT whose "IH" is a CLOSED-SORT
--   IDENTITY.  Nothing new happens: `ren-Desc-id`/`ren-IDesc-id` simply
--   need no `RepresentsR`, because those sorts have no variables.
--
-- ★★ A PINNED SLOT IS ONE PROJECTION.  `cTm-cIMu`'s `RTy ε` sits at
--   `lit(0)`, so `sPick (s-pinned _ _) d n σ q ih = q` hands back the
--   original — no eliminator descent, no IH, exactly like a ford.
--
-- ★★★ AND THE GIVEN ROW IS WHERE `Represents` PAYS FOR ITSELF.  `cTm-var`'s
--   method is `renVarM`, hand-written, not an `isubMethod` — so
--   `ren-head-red`'s premise cannot even be stated for it and
--   `ren-head-give` stops at the method instead.  What discharges the row
--   is `h x` — the RELATION itself.  ⇒ the reason step 3's statement had
--   to be a relation rather than an encoded substitution
--   (`PLAN-RENAMING.md` §16.1) is visible here as a proof step.
--
-- ⚠ `renVarM` has FIVE lams, so its payload is at de Bruijn 3 and the
--   projection needs a THREE-tower — `pw^` counted down.  `towerP` (two)
--   does not reach it, and `nrs` needed a different depth again: three
--   customers, three depths, which is why `pw^` is indexed.
--
-- ⚠ AND TWO `jsub-refl`s, not one: `symN a p = jsub _ p _` is ITSELF a
--   `jsub`, so its own path must fire before the outer one can.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenAgreeX where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; Var; vz; vs; Ren; Desc; IDesc; app; pair; icon
        ; renTm; extR; idrefl; ⌜Nat⌝; unit; ⌜Mu⌝; ⌜IMu⌝; elim; ielim; var
        ; iihs; isingle; ilookupD; subTm; extS )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; βfst; βsnd; β; ι-ielim; jsub-refl; single )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ; ⟶*-ielimⁱ
        ; ⟶*-fst; ⟶*-snd; ⟶*-appʳ; ⟶*-jsubᵖ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.ISub using ( ttsd )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enDesc; enIDesc; enTy; enVar )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import DirectedHoTT.Lib.IMeths using ( sel-here≡; sel-there≡ )
open import DirectedHoTT.Lib.Wk using ( towerP; pw^; w )
open import DirectedHoTT.Examples.Knot.RenSpec using ( inVar )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
import DirectedHoTT.Lib.ISub as IS
open import DirectedHoTT.Examples.Knot.RenMot using ( extRNK )
open import DirectedHoTT.Examples.Knot.RenTm using ( renSmap; renDecStable; renFordMap; renMethsK; renDescK; renGiveK; renVarM )
open IS.Sub extRNK renSmap renDecStable renFordMap
open import DirectedHoTT.Examples.Knot.Sorts using ( num; len; sTm; sDesc; sIDesc )
open import DirectedHoTT.Examples.Knot.RenTm using ( renTmAtK )
open import DirectedHoTT.Examples.Knot.RenRed using ( ren-head-red )
open import DirectedHoTT.Examples.Knot.SubAgree using ( RepresentsR )
open import DirectedHoTT.Examples.Knot.RenClosed using ( ren-Desc-id; ren-IDesc-id )

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

------------------------------------------------------------------------
-- ★ `cTm-cMu` (k=38) — ONE cross-sort field, `sDesc@D`.  The slot is a
--   normal recursive descent; what changes is that its "IH" is
--   `Knot/RenClosed.ren-Desc-id`, which needs no `RepresentsR` because a
--   `Desc` has no variables to rename.
------------------------------------------------------------------------

row-cMu : {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} →
          RepresentsR ρ r → (D : Desc) →
          renTmAtK sTm (num (len Γ)) (num (len Δ)) r (enTm {Γ} {Θ} (⌜Mu⌝ D))
          ⟶* enTm {Δ} {Θ} (renTm ρ (⌜Mu⌝ D))
row-cMu {Γ} {Δ} h D =
  ren-head-red 38 ttsd ttsd refl
               sTm (num (len Γ)) (num (len Δ)) _
               (pair (enDesc D) (pair (idrefl ⌜Nat⌝ sTm) unit)) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ren-Desc-id _ _ _ D)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)))

row-elim : {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} →
          RepresentsR ρ r → (D : Desc) (ms t : RTm Γ) →
          (ihm : {Θ' : Cx} {r' : RTm Θ'} → RepresentsR ρ r' →
             renTmAtK sTm (num (len Γ)) (num (len Δ)) r' (enTm ms) ⟶* enTm (renTm ρ ms)) →
          (iht : {Θ' : Cx} {r' : RTm Θ'} → RepresentsR ρ r' →
             renTmAtK sTm (num (len Γ)) (num (len Δ)) r' (enTm t) ⟶* enTm (renTm ρ t)) →          renTmAtK sTm (num (len Γ)) (num (len Δ)) r (enTm {Γ} {Θ} (elim D ms t))
          ⟶* enTm {Δ} {Θ} (renTm ρ (elim D ms t))
row-elim {Γ} {Δ} h D ms t ihm iht =
  ren-head-red 34 ttsd ttsd refl
               sTm (num (len Γ)) (num (len Δ)) _
               (pair (enDesc D) (pair (enTm ms) (pair (enTm t) (pair (idrefl ⌜Nat⌝ sTm) unit)))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst done » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ren-Desc-id _ _ _ D)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihm h))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     iht h)))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)))))

row-ielim : {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} →
          RepresentsR ρ r → (E : IDesc) (i ms t : RTm Γ) →
          (ih1 : {Θ' : Cx} {r' : RTm Θ'} → RepresentsR ρ r' →
             renTmAtK sTm (num (len Γ)) (num (len Δ)) r' (enTm i) ⟶* enTm (renTm ρ i)) →
          (ih2 : {Θ' : Cx} {r' : RTm Θ'} → RepresentsR ρ r' →
             renTmAtK sTm (num (len Γ)) (num (len Δ)) r' (enTm ms) ⟶* enTm (renTm ρ ms)) →
          (ih3 : {Θ' : Cx} {r' : RTm Θ'} → RepresentsR ρ r' →
             renTmAtK sTm (num (len Γ)) (num (len Δ)) r' (enTm t) ⟶* enTm (renTm ρ t)) →
          renTmAtK sTm (num (len Γ)) (num (len Δ)) r (enTm {Γ} {Θ} (ielim E i ms t))
          ⟶* enTm {Δ} {Θ} (renTm ρ (ielim E i ms t))
row-ielim {Γ} {Δ} h E i ms t ih1 ih2 ih3 =
  ren-head-red 36 ttsd ttsd refl
               sTm (num (len Γ)) (num (len Δ)) _
               (pair (enIDesc E) (pair (enTm i) (pair (enTm ms) (pair (enTm t) (pair (idrefl ⌜Nat⌝ sTm) unit))))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst done » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ren-IDesc-id _ _ _ E)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ih1 h))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ih2 h)))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ih3 h))))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd (⟶*-snd (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))))))

row-cIMu : {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} →
          RepresentsR ρ r → (E : IDesc) (I : RTy ε) (i : RTm Γ) →
          (ihi : {Θ' : Cx} {r' : RTm Θ'} → RepresentsR ρ r' →
             renTmAtK sTm (num (len Γ)) (num (len Δ)) r' (enTm i) ⟶* enTm (renTm ρ i)) →          renTmAtK sTm (num (len Γ)) (num (len Δ)) r (enTm {Γ} {Θ} (⌜IMu⌝ E I i))
          ⟶* enTm {Δ} {Θ} (renTm ρ (⌜IMu⌝ E I i))
row-cIMu {Γ} {Δ} h E I i ihi =
  ren-head-red 39 ttsd ttsd refl
               sTm (num (len Γ)) (num (len Δ)) _
               (pair (enIDesc E) (pair (enTy I) (pair (enTm i) (pair (idrefl ⌜Nat⌝ sTm) unit)))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst done » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ren-IDesc-id _ _ _ E)) »
  -- ⚠ SLOT 1 IS **PINNED** (`sTy@lit(0)`): `sPick (s-pinned _ _) … = q`,
  --   so it is one projection, exactly like a ford.  No descent, no IH.
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihi h)))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)))))

------------------------------------------------------------------------
-- ★★★ `cTm-var` (k=11) — A **GIVEN** ROW, so `ren-head-red` does not
--   apply: its premise is `sdMeth … ≡ isubMethod k (wOf k pj)`, and a
--   given row's method is not an `isubMethod` at all.  The variant below
--   stops at the method, whatever it is, and lets the caller β through it.
------------------------------------------------------------------------

ren-head-give :
  {Γ : Cx} (k : ℕ) (msel : InSD? renDescK k) (M : RTm Γ) →
  sdMeth renGiveK 0 renDescK k ≡ M →
  (s dd m rn p : RTm Γ) →
  renTmAtK s dd m rn (icon k p) ⟶*
    app (app (app (app (app M (pair s dd)) p)
      (iihs KnotD renMethsK (isingle (pair s dd)) (ilookupD KnotD k) p)) m) rn
ren-head-give k msel M eq s dd m rn p =
  ⟶*-appˡ (⟶*-appˡ
    (step (ι-ielim KnotD (pair s dd) renMethsK k p)
          (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
            (⟶*-castᵣ eq (isubMeths-sel renDescK 0 k msel)))))))

-- ★ and the row.  `RepresentsR` IS its content: `h x` is exactly the
--   reduction the method's body needs, which is the whole point of
--   `Represents` — a given row is discharged by the RELATION, not by a
--   computed method.
row-var : {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} →
          RepresentsR ρ r → (x : Var Γ) →
          renTmAtK sTm (num (len Γ)) (num (len Δ)) r (enTm {Γ} {Θ} (var x))
          ⟶* enTm {Δ} {Θ} (renTm ρ (var x))
row-var {Γ} {Δ} {Θ} {r = r} h x =
  ren-head-give 11 ttsd renVarM refl
                sTm (num (len Γ)) (num (len Δ)) r P »
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))) »
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
  ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
  ⟶*-appˡ (step (β _ _) done) »
  step (β _ _) done »
  -- ★ the PATH: `symN a p = jsub _ p _`, so the ford projection sits under
  --   TWO `jsub`s.  The payload is at de Bruijn 3 through five
  --   substitutions — a 3-tower, `pw^` counted down, exactly as in
  --   `Lib/ISub.isubMethod-red`.
  ⟶*-jsubᵖ (⟶*-jsubᵖ (sel-there≡ 0 tw (sel-here≡ refl))) »
  -- ⚠ TWO `jsub-refl`s: `symN` is ITSELF a `jsub`, so its own path must
  --   fire before the outer one can.  (`Knot/RenSpec.singleK-vs`'s shape.)
  ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
  step (jsub-refl _ _ _ _) done »
  -- ★★★ AND THE RELATION IS THE PROOF.  `h x` IS what the method's body
  --   needs; a GIVEN row is discharged by `RepresentsR`, not by a computed
  --   method.  That is the whole reason `Represents` was the statement.
  inVar (⟶*-appʳ (sel-here≡ tw) » h x)
  where
    P : RTm Θ
    P = pair (enVar x) (pair (idrefl ⌜Nat⌝ sTm) unit)
    IH : RTm Θ
    IH = iihs KnotD renMethsK (isingle (pair sTm (num (len Γ)))) (ilookupD KnotD 11) P

    -- ⚠ A **THREE**-TOWER, NOT `towerP`'s TWO.  `renVarM` has FIVE lams,
    --   so its payload sits at de Bruijn 3 and three weakenings must be
    --   cancelled.  `pw^` counted down — the indexed form, which is why
    --   it was worth indexing (`Lib/Wk`, and `nrs` needed a different
    --   depth again).
    tw : subTm (single r)
           (subTm (extS (single (num (len Δ))))
             (subTm (extS (extS (single IH))) (w (w (w P))))) ≡ P
    tw = trans (cong (λ z → subTm (single r) (subTm (extS (single (num (len Δ)))) z))
                     (pw^ {u = IH} 2 P))
         (trans (cong (subTm (single r)) (pw^ {u = num (len Δ)} 1 P))
                (pw^ {u = r} 0 P))
