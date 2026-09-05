------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ THE FIVE ROWS `gen_subagree` DOES NOT EMIT.
-- `Knot/RenAgreeX`'s twin.
--
--   cTm-cMu/elim/ielim   cross-sort slots, discharged by
--                        `Knot/SubClosed`'s identities
--   cTm-cIMu             ★ and a PINNED slot (`sTy@lit(0)`)
--   cTm-var              ★★ the GIVEN row
--
-- ★★★ AND THE `var` ROW IS **SIMPLER** HERE THAN FOR RENAMING.
--   `subTm σ (var x) = σ x` DIRECTLY — a variable substitutes to a TERM —
--   so `subVarM`'s body is `app σ (fst p)` with no `Tm-varK` wrapper, and
--   `h x` finishes it on the nose.  `Knot/RenAgreeX.row-var` had to
--   reduce inside a `Tm-varK` first, because `renTm ρ (var x) = var (ρ x)`
--   stays in the variable sort.
--   ⇒ the same asymmetry as `extS-Represents` vs `extR-Represents`, seen
--     from the other side: substitution LEAVES the variable sort, and
--     that makes this row shorter and the extension row longer.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubAgreeX where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; trans )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; Var; vz; vs; Sub; subTm; extS; Desc; IDesc
        ; app; pair; icon; idrefl; ⌜Nat⌝; unit; ⌜Mu⌝; ⌜IMu⌝; elim; ielim; var
        ; iihs; isingle; ilookupD; fst; snd )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; βfst; βsnd; jsub-refl; ι-ielim; single )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd
        ; ⟶*-ielimᵗ; ⟶*-ielimⁱ; ⟶*-jsubᵖ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import DirectedHoTT.Lib.ISub using ( ttsd )
open import DirectedHoTT.Lib.IMeths using ( sel-here≡; sel-there≡ )
open import DirectedHoTT.Lib.Wk using ( pw^; w )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enVar; enDesc; enIDesc; enTy )
open import DirectedHoTT.Examples.Knot.Sorts using ( num; len; sTm )
open import DirectedHoTT.Examples.Knot.SubApp using ( subAtK )
open import DirectedHoTT.Examples.Knot.SubRed using ( sub-head-red )
import DirectedHoTT.Lib.ISub as IS
open import DirectedHoTT.Examples.Knot.SubMot
  using ( extNK; sortMap; decStableK; fordMapK; subMethsK; subDescK; giveK; subVarM )
open IS.Sub extNK sortMap decStableK fordMapK
open import DirectedHoTT.Examples.Knot.SubAgree using ( Represents )
open import DirectedHoTT.Examples.Knot.SubClosed using ( sub-Desc-id; sub-IDesc-id )

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

row-cMu : {Γ Δ Θ : Cx} {σ : Sub Γ Δ} {s : RTm Θ} →
          Represents σ s → (D : Desc) →
          subAtK sTm (num (len Γ)) (num (len Δ)) s (enTm {Γ} {Θ} (⌜Mu⌝ D))
          ⟶* enTm {Δ} {Θ} (subTm σ (⌜Mu⌝ D))
row-cMu {Γ} {Δ} h D =
  sub-head-red 38 ttsd ttsd refl
               sTm (num (len Γ)) (num (len Δ)) _
               (pair (enDesc D) (pair (idrefl ⌜Nat⌝ sTm) unit)) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst done » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     sub-Desc-id _ _ _ D)) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done)))

row-elim : {Γ Δ Θ : Cx} {σ : Sub Γ Δ} {s : RTm Θ} →
          Represents σ s → (D : Desc) (ms t : RTm Γ) →
          (ih1 : {Θ' : Cx} {σ' : RTm Θ'} → Represents σ σ' →
             subAtK sTm (num (len Γ)) (num (len Δ)) σ' (enTm ms) ⟶* enTm (subTm σ ms)) →
          (ih2 : {Θ' : Cx} {σ' : RTm Θ'} → Represents σ σ' →
             subAtK sTm (num (len Γ)) (num (len Δ)) σ' (enTm t) ⟶* enTm (subTm σ t)) →
          subAtK sTm (num (len Γ)) (num (len Δ)) s (enTm {Γ} {Θ} (elim D ms t))
          ⟶* enTm {Δ} {Θ} (subTm σ (elim D ms t))
row-elim {Γ} {Δ} h D ms t ih1 ih2 =
  sub-head-red 34 ttsd ttsd refl
               sTm (num (len Γ)) (num (len Δ)) _
               (pair (enDesc D) (pair (enTm ms) (pair (enTm t) (pair (idrefl ⌜Nat⌝ sTm) unit)))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst done » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     sub-Desc-id _ _ _ D)) »
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
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst (⟶*-snd (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done)))))

row-ielim : {Γ Δ Θ : Cx} {σ : Sub Γ Δ} {s : RTm Θ} →
          Represents σ s → (E : IDesc) (i ms t : RTm Γ) →
          (ih1 : {Θ' : Cx} {σ' : RTm Θ'} → Represents σ σ' →
             subAtK sTm (num (len Γ)) (num (len Δ)) σ' (enTm i) ⟶* enTm (subTm σ i)) →
          (ih2 : {Θ' : Cx} {σ' : RTm Θ'} → Represents σ σ' →
             subAtK sTm (num (len Γ)) (num (len Δ)) σ' (enTm ms) ⟶* enTm (subTm σ ms)) →
          (ih3 : {Θ' : Cx} {σ' : RTm Θ'} → Represents σ σ' →
             subAtK sTm (num (len Γ)) (num (len Δ)) σ' (enTm t) ⟶* enTm (subTm σ t)) →
          subAtK sTm (num (len Γ)) (num (len Δ)) s (enTm {Γ} {Θ} (ielim E i ms t))
          ⟶* enTm {Δ} {Θ} (subTm σ (ielim E i ms t))
row-ielim {Γ} {Δ} h E i ms t ih1 ih2 ih3 =
  sub-head-red 36 ttsd ttsd refl
               sTm (num (len Γ)) (num (len Δ)) _
               (pair (enIDesc E) (pair (enTm i) (pair (enTm ms) (pair (enTm t) (pair (idrefl ⌜Nat⌝ sTm) unit))))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst done » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     sub-IDesc-id _ _ _ E)) »
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
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst (⟶*-snd (⟶*-snd (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done))))))

row-cIMu : {Γ Δ Θ : Cx} {σ : Sub Γ Δ} {s : RTm Θ} →
          Represents σ s → (E : IDesc) (I : RTy ε) (i : RTm Γ) →
          (ihi : {Θ' : Cx} {σ' : RTm Θ'} → Represents σ σ' →
             subAtK sTm (num (len Γ)) (num (len Δ)) σ' (enTm i) ⟶* enTm (subTm σ i)) →
          subAtK sTm (num (len Γ)) (num (len Δ)) s (enTm {Γ} {Θ} (⌜IMu⌝ E I i))
          ⟶* enTm {Δ} {Θ} (subTm σ (⌜IMu⌝ E I i))
row-cIMu {Γ} {Δ} h E I i ihi =
  sub-head-red 39 ttsd ttsd refl
               sTm (num (len Γ)) (num (len Δ)) _
               (pair (enIDesc E) (pair (enTy I) (pair (enTm i) (pair (idrefl ⌜Nat⌝ sTm) unit)))) »
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst done » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst done » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     sub-IDesc-id _ _ _ E)) »
  -- ⚠ SLOT 1 IS PINNED (`sTy@lit(0)`): one projection, no descent.
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihi h)))) »
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-fst (⟶*-snd (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
     step (jsub-refl _ _ _ _) done)))))

------------------------------------------------------------------------
-- ★★★ `cTm-var` — the GIVEN row, and here it is SIMPLER than renaming.
--   `subTm σ (var x) = σ x` DIRECTLY: a variable substitutes to a TERM,
--   so `subVarM`'s body is `app σ (fst p)` with no `Tm-varK` wrapper.
--   ⇒ `h x` finishes it on the nose, where `Knot/RenAgreeX.row-var` had
--     to reduce inside a `Tm-varK` first.
------------------------------------------------------------------------

sub-head-give :
  {Γ : Cx} (k : ℕ) (msel : InSD? subDescK k) (M : RTm Γ) →
  sdMeth giveK 0 subDescK k ≡ M →
  (s dd m σ p : RTm Γ) →
  subAtK s dd m σ (icon k p) ⟶*
    app (app (app (app (app M (pair s dd)) p)
      (iihs KnotD subMethsK (isingle (pair s dd)) (ilookupD KnotD k) p)) m) σ
sub-head-give k msel M eq s dd m σ p =
  ⟶*-appˡ (⟶*-appˡ
    (step (ι-ielim KnotD (pair s dd) subMethsK k p)
          (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
            (⟶*-castᵣ eq (isubMeths-sel subDescK 0 k msel)))))))

row-var : {Γ Δ Θ : Cx} {σ : Sub Γ Δ} {s : RTm Θ} →
          Represents σ s → (x : Var Γ) →
          subAtK sTm (num (len Γ)) (num (len Δ)) s (enTm {Γ} {Θ} (var x))
          ⟶* enTm {Δ} {Θ} (subTm σ (var x))
row-var {Γ} {Δ} {Θ} {s = s} h x =
  sub-head-give 11 ttsd subVarM refl sTm (num (len Γ)) (num (len Δ)) s P »
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))) »
  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
  ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
  ⟶*-appˡ (step (β _ _) done) »
  step (β _ _) done »
  ⟶*-jsubᵖ (⟶*-jsubᵖ (sel-there≡ 0 tw (sel-here≡ refl))) »
  ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
  step (jsub-refl _ _ _ _) done »
  ⟶*-appʳ (sel-here≡ tw) »
  h x
  where
    P : RTm Θ
    P = pair (enVar x) (pair (idrefl ⌜Nat⌝ sTm) unit)
    IH : RTm Θ
    IH = iihs KnotD subMethsK (isingle (pair sTm (num (len Γ)))) (ilookupD KnotD 11) P
    tw : subTm (single s)
           (subTm (extS (single (num (len Δ))))
             (subTm (extS (extS (single IH))) (w (w (w P))))) ≡ P
    tw = trans (cong (λ z → subTm (single s) (subTm (extS (single (num (len Δ)))) z))
                     (pw^ {u = IH} 2 P))
         (trans (cong (subTm (single s)) (pw^ {u = num (len Δ)} 1 P))
                (pw^ {u = s} 0 P))
