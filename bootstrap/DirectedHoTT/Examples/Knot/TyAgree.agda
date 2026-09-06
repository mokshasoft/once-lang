------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `wkTyK` AND `subTyAtK` ARE ADEQUATE, and both
-- are ONE LINE.
--
--     wkTyK    n A    = renTmAtK sTy n (nsuc n) (vsRenK n) A
--     subTyAtK d m σ A = subAtK   sTy d m σ A
--
-- ⇒ neither is a new theorem.  `wkTyK` is `ren-agree-ty` at the renaming
--   `vs`, exactly as `wkTmK` is `ren-agree` at the same renaming
--   (`Knot/SubSpec`), and `subTyAtK` IS `sub-agree-ty` applied.  The
--   whole cost was opening the `Ty` sort; collecting the payment is two
--   lines.
--
-- ★★★ THESE TWO WERE THE BOTTLENECK OF THE LEDGER.  `tools/gen-knot.py`'s
--   `_WRAP_LEDGER` had 20 entries marked ⬜ OWED, and 17 of them were
--   `Ty`-sorted — `atConK`, `ihTyK`, `payTyK`, `ipayTyK`, `wkTyUnderK`,
--   `conSSK` … — every one routing through `renTy vs` or `subTy σ` and
--   therefore through these two.  They are the reason the `Ty` sort was
--   done before the last three judgement rules rather than after.
--
-- ⚠ A SEPARATE MODULE, NOT AN ADDITION TO `Knot/SubSpec`.  `SubSpec`
--   already imports `Knot/RenAgreeTie`, and the substitution half's
--   `Knot/SubAgreeX` reaches back into `SubSpec` for `extSK-vz`.  Putting
--   the `Ty` corollaries there would close that loop; here nothing does.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.TyAgree where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; Sub; vs; renTy; subTy )
open import DirectedHoTT.Spec.Typing using ( _⟶*_ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Map using ( enTy )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTyAtK )
open import DirectedHoTT.Examples.Knot.SubAgree using ( Represents )
open import DirectedHoTT.Examples.Knot.SubSpec using ( wk-Represents )
open import DirectedHoTT.Examples.Knot.RenAgreeTyTie using ( ren-agree-ty )
open import DirectedHoTT.Examples.Knot.SubAgreeTyTie using ( sub-agree-ty )

-- ★ `renTy vs`, i.e. `Lib/Wk`'s `w` at the type sort.
wkTyK-agree : {Γ Θ : Cx} (A : RTy Γ) →
              wkTyK (num (len Γ)) (enTy {Γ} {Θ} A) ⟶* enTy {Γ ∙} {Θ} (renTy vs A)
wkTyK-agree {Γ} A = ren-agree-ty (wk-Represents {Γ}) A

-- ★ and the general substitution.  ⚠ `subTyAtK` is `subAtK` at `sTy`
--   DEFINITIONALLY, so this is `sub-agree-ty` with no repackaging at all.
subTyAtK-agree : {Γ Δ Θ : Cx} {σ : Sub Γ Δ} {s : RTm Θ} →
                 Represents σ s → (A : RTy Γ) →
                 subTyAtK (num (len Γ)) (num (len Δ)) s (enTy {Γ} {Θ} A)
                 ⟶* enTy {Δ} {Θ} (subTy σ A)
subTyAtK-agree h A = sub-agree-ty h A
