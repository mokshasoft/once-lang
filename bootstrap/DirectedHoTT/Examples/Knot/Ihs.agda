------------------------------------------------------------------------
-- OCP-0009 · KNOT — `ihsK` PART 5: the program and `fieldsK`.
--
-- ⚠ NEEDS THE COMPACTING COLLECTOR.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Ihs where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; var; vz; vs; pair; snd; Π; Nat; εwkTy; IMu )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢ty_; _⊢_∷_; ⊢var; here; there; ⊢snd; ty-Π; ty-IMu
        ; ⊢lam; imethTy; ty-Nat )
open import DirectedHoTT.Spec.Syntax using ( lam )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Examples.Knot.Desc using ( cDCon-i; cDCon-rho; cDCon-kap )
open import DirectedHoTT.Examples.Knot.Wf using ( cDCon-iWf; cDCon-rhoWf; cDCon-kapWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDCon-i; tagDCon-rho; tagDCon-kap )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-unitK; Tm-pairK; Tm-elimK; Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-unitKv; ⊢Tm-pairKv; ⊢Tm-elimKv; ⊢Tm-fstKv; ⊢Tm-sndKv )
open import DirectedHoTT.Spec.Syntax using ( app; fst; isingle; iext; iρ; iκ; iι; ⌜Id⌝; ⌜Nat⌝; nzero )
open import DirectedHoTT.Spec.Typing using ( ⊢app; ⊢ielim; iinst; wk-single; single )
open import DirectedHoTT.Spec.Syntax using ( ielim; subTm )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import DirectedHoTT.Lib.Wk using ( towerJ; sub-w²-single )
open import normalizer.Syntax.Types using ( cong; sym; trans )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-appK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-appKv )
open import DirectedHoTT.Lib.IPay using ( ⊢ihHere; ⊢ihSkipρ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; sDesc; ⊢sDesc; sDCon; ⊢sDCon; sTy; ⊢sTy; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.IhsMot using ( ihsMotK; ⊢ihsMotK )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( ε; ICon; IDesc; _◂_; unit; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( IConWf; IDescWfFrom; imethsTyFrom; imethsTy; ⊢unit )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methsFrom; ⊢methsCons; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Examples.Knot.IhsRho using ( ihsRho; ⊢ihsRho )
open import DirectedHoTT.Examples.Knot.IhsKap using ( ihsKap; ⊢ihsKap )

open import DirectedHoTT.Examples.Knot.IhsMeths using ( ihsMethsK; ⊢ihsMethsK )
open import DirectedHoTT.Examples.Knot.IhsMot using ( ihsMotK; ⊢ihsMotK )

------------------------------------------------------------------------
-- ★★★ `ihsK`, AS A FUNCTION — and `fieldsK` on top of it.
--
--     fields D ms C m p = app (app m p) (ihs D ms C p)   -- `Spec/Syntax:1000`
--
-- ⚠ `app` there is the RTm CONSTRUCTOR, so `fieldsK` builds `Tm-appK`
--   nodes — the same "raw terms" observation that made `selK` and `ihsK`
--   constant-motive folds.
--
-- ★ THE FOUR-APP SPINE IS `towerJ`, exactly as `⊢ipayAppK`'s is: the
--   motive's result reads the FIRST passenger, so after four `⊢app`s the
--   depth arrives through a four-rung substitution tower.
------------------------------------------------------------------------

⊢ihsAppK : {Γ : Ctx} {dd u h n D ms p : RTm ⌊ Γ ⌋} →
           Γ ⊢ h ∷ iinst (pair sDCon dd) u ihsMotK →
           Γ ⊢ n ∷ Nat → Γ ⊢ D ∷ K (pair sDesc n) →
           Γ ⊢ ms ∷ K (pair sTm n) → Γ ⊢ p ∷ K (pair sTm n) →
           Γ ⊢ app (app (app (app h n) D) ms) p ∷ K (pair sTm n)
⊢ihsAppK {n = n} {D = D} {ms = ms} {p = p} dh dn dD dms dp =
  -- ★ `⊢ipayAppK`'s shape, MINUS its per-argument casts: `ipayTyMotK`'s
  --   domains read the AMBIENT INDEX (hence its `towerA`/`subBwd`), and
  --   this motive's read a motive-LOCAL passenger, so they should just
  --   compute.  The result still arrives through the four-rung tower.
  ⊢-cast (cong (λ z → K (pair sTm z)) (towerJ p ms D n))
    (⊢app (⊢app (⊢app (⊢app dh dn) dD)
                (⊢-cast (cong (λ z → K (pair sTm z)) (sym (wk-single {v = D} n))) dms))
          -- ★ two rungs here, not one — `Lib/Wk.sub-w²-single` on the nose.
          (⊢-cast (cong (λ z → K (pair sTm z))
                        (sym (sub-w²-single {a = ms} {b = D} n))) dp))

ihsK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ihsK n C D ms p = app (app (app (app (ielim KnotD (pair sDCon n) ihsMethsK C) n) D) ms) p

⊢ihsK : {Γ : Ctx} {n C D ms p : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ Nat → Γ ⊢ C ∷ K (pair sDCon n) → Γ ⊢ D ∷ K (pair sDesc n) →
        Γ ⊢ ms ∷ K (pair sTm n) → Γ ⊢ p ∷ K (pair sTm n) →
        Γ ⊢ ihsK n C D ms p ∷ K (pair sTm n)
⊢ihsK {n = n} {C = C} dn dC dD dms dp =
  -- ⚠ `dd`/`u` PINNED: they occur only under `iinst`, which is DEFINED
  --   and so not injective — `⊢imethsTyFromK` pays the same.
  ⊢ihsAppK {dd = n} {u = C}
           (⊢ielim KnotWf ⊢ihsMotK (⊢ixP ⊢sDCon dn) ⊢ihsMethsK dC) dn dD dms dp

-- ★★★ AND `fieldsK`, which is `app (app m p) (ihs …)` — trivial once
--   `ihsK` exists, which is why `fields` was never the hard half.
fieldsK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
fieldsK n D ms C m p = Tm-appK (Tm-appK m p) (ihsK n C D ms p)

⊢fieldsK : {Γ : Ctx} {n C D ms m p : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ Nat → Γ ⊢ C ∷ K (pair sDCon n) → Γ ⊢ D ∷ K (pair sDesc n) →
           Γ ⊢ ms ∷ K (pair sTm n) → Γ ⊢ m ∷ K (pair sTm n) → Γ ⊢ p ∷ K (pair sTm n) →
           Γ ⊢ fieldsK n D ms C m p ∷ K (pair sTm n)
⊢fieldsK {n = n} dn dC dD dms dm dp =
  ⊢Tm-appKv n dn (⊢Tm-appKv n dn dm dp) (⊢ihsK dn dC dD dms dp)
