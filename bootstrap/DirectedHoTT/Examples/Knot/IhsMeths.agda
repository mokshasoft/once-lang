------------------------------------------------------------------------
-- OCP-0009 · KNOT — `ihsK` PART 4: the junk row, the tuple, and the program.
--
-- ⚠ NEEDS THE COMPACTING COLLECTOR.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhsMeths where
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
open import DirectedHoTT.Lib.Wk using ( towerJ )
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

------------------------------------------------------------------------
-- ★ THE JUNK METHOD — and for `cDCon-i` it is the RIGHT answer, not junk:
--   `ihs D ms dι p = unit`, and the junk body IS `Tm-unitK`.  So the
--   tuple is junk 0–43 · row 44 (`dρ`) · row 45 (`dκ`) · junk 46–52,
--   which is `Knot/IhTy`'s shape exactly.
------------------------------------------------------------------------

ihsJunk : {Γ : Cx} → RTm Γ
ihsJunk = lam (lam (lam (lam (lam (lam (lam Tm-unitK))))))

⊢ihsJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
           IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
           Γ ⊢ ihsJunk ∷ imethTy KnotD IPair k C ihsMotK
⊢ihsJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢ihsMotK
    (⊢lam ty-Nat
      (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢var here)))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))
          (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there here)))))
            (⊢Tm-unitKv (var (vs (vs (vs vz)))) (⊢var (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★ THE TUPLE — `Knot/IhTy`'s assembly, one description over.
------------------------------------------------------------------------

HD46 : IDesc
HD46 = cdRest (cdTake 46 KnotD)

HD45' : IDesc
HD45' = cDCon-kap ◂ HD46

HD44' : IDesc
HD44' = cDCon-rho ◂ HD45'

hspl44 : Split KnotD 44 HD44'
hspl44 = splTake spl-nil (cdTake 44 KnotD)

hwf45 : IDescWfFrom KnotD IPair HD45'
hwf45 = idwfDrop (spl-step hspl44) KnotWf

hwf46 : IDescWfFrom KnotD IPair HD46
hwf46 = idwfDrop (spl-step (spl-step hspl44)) KnotWf

ihsTail : {Γ : Cx} → RTm Γ
ihsTail = methsFrom (cdTake 7 HD46) ihsJunk unit

⊢ihsTail : {Γ : Ctx} →
           Γ ⊢ ihsTail ∷ imethsTyFrom KnotD IPair ihsMotK 46 HD46
⊢ihsTail =
  ⊢methsFrom KnotD IPair 46 (cdTake 7 HD46) KnotWf hwf46
             (spl-step (spl-step hspl44))
             ⊢IPair ⊢ihsMotK (λ {k} {C} wC _ _ → ⊢ihsJunk k C wC)
             unit ⊢unit

ihsMid45 : {Γ : Cx} → RTm Γ
ihsMid45 = pair ihsKap ihsTail

⊢ihsMid45 : {Γ : Ctx} →
            Γ ⊢ ihsMid45 ∷ imethsTyFrom KnotD IPair ihsMotK 45 HD45'
⊢ihsMid45 =
  ⊢methsCons KnotD IPair 45 {C = cDCon-kap} HD46 KnotWf hwf46
             (spl-step (spl-step hspl44)) ⊢IPair ⊢ihsMotK
             ⊢ihsKap ⊢ihsTail

ihsMid44 : {Γ : Cx} → RTm Γ
ihsMid44 = pair ihsRho ihsMid45

⊢ihsMid44 : {Γ : Ctx} →
            Γ ⊢ ihsMid44 ∷ imethsTyFrom KnotD IPair ihsMotK 44 HD44'
⊢ihsMid44 =
  ⊢methsCons KnotD IPair 44 {C = cDCon-rho} HD45' KnotWf hwf45
             (spl-step hspl44) ⊢IPair ⊢ihsMotK
             ⊢ihsRho ⊢ihsMid45

ihsMethsK : {Γ : Cx} → RTm Γ
ihsMethsK = methsFrom (cdTake 44 KnotD) ihsJunk ihsMid44

⊢ihsMethsK : {Γ : Ctx} →
             Γ ⊢ ihsMethsK ∷ imethsTy KnotD IPair ihsMotK KnotD
⊢ihsMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 44 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢ihsMotK (λ {k} {C} wC _ _ → ⊢ihsJunk k C wC)
             ihsMid44 ⊢ihsMid44

