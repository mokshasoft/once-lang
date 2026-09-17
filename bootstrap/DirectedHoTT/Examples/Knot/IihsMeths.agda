------------------------------------------------------------------------
-- OCP-0009 · KNOT — `iihsK` PART 4: the 53-row method tuple.
--
-- ★ `Knot/IhsMeths`'s assembly, ONE DESCRIPTION OVER — junk 0–48 ·
--   row 49 (`cICon-rho`) · row 50 (`cICon-kap`) · junk 51–52.
--
-- ⚠ ROW 48 (`cICon-i`) IS COVERED BY THE JUNK, and that is not a
--   shortcut: `iihs D ms σ iι p = unit`, so `cICon-i`'s own answer IS
--   the junk body.  `⊢iihsJunk` is quantified over `k` and `C`, so it
--   discharges row 48 on the nose — the same coincidence `ihsJunk`
--   exploits at `cDCon-i`.
--
-- ⚠ NEEDS THE COMPACTING COLLECTOR.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IihsMeths where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; pair; ε; ICon; IDesc; _◂_; unit; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; IConWf; IDescWfFrom; imethsTyFrom
        ; imethsTy; ⊢unit )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; cICon-i; cICon-rho; cICon-kap )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methsFrom; ⊢methsCons; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Examples.Knot.IihsMot using ( iihsMotK; ⊢iihsMotK; iihsJunk; ⊢iihsJunk )
open import DirectedHoTT.Examples.Knot.IihsRho using ( iihsRho; ⊢iihsRho )
open import DirectedHoTT.Examples.Knot.IihsKap using ( iihsKap; ⊢iihsKap )

IHD51 : IDesc
IHD51 = cdRest (cdTake 51 KnotD)

IHD50' : IDesc
IHD50' = cICon-kap ◂ IHD51

IHD49' : IDesc
IHD49' = cICon-rho ◂ IHD50'

ihspl49 : Split KnotD 49 IHD49'
ihspl49 = splTake spl-nil (cdTake 49 KnotD)

ihwf50 : IDescWfFrom KnotD IPair IHD50'
ihwf50 = idwfDrop (spl-step ihspl49) KnotWf

ihwf51 : IDescWfFrom KnotD IPair IHD51
ihwf51 = idwfDrop (spl-step (spl-step ihspl49)) KnotWf

-- ★ THE TAIL — rows 51 and 52 (`cVar-vz`, `cVar-vs`), both junk.
iihsTail : {Γ : Cx} → RTm Γ
iihsTail = methsFrom (cdTake 2 IHD51) iihsJunk unit

⊢iihsTail : {Γ : Ctx} →
            Γ ⊢ iihsTail ∷ imethsTyFrom KnotD IPair iihsMotK 51 IHD51
⊢iihsTail =
  ⊢methsFrom KnotD IPair 51 (cdTake 2 IHD51) KnotWf ihwf51
             (spl-step (spl-step ihspl49))
             ⊢IPair ⊢iihsMotK (λ {k} {C} wC _ _ → ⊢iihsJunk k C wC)
             unit ⊢unit

iihsMid50 : {Γ : Cx} → RTm Γ
iihsMid50 = pair iihsKap iihsTail

⊢iihsMid50 : {Γ : Ctx} →
             Γ ⊢ iihsMid50 ∷ imethsTyFrom KnotD IPair iihsMotK 50 IHD50'
⊢iihsMid50 =
  ⊢methsCons KnotD IPair 50 {C = cICon-kap} IHD51 KnotWf ihwf51
             (spl-step (spl-step ihspl49)) ⊢IPair ⊢iihsMotK
             ⊢iihsKap ⊢iihsTail

iihsMid49 : {Γ : Cx} → RTm Γ
iihsMid49 = pair iihsRho iihsMid50

⊢iihsMid49 : {Γ : Ctx} →
             Γ ⊢ iihsMid49 ∷ imethsTyFrom KnotD IPair iihsMotK 49 IHD49'
⊢iihsMid49 =
  ⊢methsCons KnotD IPair 49 {C = cICon-rho} IHD50' KnotWf ihwf50
             (spl-step ihspl49) ⊢IPair ⊢iihsMotK
             ⊢iihsRho ⊢iihsMid50

iihsMethsK : {Γ : Cx} → RTm Γ
iihsMethsK = methsFrom (cdTake 49 KnotD) iihsJunk iihsMid49

⊢iihsMethsK : {Γ : Ctx} →
              Γ ⊢ iihsMethsK ∷ imethsTy KnotD IPair iihsMotK KnotD
⊢iihsMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 49 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢iihsMotK (λ {k} {C} wC _ _ → ⊢iihsJunk k C wC)
             iihsMid49 ⊢iihsMid49
