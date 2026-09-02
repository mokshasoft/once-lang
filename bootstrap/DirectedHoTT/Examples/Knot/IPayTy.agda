------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `ipayTy`, ASSEMBLED.
--
--     ipayTy D I σ iι       = Unit
--     ipayTy D I σ (iρ j C) = Σ' (IMu D I (subTm σ j)) (ipayTy D I (extS σ) C)
--     ipayTy D I σ (iκ κ C) = Σ' (El (subTm σ κ))      (ipayTy D I (extS σ) C)
--
-- The motive, the junk row and the three abstract lemmas are in
-- `Knot/IPayTyMot`; the two real rows are one per module (`Knot/IPayTyRho`,
-- `Knot/IPayTyKap`) because each costs ~4 GB on its own — see either
-- row's header for the measurements.  What is left is the tuple and the
-- wrapper, and both are cheap.
--
-- ★★★ THE WRAPPER IS `⊢ipayAppK` APPLIED TO AN `ielim`, and that is the
--   whole proof.  The descent through the motive's four Π binders was
--   already paid, ONCE, for the rows' recursive calls — exactly the
--   relationship `Knot/SubApp`'s `⊢subAtK` has to `⊢motAppK`.  ⇒ an
--   abstraction built for the INSIDE of the recursion turned out to be
--   the whole of the OUTSIDE.
--
-- ★ ROWS 49 AND 50 ARE THE ONLY REAL ONES.  `ipayTy … iι = Unit` and the
--   junk answer IS `Unit`, so `cICon-i` needs no method: junk 0–48 ·
--   row 49 · row 50 · junk 51–52, `Knot/PayTy`'s shape two rows down.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IPayTy where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; RTy; IDesc; app; pair; unit; _◂_; ielim; nzero; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢unit
        ; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methsFrom; ⊢methsCons; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sIDesc; sICon; ⊢sICon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cICon-rho; cICon-kap )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.IPayTyMot
  using ( ipayTyMotK; ⊢ipayTyMotK; ipayTyJunk; ⊢ipayTyJunk; ⊢ipayAppK )
open import DirectedHoTT.Examples.Knot.IPayTyRho using ( ipayTyRho; ⊢ipayTyRho )
open import DirectedHoTT.Examples.Knot.IPayTyKap using ( ipayTyKap; ⊢ipayTyKap )

------------------------------------------------------------------------
-- ★ THE TUPLE — junk 0–48 · row 49 · row 50 · junk 51–52.
------------------------------------------------------------------------

ID51 : IDesc
ID51 = cdRest (cdTake 51 KnotD)

ID50' : IDesc
ID50' = cICon-kap ◂ ID51

ID49' : IDesc
ID49' = cICon-rho ◂ ID50'

ispl49 : Split KnotD 49 ID49'
ispl49 = splTake spl-nil (cdTake 49 KnotD)

iwf50 : IDescWfFrom KnotD IPair ID50'
iwf50 = idwfDrop (spl-step ispl49) KnotWf

iwf51 : IDescWfFrom KnotD IPair ID51
iwf51 = idwfDrop (spl-step (spl-step ispl49)) KnotWf

ipayTyTail : {Γ : Cx} → RTm Γ
ipayTyTail = methsFrom (cdTake 2 ID51) ipayTyJunk unit

⊢ipayTyTail : {Γ : Ctx} →
              Γ ⊢ ipayTyTail ∷ imethsTyFrom KnotD IPair ipayTyMotK 51 ID51
⊢ipayTyTail =
  ⊢methsFrom KnotD IPair 51 (cdTake 2 ID51) KnotWf iwf51
             (spl-step (spl-step ispl49))
             ⊢IPair ⊢ipayTyMotK (λ {k} {C} wC _ _ → ⊢ipayTyJunk k C wC)
             unit ⊢unit

ipayTyMid50 : {Γ : Cx} → RTm Γ
ipayTyMid50 = pair ipayTyKap ipayTyTail

⊢ipayTyMid50 : {Γ : Ctx} →
               Γ ⊢ ipayTyMid50 ∷ imethsTyFrom KnotD IPair ipayTyMotK 50 ID50'
⊢ipayTyMid50 =
  ⊢methsCons KnotD IPair 50 {C = cICon-kap} ID51 KnotWf iwf51
             (spl-step (spl-step ispl49)) ⊢IPair ⊢ipayTyMotK
             ⊢ipayTyKap ⊢ipayTyTail

ipayTyMid49 : {Γ : Cx} → RTm Γ
ipayTyMid49 = pair ipayTyRho ipayTyMid50

⊢ipayTyMid49 : {Γ : Ctx} →
               Γ ⊢ ipayTyMid49 ∷ imethsTyFrom KnotD IPair ipayTyMotK 49 ID49'
⊢ipayTyMid49 =
  ⊢methsCons KnotD IPair 49 {C = cICon-rho} ID50' KnotWf iwf50
             (spl-step ispl49) ⊢IPair ⊢ipayTyMotK
             ⊢ipayTyRho ⊢ipayTyMid50

ipayTyMethsK : {Γ : Cx} → RTm Γ
ipayTyMethsK = methsFrom (cdTake 49 KnotD) ipayTyJunk ipayTyMid49

⊢ipayTyMethsK : {Γ : Ctx} →
                Γ ⊢ ipayTyMethsK ∷ imethsTy KnotD IPair ipayTyMotK KnotD
⊢ipayTyMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 49 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢ipayTyMotK (λ {k} {C} wC _ _ → ⊢ipayTyJunk k C wC)
             ipayTyMid49 ⊢ipayTyMid49

------------------------------------------------------------------------
-- ★★★ `ipayTy`, AS A FUNCTION.
------------------------------------------------------------------------

ipayTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ipayTyK dd c n sb d i =
  app (app (app (app (ielim KnotD (pair sICon dd) ipayTyMethsK c) n) sb) d) i

⊢ipayTyK : {Γ : Ctx} {dd c n sb d i : RTm ⌊ Γ ⌋} →
           Γ ⊢ dd ∷ Nat → Γ ⊢ c ∷ K (pair sICon dd) →
           Γ ⊢ n ∷ Nat → Γ ⊢ sb ∷ SubTy dd n →
           Γ ⊢ d ∷ K (pair sIDesc n) → Γ ⊢ i ∷ K (pair sTy nzero) →
           Γ ⊢ ipayTyK dd c n sb d i ∷ K (pair sTy n)
⊢ipayTyK ddd dc dn dsb dD dI =
  ⊢ipayAppK (⊢ielim KnotWf ⊢ipayTyMotK (⊢ixP ⊢sICon ddd) ⊢ipayTyMethsK dc)
            dn dsb dD dI
