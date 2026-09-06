------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `iihTy`, ASSEMBLED.
--
--     iihTyK dd c n sb q M  ⟵  iihTy D I σ C q M
--
-- ★ THREE ROWS OF 53 ARE REAL, and one of those is the junk method:
--   `cICon-i` (48) takes `iihTyJunk`, and for it the junk IS the answer
--   (`iihTy … iι q M = Unit`); `cICon-rho` (49) and `cICon-kap` (50) are
--   `Knot/IhITyRows`.  ⚠ `D` and `I` are PHANTOMS in the spec and so do
--   not appear here at all.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhITy where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; IDesc; app; pair; unit; _◂_; ielim; nsuc; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢unit
        ; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methsFrom; ⊢methsCons; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sTm; sICon; ⊢sICon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cICon-rho; cICon-kap )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.IhITyMot
  using ( iihTyMotK; ⊢iihTyMotK; iihTyJunk; ⊢iihTyJunk; ⊢iihAppK )
open import DirectedHoTT.Examples.Knot.IhITyRows
  using ( iihTyRho; ⊢iihTyRho; iihTyKap; ⊢iihTyKap )

HID51 : IDesc
HID51 = cdRest (cdTake 51 KnotD)

HID50' : IDesc
HID50' = cICon-kap ◂ HID51

HID49' : IDesc
HID49' = cICon-rho ◂ HID50'

hispl49 : Split KnotD 49 HID49'
hispl49 = splTake spl-nil (cdTake 49 KnotD)

hiwf50 : IDescWfFrom KnotD IPair HID50'
hiwf50 = idwfDrop (spl-step hispl49) KnotWf

hiwf51 : IDescWfFrom KnotD IPair HID51
hiwf51 = idwfDrop (spl-step (spl-step hispl49)) KnotWf

iihTyTail : {Γ : Cx} → RTm Γ
iihTyTail = methsFrom (cdTake 2 HID51) iihTyJunk unit

⊢iihTyTail : {Γ : Ctx} →
             Γ ⊢ iihTyTail ∷ imethsTyFrom KnotD IPair iihTyMotK 51 HID51
⊢iihTyTail =
  ⊢methsFrom KnotD IPair 51 (cdTake 2 HID51) KnotWf hiwf51
             (spl-step (spl-step hispl49))
             ⊢IPair ⊢iihTyMotK (λ {k} {C} wC _ _ → ⊢iihTyJunk k C wC)
             unit ⊢unit

iihTyMid50 : {Γ : Cx} → RTm Γ
iihTyMid50 = pair iihTyKap iihTyTail

⊢iihTyMid50 : {Γ : Ctx} →
              Γ ⊢ iihTyMid50 ∷ imethsTyFrom KnotD IPair iihTyMotK 50 HID50'
⊢iihTyMid50 =
  ⊢methsCons KnotD IPair 50 {C = cICon-kap} HID51 KnotWf hiwf51
             (spl-step (spl-step hispl49)) ⊢IPair ⊢iihTyMotK
             ⊢iihTyKap ⊢iihTyTail

iihTyMid49 : {Γ : Cx} → RTm Γ
iihTyMid49 = pair iihTyRho iihTyMid50

⊢iihTyMid49 : {Γ : Ctx} →
              Γ ⊢ iihTyMid49 ∷ imethsTyFrom KnotD IPair iihTyMotK 49 HID49'
⊢iihTyMid49 =
  ⊢methsCons KnotD IPair 49 {C = cICon-rho} HID50' KnotWf hiwf50
             (spl-step hispl49) ⊢IPair ⊢iihTyMotK
             ⊢iihTyRho ⊢iihTyMid50

iihTyMethsK : {Γ : Cx} → RTm Γ
iihTyMethsK = methsFrom (cdTake 49 KnotD) iihTyJunk iihTyMid49

⊢iihTyMethsK : {Γ : Ctx} →
               Γ ⊢ iihTyMethsK ∷ imethsTy KnotD IPair iihTyMotK KnotD
⊢iihTyMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 49 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢iihTyMotK (λ {k} {C} wC _ _ → ⊢iihTyJunk k C wC)
             iihTyMid49 ⊢iihTyMid49

------------------------------------------------------------------------
-- ★ THE WRAPPER.
------------------------------------------------------------------------

iihTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
iihTyK dd c n sb q M =
  app (app (app (app (ielim KnotD (pair sICon dd) iihTyMethsK c) n) sb) q) M

⊢iihTyK : {Γ : Ctx} {dd c n sb q M : RTm ⌊ Γ ⌋} →
          Γ ⊢ dd ∷ Nat → Γ ⊢ c ∷ K (pair sICon dd) →
          Γ ⊢ n ∷ Nat → Γ ⊢ sb ∷ SubTy dd n →
          Γ ⊢ q ∷ K (pair sTm n) → Γ ⊢ M ∷ K (pair sTy (nsuc (nsuc n))) →
          Γ ⊢ iihTyK dd c n sb q M ∷ K (pair sTy n)
⊢iihTyK ddd dc dn dsb dq dM =
  ⊢iihAppK (⊢ielim KnotWf ⊢iihTyMotK (⊢ixP ⊢sICon ddd) ⊢iihTyMethsK dc)
           dn dsb dq dM
