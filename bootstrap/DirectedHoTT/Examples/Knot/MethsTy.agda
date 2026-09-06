------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `methsTyFrom` AND `methsTy`, ASSEMBLED.
--
--     methsTyFromK n D M j E  ⟵  methsTyFrom D M j E
--     methsTyK     n D M   E  ⟵  methsTy D M E = methsTyFrom D M 0 E
--
-- ★ TWO ROWS OF 53 ARE REAL.  `cDesc-nil` (41) takes the junk method,
--   and for it the junk IS the answer (`methsTyFrom D M j dnil = Unit`);
--   `cDesc-cons` (42) is `Knot/MethsTyCons`.  ⚠ Nothing here enumerates a
--   row — `Lib/IMeths.methsFrom` fills the other 51.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.MethsTy where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; IDesc; app; pair; unit; _◂_; ielim; nsuc; nzero; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢unit
        ; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim; ⊢nzero )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methsFrom; ⊢methsCons; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sDesc; ⊢sDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cDesc-cons )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.MethsTyMot
  using ( methsTyMotK; ⊢methsTyMotK; methsTyJunk; ⊢methsTyJunk; ⊢methsAppK )
open import DirectedHoTT.Examples.Knot.MethsTyCons
  using ( methsTyCons; ⊢methsTyCons )

MD43 : IDesc
MD43 = cdRest (cdTake 43 KnotD)

MD42' : IDesc
MD42' = cDesc-cons ◂ MD43

mspl42 : Split KnotD 42 MD42'
mspl42 = splTake spl-nil (cdTake 42 KnotD)

mwf43 : IDescWfFrom KnotD IPair MD43
mwf43 = idwfDrop (spl-step mspl42) KnotWf

-- ★ 53 − 43 = 10 rows after `cDesc-cons`, all junk.
methsTyTail : {Γ : Cx} → RTm Γ
methsTyTail = methsFrom (cdTake 10 MD43) methsTyJunk unit

⊢methsTyTail : {Γ : Ctx} →
               Γ ⊢ methsTyTail ∷ imethsTyFrom KnotD IPair methsTyMotK 43 MD43
⊢methsTyTail =
  ⊢methsFrom KnotD IPair 43 (cdTake 10 MD43) KnotWf mwf43 (spl-step mspl42)
             ⊢IPair ⊢methsTyMotK (λ {k} {C} wC _ _ → ⊢methsTyJunk k C wC)
             unit ⊢unit

methsTyMid42 : {Γ : Cx} → RTm Γ
methsTyMid42 = pair methsTyCons methsTyTail

⊢methsTyMid42 : {Γ : Ctx} →
                Γ ⊢ methsTyMid42 ∷ imethsTyFrom KnotD IPair methsTyMotK 42 MD42'
⊢methsTyMid42 =
  ⊢methsCons KnotD IPair 42 {C = cDesc-cons} MD43 KnotWf mwf43
             (spl-step mspl42) ⊢IPair ⊢methsTyMotK
             ⊢methsTyCons ⊢methsTyTail

methsTyMethsK : {Γ : Cx} → RTm Γ
methsTyMethsK = methsFrom (cdTake 42 KnotD) methsTyJunk methsTyMid42

⊢methsTyMethsK : {Γ : Ctx} →
                 Γ ⊢ methsTyMethsK ∷ imethsTy KnotD IPair methsTyMotK KnotD
⊢methsTyMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 42 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢methsTyMotK (λ {k} {C} wC _ _ → ⊢methsTyJunk k C wC)
             methsTyMid42 ⊢methsTyMid42

------------------------------------------------------------------------
-- ★ THE WRAPPERS.
------------------------------------------------------------------------

methsTyFromK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
methsTyFromK n D M j E =
  app (app (app (ielim KnotD (pair sDesc n) methsTyMethsK E) D) M) j

⊢methsTyFromK : {Γ : Ctx} {n D M j E : RTm ⌊ Γ ⌋} →
                Γ ⊢ n ∷ Nat → Γ ⊢ D ∷ K (pair sDesc n) →
                Γ ⊢ M ∷ K (pair sTy (nsuc n)) → Γ ⊢ j ∷ Nat →
                Γ ⊢ E ∷ K (pair sDesc n) →
                Γ ⊢ methsTyFromK n D M j E ∷ K (pair sTy n)
⊢methsTyFromK dn dD dM dj dE =
  ⊢methsAppK (⊢ielim KnotWf ⊢methsTyMotK (⊢ixP ⊢sDesc dn) ⊢methsTyMethsK dE)
             dD dM dj

-- ★ `methsTy D M E = methsTyFrom D M zero E` — the tag starts at 0.
--   ⚠ THE OFFSET IS NOT DECORATION.  `Lib`'s note on `methsTyFrom`: each
--     method's result is `atCon k M`, the motive at ITS OWN constructor,
--     so the k-th entry carries tag `k`.  With a fixed 0 every method
--     would claim to produce `M[con 0 …]` and `sel-ty` would be
--     unprovable.
methsTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
methsTyK n D M E = methsTyFromK n D M nzero E

⊢methsTyK : {Γ : Ctx} {n D M E : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ D ∷ K (pair sDesc n) →
            Γ ⊢ M ∷ K (pair sTy (nsuc n)) → Γ ⊢ E ∷ K (pair sDesc n) →
            Γ ⊢ methsTyK n D M E ∷ K (pair sTy n)
⊢methsTyK dn dD dM dE = ⊢methsTyFromK dn dD dM ⊢nzero dE
