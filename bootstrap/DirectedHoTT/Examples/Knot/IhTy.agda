------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `ihTy`, ASSEMBLED.
--
--     ihTy D dι       q M = Unit
--     ihTy D (dρ C)   q M = Σ' (subTy (single (fst q)) M) (renTy vs (ihTy D C (snd q) M))
--     ihTy D (dκ A C) q M = ihTy D C (snd q) M
--
-- Motive, junk row and the two abstract lemmas are in `Knot/IhTyMot`;
-- the two real rows are one per module.  Tags 44 and 45, ADJACENT —
-- `payTy`'s rows exactly, because `ihTy` recurses on the same `DCon`.
--
-- ★★★ AND `⊢ihAppK` IS THE WRAPPER, AGAIN.  Third time in three
--   functions (`⊢motAppK`/`⊢subAtK`, `⊢ipayAppK`/`⊢ipayTyK`, and here):
--   the lemma that applies a motive's passengers inside the recursion is
--   the whole of the proof outside it.  ⇒ that is not a coincidence about
--   these three functions; it is what an `ielim` at a Π-valued motive IS.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhTy where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; RTy; IDesc; app; pair; unit; _◂_; ielim; nzero; nsuc; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢unit
        ; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methsFrom; ⊢methsCons; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sTm; sDCon; ⊢sDCon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cDCon-rho; cDCon-kap )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.IhTyMot
  using ( ihTyMotK; ⊢ihTyMotK; ihTyJunk; ⊢ihTyJunk; ⊢ihAppK )
open import DirectedHoTT.Examples.Knot.IhTyRho using ( ihTyRho; ⊢ihTyRho )
open import DirectedHoTT.Examples.Knot.IhTyKap using ( ihTyKap; ⊢ihTyKap )

------------------------------------------------------------------------
-- ★ THE TUPLE — junk 0–43 · row 44 · row 45 · junk 46–52.
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

ihTyTail : {Γ : Cx} → RTm Γ
ihTyTail = methsFrom (cdTake 7 HD46) ihTyJunk unit

⊢ihTyTail : {Γ : Ctx} →
            Γ ⊢ ihTyTail ∷ imethsTyFrom KnotD IPair ihTyMotK 46 HD46
⊢ihTyTail =
  ⊢methsFrom KnotD IPair 46 (cdTake 7 HD46) KnotWf hwf46
             (spl-step (spl-step hspl44))
             ⊢IPair ⊢ihTyMotK (λ {k} {C} wC _ _ → ⊢ihTyJunk k C wC)
             unit ⊢unit

ihTyMid45 : {Γ : Cx} → RTm Γ
ihTyMid45 = pair ihTyKap ihTyTail

⊢ihTyMid45 : {Γ : Ctx} →
             Γ ⊢ ihTyMid45 ∷ imethsTyFrom KnotD IPair ihTyMotK 45 HD45'
⊢ihTyMid45 =
  ⊢methsCons KnotD IPair 45 {C = cDCon-kap} HD46 KnotWf hwf46
             (spl-step (spl-step hspl44)) ⊢IPair ⊢ihTyMotK
             ⊢ihTyKap ⊢ihTyTail

ihTyMid44 : {Γ : Cx} → RTm Γ
ihTyMid44 = pair ihTyRho ihTyMid45

⊢ihTyMid44 : {Γ : Ctx} →
             Γ ⊢ ihTyMid44 ∷ imethsTyFrom KnotD IPair ihTyMotK 44 HD44'
⊢ihTyMid44 =
  ⊢methsCons KnotD IPair 44 {C = cDCon-rho} HD45' KnotWf hwf45
             (spl-step hspl44) ⊢IPair ⊢ihTyMotK
             ⊢ihTyRho ⊢ihTyMid45

ihTyMethsK : {Γ : Cx} → RTm Γ
ihTyMethsK = methsFrom (cdTake 44 KnotD) ihTyJunk ihTyMid44

⊢ihTyMethsK : {Γ : Ctx} →
              Γ ⊢ ihTyMethsK ∷ imethsTy KnotD IPair ihTyMotK KnotD
⊢ihTyMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 44 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢ihTyMotK (λ {k} {C} wC _ _ → ⊢ihTyJunk k C wC)
             ihTyMid44 ⊢ihTyMid44

------------------------------------------------------------------------
-- ★★★ `ihTy`, AS A FUNCTION.  ⚠ NO `D` ARGUMENT — see `Knot/IhTyMot`.
------------------------------------------------------------------------

ihTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ihTyK n c q M = app (app (ielim KnotD (pair sDCon n) ihTyMethsK c) q) M

⊢ihTyK : {Γ : Ctx} {n c q M : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ c ∷ K (pair sDCon n) →
         Γ ⊢ q ∷ K (pair sTm n) → Γ ⊢ M ∷ K (pair sTy (nsuc n)) →
         Γ ⊢ ihTyK n c q M ∷ K (pair sTy n)
⊢ihTyK dn dc dq dM =
  ⊢ihAppK (⊢ielim KnotWf ⊢ihTyMotK (⊢ixP ⊢sDCon dn) ⊢ihTyMethsK dc) dq dM
