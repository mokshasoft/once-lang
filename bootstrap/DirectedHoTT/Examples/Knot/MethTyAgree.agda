------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `methTyK` AGREES WITH `methTy`.  PURE COMPOSITION.
--
--   methTy D k C M = Π (payTy D C)
--                      (Π (ihTy D C (var vz) (renTy (extR vs) M))
--                         (renTy vs (atCon k M)))
--
-- ★★★ EVERY INGREDIENT IS ALREADY DISCHARGED, and the last one I
--   expected to have to write was already written too:
--     payTyK-agree        ✅ Knot/PayTyAgree      (today)
--     ihTyK-agree         ✅ Knot/IhTyAgree       (today)
--     wkTyUnder-agree     ✅ Knot/WkTyAgree
--     atCon-agree         ✅ Knot/ConSAgree
--     wkTyK-agree         ✅ Knot/TyAgree
--     ren-DCon-id         ✅ Knot/RenClosed  ← inside a `mutual`, which is
--                            why a `^`-anchored grep does not find it
--
-- ⚠ `methTyK` IS NOT LEDGER-TRACKED — its body applies other programs
--   and never `ielim KnotD` directly, so the scan does not see it.  It is
--   needed here as `methsTyFromK`'s first component.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.MethTyAgree where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; Desc; DCon; var; vz; vs; extR; renTy; Π )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; methTy; atCon; ihTy; payTy )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ )
open import DirectedHoTT.Examples.Knot.Sorts using ( len; sDCon )
open import DirectedHoTT.Examples.Knot.Map using ( enTy; enDesc; enDCon )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-PiK )
open import DirectedHoTT.Examples.Knot.MethTy using ( methTyK )
open import DirectedHoTT.Examples.Knot.PayTyAgree using ( payTyK-agree; ⟶*-wkTyKᵃ )
open import DirectedHoTT.Examples.Knot.IhTyAgree using ( ihTyK-agree )
open import DirectedHoTT.Examples.Knot.WkTyAgree using ( wkTyUnder-agree )
open import DirectedHoTT.Examples.Knot.ConSAgree using ( atCon-agree )
open import DirectedHoTT.Examples.Knot.TyAgree using ( wkTyK-agree )
open import DirectedHoTT.Examples.Knot.RenClosed using ( ren-DCon-id )

-- ★ `Ty-PiK a b = icon tagTy-Pi (pair a (pair b (pair … unit)))`.
inPiL : {Γ : Cx} {a a' b : RTm Γ} → a ⟶* a' → Ty-PiK a b ⟶* Ty-PiK a' b
inPiL r = ⟶*-icon (⟶*-pairˡ r)

inPiR : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Ty-PiK a b ⟶* Ty-PiK a b'
inPiR r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

-- ★ `ihTyK n c q M = app (app (ielim … c) q) M` — three argument slots.
open import DirectedHoTT.Examples.Knot.IhTy using ( ihTyK )

⟶*-ihTyKᶜ : {Γ : Cx} {n c c' q M : RTm Γ} →
            c ⟶* c' → ihTyK n c q M ⟶* ihTyK n c' q M
⟶*-ihTyKᶜ h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ h))

⟶*-ihTyKᴹ : {Γ : Cx} {n c q M M' : RTm Γ} →
            M ⟶* M' → ihTyK n c q M ⟶* ihTyK n c q M'
⟶*-ihTyKᴹ h = ⟶*-appʳ h

------------------------------------------------------------------------
-- ★★★ THE AGREEMENT — five imported lemmas and two congruences.
------------------------------------------------------------------------

methTyK-agree : {Γ Θ : Cx} (D : Desc) (k : ℕ) (C : DCon) (M : RTy (Γ ∙)) →
                methTyK (num (len Γ)) (num k) (enDesc {Θ} D) (enDCon {Θ} C)
                        (enTy {Γ ∙} {Θ} M)
                ⟶* enTy {Γ} {Θ} (methTy {Γ} D k C M)
methTyK-agree {Γ} {Θ} D k C M =
    inPiL (payTyK-agree D C)
  -- ★ the `DCon` argument is WEAKENED on the object side and not on the
  --   meta's — and renaming a CLOSED encoding is the identity.
  » inPiR (inPiL (⟶*-ihTyKᶜ (ren-DCon-id (len Γ) (suc (len Γ)) _ C)))
  » inPiR (inPiL (⟶*-ihTyKᴹ (wkTyUnder-agree M)))
  » inPiR (inPiL (ihTyK-agree D C (var vz) (renTy (extR vs) M)))
  » inPiR (inPiR (⟶*-wkTyKᵃ (atCon-agree k M)))
  » inPiR (inPiR (wkTyK-agree {Γ ∙} (atCon k M)))
