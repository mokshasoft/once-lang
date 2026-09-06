------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `methTy`, THE OBJECT LEVEL.  One of the six
-- programs `⊢elim`/`⊢ielim` need before they can be emitted.
--
-- ★★★ AND IT IS AN ASSEMBLY, NOT A RECURSION — every piece already
--   existed and was already TYPED.  That is the dividend of closing the
--   `Ty` sort first: `payTyK`, `ihTyK`, `atConK`, `wkTyUnderK` and
--   `wkTyK` are all `Ty`-sorted, and until 2026-09-06 each was ⬜ OWED.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.MethTy where
open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; pair; nsuc; Nat )
open import DirectedHoTT.Spec.Typing using ( Ctx; _⊢_∷_; ⌊_⌋; ⊢nsuc )
open import DirectedHoTT.Examples.Knot.Desc using ( K )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( sTy; sTm; sDesc; sDCon; ⊢sDCon )
open import DirectedHoTT.Examples.Knot.PayTy using ( payTyK; ⊢payTyK )
open import DirectedHoTT.Examples.Knot.IhTy using ( ihTyK; ⊢ihTyK )
open import DirectedHoTT.Examples.Knot.ConS using ( atConK; ⊢atConK )
open import DirectedHoTT.Examples.Knot.WkSub
  using ( wkTyK; ⊢wkTyK; wkTyUnderK; ⊢wkTyUnderK; wkAtK; ⊢wkAtK )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-PiK; Tm-varK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Ty-PiKv; ⊢Tm-varKv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; ⊢Var-vzKt )

------------------------------------------------------------------------
-- ★ `methTy D k C M` — `Spec/Typing`:
--
--     Π (payTy D C)
--       (Π (ihTy D C (var vz) (renTy (extR vs) M))
--          (renTy vs (atCon k M)))
--
-- ⚠ `D` AND `C` ARRIVE AT THE AMBIENT DEPTH, not at 0.  `cDesc-cons`'s
--   fields are `rec("sDCon", D)` and `rec("sDesc", D)` — the knot stores a
--   `Desc` at depth n with its `DCon`s at depth n — so there is no `εwkK`
--   here, unlike `⊢con`'s emitted row where the rule's OWN binder is
--   closed.
--
-- ⚠⚠ AND ONE WEAKENING APPEARS THAT THE SPEC DOES NOT HAVE.  `ihTy`'s
--   ambient is `Γ ∙` (it is the inner Π's domain, under the payload
--   binder) while `C` is at `Γ`, so the object level must write
--   `wkAtK sDCon n C` where the spec just writes `C` — the spec can,
--   because `DCon` is CLOSED and carries no context at all.
--   ⇒ its adequacy is a closed-sort identity (`Knot/RenClosed`), not a
--     new theorem; recorded as owed rather than assumed.
------------------------------------------------------------------------

methTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
methTyK n k D C M =
  Ty-PiK (payTyK n C D)
         (Ty-PiK (ihTyK (nsuc n) (wkAtK sDCon n C)
                        (Tm-varK (Var-vzK n)) (wkTyUnderK n M))
                 (wkTyK (nsuc n) (atConK n k M)))

⊢methTyK : {Γ : Ctx} {n k D C M : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat →
           Γ ⊢ D ∷ K (pair sDesc n) → Γ ⊢ C ∷ K (pair sDCon n) →
           Γ ⊢ M ∷ K (pair sTy (nsuc n)) →
           Γ ⊢ methTyK n k D C M ∷ K (pair sTy n)
⊢methTyK {n = n} dn dk dD dC dM =
  ⊢Ty-PiKv n dn
    (⊢payTyK dn dC dD)
    (⊢Ty-PiKv (nsuc n) (⊢nsuc dn)
      (⊢ihTyK (⊢nsuc dn) (⊢wkAtK ⊢sDCon dn dC)
              (⊢Tm-varKv (nsuc n) (⊢nsuc dn) (⊢Var-vzKt dn))
              (⊢wkTyUnderK dn dM))
      (⊢wkTyK (⊢nsuc dn) (⊢atConK dn dk dM)))
