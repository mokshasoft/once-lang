------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `imethTy`, THE OBJECT LEVEL.
--
--     imethTy D I k C M =
--       Π (εwkTy I)
--         (Π (ipayTy D I (isingle (var vz)) C)
--            (Π (iihTy D I (isingle (var (vs vz))) C (var vz)
--                      (renTy (extR (extR vs)) (renTy (extR (extR vs)) M)))
--               (renTy vs (iatCon k (var vz) (renTy (extR (extR vs)) M)))))
--
-- ⚠⚠ THE MOTIVE APPEARS AT THREE DIFFERENT DEPTHS, and they are NOT the
--   same term.  `M` is at n+2; the RESULT weakens it ONCE (to n+3) while
--   the IH-tuple's type weakens it TWICE (to n+4).  Reading `renTy (extR
--   (extR vs))` as "the same weakening" and sharing it would put the
--   result one binder too deep.
--
-- ⚠ AND THE TWO `var vz`s ARE DIFFERENT BINDERS.  In the `iihTy` argument
--   `var vz` is Π₂'s (the PAYLOAD, at n+2); in `iatCon` it is Π₁'s (the
--   INDEX, at n+1) — because `iatCon k i M` is written in `Γ ∙` and then
--   renamed up by the outer `renTy vs`.  At the object level a variable
--   is a CONSTRUCTOR, so this shows up as two different `Var-vzK` depths
--   rather than as two different de Bruijn indices.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IMethTy where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; pair; nsuc; nzero; Nat; vs; renTm )
open import DirectedHoTT.Spec.Typing using ( Ctx; _⊢_∷_; ⌊_⌋; ⊢nsuc )
open import DirectedHoTT.Lib.NatNum using ( num; ⊢num )

open import DirectedHoTT.Examples.Knot.Desc using ( K )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( sTy; ⊢sTy; sTm; sICon; sIDesc; ⊢sIDesc )
open import DirectedHoTT.Examples.Knot.SubMot using ( sortMap-ty )
open import DirectedHoTT.Examples.Knot.EWk
  using ( εwkK; ⊢εwkK; isingleK; ⊢isingleK )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-PiK; Tm-varK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Ty-PiKv; ⊢Tm-varKv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; ⊢Var-vzKt )
open import DirectedHoTT.Examples.Knot.RenTm
  using ( renTmAtK; ⊢renTmAtK; vsRenK; ⊢vsRenK )
open import DirectedHoTT.Examples.Knot.RenMot using ( extRNK; ⊢extRNK )
open import DirectedHoTT.Examples.Knot.WkSub
  using ( wkTyK; ⊢wkTyK; wkAtK; ⊢wkAtK )
open import DirectedHoTT.Examples.Knot.IPayTy using ( ipayTyK; ⊢ipayTyK )
open import DirectedHoTT.Examples.Knot.IhITy using ( iihTyK; ⊢iihTyK )
open import DirectedHoTT.Examples.Knot.IConS using ( iatConK; ⊢iatConK )

------------------------------------------------------------------------
-- ★ `renTy (extR (extR vs))` — weakening UNDER TWO binders.
-- ⚠ `Knot/WkSub.wkTyUnderK` is the one-binder form; this is `extRNK`
--   applied once more, and nothing else needed it until now.
------------------------------------------------------------------------

wkTyUnder2K : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkTyUnder2K n A =
  renTmAtK sTy (nsuc (nsuc n)) (nsuc (nsuc (nsuc n)))
           (extRNK (nsuc n) (nsuc (nsuc n)) (extRNK n (nsuc n) (vsRenK n))) A

⊢wkTyUnder2K : {Γ : Ctx} {n A : RTm ⌊ Γ ⌋} →
               Γ ⊢ n ∷ Nat → Γ ⊢ A ∷ K (pair sTy (nsuc (nsuc n))) →
               Γ ⊢ wkTyUnder2K n A ∷ K (pair sTy (nsuc (nsuc (nsuc n))))
⊢wkTyUnder2K dn dA =
  ⊢renTmAtK ⊢sTy (⊢nsuc (⊢nsuc dn)) (⊢nsuc (⊢nsuc (⊢nsuc dn)))
            (⊢extRNK (⊢nsuc dn) (⊢nsuc (⊢nsuc dn))
                     (⊢extRNK dn (⊢nsuc dn) (⊢vsRenK dn)))
            dA

------------------------------------------------------------------------
-- ★★★ `imethTy`.
------------------------------------------------------------------------

imethTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
imethTyK n k D I C M =
  Ty-PiK (εwkK sTy n I)
    (Ty-PiK (ipayTyK (num 1) C (nsuc n)
                     (isingleK (Tm-varK (Var-vzK n)))
                     (wkAtK sIDesc n D) I)
      (Ty-PiK (iihTyK (num 1) C (nsuc (nsuc n))
                      (isingleK (Tm-varK (Var-vzK (nsuc n))))
                      (Tm-varK (Var-vzK (nsuc n)))
                      (wkTyUnder2K (nsuc n) (wkTyUnder2K n M)))
              (wkTyK (nsuc (nsuc n))
                     (iatConK (nsuc n) k (Tm-varK (Var-vzK n))
                              (wkTyUnder2K n M)))))

⊢imethTyK : {Γ : Ctx} {n k D I C M : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat →
            Γ ⊢ D ∷ K (pair sIDesc n) → Γ ⊢ I ∷ K (pair sTy nzero) →
            Γ ⊢ C ∷ K (pair sICon (num 1)) →
            Γ ⊢ M ∷ K (pair sTy (nsuc (nsuc n))) →
            Γ ⊢ imethTyK n k D I C M ∷ K (pair sTy n)
⊢imethTyK {n = n} dn dk dD dI dC dM =
  ⊢Ty-PiKv n dn
    (⊢εwkK ⊢sTy sortMap-ty dn dI)
    (⊢Ty-PiKv (nsuc n) (⊢nsuc dn)
      (⊢ipayTyK (⊢num 1) dC (⊢nsuc dn)
                (⊢isingleK _ (⊢nsuc dn) (⊢Tm-varKv _ (⊢nsuc dn) (⊢Var-vzKt dn)))
                (⊢wkAtK ⊢sIDesc dn dD) dI)
      (⊢Ty-PiKv (nsuc (nsuc n)) (⊢nsuc (⊢nsuc dn))
        (⊢iihTyK (⊢num 1) dC (⊢nsuc (⊢nsuc dn))
                 (⊢isingleK _ (⊢nsuc (⊢nsuc dn))
                            (⊢Tm-varKv _ (⊢nsuc (⊢nsuc dn))
                                       (⊢Var-vzKt (⊢nsuc dn))))
                 (⊢Tm-varKv _ (⊢nsuc (⊢nsuc dn)) (⊢Var-vzKt (⊢nsuc dn)))
                 (⊢wkTyUnder2K (⊢nsuc dn) (⊢wkTyUnder2K dn dM)))
        (⊢wkTyK (⊢nsuc (⊢nsuc dn))
                (⊢iatConK (⊢nsuc dn) dk
                          (⊢Tm-varKv _ (⊢nsuc dn) (⊢Var-vzKt dn))
                          (⊢wkTyUnder2K dn dM)))))
