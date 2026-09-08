------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE TWO `wkTyUnder` WEAKENINGS AGREE.
--
--   wkTyUnder-agree  : wkTyUnderK  ⌈|Γ|⌉ ⌈A⌉ ⟶* ⌈ renTy (extR vs) A ⌉
--   wkTyUnder2-agree : wkTyUnder2K ⌈|Γ|⌉ ⌈A⌉ ⟶* ⌈ renTy (extR (extR vs)) A ⌉
--
-- Discharges two ledger entries.  Both are ONE `renTmAtK sTy` over a
-- stack of `extRNK`s ending in `vsRenK`, so both are `ren-agree-ty`
-- applied to a `RepresentsR` witness built by iterating
-- `extR-Represents` over `wk-Represents`.  One line each.
--
-- ★★★ THE `vsRenK` WITNESS ALREADY EXISTED, AND THAT IS THE WHOLE STORY.
--   `Knot/SubSpec.wk-Represents : RepresentsR vs (vsRenK (num (len Γ)))`
--   has been there since the renaming layer.  Nothing pointed at it from
--   these entries because `vsRenK` IS NOT IN THE LEDGER — it is a `lam`
--   around the constructor `Var-vsK`, so the scanner never flagged it,
--   so it never appeared as a dependency to check.
--
--   ⚠ GENERALISE: "callee not in the ledger" does NOT mean "callee is
--     free", and it does not mean "blocked" either.  It means the
--     scanner had no opinion, and someone has to look.  Three entries
--     sat OWED behind a lemma that was already proved.
--
-- ⚠ `wkTyUnder2K` IS NOT `wkTyUnderK` TWICE — it is ONE renaming by
--   `extR (extR vs)`, not two successive weakenings.  The witness nests
--   (`extR-Represents` applied twice) but the reduction does not.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.WkTyAgree where

open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; RTm; RTy; extR; renTy; vs )
open import DirectedHoTT.Spec.Typing using ( _⟶*_ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )
open import DirectedHoTT.Examples.Knot.Map using ( enTy )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyUnderK )
open import DirectedHoTT.Examples.Knot.IMethTy using ( wkTyUnder2K )
open import DirectedHoTT.Examples.Knot.RenAgreeTyTie using ( ren-agree-ty )
open import DirectedHoTT.Examples.Knot.SubAgree using ( extR-Represents )
open import DirectedHoTT.Examples.Knot.SubSpec using ( wk-Represents )

wkTyUnder-agree : {Γ Θ : Cx} (A : RTy (Γ ∙)) →
                  wkTyUnderK {Θ} (num (len Γ)) (enTy {Γ ∙} {Θ} A)
                  ⟶* enTy {(Γ ∙) ∙} {Θ} (renTy (extR vs) A)
wkTyUnder-agree {Γ} A =
  ren-agree-ty (extR-Represents (num (len Γ)) wk-Represents) A

wkTyUnder2-agree : {Γ Θ : Cx} (A : RTy ((Γ ∙) ∙)) →
                   wkTyUnder2K {Θ} (num (len Γ)) (enTy {(Γ ∙) ∙} {Θ} A)
                   ⟶* enTy {((Γ ∙) ∙) ∙} {Θ} (renTy (extR (extR vs)) A)
wkTyUnder2-agree {Γ} A =
  ren-agree-ty
    (extR-Represents (num (len (Γ ∙)))
      (extR-Represents (num (len Γ)) wk-Represents)) A
