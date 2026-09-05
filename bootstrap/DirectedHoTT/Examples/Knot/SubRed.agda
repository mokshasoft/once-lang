------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ THE PER-ROW HEAD REDUCTION FOR **SUBSTITUTION**.
-- `Knot/RenRed`'s twin, at the other instantiation.
--
--     subAtK s dd m σ (icon k p)
--       ⟶  ι-ielim           app³ (sel k subMethsK) i p ih
--       ⟶* isubMeths-sel     app³ (sdMeth giveK 0 subDescK k) i p ih   (half 1)
--       ⟶* isubMethod-red    icon k (isubPay w …)                       (half 2)
--
-- ★ THE HYPOTHESES ARE DISCHARGED: `Knot/SubNat.extNK-sub` is `ExtNSub`
--   and `fordMapK-sub` is `FordMapSub`.  At the RENAMING instantiation the
--   second was `refl`; here it is a real proof, because `fordMapK` USES
--   the tag that `renFordMap` ignores.
--
-- ★★★ AND THAT IS WHERE COMPUTING THE `SubCon` EARNS ITS KEEP.  A wrong
--   ford tag is INVISIBLE at the renaming instantiation — measured: it
--   left a row green — and would surface only HERE, after 30 renaming
--   rows had been trusted.  `wOfS` reads the classification off
--   `decSubCon`, so there is no tag to get wrong at either instance.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubRed where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; Var; vz; vs; app; pair; fst; snd; icon; ICon
        ; iihs; isingle; ilookupD; IDesc )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; ι-ielim )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import DirectedHoTT.Lib.ISub using ( ttsd; ⊤sd; ⊥sd )
open import DirectedHoTT.Lib.IWk using ( Maybe; just; nothing )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
import DirectedHoTT.Lib.ISub as IS
open import DirectedHoTT.Examples.Knot.SubMot
  using ( extNK; sortMap; decStableK; fordMapK; subTmK; subMethsK; subDescK; giveK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subAtK )
open import DirectedHoTT.Examples.Knot.SubNat using ( extNK-sub; fordMapK-sub )
open IS.Sub extNK sortMap decStableK fordMapK

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

-- ★ the two hypotheses, at THIS instantiation.
hE-sub : ExtNSub
hE-sub = extNK-sub

hF-sub : FordMapSub
hF-sub = fordMapK-sub

------------------------------------------------------------------------
-- ★ THE ROW'S `SubCon`, COMPUTED — `Knot/RenRed.wOf`'s twin.  ⚠ AND HERE
--   IT EARNS ITS KEEP: `fordMapK` USES the ford tag (three times), so a
--   wrong tag would fail HERE, at this instantiation, after having gone
--   green through all 30 renaming rows.  Computing it makes that
--   impossible rather than merely caught.
------------------------------------------------------------------------

JustOf : {A : Set} → Maybe A → Set
JustOf (just _) = ⊤sd
JustOf nothing  = ⊥sd

theJust : {A : Set} (m : Maybe A) → JustOf m → A
theJust (just a) _ = a
theJust nothing ()

wOfS : (k : ℕ) → JustOf (decSubCon vz (ilookupD KnotD k)) →
       SubCon vz (ilookupD KnotD k)
wOfS k p = theJust (decSubCon vz (ilookupD KnotD k)) p

sub-head-red :
  {Γ : Cx} (k : ℕ) (msel : InSD? subDescK k)
  (pj : JustOf (decSubCon vz (ilookupD KnotD k))) →
  sdMeth giveK 0 subDescK k ≡ isubMethod k (wOfS k pj) →
  (s dd m σ p : RTm Γ) →
  subAtK s dd m σ (icon k p) ⟶*
    icon k (isubPay (wOfS k pj) (fst (pair s dd)) (snd (pair s dd)) m σ p
              (iihs KnotD subMethsK (isingle (pair s dd)) (ilookupD KnotD k) p))
sub-head-red k msel pj eq s dd m σ p =
  ⟶*-appˡ (⟶*-appˡ
    (step (ι-ielim KnotD (pair s dd) subMethsK k p)
          (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
            (⟶*-castᵣ eq (isubMeths-sel subDescK 0 k msel))))))) »
  isubMethod-red hE-sub hF-sub (wOfS k pj) k _ _ _ _ _

-- ⇒ AND IT IS CALLABLE.
-- ⇒ AND IT IS CALLABLE (`judge-abstractions-at-the-use-site`).
rowS0 : {Γ : Cx} (s dd m σ p : RTm Γ) → _
rowS0 s dd m σ p = sub-head-red 0 ttsd ttsd refl s dd m σ p
