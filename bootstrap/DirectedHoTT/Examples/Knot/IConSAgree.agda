------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `iconSSK`'s ADEQUACY, BOTH ROWS.
--
-- `Knot/ConSAgree`'s CLONE, and the ledger called it one: "a clone of
-- `conSSK` with `icon` for `con`".  Measured, it is tighter than that —
-- `Knot/IConS` reuses `conSMotK`, `conSJunk` AND `conSVs` VERBATIM
-- (`iconSTail = pair iconSVz (pair conSVs unit)`), so only the `vz` row
-- differs, and only in `Tm-iconK` for `Tm-conK`.
--
-- ⚠⚠ AND THIS IS WHERE THE CASCADE STOPS BEING A CLONE.  The meta-level
--   `iconS` has THREE clauses, not two (`Spec/Typing:169`):
--
--       iconS k i vz          = icon k (var vz)
--       iconS k i (vs vz)     = renTm vs i
--       iconS k i (vs (vs x)) = var (vs x)
--
--   `iconSSK`/`icSK` are the ONE-LEVEL `Var`-sort part — two rows, and
--   those are what this module proves.  The third clause is `iconSK`'s
--   job, which is why `iconSK` composes with `extNK` and is NOT a clone
--   of `conSK`.  ⇒ do not expect `atConK`'s one-liner at `iatConK`:
--   its substitution also CHANGES DEPTH (`nsuc (nsuc n) → nsuc n`).
--
-- ★ No `Represents` packaging here, for the same reason: `Represents`
--   wants the full `iconS`, which is `iconSK`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IConSAgree where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; ielim; app; icon; pair; unit; idrefl; ⌜Nat⌝
        ; iihs; isingle; sel; nsuc )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; step; done; βfst; βsnd; β; jsub-refl; wk-single )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-jsubᵖ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst
        ; ⟶*-idreflᵃ; ⟶*-nsuc )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂ )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Lib.IMeths using ( cdTake; methsFrom-past; sel-there; sel-here )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Sorts using ( sVar )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz; tagVar-vs )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK )
open import DirectedHoTT.Examples.Knot.ConS using ( conSVs )
open import DirectedHoTT.Examples.Knot.IConS using ( iconSMeths; iconSVz; icSK; iconSSK )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-varK; Tm-iconK )
open import DirectedHoTT.Examples.Knot.RenSpec using ( inVar )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import DirectedHoTT.Lib.Wk using ( sub-w²-single )
open import DirectedHoTT.Spec.Syntax using ( Var; vz; vs )
open import DirectedHoTT.Spec.Typing using ( conS )
open import DirectedHoTT.Examples.Knot.SubAgree using ( Represents )
open import DirectedHoTT.Examples.Knot.Map using ( enVar; enTm )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )

------------------------------------------------------------------------
-- STEP 1 — the head reduction at the `vz` row.
--
-- ★ Written with `Lib/IHeadRed.ihead-red` rather than spelled out, which
--   is what `Knot/RenSpec.singleSK-vz` does by hand.
------------------------------------------------------------------------
iconSS-vz : {Γ : Cx} (i m : RTm Γ) →
           ielim KnotD i iconSMeths (Var-vzK m) ⟶*
             app (app (app iconSVz i)
                      (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                    (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
                 (iihs KnotD iconSMeths (isingle i) cVar-vz
                       (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                     (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
iconSS-vz i m =
  ihead-red KnotD iconSMeths tagVar-vz i _
    (methsFrom-past (cdTake 51 KnotD) zero » step (βfst _ _) done)
    done

------------------------------------------------------------------------
-- STEP 2 — the head reduction at the `vs` row.
--
-- ⚠ The SELECTION differs, not the shape: `vz` is the tail's first
--   element (one `βfst`), `vs` its second (`sel-there` then `sel-here`).
------------------------------------------------------------------------
iconSS-vs : {Γ : Cx} (i m x : RTm Γ) →
           ielim KnotD i iconSMeths (Var-vsK m x) ⟶*
             app (app (app conSVs i)
                      (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                            (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
                 (iihs KnotD iconSMeths (isingle i) cVar-vs
                       (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                             (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
iconSS-vs i m x =
  ihead-red KnotD iconSMeths tagVar-vs i _
    (methsFrom-past (cdTake 51 KnotD) (suc zero) »
     sel-there 0 _ _ (sel-here _ _))
    done

------------------------------------------------------------------------
-- ★ BOTH HEAD REDUCTIONS GO THROUGH `Lib/IHeadRed.ihead-red`, of which
--   `iconSSK` is the fourth client.  Only the SELECTION differs between
--   the two rows: `vz` is the tail's first element (one `βfst`), `vs`
--   its second (`sel-there` then `sel-here`).
------------------------------------------------------------------------

-- ★★ THREE CONGRUENCES `singleK-vs` DID NOT NEED.  `Var-vzK a` and
--   `Var-vsK a b` mention the LEVEL `a` TWICE — the field AND the
--   ford's `nsuc a` — so reducing it is two descents, not one.  That is
--   the whole difference from `singleK-vs`, whose target `Tm-varK x`
--   mentions its argument once.  ⇒ `narrow-twin-shadows-general-form`
--   in miniature: the template's ONE descent was never the general case.
------------------------------------------------------------------------

vsLvl : {Γ : Cx} {a a' b : RTm Γ} → a ⟶* a' → Var-vsK a b ⟶* Var-vsK a' b
vsLvl r = ⟶*-icon (⟶*-pairˡ r)
        » ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairʳ
            (⟶*-pairˡ (⟶*-idreflᵃ (⟶*-nsuc r))))))

vsVal : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Var-vsK a b ⟶* Var-vsK a b'
vsVal r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

vzLvl : {Γ : Cx} {a a' : RTm Γ} → a ⟶* a' → Var-vzK a ⟶* Var-vzK a'
vzLvl r = ⟶*-icon (⟶*-pairˡ r)
        » ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ
            (⟶*-pairˡ (⟶*-idreflᵃ (⟶*-nsuc r)))))

inIcon : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Tm-iconK a b ⟶* Tm-iconK a b'
inIcon r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

------------------------------------------------------------------------
-- ★★★ STEP 3 — `iconSSK`, AT THE LEDGER'S OWN NAME.
--
--     conS k vz     = con k (var vz)
--     conS k (vs x) = var (vs x)
--
-- ★ See the module header for why the four earlier attempts stuck, and
--   for the three differences from the `singleK` template.
------------------------------------------------------------------------

iconSSK-vz : {Γ : Cx} (i m k : RTm Γ) →
            iconSSK i (Var-vzK m) k ⟶* Tm-iconK k (Tm-varK (Var-vzK m))
iconSSK-vz i m k =
  -- ⚠ THE FORD IS ONE FIELD SHALLOWER THAN THE `vs` ROW's: `Var-vzK`'s
  --   payload has three fields to `Var-vsK`'s four (no `x`), so the
  --   depth ford is `sel 2`, not `sel 3`.
  ⟶*-castᵣ (cong (λ z → Tm-iconK k (Tm-varK (Var-vzK z))) (sub-w²-single m))
  (⟶*-appˡ (iconSS-vz _ _) »
   ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
   ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
   ⟶*-appˡ (step (β _ _) done) »
   step (β _ _) done »
   inIcon (inVar (⟶*-jsubᵖ (⟶*-jsubᵖ
     (sel-there 1 _ _ (sel-there 0 _ _ (sel-here _ _)))))) »
   inIcon (inVar (⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done))) »
   inIcon (inVar (step (jsub-refl _ _ _ _) done)) »
   inIcon (inVar (vzLvl (sel-here _ _))))

iconSSK-vs : {Γ : Cx} (i m x k : RTm Γ) →
            iconSSK i (Var-vsK m x) k ⟶* Tm-varK (Var-vsK m x)
iconSSK-vs i m x k =
  ⟶*-castᵣ (cong₂ (λ p q → Tm-varK (Var-vsK p q))
                  (sub-w²-single m) (sub-w²-single x))
  (⟶*-appˡ (iconSS-vs _ _ _) »
   ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
   ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
   ⟶*-appˡ (step (β _ _) done) »
   step (β _ _) done »
   inVar (⟶*-jsubᵖ (⟶*-jsubᵖ
     (sel-there 2 _ _ (sel-there 1 _ _ (sel-there 0 _ _ (sel-here _ _)))))) »
   inVar (⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done)) »
   inVar (step (jsub-refl _ _ _ _) done) »
   inVar (vsLvl (sel-here _ _)) »
   inVar (vsVal (sel-there 0 _ _ (sel-here _ _))))

------------------------------------------------------------------------
-- ★★ STEP 4 — `icSK`, THE SUBSTITUTION.  Both rows are ONE β on top of
--   step 3, which is what stating the theorem at `iconSSK` bought.
--
-- ★ THE `vs` ROW NEEDS NO CAST AT ALL: its target mentions neither `n`
--   nor `k`, so `icSK`'s two weakenings never have to be undone.  The
--   `vz` row DOES carry the tag, and that is the one `wk-single`.
------------------------------------------------------------------------

icSK-vz : {Γ : Cx} (n k m : RTm Γ) →
           app (icSK n k) (Var-vzK m) ⟶* Tm-iconK k (Tm-varK (Var-vzK m))
icSK-vz n k m =
  ⟶*-castᵣ (cong (λ z → Tm-iconK z (Tm-varK (Var-vzK m)))
                 (wk-single {v = Var-vzK m} k))
           (step (β _ _) (iconSSK-vz _ _ _))

icSK-vs : {Γ : Cx} (n k m x : RTm Γ) →
           app (icSK n k) (Var-vsK m x) ⟶* Tm-varK (Var-vsK m x)
icSK-vs n k m x = step (β _ _) (iconSSK-vs _ _ _ _)

