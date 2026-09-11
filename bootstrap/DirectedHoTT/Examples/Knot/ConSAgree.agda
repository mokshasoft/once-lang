------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `conSSK`'s ADEQUACY, BOTH ROWS.
--
--     conS k vz     = con k (var vz)
--     conS k (vs x) = var (vs x)            -- `Spec/Typing:107`
--
-- ★ THE CHEAPEST of the ledger's 20 recursive entries, and the reason is
--   the SORT: `conSSK` eliminates at `Var`, which has two constructors,
--   so the meta side is two clauses rather than thirty.  `conSTail` is
--   `pair conSVz (pair conSVs unit)`; the other 51 methods are junk and
--   are never entered.
--
-- ★★ THE CASCADE this is the base of:
--       conSSK  → conSK  → atConK
--       iconSSK → icSK   → iconSK → iatConK
--   `iconSSK` is a clone of `conSSK` with `icon` for `con`, so six
--   ledger entries hang off this shape.
--
-- ★★★ WHAT UNSTUCK IT, after four attempts in `OCC-ATTEMPTS.md` §B that
--   read the residue as *"`subTm` cannot compute through a hand-written
--   method body"* and concluded a naturality lemma was owed:
--
--     THE SUBSTITUTIONS DO COMPUTE.  `subTm`/`renTm` distribute over
--     `pair` DEFINITIONALLY, so the β-substituted payload IS a literal
--     pair and `sel-here`/`sel-there` apply to it unchanged.  What does
--     not compute is the object-level `fst`/`snd` REDEX sitting on top
--     of it — and a redex wants a REDUCTION STEP, not a lemma.
--
-- ⚠⚠ SO THE 2026-09-08 DIAGNOSIS WAS RIGHT IN ITS EVIDENCE AND WRONG IN
--   ITS CONCLUSION.  The printed residue really did read
--   `fst (subTm … (subTm … (var (vs (vs vz)))))`.  What did not follow
--   is that a naturality lemma was therefore needed: `⟶*` and `≡` were
--   being asked to do each other's jobs.  The projections are
--   REDUCTIONS (`sel-here`), the leftover weakenings are EQUALITIES
--   (`sub-w²-single`), and each needs its own tool.  ⇒ before writing a
--   new lemma for a stuck residue, split it into the part that reduces
--   and the part that is merely equal.
--
-- ★ THE THREE REAL DIFFERENCES FROM THE `singleK` TEMPLATE, all of which
--   cost an attempt each:
--     1. the target REBUILDS the variable — `Tm-varK (Var-vsK m x)`, not
--        `Tm-varK x`.  Copying `singleK-vs`'s statement gives a lemma
--        that TYPE-CHECKS AND IS FALSE, because `single` lowers where
--        `conS` neither lowers nor raises (`Knot/ConS`'s header).
--     2. jsub nesting is TWO, not three: `symN a p = jsub … p (reflN a)`
--        is one jsub, and `conSVs` has no `predN` inside it.
--     3. the LEVEL is reduced TWICE — `Var-vzK a` / `Var-vsK a b`
--        mention `a` in the field AND in the ford's `nsuc a`, where
--        `Tm-varK x` mentions its argument once.
--
-- ⚠ COST: two chains and four congruences.  No new library lemma, no
--   redesign, and `Knot/ConS` is untouched.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.ConSAgree where

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
open import DirectedHoTT.Examples.Knot.ConS using ( conSMeths; conSVz; conSVs; conSK; conSSK )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-varK; Tm-conK )
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
conSS-vz : {Γ : Cx} (i m : RTm Γ) →
           ielim KnotD i conSMeths (Var-vzK m) ⟶*
             app (app (app conSVz i)
                      (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                    (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
                 (iihs KnotD conSMeths (isingle i) cVar-vz
                       (pair m (pair (idrefl ⌜Nat⌝ sVar)
                                     (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))
conSS-vz i m =
  ihead-red KnotD conSMeths tagVar-vz i _
    (methsFrom-past (cdTake 51 KnotD) zero » step (βfst _ _) done)
    done

------------------------------------------------------------------------
-- STEP 2 — the head reduction at the `vs` row.
--
-- ⚠ The SELECTION differs, not the shape: `vz` is the tail's first
--   element (one `βfst`), `vs` its second (`sel-there` then `sel-here`).
------------------------------------------------------------------------
conSS-vs : {Γ : Cx} (i m x : RTm Γ) →
           ielim KnotD i conSMeths (Var-vsK m x) ⟶*
             app (app (app conSVs i)
                      (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                            (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
                 (iihs KnotD conSMeths (isingle i) cVar-vs
                       (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                             (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
conSS-vs i m x =
  ihead-red KnotD conSMeths tagVar-vs i _
    (methsFrom-past (cdTake 51 KnotD) (suc zero) »
     sel-there 0 _ _ (sel-here _ _))
    done

------------------------------------------------------------------------
-- ★ BOTH HEAD REDUCTIONS GO THROUGH `Lib/IHeadRed.ihead-red`, of which
--   `conSSK` is the fourth client.  Only the SELECTION differs between
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

inCon : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Tm-conK a b ⟶* Tm-conK a b'
inCon r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

------------------------------------------------------------------------
-- ★★★ STEP 3 — `conSSK`, AT THE LEDGER'S OWN NAME.
--
--     conS k vz     = con k (var vz)
--     conS k (vs x) = var (vs x)
--
-- ★ See the module header for why the four earlier attempts stuck, and
--   for the three differences from the `singleK` template.
------------------------------------------------------------------------

conSSK-vz : {Γ : Cx} (i m k : RTm Γ) →
            conSSK i (Var-vzK m) k ⟶* Tm-conK k (Tm-varK (Var-vzK m))
conSSK-vz i m k =
  -- ⚠ THE FORD IS ONE FIELD SHALLOWER THAN THE `vs` ROW's: `Var-vzK`'s
  --   payload has three fields to `Var-vsK`'s four (no `x`), so the
  --   depth ford is `sel 2`, not `sel 3`.
  ⟶*-castᵣ (cong (λ z → Tm-conK k (Tm-varK (Var-vzK z))) (sub-w²-single m))
  (⟶*-appˡ (conSS-vz _ _) »
   ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
   ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
   ⟶*-appˡ (step (β _ _) done) »
   step (β _ _) done »
   inCon (inVar (⟶*-jsubᵖ (⟶*-jsubᵖ
     (sel-there 1 _ _ (sel-there 0 _ _ (sel-here _ _)))))) »
   inCon (inVar (⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done))) »
   inCon (inVar (step (jsub-refl _ _ _ _) done)) »
   inCon (inVar (vzLvl (sel-here _ _))))

conSSK-vs : {Γ : Cx} (i m x k : RTm Γ) →
            conSSK i (Var-vsK m x) k ⟶* Tm-varK (Var-vsK m x)
conSSK-vs i m x k =
  ⟶*-castᵣ (cong₂ (λ p q → Tm-varK (Var-vsK p q))
                  (sub-w²-single m) (sub-w²-single x))
  (⟶*-appˡ (conSS-vs _ _ _) »
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
-- ★★ STEP 4 — `conSK`, THE SUBSTITUTION.  Both rows are ONE β on top of
--   step 3, which is what stating the theorem at `conSSK` bought.
--
-- ★ THE `vs` ROW NEEDS NO CAST AT ALL: its target mentions neither `n`
--   nor `k`, so `conSK`'s two weakenings never have to be undone.  The
--   `vz` row DOES carry the tag, and that is the one `wk-single`.
------------------------------------------------------------------------

conSK-vz : {Γ : Cx} (n k m : RTm Γ) →
           app (conSK n k) (Var-vzK m) ⟶* Tm-conK k (Tm-varK (Var-vzK m))
conSK-vz n k m =
  ⟶*-castᵣ (cong (λ z → Tm-conK z (Tm-varK (Var-vzK m)))
                 (wk-single {v = Var-vzK m} k))
           (step (β _ _) (conSSK-vz _ _ _))

conSK-vs : {Γ : Cx} (n k m x : RTm Γ) →
           app (conSK n k) (Var-vsK m x) ⟶* Tm-varK (Var-vsK m x)
conSK-vs n k m x = step (β _ _) (conSSK-vs _ _ _ _)

------------------------------------------------------------------------
-- ★★★ STEP 5 — PACKAGED AS `Represents`, which is what the substitution
--   layer (and `atConK` through it) consumes.
--
-- ★ `single-Represents`'s three lines exactly.  `conS`'s two clauses ARE
--   step 4's two lemmas, read back — `Spec/Typing:107`.
------------------------------------------------------------------------


conS-Represents : {Γ Θ : Cx} (n : RTm Θ) (k : ℕ) →
                  Represents {Γ = Γ ∙} {Θ = Θ} (conS k) (conSK n (num k))
conS-Represents {Γ = Γ} n k vz     = conSK-vz n (num k) (num (len Γ))
conS-Represents {Γ = Γ} n k (vs x) = conSK-vs n (num k) (num (len Γ)) (enVar x)

------------------------------------------------------------------------
-- ★★★ STEP 6 — `atConK`, THE NEXT LEDGER ENTRY, AND IT IS A COROLLARY.
--
--     atCon k M  = subTy (conS k) M            -- `Spec/Typing:111`
--     atConK n k = subTyAtK (nsuc n) (nsuc n) (conSK n k)
--
-- ★ `subTyAtK`'s adequacy is `Knot/SubAgreeTyTie.sub-agree-ty`, all 11
--   `RTy` rows, and it consumes exactly a `Represents`.  Step 5 supplies
--   one.  ⇒ the entry costs a line, which is what the cascade in
--   `conSSK`'s ledger entry predicted.
--
-- ⚠ THE DEPTH IS FORCED, and that is why `n` is not free here as it is
--   in step 5: `sub-agree-ty` reads `num (len Γ)` off the ENCODING, and
--   `atConK`'s two depths are both `nsuc n`.  `num (suc m) = nsuc (num m)`
--   holds definitionally, so `n := num (len Γ)` is the only choice that
--   types — the same "the depth may only be stated where the encoding
--   uses it" as `extR-Represents`.
------------------------------------------------------------------------

open import DirectedHoTT.Spec.Syntax using ( RTy )
open import DirectedHoTT.Spec.Typing using ( atCon )
open import DirectedHoTT.Examples.Knot.Map using ( enTy )
open import DirectedHoTT.Examples.Knot.ConS using ( atConK )
open import DirectedHoTT.Examples.Knot.SubAgreeTyTie using ( sub-agree-ty )

atCon-agree : {Γ Θ : Cx} (k : ℕ) (M : RTy (Γ ∙)) →
              atConK (num (len Γ)) (num k) (enTy {Γ ∙} {Θ} M)
              ⟶* enTy {Γ ∙} {Θ} (atCon k M)
atCon-agree {Γ} k M = sub-agree-ty (conS-Represents (num (len Γ)) k) M
