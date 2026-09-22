------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `methsTyFromK`'s ADEQUACY, AND `methsTyK`.
--
--     methsTyFrom D M j dnil    = Unit
--     methsTyFrom D M j (C ◃ E) = Σ' (methTy D j C M)
--                                    (renTy vs (methsTyFrom D M (suc j) E))
--
-- ★ TWO ROWS OF 53, and `Knot/MethsTy`'s header said so: this eliminates
--   an encoded `Desc`, which has two constructors.
--
-- ★★ AND ROW 41 IS FREE, for `lookupDK`'s reason — the JUNK method
--   answers it and the junk IS the answer (`methsTyJunk = lam⁶ Ty-UnitK`,
--   `methsTyFrom D M j dnil = Unit`).  Its body is CLOSED, so zero rungs.
--
-- ⚠ SIX BINDERS, NOT THREE.  `methsTyMotK` is a Π-telescope over D, M
--   and j, so each method is `lam⁶` and the wrapper applies three more
--   arguments after the eliminator.  ⇒ the row's β-law is stated ONCE,
--   GENERIC in all six (`consK-app`) — `Knot/IExtRep`'s move, and what
--   `abstract-the-substituted-terms` measured at 87×.
--
-- ⚠⚠ AND THE STACK DOES NOT REACH `methTyK`'s ARGUMENTS ON ITS OWN.
--   Both `methTyK` and `wkTyK` bottom out in
--   `vsRenK n = lam (Var-vsK (w n) (var vz))`, which puts `n` UNDER A
--   BINDER, so a substitution crossing it is `extS`-lifted and the `w`
--   lands inside.  ⇒ push the six substitutions through FIRST (`nat6₅`,
--   `nat6₂` over `methTyK-sub`/`wkTyK-sub`), and only then collapse each
--   slot by its own rung — the rung being its BINDER POSITION: the index
--   owes six, the payload five, the IH tuple four, `D` three, `M` two,
--   and `j` — the innermost binder — owes nothing.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.MethsTyAgree where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; Desc; dnil; _◃_; DCon; var; vz; vs; lam; app
        ; pair; unit; fst; snd; nsuc; icon; ielim; iihs; isingle; sel; ilookupD )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; step; done; β; βfst; βsnd; methsTyFrom; methsTy )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Spec.Syntax using ( Sub; extS; subTm; renTm )
open import DirectedHoTT.Spec.Typing using ( single; wk-single )
open import DirectedHoTT.Lib.Wk
  using ( w; cong₅; towerJ; towerJ⁵; towerA; towerP )
-- ★★ `tower⁶` ALREADY EXISTED.  Found by a same-type-modulo-holes query,
--   AFTER a duplicate had been written: `Lib/Wk`'s family stops at
--   `towerJ⁵` and says "at a fourth, stop and write `tower^`", but the
--   sixth and seventh rungs were already sitting in `Knot/IihsAgree`.
open import DirectedHoTT.Examples.Knot.IihsAgree using ( tower⁶ )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ )
open import DirectedHoTT.Lib.IMeths
  using ( cdTake; methsFrom-sel; methsFrom-past; inCD; tt; sel-here; sel-there
        ; methsFrom-sub )
open import DirectedHoTT.Examples.Knot.Sorts using ( sDCon )
open import DirectedHoTT.Examples.Knot.PayTy
  using ( payTyK; payTyMethsK; payTyMid44; payTyJunk )
open import DirectedHoTT.Examples.Knot.IhTy
  using ( ihTyK; ihTyMethsK; ihTyMid44 )
open import DirectedHoTT.Examples.Knot.IhTyMot using ( ihTyJunk )
open import DirectedHoTT.Examples.Knot.ConS
  using ( conSMeths; conSJunk; conSTail; conSSK; conSK; atConK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyUnderK )
open import DirectedHoTT.Examples.Knot.IhTyAgree using ( subTyAtK-sub )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTyAtK )
open import DirectedHoTT.Examples.Knot.SubSpec
  using ( renMethsK-sub; vsRenK-sub )
open import DirectedHoTT.Examples.Knot.RenNat using ( extRNK-sub )
open import DirectedHoTT.Examples.Knot.RenMot using ( extRNK )
open import DirectedHoTT.Examples.Knot.RenTm using ( vsRenK; renTmAtK )
open import DirectedHoTT.Examples.Knot.Sorts using ( sVar; sTy )
open import DirectedHoTT.Lib.Wk using ( sub-w; cong₃ )
open import DirectedHoTT.Examples.Knot.IhTyAgree using ( nat5₂' )
open import DirectedHoTT.Examples.Knot.PayTyAgree using ( wkTyK-sub )
open import DirectedHoTT.Examples.Knot.IPayTyAgree using ( wkAtK-sub )
open import DirectedHoTT.Examples.Knot.PayTyAgree using ( inSgL; inSgR; ⟶*-wkTyKᵈ; ⟶*-wkTyKᵃ )
open import DirectedHoTT.Examples.Knot.DepthCong using ( ⟶*-methTyKᵈ; ⟶*-ihTyKᶜ' )
open import DirectedHoTT.Examples.Knot.MethTyAgree using ( methTyK-agree; inPiL; inPiR )
open import DirectedHoTT.Examples.Knot.TyAgree using ( wkTyK-agree )
open import DirectedHoTT.Examples.Knot.Map using ( enDCon )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-snd; ⟶*-fst; ⟶*-pairʳ; ⟶*-ielimᵗ )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkAtK )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-PiK; Tm-varK )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK )
open import DirectedHoTT.Examples.Knot.Sorts using ( sDCon )
open import DirectedHoTT.Spec.Syntax using ( Sub; extS; subTm; idrefl; ⌜Nat⌝ )
open import DirectedHoTT.Lib.IHeadRed using ( ihead-red )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDesc-nil; tagDesc-cons )
open import DirectedHoTT.Examples.Knot.Sorts using ( sDesc; len )
open import DirectedHoTT.Examples.Knot.Map using ( enTy; enDesc; enDCon )
open import DirectedHoTT.Examples.Knot.MethsTyMot using ( methsTyJunk )
open import DirectedHoTT.Examples.Knot.MethsTyCons using ( methsTyCons )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-SgK )
open import DirectedHoTT.Examples.Knot.MethTy using ( methTyK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK )
open import DirectedHoTT.Examples.Knot.MethsTy
  using ( methsTyMethsK; methsTyTail; methsTyMid42; MD43; methsTyFromK; methsTyK )

head-red : {Γ : Cx} (k : ℕ) {mth : RTm Γ} → sel k (methsTyMethsK {Γ}) ⟶* mth →
           (i p : RTm Γ) {u : RTm Γ} →
           app (app (app mth i) p)
               (iihs KnotD methsTyMethsK (isingle i) (ilookupD KnotD k) p) ⟶* u →
           ielim KnotD i methsTyMethsK (icon k p) ⟶* u
head-red k sp i p h = ihead-red KnotD methsTyMethsK k i p sp h

------------------------------------------------------------------------
-- ★ THE SELECTION — a three-segment map: 42 junk, `methsTyCons`, 10 junk.
------------------------------------------------------------------------
sel41 : {Γ : Cx} → sel tagDesc-nil (methsTyMethsK {Γ}) ⟶* methsTyJunk
sel41 = methsFrom-sel (cdTake 42 KnotD) {m = methsTyJunk} tagDesc-nil
                      (inCD (cdTake 42 KnotD) tagDesc-nil tt)

sel42 : {Γ : Cx} → sel tagDesc-cons (methsTyMethsK {Γ}) ⟶* methsTyCons
sel42 = methsFrom-past (cdTake 42 KnotD) {m = methsTyJunk} {tl = methsTyMid42} 0
      » sel-here _ _

------------------------------------------------------------------------
-- ★★★ ROW 41 — `dnil`, and it is FREE.  Six βs onto a CLOSED body.
------------------------------------------------------------------------
row-nil : {Γ Θ : Cx} (i D M j : RTm Θ) (Mm : RTy (Γ ∙)) (jj : ℕ) (DD : Desc) →
          app (app (app (ielim KnotD i methsTyMethsK (enDesc {Θ} dnil)) D) M) j
          ⟶* enTy {Γ} {Θ} (methsTyFrom {Γ} DD Mm jj dnil)
row-nil i D M j Mm jj DD =
     ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (head-red tagDesc-nil sel41 i _
         (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
          ⟶*-appˡ (step (β _ _) done) »
          step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done

------------------------------------------------------------------------
-- ★★★ THE NATURALITY BLOCK — pushing a substitution through `methTyK`.
--
-- ⚠⚠ EVERY ONE OF THESE IS THE SAME LEMMA: a `…K` program is an `ielim`
--   over a CLOSED method tuple, and `subTm τ tuple ≡ tuple` is the only
--   thing that does not compute.  `Lib/IMeths.methsFrom-sub` does the
--   walk; the leaves are closed `lam` bodies and so are `refl`.
--
-- ★ `wkTyK-sub` (Knot/PayTyAgree) and `wkAtK-sub` (Knot/IPayTyAgree)
--   and `subTyAtK-sub` (Knot/IhTyAgree) already existed — scattered one
--   per adequacy module, which is what `tools/find-dup-lemmas.py` flags
--   as a family with no home.
------------------------------------------------------------------------

payTyMethsK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) →
                  subTm τ (payTyMethsK {Γ}) ≡ payTyMethsK {Δ}
payTyMethsK-sub τ = methsFrom-sub (cdTake 44 KnotD) τ payTyJunk payTyMid44

ihTyMethsK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) →
                 subTm τ (ihTyMethsK {Γ}) ≡ ihTyMethsK {Δ}
ihTyMethsK-sub τ = methsFrom-sub (cdTake 44 KnotD) τ ihTyJunk ihTyMid44

payTyK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n c d : RTm Γ) →
             subTm τ (payTyK n c d)
             ≡ payTyK (subTm τ n) (subTm τ c) (subTm τ d)
payTyK-sub τ n c d =
  cong (λ ms → app (ielim KnotD (pair sDCon (subTm τ n)) ms (subTm τ c))
                   (subTm τ d))
       (payTyMethsK-sub τ)

ihTyK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n c q M : RTm Γ) →
            subTm τ (ihTyK n c q M)
            ≡ ihTyK (subTm τ n) (subTm τ c) (subTm τ q) (subTm τ M)
ihTyK-sub τ n c q M =
  cong (λ ms → app (app (ielim KnotD (pair sDCon (subTm τ n)) ms (subTm τ c))
                        (subTm τ q)) (subTm τ M))
       (ihTyMethsK-sub τ)

------------------------------------------------------------------------
-- ★★★ THE CASCADE — four lemmas, none of them an induction.
--
-- ⚠ AND THE BOTTOM TWO ARE A PORT.  `Knot/IConSRep` already has
--   `iconSSK-sub` and `icSK-sub`, the INDEXED twins, and `conSSK`/
--   `conSK` have identical shape one sort down.  The `ilookupDK` ledger
--   entry called this exactly: *do the non-indexed twin first and port;
--   the two are one proof.*  Here it runs the other way — up-sort first,
--   port down — because the indexed one happened to be needed first.
------------------------------------------------------------------------

conSMeths-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) →
                subTm τ (conSMeths {Γ}) ≡ conSMeths {Δ}
conSMeths-sub τ = methsFrom-sub (cdTake 51 KnotD) τ conSJunk conSTail

conSSK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (i x k : RTm Γ) →
             subTm τ (conSSK i x k)
             ≡ conSSK (subTm τ i) (subTm τ x) (subTm τ k)
conSSK-sub τ i x k =
  cong (λ z → app (ielim KnotD (subTm τ i) z (subTm τ x)) (subTm τ k))
       (conSMeths-sub τ)

-- ★ `Knot/IConSRep.icSK-sub` verbatim, one sort down.
conSK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n k : RTm Γ) →
            subTm τ (conSK n k) ≡ conSK (subTm τ n) (subTm τ k)
conSK-sub τ n k =
  cong lam (trans (conSSK-sub (extS τ) (pair sVar (nsuc (w n))) (var vz) (w k))
                  (cong₂ (λ a b → conSSK (pair sVar (nsuc a)) (var vz) b)
                         (sub-w {σ = τ} n) (sub-w {σ = τ} k)))

atConK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n k M : RTm Γ) →
             subTm τ (atConK n k M)
             ≡ atConK (subTm τ n) (subTm τ k) (subTm τ M)
atConK-sub τ n k M =
  trans (subTyAtK-sub τ (nsuc n) (nsuc n) (conSK n k) M)
        (cong (λ z → subTyAtK (nsuc (subTm τ n)) (nsuc (subTm τ n)) z (subTm τ M))
              (conSK-sub τ n k))

wkTyUnderK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n A : RTm Γ) →
                 subTm τ (wkTyUnderK n A)
                 ≡ wkTyUnderK (subTm τ n) (subTm τ A)
wkTyUnderK-sub τ n A =
  cong₂ (λ ms rn →
           app (app (ielim KnotD (pair sTy (nsuc (subTm τ n))) ms (subTm τ A))
                    (nsuc (nsuc (subTm τ n)))) rn)
        (renMethsK-sub τ)
        (trans (extRNK-sub τ n (nsuc n) (vsRenK n))
               (cong (extRNK (subTm τ n) (nsuc (subTm τ n))) (vsRenK-sub τ n)))

------------------------------------------------------------------------
-- ★ THE SIX-FOLD LIFTS.  `Knot/IhTyAgree`'s `nat5₂'`/`nat5₄` family at
--   one more substitution, because `methsTyCons` is `lam⁶`.
--
-- ⚠ Queried first (`find-dup-lemmas.py "nat5₂'" 4` → 0 hits): there is
--   no 6-fold member of this family and no `methTyK-sub`.  Both are
--   genuinely new.
------------------------------------------------------------------------

nat6₅ : (F : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ) →
        ({Γ Δ : Cx} (τ : Sub Γ Δ) (a b c d e : RTm Γ) →
           subTm τ (F a b c d e)
           ≡ F (subTm τ a) (subTm τ b) (subTm τ c) (subTm τ d) (subTm τ e)) →
        {Γ0 Γ1 Γ2 Γ3 Γ4 Γ5 Γ6 : Cx}
        (τ0 : Sub Γ1 Γ0) (τ1 : Sub Γ2 Γ1) (τ2 : Sub Γ3 Γ2) (τ3 : Sub Γ4 Γ3)
        (τ4 : Sub Γ5 Γ4) (τ5 : Sub Γ6 Γ5) (a b c d e : RTm Γ6) →
        subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (F a b c d e))))))
        ≡ F (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 a))))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 b))))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 c))))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 d))))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 e))))))
nat6₅ F hF τ0 τ1 τ2 τ3 τ4 τ5 a b c d e =
  trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 z)))))
              (hF τ5 a b c d e))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 z)))) (hF τ4 _ _ _ _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 z))) (hF τ3 _ _ _ _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 z)) (hF τ2 _ _ _ _ _))
  (trans (cong (subTm τ0) (hF τ1 _ _ _ _ _)) (hF τ0 _ _ _ _ _)))))

nat6₂ : (F : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ) →
        ({Γ Δ : Cx} (τ : Sub Γ Δ) (a b : RTm Γ) →
           subTm τ (F a b) ≡ F (subTm τ a) (subTm τ b)) →
        {Γ0 Γ1 Γ2 Γ3 Γ4 Γ5 Γ6 : Cx}
        (τ0 : Sub Γ1 Γ0) (τ1 : Sub Γ2 Γ1) (τ2 : Sub Γ3 Γ2) (τ3 : Sub Γ4 Γ3)
        (τ4 : Sub Γ5 Γ4) (τ5 : Sub Γ6 Γ5) (a b : RTm Γ6) →
        subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 (F a b))))))
        ≡ F (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 a))))))
            (subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 (subTm τ5 b))))))
nat6₂ F hF τ0 τ1 τ2 τ3 τ4 τ5 a b =
  trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 (subTm τ4 z)))))
              (hF τ5 a b))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 (subTm τ3 z)))) (hF τ4 _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 (subTm τ2 z))) (hF τ3 _ _))
  (trans (cong (λ z → subTm τ0 (subTm τ1 z)) (hF τ2 _ _))
  (trans (cong (subTm τ0) (hF τ1 _ _)) (hF τ0 _ _)))))

-- ★★ `methTyK`'s NATURALITY — the cascade assembled.  `Ty-PiK` is an
--   `icon`/`pair`, so it distributes definitionally; only the three
--   `…K` programs inside it are stuck, and each now has its `-sub`.
methTyK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n k D C M : RTm Γ) →
              subTm τ (methTyK n k D C M)
              ≡ methTyK (subTm τ n) (subTm τ k) (subTm τ D) (subTm τ C) (subTm τ M)
methTyK-sub τ n k D C M =
  cong₃ (λ a b c → Ty-PiK a (Ty-PiK b c))
        (payTyK-sub τ n C D)
        (trans (ihTyK-sub τ (nsuc n) (wkAtK sDCon n C)
                           (Tm-varK (Var-vzK n)) (wkTyUnderK n M))
               (cong₂ (λ x y → ihTyK (nsuc (subTm τ n)) x
                                 (Tm-varK (Var-vzK (subTm τ n))) y)
                      (wkAtK-sub τ sDCon n C) (wkTyUnderK-sub τ n M)))
        (trans (wkTyK-sub τ (nsuc n) (atConK n k M))
               (cong (wkTyK (nsuc (subTm τ n))) (atConK-sub τ n k M)))

------------------------------------------------------------------------
-- ★★★ THE ROW'S β-LAW, STATED ONCE AND GENERIC IN ALL SIX ARGUMENTS.
--
-- ⚠⚠ DO NOT COLLAPSE THE TOWER AT THE USE SITE.  `methsTyCons` is
--   `lam⁶`, so a use site reduces six βs and is then left with six
--   stacked substitutions on FIVE different slots, each at its own
--   depth.  Proving that once HERE, with the arguments ABSTRACT, is
--   `Knot/IExtRep`'s move — the one the ledger credits for `iextK` and
--   `iconSK` — and `abstract-the-substituted-terms` measured it at 87×:
--   a substitution lemma cares about DEPTH, not content.
------------------------------------------------------------------------
consK-app : {Γ : Cx} (i p ihs D M j : RTm Γ) →
  app (app (app (app (app (app methsTyCons i) p) ihs) D) M) j
  ⟶* Ty-SgK (methTyK (snd i) j D (fst p) M)
             (wkTyK (snd i)
                (app (app (app (fst (snd ihs)) D) M) (nsuc j)))
consK-app i p ihs D M j =
     ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))))
  » ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))
  » ⟶*-appˡ (⟶*-appˡ (step (β _ _) done))
  » ⟶*-appˡ (step (β _ _) done)
  » step (β _ _) done
  -- ★★★ THE CAST, IN TWO HALVES — `Ty-SgK` distributes definitionally.
  --
  -- ⚠⚠ EACH HALF IS A NATURALITY LIFT **THEN** A TOWER COLLAPSE, and the
  --   order is forced.  The six substitutions do NOT reach `methTyK`'s
  --   or `wkTyK`'s arguments on their own: both bottom out in
  --   `vsRenK n = lam (Var-vsK (w n) (var vz))`, which puts `n` UNDER A
  --   BINDER, so a substitution crossing it is `extS`-lifted and the
  --   `w` lands inside.  ⇒ push the stack through FIRST (`nat6₅`,
  --   `nat6₂`), and only then collapse each slot by its own rung.
  --
  -- ★ AND THE RUNG IS THE BINDER POSITION: the index sits at
  --   `var (vs⁵ vz)` and owes six, the payload five, the IH tuple four,
  --   `D` three, `M` two, and `j` — innermost — owes nothing.
  » ⟶*-castₗ (cong₂ Ty-SgK eMeth eWk) done
  where
    eMeth : _ ≡ methTyK (snd i) j D (fst p) M
    eMeth =
      trans (nat6₅ methTyK methTyK-sub
               (single j) (extS (single M)) (extS (extS (single D)))
               (extS (extS (extS (single ihs))))
               (extS (extS (extS (extS (single p)))))
               (extS (extS (extS (extS (extS (single i))))))
               (snd (var (vs (vs (vs (vs (vs vz)))))))
               (var vz)
               (var (vs (vs vz)))
               (fst (var (vs (vs (vs (vs vz))))))
               (var (vs vz)))
            (cong₅ methTyK
               (cong snd (tower⁶ j M D ihs p i))
               refl
               (towerA j M D)
               (cong fst (towerJ⁵ j M D ihs p))
               (towerP j M))
    eWk : _ ≡ wkTyK (snd i) (app (app (app (fst (snd ihs)) D) M) (nsuc j))
    eWk =
      trans (nat6₂ wkTyK wkTyK-sub
               (single j) (extS (single M)) (extS (extS (single D)))
               (extS (extS (extS (single ihs))))
               (extS (extS (extS (extS (single p)))))
               (extS (extS (extS (extS (extS (single i))))))
               (snd (var (vs (vs (vs (vs (vs vz)))))))
               (app (app (app (fst (snd (var (vs (vs (vs vz))))))
                              (var (vs (vs vz)))) (var (vs vz)))
                    (nsuc (var vz))))
            (cong₂ (λ z w → wkTyK (snd z) w)
               (tower⁶ j M D ihs p i)
               (cong₃ (λ a b c → app (app (app (fst (snd a)) b) c) (nsuc j))
                      (towerJ j M D ihs) (towerA j M D) (towerP j M)))



------------------------------------------------------------------------
-- ★ THE `C` SLOT.  `Knot/DepthCong` has `⟶*-methTyKᵈ` (the depth) but
--   not this one; `C` occurs TWICE in `methTyK` — as `payTyK`'s
--   scrutinee and inside `wkAtK` — so it is two descents.
------------------------------------------------------------------------
⟶*-payTyKᶜ : {Γ : Cx} {n c c' d : RTm Γ} →
             c ⟶* c' → payTyK n c d ⟶* payTyK n c' d
⟶*-payTyKᶜ h = ⟶*-appˡ (⟶*-ielimᵗ h)

⟶*-wkAtKᵃ : {Γ : Cx} {so n t t' : RTm Γ} →
            t ⟶* t' → wkAtK so n t ⟶* wkAtK so n t'
⟶*-wkAtKᵃ h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ h))

⟶*-methTyKᶜ : {Γ : Cx} {n k D C C' M : RTm Γ} →
              C ⟶* C' → methTyK n k D C M ⟶* methTyK n k D C' M
⟶*-methTyKᶜ h =
    inPiL (⟶*-payTyKᶜ h)
  » inPiR (inPiL (⟶*-ihTyKᶜ' (⟶*-wkAtKᵃ h)))

------------------------------------------------------------------------
-- ★★★ THE INDUCTION — two rows, and the `dnil` one is free.
--
--     methsTyFrom D M j dnil    = Unit
--     methsTyFrom D M j (C ◃ E) = Σ' (methTy D j C M)
--                                    (renTy vs (methsTyFrom D M (suc j) E))
--
-- ⚠ THE INDEX IS QUANTIFIED WITH A REDUCTION, as in `Knot/PwBodyAgree`:
--   the method READS `snd ⟨i⟩`, and the child's index only REDUCES to
--   the same pair, so a pinned index could never match the recursion.
------------------------------------------------------------------------
agree : {Γ Θ : Cx} (i : RTm Θ) → i ⟶* pair sDesc (num (len Γ)) →
        (DD : Desc) (Mm : RTy (Γ ∙)) (jj : ℕ) (E : Desc) →
        app (app (app (ielim KnotD i methsTyMethsK (enDesc {Θ} E))
                      (enDesc {Θ} DD)) (enTy {Γ ∙} {Θ} Mm)) (num jj)
        ⟶* enTy {Γ} {Θ} (methsTyFrom {Γ} DD Mm jj E)
agree i hi DD Mm jj dnil      = row-nil i _ _ _ Mm jj DD
agree {Γ} {Θ} i hi DD Mm jj (C ◃ E) =
     ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
        (head-red tagDesc-cons sel42 i PAY done)))
  » consK-app i PAY IHS (enDesc DD) (enTy Mm) (num jj)
  -- the LEFT component — `methTy D j C M`
  » inSgL (⟶*-methTyKᵈ hd)
  » inSgL (⟶*-methTyKᶜ (step (βfst _ _) done))
  » inSgL (methTyK-agree DD jj C Mm)
  -- the RIGHT — the IH, then `wkTyK`'s own agreement
  » inSgR (⟶*-wkTyKᵈ hd)
  » inSgR (⟶*-wkTyKᵃ
       (   ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-fst (step (βsnd _ _) done))))
       »  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)))
       -- ★ the recursive eliminator's SCRUTINEE is `fst (snd p)` — the
       --   tail `Desc` — so two more projections before the IH applies.
       --   `Knot/LookupD`'s `lookupD-agree` does exactly this.
       »  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (step (βsnd _ _) done)))))
       »  ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))))
       »  agree _ (⟶*-pairʳ hd) DD Mm (suc jj) E))
  » inSgR (wkTyK-agree {Γ} (methsTyFrom DD Mm (suc jj) E))
  where
    PAY : RTm Θ
    PAY = pair (enDCon C) (pair (enDesc E) (pair (idrefl ⌜Nat⌝ sDesc) unit))
    IHS : RTm Θ
    IHS = iihs KnotD methsTyMethsK (isingle i) (ilookupD KnotD tagDesc-cons) PAY
    hd : snd i ⟶* num (len Γ)
    hd = ⟶*-snd hi » step (βsnd _ _) done

------------------------------------------------------------------------
-- ★★★ AT THE LEDGER'S NAMES.
--
--     methsTyFromK n D M j E = app³ (ielim KnotD (sDesc , n) msK E) D M j
--     methsTyK     n D M   E = methsTyFromK n D M nzero E
------------------------------------------------------------------------
methsTyFromK-agree : {Γ Θ : Cx} (n : RTm Θ) → n ⟶* num (len Γ) →
                     (DD : Desc) (Mm : RTy (Γ ∙)) (jj : ℕ) (E : Desc) →
                     methsTyFromK n (enDesc {Θ} DD) (enTy {Γ ∙} {Θ} Mm)
                                  (num jj) (enDesc {Θ} E)
                     ⟶* enTy {Γ} {Θ} (methsTyFrom {Γ} DD Mm jj E)
methsTyFromK-agree n hn DD Mm jj E = agree (pair sDesc n) (⟶*-pairʳ hn) DD Mm jj E

-- ★ `methsTy D M E = methsTyFrom D M zero E`, and `num 0` IS `nzero`.
methsTyK-agree : {Γ Θ : Cx} (DD : Desc) (Mm : RTy (Γ ∙)) (E : Desc) →
                 methsTyK (num (len Γ)) (enDesc {Θ} DD) (enTy {Γ ∙} {Θ} Mm)
                          (enDesc {Θ} E)
                 ⟶* enTy {Γ} {Θ} (methsTy {Γ} DD Mm E)
methsTyK-agree {Γ} DD Mm E = methsTyFromK-agree (num (len Γ)) done DD Mm 0 E
