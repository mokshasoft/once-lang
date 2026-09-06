------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `iihTy`'s MOTIVE, JUNK ROW AND DESCENT.
--
--     iihTy D I σ iι       q M = Unit
--     iihTy D I σ (iρ j C) q M =
--       Σ' (iinst (subTm σ j) (fst q) M)
--          (renTy vs (iihTy D I (iext σ (fst q)) C (snd q) M))
--     iihTy D I σ (iκ κ C) q M = iihTy D I (iext σ (fst q)) C (snd q) M
--
-- ★ `D` AND `I` ARE PHANTOMS — neither is ever matched on, both are only
--   passed along — so they are NOT passengers.  Four are: `n`, `σ`, `q`,
--   `M`.  ⚠ `Knot/IPayTyMot` carries four as well, so `towerA`/`towerJ`
--   suffice and no new rung is needed (unlike `Knot/MethsTyMot`).
--
-- ⚠⚠ AND THE RECURSION DOES **NOT** RAISE THE TARGET, WHICH IS WHERE
--   THIS DIFFERS FROM `ipayTy`.  `ipayTy`'s step is `extS σ`, which
--   raises, so its IH is taken at `nsuc n`.  `iihTy`'s step is
--   `iext σ (fst q)` — a CONS — so the target is unchanged and the IH is
--   taken at the SAME `n`.  Reading that off `⊢ipayAppK`'s call and not
--   the spec would put every row one binder too deep.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhITyMot where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IMu; εwkTy; app; fst; iρ; iκ; iι
        ; ⌜Id⌝; ⌜Nat⌝; isingle; iext; unit; nzero; nsuc; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢fst; ⊢lam; ⊢app; ⊢nzero; ⊢nsuc
        ; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; ξ-pairʳ; βsnd; done; step; single; wk-single; iinst )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import normalizer.Syntax.Types using ( cong; sym )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Lib.ICast using ( muFwd; muBwd* )
open import DirectedHoTT.Lib.Wk using ( towerA; towerJ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sTm; ⊢sTm; sICon; ⊢sICon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy; ty-SubTy; subBwd )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-UnitK; Ty-SgK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Ty-UnitKv; ⊢Ty-SgKv )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK; ⊢wkTyK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK; ⊢subTmAtK )
open import DirectedHoTT.Examples.Knot.IExt using ( iinstK; ⊢iinstK )

------------------------------------------------------------------------
-- ★ THE MOTIVE — four passengers, result reads the FIRST.
------------------------------------------------------------------------

iihTyMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
iihTyMotK =
  Π Nat                                                          -- n
   (Π (SubTy (snd (var (vs (vs vz)))) (var vz))                   -- σ
    (Π (IMu KnotD IPair (pair sTm (var (vs vz))))                 -- q
     (Π (IMu KnotD IPair
           (pair sTy (nsuc (nsuc (var (vs (vs vz))))))) -- M, at n+2
        (IMu KnotD IPair (pair sTy (var (vs (vs (vs vz)))))))))

⊢iihTyMotK : {Γ : Ctx} →
             ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty iihTyMotK
⊢iihTyMotK =
  ty-Π ty-Nat
   (ty-Π (ty-SubTy (⊢snd (⊢var (there (there here)))) (⊢var here))
    (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))
     (ty-Π (ty-IMu KnotWf
              (⊢ixP ⊢sTy (⊢nsuc (⊢nsuc (⊢var (there (there here)))))))
        (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★ THE JUNK ROW — and for `cICon-i` it is the RIGHT answer: `Unit`.
------------------------------------------------------------------------

iihTyJunk : {Γ : Cx} → RTm Γ
iihTyJunk = lam (lam (lam (lam (lam (lam (lam Ty-UnitK))))))

⊢iihTyJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
             IConWf KnotD IPair (◇ ▹ IPair) C →
             Γ ⊢ iihTyJunk ∷ imethTy KnotD IPair k C iihTyMotK
⊢iihTyJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢iihTyMotK
    (⊢lam ty-Nat
      (⊢lam (ty-SubTy (⊢snd (⊢var (there (there (there here))))) (⊢var here))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))
          (⊢lam (ty-IMu KnotWf
                   (⊢ixP ⊢sTy (⊢nsuc (⊢nsuc (⊢var (there (there here)))))))
            (⊢Ty-UnitKv _ (⊢var (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★★★ THE DESCENT THROUGH THE FOUR Π BINDERS, ONCE.
-- ⚠ EACH PASSENGER PAYS A DIFFERENT RUNG, and the count is positional:
--   passenger 2 reads `n` definitionally, 3 needs `wk-single`, 4 needs
--   `towerA`, and the RESULT needs `towerJ`.
------------------------------------------------------------------------

⊢iihAppK : {Γ : Ctx} {dd u h n sb q MM : RTm ⌊ Γ ⌋} →
           Γ ⊢ h ∷ iinst (pair sICon dd) u iihTyMotK →
           Γ ⊢ n ∷ Nat → Γ ⊢ sb ∷ SubTy dd n →
           Γ ⊢ q ∷ K (pair sTm n) → Γ ⊢ MM ∷ K (pair sTy (nsuc (nsuc n))) →
           Γ ⊢ app (app (app (app h n) sb) q) MM ∷ K (pair sTy n)
⊢iihAppK {dd = dd} {u = u} {n = n} {sb = sb} {q = q} {MM = MM}
         dh dn dsb dq dM =
  ⊢-cast (cong (λ z → K (pair sTy z)) (towerJ MM q sb n))
    (⊢app (⊢app (⊢app (⊢app dh dn)
                      (⊢-cast (cong (λ z → SubTy (snd z) n)
                                    (sym (towerA n u (pair sICon dd))))
                              (subBwd (βsnd sICon dd) dsb)))
                (⊢-cast (cong (λ z → K (pair sTm z))
                              (sym (wk-single {v = sb} n)))
                        dq))
          (⊢-cast (cong (λ z → K (pair sTy (nsuc (nsuc z))))
                        (sym (towerA q sb n)))
                  dM))

------------------------------------------------------------------------
-- ★ THE `iρ` ROW'S ANSWER, AT ABSTRACT PIECES.
--   `Σ' (iinst (subTm σ j) (fst q) M) <rest>`
------------------------------------------------------------------------

⊢iihRowρ : {Γ : Ctx} {n dd sb j fq MM rest : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ Nat → Γ ⊢ dd ∷ Nat → Γ ⊢ sb ∷ SubTy dd n →
           Γ ⊢ j ∷ K (pair sTm dd) → Γ ⊢ fq ∷ K (pair sTm n) →
           Γ ⊢ MM ∷ K (pair sTy (nsuc (nsuc n))) →
           Γ ⊢ rest ∷ K (pair sTy n) →
           Γ ⊢ Ty-SgK (iinstK n (subTmAtK dd n sb j) fq MM) (wkTyK n rest)
             ∷ K (pair sTy n)
⊢iihRowρ dn ddd dsb dj dfq dM drest =
  ⊢Ty-SgKv _ dn (⊢iinstK dn (⊢subTmAtK ddd dn dsb dj) dfq dM)
                (⊢wkTyK dn drest)
