------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `imethsTyFrom`'s MOTIVE, JUNK ROW AND DESCENT.
--
--     imethsTyFrom D I M j inil    = Unit
--     imethsTyFrom D I M j (C ◂ E) =
--       Σ' (imethTy D I j C M) (renTy vs (imethsTyFrom D I M (suc j) E))
--
-- ★★★ AND HERE THE DEPTH **CAN** BE A PASSENGER, where in
--   `Knot/MethsTyMot` it could not.  The difference is one table entry:
--
--       cDesc-cons   [rec("sDCon",  D),      rec("sDesc",  D),  ford]
--       cIDesc-cons  [rec("sICon",  lit(1)), rec("sIDesc", D),  ford]
--
--   `cIDesc-cons`'s `ICon` field is PINNED at 1 — an `ICon` inside an
--   `IDesc` is a CODE, binding exactly its index — so `C` arrives at
--   depth 1 whatever the ambient is, and nothing forces the row to be
--   built at `snd ⟨i⟩`.  `cDesc-cons`'s `DCon` field is at `D`, the
--   AMBIENT, which is what made the passenger-depth motive untypable
--   there.  ⇒ same-looking recursions, opposite answers, and the tell is
--   `lit` versus `D`.
--
-- ⚠ FIVE PASSENGERS (`n`, `D`, `I`, `M`, `j`) with the result reading the
--   FIRST puts it at `var (vs⁴ vz)` — five rungs, which is exactly
--   `Lib/Wk.towerJ⁵`.  ★ Its SECOND customer, one commit after it was
--   written; the note there says to stop and index at the fourth.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IMethsTyMot where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IMu; εwkTy; app; nzero; nsuc )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢lam; ⊢app; ⊢nzero; ⊢nsuc
        ; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; single; wk-single; iinst )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import normalizer.Syntax.Types using ( cong; sym )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.Wk using ( towerA; towerJ⁵ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sICon; sIDesc; ⊢sIDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-UnitK; Ty-SgK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Ty-UnitKv; ⊢Ty-SgKv )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK; ⊢wkTyK )
open import DirectedHoTT.Examples.Knot.IMethTy using ( imethTyK; ⊢imethTyK )

imethsTyMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
imethsTyMotK =
  Π Nat                                                          -- n
   (Π (IMu KnotD IPair (pair sIDesc (var vz)))                    -- D
    (Π (IMu KnotD IPair (pair sTy nzero))                         -- I, closed
     (Π (IMu KnotD IPair (pair sTy (nsuc (nsuc (var (vs (vs vz))))))) -- M
      (Π Nat                                                      -- j
         (IMu KnotD IPair (pair sTy (var (vs (vs (vs (vs vz)))))))))))

⊢imethsTyMotK : {Γ : Ctx} →
                ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty imethsTyMotK
⊢imethsTyMotK =
  ty-Π ty-Nat
   (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var here)))
    (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTy ⊢nzero))
     (ty-Π (ty-IMu KnotWf
              (⊢ixP ⊢sTy (⊢nsuc (⊢nsuc (⊢var (there (there here)))))))
      (ty-Π ty-Nat
         (ty-IMu KnotWf
            (⊢ixP ⊢sTy (⊢var (there (there (there (there here)))))))))))

-- ★ for `cIDesc-nil` the junk IS the answer: `Unit`.
imethsTyJunk : {Γ : Cx} → RTm Γ
imethsTyJunk = lam (lam (lam (lam (lam (lam (lam (lam Ty-UnitK)))))))

⊢imethsTyJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
                IConWf KnotD IPair (◇ ▹ IPair) C →
                Γ ⊢ imethsTyJunk ∷ imethTy KnotD IPair k C imethsTyMotK
⊢imethsTyJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢imethsTyMotK
    (⊢lam ty-Nat
      (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var here)))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTy ⊢nzero))
          (⊢lam (ty-IMu KnotWf
                   (⊢ixP ⊢sTy (⊢nsuc (⊢nsuc (⊢var (there (there here)))))))
            (⊢lam ty-Nat
              (⊢Ty-UnitKv _
                 (⊢var (there (there (there (there here))))))))))) 

------------------------------------------------------------------------
-- ★★★ THE DESCENT THROUGH THE FIVE Π BINDERS.
-- ⚠ ONLY `M` NEEDS A RUNG.  `D` reads `n` one binder back, which is
--   definitional; `I` is closed and `j` is `Nat`.  The cost is entirely
--   in the RESULT.
------------------------------------------------------------------------

⊢imethsAppK : {Γ : Ctx} {dd u h n DD II MM j : RTm ⌊ Γ ⌋} →
              Γ ⊢ h ∷ iinst (pair sIDesc dd) u imethsTyMotK →
              Γ ⊢ n ∷ Nat → Γ ⊢ DD ∷ K (pair sIDesc n) →
              Γ ⊢ II ∷ K (pair sTy nzero) →
              Γ ⊢ MM ∷ K (pair sTy (nsuc (nsuc n))) → Γ ⊢ j ∷ Nat →
              Γ ⊢ app (app (app (app (app h n) DD) II) MM) j ∷ K (pair sTy n)
⊢imethsAppK {n = n} {DD = DD} {II = II} {MM = MM} {j = j} dh dn dD dI dM dj =
  ⊢-cast (cong (λ z → K (pair sTy z)) (towerJ⁵ j MM II DD n))
    (⊢app (⊢app (⊢app (⊢app (⊢app dh dn) dD) dI)
                (⊢-cast (cong (λ z → K (pair sTy (nsuc (nsuc z))))
                              (sym (towerA II DD n)))
                        dM))
          dj)

-- ★ the `cIDesc-cons` row's answer, at abstract pieces.
⊢imethsRowCons : {Γ : Ctx} {n j D I C M rest : RTm ⌊ Γ ⌋} →
                 Γ ⊢ n ∷ Nat → Γ ⊢ j ∷ Nat →
                 Γ ⊢ D ∷ K (pair sIDesc n) → Γ ⊢ I ∷ K (pair sTy nzero) →
                 Γ ⊢ C ∷ K (pair sICon (num 1)) →
                 Γ ⊢ M ∷ K (pair sTy (nsuc (nsuc n))) →
                 Γ ⊢ rest ∷ K (pair sTy n) →
                 Γ ⊢ Ty-SgK (imethTyK n j D I C M) (wkTyK n rest)
                   ∷ K (pair sTy n)
⊢imethsRowCons dn dj dD dI dC dM drest =
  ⊢Ty-SgKv _ dn (⊢imethTyK dn dj dD dI dC dM) (⊢wkTyK dn drest)
