------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `methsTyFrom`'s MOTIVE, JUNK ROW AND DESCENT.
--
-- ⚠ THE ROWS THEMSELVES ARE NOT HERE, and that is `Knot/IPayTyMot`'s
--   MEASURED rule, not tidiness: inlining one half of a row's answer took
--   that module 9.7s → 20.6s, and both halves OOM-KILLED at 5.5 GB.
--   Naming the descent at ABSTRACT `RTm`s elaborates its equations once,
--   against variables; a call site then only instantiates.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.MethsTyMot where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IMu; εwkTy; app; unit; ielim; nzero; nsuc; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢lam; ⊢app; ⊢nzero; ⊢nsuc
        ; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; ξ-pairʳ; ξ-nsuc; βsnd; done; step; single; wk-single; iinst )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import normalizer.Syntax.Types using ( cong; trans; sym )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Lib.ICast using ( muFwd; muBwd* )
open import DirectedHoTT.Lib.Wk using ( towerA; towerJ⁵ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sDesc; ⊢sDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-UnitK; Ty-SgK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Ty-UnitKv; ⊢Ty-SgKv )
open import DirectedHoTT.Examples.Knot.Sorts using ( sDCon )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK; ⊢wkTyK )
open import DirectedHoTT.Examples.Knot.MethTy using ( methTyK; ⊢methTyK )

------------------------------------------------------------------------
-- ★★★ THE MOTIVE — THREE PASSENGERS, AND THE RESULT READS THE INDEX.
--
--     methsTyFrom D M j dnil    = Unit
--     methsTyFrom D M j (C ◃ E) = Σ' (methTy D j C M)
--                                    (renTy vs (methsTyFrom D M (suc j) E))
--
-- ⚠⚠ THE DEPTH IS **NOT** A PASSENGER, and I tried it as one first.
--   `Knot/IPayTyMot` takes `n` as its first Π binder so its result reads
--   `var (vs³ vz)` and `towerJ` reaches it — but that only works because
--   `ipayTy` carries a SUBSTITUTION `σ : Sub Δ Γ` that bridges the code's
--   depth to the target.  `methsTyFrom` has no such bridge: the payload's
--   `C` arrives at `snd ⟨i⟩`, so a row built at a passenger `n` would put
--   `C` and `D` at DIFFERENT depths and `payTyK n C D` would not type.
--   ⇒ the result depth genuinely IS the scrutinee's, the motive must read
--     the index, and the fifth tower rung is the honest price
--     (`Lib/Wk.towerJ⁵`, where the reasoning is recorded).
--
-- ★ THE PASSENGER ORDER IS STILL THE `IPayTyMot` RULE.  `j` is `Nat` —
--   CLOSED — so it costs no cast wherever it sits, and goes last; `D`
--   reads the index at one binder (`wk-single`) and `M` at two
--   (`towerA`).  Only the body needs the new rung.
------------------------------------------------------------------------

methsTyMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
methsTyMotK =
  Π (IMu KnotD IPair (pair sDesc (snd (var (vs vz)))))                  -- D
   (Π (IMu KnotD IPair (pair sTy (nsuc (snd (var (vs (vs vz)))))))      -- M
    (Π Nat                                                              -- j
       (IMu KnotD IPair (pair sTy (snd (var (vs (vs (vs (vs vz))))))))))

⊢methsTyMotK : {Γ : Ctx} →
               ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty methsTyMotK
⊢methsTyMotK =
  ty-Π (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢snd (⊢var (there here)))))
   (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢nsuc (⊢snd (⊢var (there (there here)))))))
    (ty-Π ty-Nat
       (ty-IMu KnotWf
          (⊢ixP ⊢sTy (⊢snd (⊢var (there (there (there (there here))))))))))

------------------------------------------------------------------------
-- ★ THE JUNK ROW — and for `cDesc-nil` it is the RIGHT answer, not junk:
--   `methsTyFrom D M j dnil = Unit`.
-- ⚠ 3 + #passengers lams, and every index reference is ONE `there`
--   deeper than the motive's — `⊢methLam` binds one more before the
--   passengers start.
------------------------------------------------------------------------

methsTyJunk : {Γ : Cx} → RTm Γ
methsTyJunk = lam (lam (lam (lam (lam (lam Ty-UnitK)))))

⊢methsTyJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
               IConWf KnotD IPair (◇ ▹ IPair) C →
               Γ ⊢ methsTyJunk ∷ imethTy KnotD IPair k C methsTyMotK
⊢methsTyJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢methsTyMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢snd (⊢var (there (there here))))))
      (⊢lam (ty-IMu KnotWf
               (⊢ixP ⊢sTy (⊢nsuc (⊢snd (⊢var (there (there (there here))))))))
        (⊢lam ty-Nat
          (⊢Ty-UnitKv _
            (⊢snd (⊢var (there (there (there (there (there here))))))))))) 

------------------------------------------------------------------------
-- ★★★ THE DESCENT THROUGH THE THREE Π BINDERS, ONCE — and it is the
--   wrapper too, exactly as `⊢ipayAppK` is.
------------------------------------------------------------------------

⊢methsAppK : {Γ : Ctx} {dd u h DD MM j : RTm ⌊ Γ ⌋} →
             Γ ⊢ h ∷ iinst (pair sDesc dd) u methsTyMotK →
             Γ ⊢ DD ∷ K (pair sDesc dd) →
             Γ ⊢ MM ∷ K (pair sTy (nsuc dd)) → Γ ⊢ j ∷ Nat →
             Γ ⊢ app (app (app h DD) MM) j ∷ K (pair sTy dd)
⊢methsAppK {dd = dd} {u = u} {DD = DD} {MM = MM} {j = j} dh dD dM dj =
  muFwd (ξ-pairʳ (βsnd sDesc dd))
    (⊢-cast (cong (λ z → K (pair sTy (snd z)))
                  (towerJ⁵ j MM DD u (pair sDesc dd)))
      (⊢app (⊢app (⊢app dh
                     (⊢-cast (cong (λ z → K (pair sDesc (snd z)))
                                   (sym (wk-single {v = u} (pair sDesc dd))))
                             (muBwd* (step (ξ-pairʳ (βsnd sDesc dd)) done) dD)))
                  (⊢-cast (cong (λ z → K (pair sTy (nsuc (snd z))))
                                (sym (towerA DD u (pair sDesc dd))))
                          (muBwd* (step (ξ-pairʳ (ξ-nsuc (βsnd sDesc dd))) done)
                                  dM)))
            dj))

-- ★ the `cDesc-cons` clause's answer, AT ABSTRACT PIECES.
--   `Σ' (methTy D j C M) (renTy vs (methsTyFrom D M (suc j) E))`
-- ⚠ Stated here rather than inlined in the row for `Knot/IPayTyMot`'s
--   MEASURED reason: inlining half an answer took that module 9.7s →
--   20.6s and both halves OOM-killed at 5.5 GB.
⊢methsRowCons : {Γ : Ctx} {n j D C M rest : RTm ⌊ Γ ⌋} →
                Γ ⊢ n ∷ Nat → Γ ⊢ j ∷ Nat →
                Γ ⊢ D ∷ K (pair sDesc n) → Γ ⊢ C ∷ K (pair sDCon n) →
                Γ ⊢ M ∷ K (pair sTy (nsuc n)) → Γ ⊢ rest ∷ K (pair sTy n) →
                Γ ⊢ Ty-SgK (methTyK n j D C M) (wkTyK n rest)
                  ∷ K (pair sTy n)
⊢methsRowCons dn dj dD dC dM drest =
  ⊢Ty-SgKv _ dn (⊢methTyK dn dj dD dC dM) (⊢wkTyK dn drest)
