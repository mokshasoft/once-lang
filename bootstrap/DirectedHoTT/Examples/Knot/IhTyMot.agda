------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `ihTy`'s MOTIVE, JUNK ROW AND THE ABSTRACT
-- LEMMAS its rows are built from.
--
--     ihTy D dι       q M = Unit
--     ihTy D (dρ C)   q M = Σ' (subTy (single (fst q)) M) (renTy vs (ihTy D C (snd q) M))
--     ihTy D (dκ A C) q M = ihTy D C (snd q) M
--
-- ★★★ `D` IS A VESTIGIAL PARAMETER — `ihTy` never inspects it.  Read the
--   three clauses: `D` is threaded and never used.  ⇒ the object-level
--   form DROPS it, and that is one passenger fewer than `payTy` needs.
--   ⚠ The Agda function keeps it because `Spec/Typing` states `ihTy`
--     beside `payTy` and the pair reads better; nothing forces it.
--
-- ★★ TWO PASSENGERS: the payload `q` and the motive `M`.  `q` steps to
--   `snd q` at every field, `M` never changes — but `M` cannot be a free
--   variable of `Γ` (`⊢methLam` fixes the motive's `Γ`), so it rides.
--
-- ★ AND THE SHAPE IS `subMotK`'s AGAIN.  Two passengers, `⟨i⟩` read in
--   BOTH domains and in the result ⇒ the descent is `wk-single`,
--   `Lib/Wk.towerA` and `Lib/Wk.towerJ`, the same three `⊢motAppK` and
--   `⊢ipayAppK` climb.  THIRD customer; that is what moved them to `Lib`.
--
-- ⚠ THE ROWS ARE ONE PER MODULE for the reason `Knot/IPayTyRho`'s header
--   measures: a concrete row with a real body runs to ~4 GB.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhTyMot where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IDesc; εwkTy; IMu; app; fst; iρ; iκ; iι
        ; ⌜Id⌝; ⌜Nat⌝; isingle; iext; unit; _◂_; ielim; nzero; nsuc; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢fst; ⊢lam; ⊢app; ⊢unit; ⊢nzero; ⊢nsuc
        ; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; ξ-pairʳ; ξ-nsuc; βsnd; done; step; single; wk-single; iinst )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast )
open import normalizer.Syntax.Types using ( cong; trans; sym )
open import DirectedHoTT.Lib.Wk using ( towerA; towerJ )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ )
open import DirectedHoTT.Lib.ICast using ( muFwd; muBwd* )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sTm; ⊢sTm; sDCon; ⊢sDCon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cDCon-rho; cDCon-kap )
open import DirectedHoTT.Examples.Knot.Wf
  using ( KnotWf; cDCon-rhoWf; cDCon-kapWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDCon-rho; tagDCon-kap )
open import DirectedHoTT.Examples.Knot.Ctors
  using ( Ty-UnitK; Ty-SgK; Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.CtorsV
  using ( ⊢Ty-UnitKv; ⊢Ty-SgKv; ⊢Tm-fstKv; ⊢Tm-sndKv )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkKat )
open import DirectedHoTT.Examples.Knot.Single using ( singleK; ⊢singleK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTyAtK; ⊢subTyAtK )

------------------------------------------------------------------------
-- ★ THE MOTIVE.  `⟨i⟩` is `var (vs vz)`; all three positions read it.
------------------------------------------------------------------------

ihTyMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
ihTyMotK =
  Π (IMu KnotD IPair (pair sTm (snd (var (vs vz)))))
   (Π (IMu KnotD IPair (pair sTy (nsuc (snd (var (vs (vs vz)))))))
      (IMu KnotD IPair (pair sTy (snd (var (vs (vs (vs vz)))))))) 

⊢ihTyMotK : {Γ : Ctx} →
            ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty ihTyMotK
⊢ihTyMotK =
  ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢var (there here)))))
   (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢nsuc (⊢snd (⊢var (there (there here)))))))
      (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢snd (⊢var (there (there (there here))))))))

------------------------------------------------------------------------
-- ★ THE JUNK ROW — and for `dι` it is the RIGHT answer, not junk.
------------------------------------------------------------------------

ihTyJunk : {Γ : Cx} → RTm Γ
ihTyJunk = lam (lam (lam (lam (lam Ty-UnitK))))

⊢ihTyJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
            IConWf KnotD IPair (◇ ▹ IPair) C →
            Γ ⊢ ihTyJunk ∷ imethTy KnotD IPair k C ihTyMotK
⊢ihTyJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢ihTyMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢var (there (there here))))))
      (⊢lam (ty-IMu KnotWf
               (⊢ixP ⊢sTy (⊢nsuc (⊢snd (⊢var (there (there (there here))))))))
        (⊢Ty-UnitKv _ (⊢snd (⊢var (there (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★★★ THE DESCENT, ONCE — and it is the wrapper too.
------------------------------------------------------------------------

⊢ihAppK : {Γ : Ctx} {dd u h q MM : RTm ⌊ Γ ⌋} →
          Γ ⊢ h ∷ iinst (pair sDCon dd) u ihTyMotK →
          Γ ⊢ q ∷ K (pair sTm dd) → Γ ⊢ MM ∷ K (pair sTy (nsuc dd)) →
          Γ ⊢ app (app h q) MM ∷ K (pair sTy dd)
⊢ihAppK {dd = dd} {u = u} {q = q} {MM = MM} dh dq dM =
  muFwd (ξ-pairʳ (βsnd sDCon dd))
    (⊢-cast (cong (λ z → K (pair sTy (snd z)))
                  (towerJ MM q u (pair sDCon dd)))
      (⊢app (⊢app dh
               (⊢-cast (cong (λ z → K (pair sTm (snd z)))
                             (sym (wk-single {v = u} (pair sDCon dd))))
                       (muBwd* (step (ξ-pairʳ (βsnd sDCon dd)) done) dq)))
            (⊢-cast (cong (λ z → K (pair sTy (nsuc (snd z))))
                          (sym (towerA q u (pair sDCon dd))))
                    (muBwd* (step (ξ-pairʳ (ξ-nsuc (βsnd sDCon dd))) done) dM))))

-- ★ the `dρ` clause's answer.  ⚠ `fst q` here is the OBJECT-LEVEL `fst`
--   (`Tm-fstK`), not the kernel's: `q` is an encoded TERM, not a method
--   payload.  `payTy`'s rows read the kernel's, one layer up.
⊢ihRowρ : {Γ : Ctx} {n q MM rest : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ Nat → Γ ⊢ q ∷ K (pair sTm n) →
          Γ ⊢ MM ∷ K (pair sTy (nsuc n)) → Γ ⊢ rest ∷ K (pair sTy (nsuc n)) →
          Γ ⊢ Ty-SgK (subTyAtK (nsuc n) n (singleK n (Tm-fstK q)) MM) rest
            ∷ K (pair sTy n)
⊢ihRowρ dn dq dM drest =
  ⊢Ty-SgKv _ dn
    (⊢subTyAtK (⊢nsuc dn) dn (⊢singleK dn (⊢Tm-fstKv _ dn dq)) dM) drest
