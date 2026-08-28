------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE MOTIVE `extS`/`subTm` ELIMINATE AT, AND
-- THE 51 METHODS THAT DO NOTHING.
--
--     M(i, t) = ∀n. (Var (snd ⟨i⟩) → Tm n) → Tm n
--
-- ⚠⚠ WHY EVERY ROW GETS A METHOD.  The knot is ONE description, so
--   casing on a `Var` is an `ielim KnotD` — which demands a method for
--   all 53 rows at a motive defined at all seven SORTS.  Only the two
--   `cVar-*` rows do anything; the other 51 are noise the eliminator
--   insists on.
--
-- ★ THE MOTIVE NEED NOT BE SORT-DEPENDENT, which is the thing worth
--   checking before building anything.  The type above is uniform in the
--   sort — it simply says something UNINTERESTING at the other six.
--   ⚠ But it must still be INHABITED there, and it is: the knot has
--   CLOSED `Tm` rows (`Tm-nzeroK`), so `Tm n` is inhabited at every `n`,
--   variable or not.  Had it not been, the motive would have had to case
--   on the sort tag — a `natrec` over codes — and every one of the 51
--   would have paid for it.
--
-- ★★ AND THE METHOD IS THE SAME TERM AT EVERY ROW.  `imethTy` binds
--   exactly THREE things — the index, the payload, the IH tuple —
--   regardless of how many fields the row has; the motive adds two more.
--   So a method that ignores everything is five `lam`s and a constant,
--   and it is proved once at an ABSTRACT `C`, exactly as `Lib/IFold`
--   proves its fold method.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubMot where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; pair; snd; Nat; Π; IMu
        ; ICon; IDesc; _◂_; inil; renTy; εwkTy; isingle; ipayTy; εwk-ren; ipayTy-ren; ipayTy-cong )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢pair; ⊢unit; ⊢icon; ⊢lam; ty-Nat; ty-Π; ty-IMu; ty-Unit
        ; IConWf; imethTy; imethsTyFrom; ty-Σ
        ; IDescWfFrom; idwf-nil; idwf-cons )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; isingle-Sub⊢; iihTy-wf; ren-ty )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf )
open import DirectedHoTT.Examples.Knot.Tags using ( memTm-nzero )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-nzeroK )
open import DirectedHoTT.Examples.Knot.Terms using ( fordFst )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sTm; sVar; ⊢sTm; ⊢sVar; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )

------------------------------------------------------------------------
-- Binder layout.  The motive is checked at
--     Θ = Γ ▹ εwkTy IPair ▹ K (var vz)
-- so `vz` is the SCRUTINEE and `vs vz` the ambient INDEX.  Under the
-- motive's own `Π Nat`:  n = vz · t = vs vz · i = vs (vs vz).
--
-- ⚠ THE SCRUTINEE NEVER APPEARS.  That is deliberate and it is what
--   makes `iatCon` compute later: instantiating the motive at a row
--   touches only the INDEX slot.
------------------------------------------------------------------------

subMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
subMotK =
  Π Nat (Π (Π (IMu KnotD IPair (pair sVar (snd (var (vs (vs vz))))))
              (IMu KnotD IPair (pair sTm (var (vs vz)))))
           (IMu KnotD IPair (pair sTm (var (vs vz)))))

⊢subMotK : {Γ : Ctx} →
           ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty subMotK
⊢subMotK =
  ty-Π ty-Nat
    (ty-Π (ty-Π (ty-IMu KnotWf
                   (⊢ixP ⊢sVar (⊢snd (⊢var (there (there here))))))
                (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
          (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))

------------------------------------------------------------------------
-- ★ THE INHABITANT THE 51 DO-NOTHING METHODS RETURN.
--
-- Each must produce a `Tm n` at an `n` the MOTIVE bound, so the numeral
-- form `⊢Tm-nzeroK : (n : ℕ) → … K (pair sTm (num n))` does not apply.
--
-- ⚠ AND THE ARBITRARY-DEPTH FORM COSTS NOTHING HERE.  `cTm-nzero`'s row
--   is `[FORD_TM]` — one sort ford, no depth field — so the payload
--   never mentions the depth and there is nothing for a renaming or a
--   substitution to disturb: no cast, no `wk-single`, no `num-ren`.
--
-- ⚠⚠ THAT IS ALSO WHY `⊢Var-vzKv` NEEDS ITS DEPTH TO BE A VARIABLE AND
--   THIS DOES NOT.  The two `cVar-*` rows carry a DEPTH FORD
--   (`snd ⟨i⟩ ≡ nsuc m`), so their payload DOES mention the depth and
--   the weaken-then-substitute round trip has to compute — which it does
--   for a bare variable and does not for a general term.  Of the 53 rows
--   exactly those two are depth-Forded, so the restriction is on two
--   rows, NOT on the table.
------------------------------------------------------------------------

⊢Tm-nzeroKv : {Δ : Ctx} {d : RTm ⌊ Δ ⌋} → Δ ⊢ d ∷ Nat →
              Δ ⊢ Tm-nzeroK ∷ K (pair sTm d)
⊢Tm-nzeroKv dd =
  ⊢icon KnotWf memTm-nzero (⊢ixP ⊢sTm dd)
    (⊢pair ty-Unit (fordFst ⊢sTm) ⊢unit)

------------------------------------------------------------------------
-- ★★★ THE DO-NOTHING METHOD — ONE TERM, ONE PROOF, ALL 51 ROWS.
--
-- `imethTy` binds exactly THREE things — the index, the payload, the IH
-- tuple — however many fields the row has; `subMotK` adds `n` and `σ`.
-- So the method is five `lam`s and a constant, and `C` stays ABSTRACT
-- throughout, exactly as `Lib/IFold` keeps it abstract for the fold.
--
-- ⚠ THE SCAFFOLDING IS `Lib/IFold.⊢ifMethod`'s, with the motive swapped
--   from `Nat` to `subMotK`.  `ipayTy-wf` and `iihTy-wf` are already
--   generic in the motive; only `Lib/IPay`'s two `…Nat-wf` helpers are
--   not, and this proof does not need them.
------------------------------------------------------------------------

constMeth : {Γ : Cx} → RTm Γ
constMeth = lam (lam (lam (lam (lam Tm-nzeroK))))

⊢constMeth : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
             IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
             Γ ⊢ constMeth ∷ imethTy KnotD IPair k C subMotK
⊢constMeth {Γ = Γ} k C wC =
  ⊢lam ⊢IPair
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) C
                     KnotWf wC
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) C}
                      KnotD IPair subMotK (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢subMotK
                      (⊢-cast (trans (ipayTy-ren vs KnotD IPair (isingle (var vz)) C)
                                     (ipayTy-cong KnotD IPair C
                                       (λ { vz → refl ; (vs ()) })))
                              (⊢var here)))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
            (⊢Tm-nzeroKv (⊢var (there here)))))))

------------------------------------------------------------------------
-- THE METHOD **TYPE** IS WELL-FORMED — the same proof, one level up.
--
-- ⚠ `Lib/IPay` has this only at `Nat` (`imethTyNat-wf`), because that is
--   all `Lib/IFold` needed.  Generalising it in `Lib/IPay` would need an
--   `iatCon-wf` — the codomain is `iatCon k ⟨-⟩ M` at an ABSTRACT `M`,
--   and no such lemma exists.
--
-- ★ Here it is not needed: `subMotK` IGNORES THE SCRUTINEE, so
--   instantiating it touches only the index slot and `iatCon` COMPUTES.
--   That is the same property that made `⊢constMeth`'s body writable,
--   and it is why the motive was written to ignore the scrutinee.
------------------------------------------------------------------------

imethTyK-wf : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
              IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
              Γ ⊢ty imethTy KnotD IPair k C subMotK
imethTyK-wf {Γ = Γ} k C wC =
  ty-Π ⊢IPair
    (ty-Π (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) C
                     KnotWf wC
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (ty-Π (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) C}
                      KnotD IPair subMotK (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢subMotK
                      (⊢-cast (trans (ipayTy-ren vs KnotD IPair (isingle (var vz)) C)
                                     (ipayTy-cong KnotD IPair C
                                       (λ { vz → refl ; (vs ()) })))
                              (⊢var here)))
            (ty-Π ty-Nat
              (ty-Π (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                          (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
                    (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))))))

------------------------------------------------------------------------
-- THE TUPLE'S TYPE, by the same induction as `Lib/IPay`'s Nat version.
------------------------------------------------------------------------

imethsTyFromK-wf : {Γ : Ctx} (j : ℕ) (E : IDesc) →
                   IDescWfFrom KnotD IPair E →
                   Γ ⊢ty imethsTyFrom KnotD IPair subMotK j E
imethsTyFromK-wf j inil    idwf-nil          = ty-Unit
imethsTyFromK-wf j (C ◂ E) (idwf-cons wC wE) =
  ty-Σ (imethTyK-wf j C wC)
       (ren-ty (imethsTyFromK-wf (suc j) E wE) there)

------------------------------------------------------------------------
-- ★★★ THE TUPLE: `n` COMPUTED ROWS THEN A GIVEN TAIL.
--
-- ⚠ THE ESCAPE HATCH IS STRUCTURAL, exactly as in `Lib/IWk`: the method
--   tuple is RIGHT-NESTED, so "computed rows then given rows" is just
--   where the nest stops — one constructor and one tail argument.  No
--   row is named and no ordering is required of the table; ordering only
--   decides how much gets computed.
--
-- ★ AND UNLIKE `Lib/IWk` THERE IS NOTHING TO DECIDE.  `Lib/IWk` must
--   CLASSIFY each row (`WkIx`, `WkKa`, …) because a weakening method
--   depends on the row's fields.  A do-nothing method does not, so
--   `CDesc` carries no per-row data — it is a length, made type-safe by
--   being indexed by the description it walks.
------------------------------------------------------------------------

data CDesc : IDesc → Set where
  cd-stop : (E : IDesc) → CDesc E
  cd-cons : {C : ICon (ε ∙)} {E : IDesc} → CDesc E → CDesc (C ◂ E)

cdRest : {E : IDesc} → CDesc E → IDesc
cdRest (cd-stop E) = E
cdRest (cd-cons W)  = cdRest W

cdPos : {E : IDesc} → CDesc E → ℕ → ℕ
cdPos (cd-stop E) j = j
cdPos (cd-cons W)  j = cdPos W (suc j)

constMethsFrom : {Γ : Cx} {E : IDesc} → CDesc E → RTm Γ → RTm Γ
constMethsFrom (cd-stop E) t = t
constMethsFrom (cd-cons W)  t = pair constMeth (constMethsFrom W t)

⊢constMethsFrom : {Γ : Ctx} (j : ℕ) {E : IDesc} (W : CDesc E) →
                  IDescWfFrom KnotD IPair E →
                  (tl : RTm ⌊ Γ ⌋) →
                  Γ ⊢ tl ∷ imethsTyFrom KnotD IPair subMotK (cdPos W j) (cdRest W) →
                  Γ ⊢ constMethsFrom W tl ∷ imethsTyFrom KnotD IPair subMotK j E
⊢constMethsFrom j (cd-stop E) wE tl dtl = dtl
⊢constMethsFrom j (cd-cons {C = C} {E = E} W) (idwf-cons wC wE) tl dtl =
  ⊢pair (ren-ty (imethsTyFromK-wf (suc j) E wE) there)
        (⊢constMeth j C wC)
        (⊢-cast (sym (wk-singleTy {v = constMeth}
                                  (imethsTyFrom KnotD IPair subMotK (suc j) E)))
                (⊢constMethsFrom (suc j) W wE tl dtl))

------------------------------------------------------------------------
-- ★ TAKING THE FIRST `n` ROWS — total, and it stops early if the
--   description runs out.
------------------------------------------------------------------------

cdTake : ℕ → (E : IDesc) → CDesc E
cdTake zero    E        = cd-stop E
cdTake (suc n) inil     = cd-stop inil
cdTake (suc n) (C ◂ E)  = cd-cons (cdTake n E)

------------------------------------------------------------------------
-- ★★★ AND THE SPLIT IS WHERE IT SHOULD BE — CHECKED, NOT ASSUMED.
--
-- ⚠ The same control `Examples/Knot/WkProbe` runs for `Lib/IWk`
--   (`wkdLen (decDesc KnotD) ≡ 51`).  Without it, "51 computed + 2
--   given" is an assertion about a 53-row generated table.
------------------------------------------------------------------------

_ : cdPos (cdTake 51 KnotD) 0 ≡ 51
_ = refl

_ : cdRest (cdTake 51 KnotD) ≡ (cVar-vz ◂ (cVar-vs ◂ inil))
_ = refl
