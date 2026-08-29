------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE MOTIVE `extS`/`subTm` ELIMINATE AT, AND
-- THE 51 METHODS THAT DO NOTHING.
--
--     M(i, t) = ∀n. (Var (predTm (snd ⟨i⟩)) → Tm n) → Tm (nsuc n)
--
-- ⚠⚠ THE `predTm` IS FORCED, and it is what `Lib/IdSuc` was built for.
--   `extS` eliminates a VARIABLE: its `vs` method holds `x : Var m` and
--   a ford `snd ⟨i⟩ ≡ nsuc m`, while `σ` is stated at the ambient index.
--   Those line up only if `σ`'s domain is the PREDECESSOR — then
--   `⊢fordPredN` turns the ford into `predTm (snd ⟨i⟩) ≡ m` and `σ x`
--   type-checks.  A motive stated at `snd ⟨i⟩` cannot be repaired; it is
--   off by one at the only two rows that matter.
--
-- ⬜ AND `subTm`'s MOTIVE IS A DIFFERENT ONE — recorded here so it is not
--   confused with this:
--
--       M(i, t) = ∀n. (Var (snd ⟨i⟩) → Tm n) → K (pair (fst ⟨i⟩) n)
--
--   ★ Uniform, and NOT sort-dependent after all: substitution must send
--     a `Ty` to a `Ty` and a `Tm` to a `Tm`, but the sort is just
--     `fst ⟨i⟩` — a PROJECTION of the index, not a case split.  ⚠ And
--     there the 51 do-nothing methods do NOT exist: every row rebuilds
--     its own constructor.  The no-op story below belongs to `extS`
--     alone.
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
        ; ICon; IDesc; _◂_; inil; nsuc; nzero; unit; natrec; renTm; renTy; εwkTy
        ; app; fst; jsub; ⌜IMu⌝; ielim; Σ'; isingle; ipayTy; εwk-ren; ipayTy-ren; ipayTy-cong )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢pair; ⊢unit; ⊢icon; ⊢lam; ⊢nsuc; ⊢nzero; ⊢natrec; wk-single; ty-Nat; ty-Π; ty-IMu; ty-Unit
        ; IConWf; imethTy; imethsTyFrom; ty-Σ; βsnd; βfst; ξ-pairʳ; ξ-pairˡ; ξ-nsuc; single
        ; _⟶*_; done; step; natrec-suc; natrec-zero
        ; ⊢app; ⊢jsub; ⊢fst; ⊢conv; ⊢⌜IMu⌝; ⊢⌜Id⌝; ⊢⌜Nat⌝; ty-El; ⊢ielim; imethsTy
        ; IDescWfFrom; idwf-nil; idwf-cons )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy; w; sub-w )
open import DirectedHoTT.Lib.IMeths using ( CDesc; cd-stop; cd-cons; cdRest; cdPos; cdTake )
open import DirectedHoTT.Lib.IFold using ( eqℕ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )
import DirectedHoTT.Lib.ISub as IS
open import DirectedHoTT.Lib.IWk using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax using ( Sub; ipayTy; iihTy )
open import DirectedHoTT.Lib.Monus using ( predTm; ⊢pred; pred-suc; pred-zero )
open import DirectedHoTT.Lib.ArithMonus using ( pred* )
open import DirectedHoTT.Metatheory.Confluence using ( ⟶*-trans; ⟶*-natrecⁿ; ⟶*-pairˡ )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN )
open import DirectedHoTT.Lib.IdSuc using ( predN; ⊢fordPredN )
open import DirectedHoTT.Examples.Knot.JudgeLib
  using ( muFwd; muBwd*; fordAs; toMu; fromMu )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkK )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; isingle-Sub⊢; iihTy-wf; ren-ty; ⊢wk )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf )
open import DirectedHoTT.Examples.Knot.Tags
  using ( memTm-nzero; memTm-var; memVar-vz; tagVar-vz; tagVar-vs; tagTm-var )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-nzeroK; Tm-varK )
open import DirectedHoTT.Examples.Knot.Terms using ( fordFst; fordSnd; tyFordFst; ixConv )
open import DirectedHoTT.Examples.Knot.Build
  using ( Var-vzK; Var-vsK; ⊢Var-vzKv; ⊢Var-vzKt; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz )
open import DirectedHoTT.Examples.Knot.Desc using ( cVar-vz; cVar-vs; cTm-var )
open import DirectedHoTT.Examples.Knot.Wf using ( cVar-vzWf; cVar-vsWf; cTm-varWf )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; ⊢sTm; ⊢sVar; ⊢ixP; toI; fromI )
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

extMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
extMotK =
  Π Nat (Π (Π (IMu KnotD IPair (pair sVar (predTm (snd (var (vs (vs vz)))))))
              (IMu KnotD IPair (pair sTm (var (vs vz)))))
           (IMu KnotD IPair (pair sTm (nsuc (var (vs vz))))))

⊢extMotK : {Γ : Ctx} →
           ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty extMotK
⊢extMotK =
  ty-Π ty-Nat
    (ty-Π (ty-Π (ty-IMu KnotWf
                   (⊢ixP ⊢sVar (⊢pred (⊢snd (⊢var (there (there here)))))))
                (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
          (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢nsuc (⊢var (there here))))))

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
-- tuple — however many fields the row has; `extMotK` adds `n` and `σ`.
-- So the method is five `lam`s and a constant, and `C` stays ABSTRACT
-- throughout, exactly as `Lib/IFold` keeps it abstract for the fold.
--
-- ⚠ THE SCAFFOLDING IS `Lib/IFold.⊢ifMethod`'s, with the motive swapped
--   from `Nat` to `extMotK`.  `ipayTy-wf` and `iihTy-wf` are already
--   generic in the motive; only `Lib/IPay`'s two `…Nat-wf` helpers are
--   not, and this proof does not need them.
------------------------------------------------------------------------

constMeth : {Γ : Cx} → RTm Γ
constMeth = lam (lam (lam (lam (lam Tm-nzeroK))))

⊢constMeth : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
             IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
             Γ ⊢ constMeth ∷ imethTy KnotD IPair k C extMotK
⊢constMeth {Γ = Γ} k C wC =
  ⊢lam ⊢IPair
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) C
                     KnotWf wC
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) C}
                      KnotD IPair extMotK (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢extMotK
                      (⊢-cast (trans (ipayTy-ren vs KnotD IPair (isingle (var vz)) C)
                                     (ipayTy-cong KnotD IPair C
                                       (λ { vz → refl ; (vs ()) })))
                              (⊢var here)))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢pred (⊢snd (⊢var (there (there (there here))))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
            (⊢Tm-nzeroKv (⊢nsuc (⊢var (there here))))))))

------------------------------------------------------------------------
-- THE METHOD **TYPE** IS WELL-FORMED — the same proof, one level up.
--
-- ⚠ `Lib/IPay` has this only at `Nat` (`imethTyNat-wf`), because that is
--   all `Lib/IFold` needed.  Generalising it in `Lib/IPay` would need an
--   `iatCon-wf` — the codomain is `iatCon k ⟨-⟩ M` at an ABSTRACT `M`,
--   and no such lemma exists.
--
-- ★ Here it is not needed: `extMotK` IGNORES THE SCRUTINEE, so
--   instantiating it touches only the index slot and `iatCon` COMPUTES.
--   That is the same property that made `⊢constMeth`'s body writable,
--   and it is why the motive was written to ignore the scrutinee.
------------------------------------------------------------------------

imethTyK-wf : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
              IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
              Γ ⊢ty imethTy KnotD IPair k C extMotK
imethTyK-wf {Γ = Γ} k C wC =
  ty-Π ⊢IPair
    (ty-Π (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) C
                     KnotWf wC
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (ty-Π (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) C}
                      KnotD IPair extMotK (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢extMotK
                      (⊢-cast (trans (ipayTy-ren vs KnotD IPair (isingle (var vz)) C)
                                     (ipayTy-cong KnotD IPair C
                                       (λ { vz → refl ; (vs ()) })))
                              (⊢var here)))
            (ty-Π ty-Nat
              (ty-Π (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢pred (⊢snd (⊢var (there (there (there here))))))))
                          (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
                    (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢nsuc (⊢var (there here)))))))))

------------------------------------------------------------------------
-- THE TUPLE'S TYPE, by the same induction as `Lib/IPay`'s Nat version.
------------------------------------------------------------------------

imethsTyFromK-wf : {Γ : Ctx} (j : ℕ) (E : IDesc) →
                   IDescWfFrom KnotD IPair E →
                   Γ ⊢ty imethsTyFrom KnotD IPair extMotK j E
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

-- ⚠ `CDesc` AND ITS OPERATIONS MOVED TO `Lib/IMeths` — nothing in them
--   mentions the knot, a motive or a sort.  A library wanting to import
--   an example is the signal that the example held something general.

constMethsFrom : {Γ : Cx} {E : IDesc} → CDesc E → RTm Γ → RTm Γ
constMethsFrom (cd-stop E) t = t
constMethsFrom (cd-cons W)  t = pair constMeth (constMethsFrom W t)

⊢constMethsFrom : {Γ : Ctx} (j : ℕ) {E : IDesc} (W : CDesc E) →
                  IDescWfFrom KnotD IPair E →
                  (tl : RTm ⌊ Γ ⌋) →
                  Γ ⊢ tl ∷ imethsTyFrom KnotD IPair extMotK (cdPos W j) (cdRest W) →
                  Γ ⊢ constMethsFrom W tl ∷ imethsTyFrom KnotD IPair extMotK j E
⊢constMethsFrom j (cd-stop E) wE tl dtl = dtl
⊢constMethsFrom j (cd-cons {C = C} {E = E} W) (idwf-cons wC wE) tl dtl =
  ⊢pair (ren-ty (imethsTyFromK-wf (suc j) E wE) there)
        (⊢constMeth j C wC)
        (⊢-cast (sym (wk-singleTy {v = constMeth}
                                  (imethsTyFrom KnotD IPair extMotK (suc j) E)))
                (⊢constMethsFrom (suc j) W wE tl dtl))

------------------------------------------------------------------------
-- ★ TAKING THE FIRST `n` ROWS — total, and it stops early if the
--   description runs out.
------------------------------------------------------------------------

_ : cdPos (cdTake 51 KnotD) 0 ≡ 51
_ = refl

_ : cdRest (cdTake 51 KnotD) ≡ (cVar-vz ◂ (cVar-vs ◂ inil))
_ = refl

------------------------------------------------------------------------
-- ★ `Tm-varK` AT AN ARBITRARY DEPTH — `Knot/Build`'s `⊢kLam` pattern.
--
-- ⚠ `cTm-var`'s row is `iρ (pair sVar (snd ⟨i⟩)) (iκ <sort ford> iι)`:
--   one recursive field AT THE AMBIENT DEPTH and a sort ford, no depth
--   ford.  So it takes an arbitrary `d`, and the only cast is the one
--   `⊢kLam` also pays — `βsnd` reducing the field's index, with no
--   `ξ-nsuc` because the field sits at the ambient depth, not its
--   successor.
------------------------------------------------------------------------

⊢Tm-varKv : {Δ : Ctx} {d a0 : RTm ⌊ Δ ⌋} →
            Δ ⊢ d ∷ Nat → Δ ⊢ a0 ∷ K (pair sVar d) →
            Δ ⊢ Tm-varK a0 ∷ K (pair sTm d)
⊢Tm-varKv {d = d} dd d0 =
  ⊢icon KnotWf memTm-var (⊢ixP ⊢sTm dd)
    (⊢pair (tyFordFst ⊢sTm (⊢wk dd))
           (ixConv (ξ-pairʳ (βsnd sTm d)) d0)
           (⊢pair ty-Unit (fordFst ⊢sTm) ⊢unit))

------------------------------------------------------------------------
-- ★★★ THE FIRST REAL METHOD: `extS σ vz = var vz`.
--
-- ⚠ NOTHING IS TRANSPORTED HERE.  `vz`'s row has no recursive field, so
--   there is no `σ` application and the depth ford is never inverted —
--   the answer is built outright at `nsuc n`.  All the ford work is in
--   the `vs` method.
------------------------------------------------------------------------

extVz : {Γ : Cx} → RTm Γ
extVz = lam (lam (lam (lam (lam (Tm-varK (Var-vzK (var (vs vz))))))))

⊢extVz : {Γ : Ctx} →
         Γ ⊢ extVz ∷ imethTy KnotD IPair tagVar-vz cVar-vz extMotK
⊢extVz {Γ = Γ} =
  ⊢lam ⊢IPair
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) cVar-vz
                     KnotWf cVar-vzWf
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) cVar-vz}
                      KnotD IPair extMotK (isingle (var (vs vz))) cVar-vz (var vz) cVar-vzWf
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢extMotK
                      -- ⚠ NO CAST HERE, unlike `⊢constMeth`.  At an ABSTRACT
                      --   `C` the payload type is stuck and the two
                      --   environments must be identified by `ipayTy-ren` +
                      --   `ipayTy-cong`; at the CONCRETE `cVar-vz` `ipayTy`
                      --   COMPUTES and they are definitionally equal.
                      -- ★ Which also means the lemma could not be used here:
                      --   computed away, its `σ`/`σ'` are unrecoverable —
                      --   `half-generalization-is-worst`, at one row.
                      (⊢var here))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf
                         (⊢ixP ⊢sVar (⊢pred (⊢snd (⊢var (there (there (there here))))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
            -- ⚠ PINNED: `K` is a DEFINED function, so the goal
            --   `K (pair sTm _)` does not solve the depth by unification.
            (⊢Tm-varKv {d = nsuc (var (vs vz))} {a0 = Var-vzK (var (vs vz))}
                       (⊢nsuc (⊢var (there here)))
                       (⊢Var-vzKv {x = vs vz} (⊢var (there here))))))))

------------------------------------------------------------------------
-- ★★★ THE SECOND REAL METHOD: `extS σ (vs x) = wk (σ x)`.
--
-- ⚠ THIS IS WHERE THE FORD IS PAID.  `cVar-vs`'s payload is
--   `(m, x, fordFst, fordSnd)` with `x : Var m`, while `σ` is stated at
--   `Var (predTm (snd ⟨i⟩))`.  `⊢fordPredN` turns the DEPTH ford
--   `snd ⟨i⟩ ≡ nsuc m` into `predTm (snd ⟨i⟩) ≡ m`, and `symN` orients
--   it so a single `⊢jsub` moves `x` to where `σ` can eat it.
--
-- ★ ONE `jsub`, exactly as `Examples/WkFin` measured — and it works only
--   because `⌜IMu⌝` IS A CODE, so `⊢jsub` can transport along the
--   family.  §12's decision, cashed again.
--
-- ⚠ AND THE RESULT NEEDS TWO β STEPS.  `⊢wkK` lands at `K (sh i)` with
--   `sh i = pair (fst i) (nsuc (snd i))`; at `i = pair sTm n` both
--   projections are REDEXES, so `muFwd` fires twice to reach
--   `K (pair sTm (nsuc n))`.
------------------------------------------------------------------------

extVs : {Γ : Cx} → RTm Γ
extVs =
  lam (lam (lam (lam (lam
    (wkK (pair sTm (var (vs vz)))
         (app (var vz)
              (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                    (symN (predTm (snd (var (vs (vs (vs (vs vz)))))))
                          (predN (snd (var (vs (vs (vs (vs vz))))))
                                 (fst (snd (snd (snd (var (vs (vs (vs vz))))))))))
                    (fst (snd (var (vs (vs (vs vz)))))))))))))

⊢extVs : {Γ : Ctx} →
         Γ ⊢ extVs ∷ imethTy KnotD IPair tagVar-vs cVar-vs extMotK
⊢extVs {Γ = Γ} =
  ⊢lam ⊢IPair
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) cVar-vs
                     KnotWf cVar-vsWf
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) cVar-vs}
                      KnotD IPair extMotK (isingle (var (vs vz))) cVar-vs (var vz) cVar-vsWf
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢extMotK
                      (⊢var here))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf
                         (⊢ixP ⊢sVar (⊢pred (⊢snd (⊢var (there (there (there here))))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
            -- ⚠ TWO β STEPS, INNERMOST FIRST: `sh i` projects `i` twice
            --   and both projections are redexes at `pair sTm n`.
            (muFwd (ξ-pairʳ (ξ-nsuc (βsnd sTm (var (vs vz)))))
              (muFwd (ξ-pairˡ (βfst sTm (var (vs vz))))
                (⊢wkK (⊢ixP ⊢sTm (⊢var (there here)))
                      (⊢app (⊢var here) tx))))))))
  where
    -- the payload binder, and the two components the method needs
    dp = ⊢var (there (there (there here)))
    dm = elAsNat (⊢fst dp)
    dsi = ⊢pred (⊢snd (⊢var (there (there (there (there here))))))
    -- ★ THE FORD, INVERTED AND ORIENTED.
    deq = ⊢symN (⊢pred (⊢snd (⊢var (there (there (there (there here)))))))
                dm
                (⊢fordPredN (⊢snd (⊢var (there (there (there (there here))))))
                            dm
                            (fordAs (⊢fst (⊢snd (⊢snd (⊢snd dp))))))
    -- ⚠ `⊢jsub`'s ENDPOINTS live at `El ⌜Nat⌝` (that is `IdN`'s carrier)
    --   while `⊢pred`/`⊢symN`/`⊢fordPredN` all want `Nat`.  Both forms of
    --   the same two terms are needed; the conversion is free but the
    --   mismatch is invisible until `⊢jsub` is applied.
    tx = fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                       (natAsEl dm) (natAsEl dsi) deq
                       (toMu (⊢fst (⊢snd dp))))

------------------------------------------------------------------------
-- ★★★ THE 53-METHOD TUPLE, AND `extS`.
--
-- 51 do-nothing methods computed at an abstract row, then the two that
-- matter — the split `Examples/Knot/SzProbe`-style controls above show
-- lands exactly at `cVar-vz ◂ cVar-vs ◂ inil`.
------------------------------------------------------------------------

extTail : {Γ : Cx} → RTm Γ
extTail = pair extVz (pair extVs unit)

⊢extTail : {Γ : Ctx} →
           Γ ⊢ extTail ∷ imethsTyFrom KnotD IPair extMotK 51
                                      (cVar-vz ◂ (cVar-vs ◂ inil))
⊢extTail =
  ⊢pair (ren-ty (imethsTyFromK-wf 52 (cVar-vs ◂ inil)
                                  (idwf-cons cVar-vsWf idwf-nil)) there)
        ⊢extVz
        (⊢-cast (sym (wk-singleTy {v = extVz}
                        (imethsTyFrom KnotD IPair extMotK 52 (cVar-vs ◂ inil))))
          (⊢pair (ren-ty (imethsTyFromK-wf 53 inil idwf-nil) there)
                 ⊢extVs
                 (⊢-cast (sym (wk-singleTy {v = extVs}
                                 (imethsTyFrom KnotD IPair extMotK 53 inil)))
                         ⊢unit)))

extMethsK : {Γ : Cx} → RTm Γ
extMethsK = constMethsFrom (cdTake 51 KnotD) extTail

⊢extMethsK : {Γ : Ctx} → Γ ⊢ extMethsK ∷ imethsTy KnotD IPair extMotK KnotD
⊢extMethsK = ⊢constMethsFrom 0 (cdTake 51 KnotD) KnotWf extTail ⊢extTail

-- ★★★ `extS` — the eliminator.  `extSK i k` is `∀n. (Var (predTm (snd i))
--   → Tm n) → Tm (nsuc n)`; at `i = pair sVar (nsuc m)` the domain
--   reduces to `Var m`, which is `extS`'s type.
extSK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
extSK i k = ielim KnotD i extMethsK k

⊢extSK : {Γ : Ctx} {i k : RTm ⌊ Γ ⌋} →
         Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ k ∷ K i →
         Γ ⊢ extSK i k ∷ Π Nat (Π (Π (K (pair sVar (predTm (snd (w i)))))
                                     (K (pair sTm (var (vs vz)))))
                                  (K (pair sTm (nsuc (var (vs vz))))))
-- ⚠ ONE CAST, AND IT IS THE ROUND TRIP AGAIN.  `iinst` leaves the index
--   as `subTm (extS (single k)) (w (w i))`; `sub-w` pushes the
--   substitution under one weakening and `wk-single` cancels it against
--   the other.  Same composite `⊢wkK` pays, one binder deeper.
⊢extSK {i = i} {k = k} di dk =
  ⊢-cast (cong (λ z → Π Nat (Π (Π (K (pair sVar (predTm (snd z))))
                                  (K (pair sTm (var (vs vz)))))
                               (K (pair sTm (nsuc (var (vs vz)))))))
               (trans (sub-w {σ = single k} (w i)) (cong w (wk-single {v = k} i))))
         (⊢ielim KnotWf ⊢extMotK di ⊢extMethsK dk)

------------------------------------------------------------------------
-- ⬜ TOWARD `subTm` — AND THE SORT MAP ITS MOTIVE NEEDS.
--
-- ⚠⚠ THE OBVIOUS MOTIVE IS UNWRITABLE.  Substitution must send a `Ty`
--   to a `Ty` and a `Tm` to a `Tm`, so
--
--       ∀n. (Var (snd ⟨i⟩) → Tm n) → K (pair (fst ⟨i⟩) n)
--
--   looks right and is uniform — but at sort `sVar` it demands a
--   `Var n` at a GENERIC `n`, and `Var 0` is EMPTY.  Those two methods
--   could not be written at all.  ⇒ and that is not an encoding
--   accident: substitution genuinely maps a VARIABLE to a TERM.
--
-- ★★★ SO THE SORT MOVES: `sVar ↦ sTm`, everything else fixed.  ⚠ AND IT
--   IS NOT A CASE AT THE TYPE LEVEL — only the INDEX is computed, so the
--   motive stays a plain `K (pair … n)`:
--
--       sortMap s = natrec s sTm (pred⁵ s)
--
--   `pred⁵ s` is `0` for every sort but `sVar` (which is 6), so the
--   `natrec` returns `s` on the nose everywhere else and `sTm` there.
--   ⚠ `pred⁵`, NOT `s ∸ 5`: they compute the same thing here, but
--   `pred-suc`/`pred-zero` chain directly while `monus` costs a
--   `monus-suc` per step FIRST and then the same `pred`s.
--
-- ⚠ IT DOES NOT COMPUTE DEFINITIONALLY.  The object-level `natrec`
--   steps by `⟶`, not by Agda's equality, so every row pays ONE
--   CONVERSION to reduce `sortMap <its sort>` — about six steps, and
--   uniform.  That is the price of not having a type-level case.
------------------------------------------------------------------------

p5 : {Γ : Cx} → RTm Γ → RTm Γ
p5 s = predTm (predTm (predTm (predTm (predTm s))))

⊢p5 : {Γ : Ctx} {s : RTm ⌊ Γ ⌋} → Γ ⊢ s ∷ Nat → Γ ⊢ p5 s ∷ Nat
⊢p5 ds = ⊢pred (⊢pred (⊢pred (⊢pred (⊢pred ds))))

sortMap : {Γ : Cx} → RTm Γ → RTm Γ
sortMap s = natrec s sTm (p5 s)

⊢sortMap : {Γ : Ctx} {s : RTm ⌊ Γ ⌋} → Γ ⊢ s ∷ Nat → Γ ⊢ sortMap s ∷ Nat
⊢sortMap ds = ⊢natrec ty-Nat ds ⊢sTm (⊢p5 ds)

------------------------------------------------------------------------
-- ★★★ AND IT REDUCES AS CLAIMED — CHECKED, NOT ASSERTED.
--
-- ⚠ The whole design rests on `sortMap` moving EXACTLY ONE sort.  Three
--   controls: the sort below the boundary, the boundary itself, and the
--   one that moves.
------------------------------------------------------------------------

sortMap-var : {Γ : Cx} → sortMap {Γ} sVar ⟶* sTm
sortMap-var =
  ⟶*-trans (⟶*-natrecⁿ (⟶*-trans (pred* (pred* (pred* (pred* (pred-suc _)))))
                       (⟶*-trans (pred* (pred* (pred* (pred-suc _))))
                       (⟶*-trans (pred* (pred* (pred-suc _)))
                       (⟶*-trans (pred* (pred-suc _)) (pred-suc _))))))
           (step (natrec-suc _ _ _) done)

sortMap-icon : {Γ : Cx} → sortMap {Γ} sICon ⟶* sICon
sortMap-icon =
  ⟶*-trans (⟶*-natrecⁿ (⟶*-trans (pred* (pred* (pred* (pred* (pred-suc _)))))
                       (⟶*-trans (pred* (pred* (pred* (pred-suc _))))
                       (⟶*-trans (pred* (pred* (pred-suc _)))
                       (⟶*-trans (pred* (pred-suc _)) (pred-suc _))))))
           (step (natrec-zero _ _) done)

sortMap-ty : {Γ : Cx} → sortMap {Γ} sTy ⟶* sTy
sortMap-ty =
  ⟶*-trans (⟶*-natrecⁿ (⟶*-trans (pred* (pred* (pred* (pred* pred-zero))))
                       (⟶*-trans (pred* (pred* (pred* pred-zero)))
                       (⟶*-trans (pred* (pred* pred-zero))
                       (⟶*-trans (pred* pred-zero) pred-zero)))))
           (step (natrec-zero _ _) done)

------------------------------------------------------------------------
-- ★★★ AND THEREFORE `subTm`'s MOTIVE.
--
--     M(i, t) = ∀n. (Var (snd ⟨i⟩) → Tm n) → K (pair (sortMap (fst ⟨i⟩)) n)
--
-- ⚠ THE SORT IS A COMPUTED INDEX, NOT A TYPE-LEVEL CASE.  `K (pair … n)`
--   is one type former applied to one term; only that term discriminates.
--   ⇒ nothing here needs a `natrec` over CODES, which is what a genuinely
--   sort-dependent motive would have cost.
--
-- ⚠⚠ AND UNLIKE `extMotK` THERE ARE NO NO-OP ROWS.  Every one of the 53
--   rebuilds its own constructor with substituted children, so this is
--   generator work — `tools/gen-knot.py` already holds the field list
--   each method needs.
------------------------------------------------------------------------

subMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
subMotK =
  Π Nat (Π (Π (IMu KnotD IPair (pair sVar (snd (var (vs (vs vz))))))
              (IMu KnotD IPair (pair sTm (var (vs vz)))))
           (IMu KnotD IPair (pair (sortMap (fst (var (vs (vs (vs vz)))))) (var (vs vz)))))

⊢subMotK : {Γ : Ctx} →
           ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty subMotK
⊢subMotK =
  ty-Π ty-Nat
    (ty-Π (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢snd (⊢var (there (there here))))))
                (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
          (ty-IMu KnotWf
             (⊢ixP (⊢sortMap (⊢fst (⊢var (there (there (there here))))))
                   (⊢var (there here)))))

------------------------------------------------------------------------
-- ★★★ `subTm`'s METHOD TUPLE — 50 COMPUTED, 3 GIVEN.
--
-- ⚠ `extN` TAKES THE SOURCE DEPTH.  `extS` is an `ielim` at index
--   `pair sVar (nsuc d)`, so pushing `σ` under a binder needs `d` as
--   well as the target `n`.  Everything is weakened by one inside the
--   `lam`, which is the whole content of the definition.
------------------------------------------------------------------------

extNK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
extNK d n σ =
  lam (app (app (extSK (pair sVar (nsuc (w d))) (var vz)) (w n)) (w σ))


-- ★ the reduction each row supplies.  `sTm` is the one the `Tm` rows and
--   both `Var` rows need; `sortMap-var` above is the only one that MOVES.
sortMap-tm : {Γ : Cx} → sortMap {Γ} sTm ⟶* sTm
sortMap-tm =
  ⟶*-trans (⟶*-natrecⁿ (⟶*-trans (pred* (pred* (pred* (pred* (pred-suc _)))))
                       (⟶*-trans (pred* (pred* (pred* pred-zero)))
                       (⟶*-trans (pred* (pred* pred-zero))
                       (⟶*-trans (pred* pred-zero) pred-zero)))))
           (step (natrec-zero _ _) done)

sortMap-desc : {Γ : Cx} → sortMap {Γ} sDesc ⟶* sDesc
sortMap-desc =
  ⟶*-trans (⟶*-natrecⁿ (⟶*-trans (pred* (pred* (pred* (pred* (pred-suc _)))))
                       (⟶*-trans (pred* (pred* (pred* (pred-suc _))))
                       (⟶*-trans (pred* (pred* pred-zero))
                       (⟶*-trans (pred* pred-zero)
                       pred-zero)))))
           (step (natrec-zero _ _) done)

sortMap-dcon : {Γ : Cx} → sortMap {Γ} sDCon ⟶* sDCon
sortMap-dcon =
  ⟶*-trans (⟶*-natrecⁿ (⟶*-trans (pred* (pred* (pred* (pred* (pred-suc _)))))
                       (⟶*-trans (pred* (pred* (pred* (pred-suc _))))
                       (⟶*-trans (pred* (pred* (pred-suc _)))
                       (⟶*-trans (pred* pred-zero)
                       pred-zero)))))
           (step (natrec-zero _ _) done)

sortMap-idesc : {Γ : Cx} → sortMap {Γ} sIDesc ⟶* sIDesc
sortMap-idesc =
  ⟶*-trans (⟶*-natrecⁿ (⟶*-trans (pred* (pred* (pred* (pred* (pred-suc _)))))
                       (⟶*-trans (pred* (pred* (pred* (pred-suc _))))
                       (⟶*-trans (pred* (pred* (pred-suc _)))
                       (⟶*-trans (pred* (pred-suc _))
                       pred-zero)))))
           (step (natrec-zero _ _) done)

------------------------------------------------------------------------
-- ★★★ `sortMap`-STABILITY, DECIDED.
--
-- ⚠ THE ONE DATUM `Lib/IWk`'s CLASSIFIER DOES NOT CARRY.  A computed
--   row's field lands at `K (pair (sortMap s) …)` where the slot wants
--   `K (pair s …)`, so the typing needs `sortMap s ⟶* s` per field.
--
-- ★ Six sorts satisfy it and one does not — `sVar`, the sort `sortMap`
--   exists to move.  ⚠ And that is exactly right: the three rows whose
--   fields are `sVar`-sorted are the LOOKUP rows, which are GIVEN, so
--   `nothing` here can never block a computed row.  Measured over
--   `KnotD`: the 50 computed rows use `sTy`/`sTm`/`sDesc`/`sDCon`/
--   `sIDesc`/`sICon` and never `sVar`.
------------------------------------------------------------------------

decStableK : {Δ : Cx} (s : RTm Δ) → Maybe (sortMap s ⟶* s)
decStableK nzero                                    = just sortMap-ty
decStableK (nsuc nzero)                             = just sortMap-tm
decStableK (nsuc (nsuc nzero))                      = just sortMap-desc
decStableK (nsuc (nsuc (nsuc nzero)))               = just sortMap-dcon
decStableK (nsuc (nsuc (nsuc (nsuc nzero))))        = just sortMap-idesc
decStableK (nsuc (nsuc (nsuc (nsuc (nsuc nzero))))) = just sortMap-icon
decStableK _                                        = nothing

-- ⚠ the module now takes the SORT MAP and its stability decider too.
open IS.Sub extNK sortMap decStableK

-- ★ the three rows that APPLY `σ` rather than rebuilding: `cTm-var` and
--   the two `cVar-*`.  ⚠ Their positions are DATA about the generated
--   table, so they are asserted below rather than trusted.
-- ⚠ NOT literal PATTERNS: Agda expands them to `suc (suc …)` and
--   refuses at this size (`LiteralTooBig`).  `eqℕ` compares instead.
orB : 𝔹 → 𝔹 → 𝔹
orB true  _ = true
orB false b = b

isLookup : ℕ → 𝔹
isLookup k = orB (eqℕ k 11) (orB (eqℕ k 51) (eqℕ k 52))

------------------------------------------------------------------------
-- ★★★ AND THE MASK HITS EXACTLY THREE ROWS — CHECKED.
--
-- ⚠⚠ THIS CONTROL IS STRONGER THAN IT LOOKS.  `decSub` falls back to
--   GIVEN for any row `Lib/IWk`'s decider cannot classify, so a count of
--   3 says BOTH that the three lookups are where `isLookup` claims AND
--   that the other FIFTY all classify.  A silent misclassification would
--   show up here as 4 or more.
------------------------------------------------------------------------

_ : sdGiven (decSub isLookup 0 KnotD) ≡ 3
_ = refl

------------------------------------------------------------------------
-- ★★★ THE ONE LEMMA EVERY ROW NEEDS.
--
-- A method's RESULT is at index `pair (sortMap (fst ⟨i⟩)) n`, while what
-- it builds — an `icon` for a computed row, `σ x` for a lookup one —
-- sits at the row's OWN sort `s`.  The row's sort ford says
-- `fst ⟨i⟩ ≡ s`, so the two are reconciled by transporting along it.
--
-- ⚠ TWO MOVES, AND ONLY ONE OF THEM IS THE FORD.
--   1. `sortMap s ⟶* s` — the row's own reduction (six steps), run
--      BACKWARDS: the value is built at `s` and must be READ at
--      `sortMap s`.  ★ Free, because `≅ᵀ` is symmetric; no reduction is
--      inverted, only a conversion.
--   2. `jsub` along `symN` of the ford, through the motive
--      `λ z. K (pair (sortMap z) n)`.
--
-- ★ ONE lemma for all 53 rows, computed and given alike — which is why
--   it belongs beside the motive rather than in any method.
------------------------------------------------------------------------

-- ⚠⚠ THE OUTPUT SORT IS `s'`, NOT `s`, AND THE DIFFERENCE IS THE WHOLE
--   POINT.  Stated with `sortMap s ⟶* s` this lemma is unusable at
--   exactly the rows it was written for: `sVar` is the ONE sort
--   `sortMap` moves, so the two `cVar-*` methods build at `sTm` while
--   their ford names `sVar`.  Every other row has `s' = s` and pays
--   nothing for the extra generality.
sortConv : {Γ : Ctx} {fi s s' n t : RTm ⌊ Γ ⌋} {p : RTm ⌊ Γ ⌋} →
           Γ ⊢ fi ∷ Nat → Γ ⊢ s ∷ Nat → Γ ⊢ n ∷ Nat →
           Γ ⊢ p ∷ IdN fi s →
           sortMap s ⟶* s' →
           Γ ⊢ t ∷ K (pair s' n) →
           Γ ⊢ jsub (⌜IMu⌝ KnotD IPair (pair (sortMap (var vz)) (w n)))
                    (symN fi p) t
             ∷ K (pair (sortMap fi) n)
-- ⚠ ONE CAST: the motive carries `n` WEAKENED past its own binder, so
--   instantiating it leaves `subTm (single fi) (w n)`.  `wk-single`
--   cancels it — the same round trip `⊢wkK` and `⊢extSK` both pay.
sortConv {fi = fi} {s = s} {s' = s'} {n = n} dfi ds dn dp red dt =
  ⊢-cast (cong (λ z → K (pair (sortMap fi) z)) (wk-single {v = fi} n))
   (fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf
                   (⊢ixP (⊢sortMap (elAsNat (⊢var here))) (⊢wk dn)))
                (natAsEl ds) (natAsEl dfi)
                (⊢symN dfi ds dp)
                -- ⚠ AND THE SAME ROUND TRIP ON THE OTHER SIDE, at `s`
                --   instead of `fi`: `⊢jsub`'s `e` premise instantiates
                --   the motive too.
                (toMu (muBwd* (⟶*-pairˡ red)
                        (⊢-cast (cong (λ z → K (pair s' z))
                                      (sym (wk-single {v = s} n)))
                                dt)))))

------------------------------------------------------------------------
-- ★★★ LOOKUP METHOD 1 of 3: `subTm σ (var x) = σ x`.
--
-- ⚠ THIS ROW CANNOT BE COMPUTED, which is why the mask exists.  A
--   rebuild would produce `icon tagTm-var (pair <a Tm> …)` — `var`
--   applied to a TERM — so the method's SHAPE differs, not one field.
--
-- Binders: σ = vz · n = vs vz · ih = vs² vz · p = vs³ vz · i = vs⁴ vz.
-- The payload is `(x, fordFst, unit)`, so `x = fst p` and the sort ford
-- is `fst (snd p)`.  ⚠ The IH exists and is UNUSED — `σ` is applied to
-- the field itself, not to anything recursive.
------------------------------------------------------------------------

subVarM : {Γ : Cx} → RTm Γ
subVarM =
  lam (lam (lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair (pair (sortMap (var vz)) (var (vs (vs vz)))))
          (symN (fst (var (vs (vs (vs (vs vz))))))
                (fst (snd (var (vs (vs (vs vz)))))))
          (app (var vz) (fst (var (vs (vs (vs vz)))))))))))

⊢subVarM : {Γ : Ctx} →
           Γ ⊢ subVarM ∷ imethTy KnotD IPair tagTm-var cTm-var subMotK
⊢subVarM {Γ = Γ} =
  ⊢lam ⊢IPair
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) cTm-var
                     KnotWf cTm-varWf
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) cTm-var}
                      KnotD IPair subMotK (isingle (var (vs vz))) cTm-var (var vz) cTm-varWf
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢subMotK
                      (⊢var here))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf
                         (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
            (sortConv (⊢fst (⊢var (there (there (there (there here))))))
                      ⊢sTm
                      (⊢var (there here))
                      (fordAs (⊢fst (⊢snd (⊢var (there (there (there here)))))))
                      sortMap-tm
                      (⊢app (⊢var here) (⊢fst (⊢var (there (there (there here)))))))))))

------------------------------------------------------------------------
-- ★ THE SECOND TRANSPORT, shared by both `Var` rows.
--
-- Their methods must hand `σ` a `Var (snd ⟨i⟩)`, but what they can BUILD
-- is `Var-vzK m` / `Var-vsK m x` at depth `nsuc m`.  The DEPTH ford
-- `snd ⟨i⟩ ≡ nsuc m` closes that gap — a second `jsub`, at the simpler
-- motive `λ z. K (pair sVar z)`.
--
-- ⚠ NO `wk-single` HERE, unlike `sortConv`: this motive mentions no
--   weakened variable, so instantiating it leaves nothing to cancel.
------------------------------------------------------------------------

varAt : {Γ : Ctx} {di m t p : RTm ⌊ Γ ⌋} →
        Γ ⊢ di ∷ Nat → Γ ⊢ m ∷ Nat →
        Γ ⊢ p ∷ IdN di (nsuc m) →
        Γ ⊢ t ∷ K (pair sVar (nsuc m)) →
        Γ ⊢ jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz))) (symN di p) t
          ∷ K (pair sVar di)
varAt ddi dm dp dt =
  fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                (natAsEl (⊢nsuc dm)) (natAsEl ddi)
                (⊢symN ddi (⊢nsuc dm) dp)
                (toMu dt))

------------------------------------------------------------------------
-- ★★★ LOOKUP METHODS 2 and 3 — the `Var` rows.
--
-- At sort `sVar` the motive's target is `K (pair (sortMap (fst ⟨i⟩)) n)`
-- and `sortMap sVar ⟶* sTm`, so these produce a TERM — which is exactly
-- what substituting a variable does.  ⚠ That is why the motive needed
-- `sortMap`: `K (pair (fst ⟨i⟩) n)` would demand a `Var n` here, and
-- `Var 0` is empty.
--
-- ⚠ TWO TRANSPORTS EACH, along DIFFERENT fords:
--   `varAt`    — the DEPTH ford, to hand `σ` a `Var (snd ⟨i⟩)`.
--   `sortConv` — the SORT ford, to read the resulting `Tm n` at
--                `sortMap (fst ⟨i⟩)`.
--
-- ★ AND THE VARIABLE IS REBUILT, not reused.  `imethTy` does hand the
--   method its index and payload, so `icon k p` would reconstruct the
--   scrutinee at `K ⟨i⟩` — but `σ` wants `K (pair sVar (snd ⟨i⟩))` and
--   `⟨i⟩` is OPAQUE; closing that needs a pair-η the kernel does not
--   have.  Hence `Knot/Build`'s arbitrary-depth `⊢Var-vzKt`/`⊢Var-vsKt`.
------------------------------------------------------------------------

subVzM : {Γ : Cx} → RTm Γ
subVzM =
  lam (lam (lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair (pair (sortMap (var vz)) (var (vs (vs vz)))))
          (symN (fst (var (vs (vs (vs (vs vz))))))
                (fst (snd (var (vs (vs (vs vz)))))))
          (app (var vz)
               (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                     (symN (snd (var (vs (vs (vs (vs vz)))))) (fst (snd (snd (var (vs (vs (vs vz))))))))
                     (Var-vzK (fst (var (vs (vs (vs vz)))))))))))))

⊢subVzM : {Γ : Ctx} →
          Γ ⊢ subVzM ∷ imethTy KnotD IPair tagVar-vz cVar-vz subMotK
⊢subVzM {Γ = Γ} =
  ⊢lam ⊢IPair
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) cVar-vz
                     KnotWf cVar-vzWf
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) cVar-vz}
                      KnotD IPair subMotK (isingle (var (vs vz))) cVar-vz (var vz) cVar-vzWf
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢subMotK
                      (⊢var here))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf
                         (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
            (sortConv (⊢fst (⊢var (there (there (there (there here))))))
                      ⊢sVar
                      (⊢var (there here))
                      (fordAs (⊢fst (⊢snd (⊢var (there (there (there here)))))))
                      sortMap-var
                      (⊢app (⊢var here)
                            (varAt (⊢snd (⊢var (there (there (there (there here))))))
                                   (elAsNat (⊢fst (⊢var (there (there (there here))))))
                                   (fordAs (⊢fst (⊢snd (⊢snd (⊢var (there (there (there here))))))))
                                   (⊢Var-vzKt (elAsNat (⊢fst (⊢var (there (there (there here))))))))))))))

subVsM : {Γ : Cx} → RTm Γ
subVsM =
  lam (lam (lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair (pair (sortMap (var vz)) (var (vs (vs vz)))))
          (symN (fst (var (vs (vs (vs (vs vz))))))
                (fst (snd (snd (var (vs (vs (vs vz))))))))
          (app (var vz)
               (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                     (symN (snd (var (vs (vs (vs (vs vz)))))) (fst (snd (snd (snd (var (vs (vs (vs vz)))))))))
                     (Var-vsK (fst (var (vs (vs (vs vz))))) (fst (snd (var (vs (vs (vs vz))))))))))))))

⊢subVsM : {Γ : Ctx} →
          Γ ⊢ subVsM ∷ imethTy KnotD IPair tagVar-vs cVar-vs subMotK
⊢subVsM {Γ = Γ} =
  ⊢lam ⊢IPair
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) cVar-vs
                     KnotWf cVar-vsWf
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) cVar-vs}
                      KnotD IPair subMotK (isingle (var (vs vz))) cVar-vs (var vz) cVar-vsWf
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢subMotK
                      (⊢var here))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf
                         (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
            (sortConv (⊢fst (⊢var (there (there (there (there here))))))
                      ⊢sVar
                      (⊢var (there here))
                      (fordAs (⊢fst (⊢snd (⊢snd (⊢var (there (there (there here))))))))
                      sortMap-var
                      (⊢app (⊢var here)
                            (varAt (⊢snd (⊢var (there (there (there (there here))))))
                                   (elAsNat (⊢fst (⊢var (there (there (there here))))))
                                   (fordAs (⊢fst (⊢snd (⊢snd (⊢snd (⊢var (there (there (there here)))))))))
                                   (⊢Var-vsKt (elAsNat (⊢fst (⊢var (there (there (there here)))))) (⊢fst (⊢snd (⊢var (there (there (there here))))))))))))))

------------------------------------------------------------------------
-- ⬜ THE 50 COMPUTED ROWS' TYPING — statement first.
--
-- ★ MIRRORS `Lib/IWk.⊢iwkPay` EXACTLY, including the discipline that
--   matters: the environment stays ABSTRACT (`σ`, `τ` with `Sub⊢`) and
--   is stepped with `payStep`, never unfolded.  ⚠ Unfolding it is what
--   produced the round-trip thicket in `Knot/Build` rungs 4–5, and that
--   was forced there (a CONCRETE constructor); here it is not.
--
-- ⚠ AND THE RELATION IS THE SAME SHAPE.  `Lib/IWk` relates its two
--   environments by `τ a ≡ sh (σ a)`; substitution relates them by
--
--       τ a ≡ shS n (σ a)   where   shS n i = pair (sortMap (fst i)) n
--
--   — the index's SORT is mapped and its DEPTH replaced, where weakening
--   kept the sort and bumped the depth.  Same slot, different action.
--
-- ⚠⚠ THE TYPING LIVES HERE, NOT IN `Lib/ISub`, because `subMotK`
--   mentions `sortMap`/`KnotD`/`IPair`.  Parameterising `Lib/ISub` by a
--   motive would be speculative — `Lib/IFold` earned its algebra
--   parameter by having two customers.  `C` still stays ABSTRACT, which
--   is what keeps this ONE proof rather than 50.
------------------------------------------------------------------------

shS : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
shS n i = pair (sortMap (fst i)) n

------------------------------------------------------------------------
-- ⬜ NEXT: `⊢isubPay` — the payload rebuild's typing.
--
-- ★★ THE STATEMENT TYPE-CHECKS (verified 2026-08-29, then backed out
--   because its holes break the build).  Recorded so the next attempt
--   starts from a known-good signature rather than re-deriving it:
--
--     SubTy d n = Π (K (pair sVar d)) (K (pair sTm (renTm vs n)))
--
--     ⊢isubPay : {Γ Θ : Ctx} {σ τ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋} {a : Var ⌊ Θ ⌋}
--                {C : ICon ⌊ Θ ⌋} {dp n sb q ih : RTm ⌊ Γ ⌋}
--                (w : SubCon a C) → IConWf KnotD IPair Θ C →
--                Sub⊢ Θ Γ σ → Sub⊢ Θ Γ τ → τ a ≡ shS n (σ a) →
--                Γ ⊢ n ∷ Nat → Γ ⊢ sb ∷ SubTy dp n →
--                Γ ⊢ q ∷ ipayTy KnotD IPair σ C →
--                Γ ⊢ ih ∷ iihTy KnotD IPair σ C q subMotK →
--                Γ ⊢ isubPay w dp n sb q ih ∷ ipayTy KnotD IPair τ C
--
--   ⚠ It mirrors `Lib/IWk.⊢iwkPay` slot for slot, with `τ a ≡ sh (σ a)`
--     replaced by `τ a ≡ shS n (σ a)` — same relation, different action.
--
-- ✅ WHAT ALREADY CLOSES: the `sc-ι` case (`⊢unit`), and `⊢sPick`'s
--   `pinned` case — `Lib/IWk`'s `pinned-stable` transfers VERBATIM,
--   which is the part of the shared classification that really is shared.
--
-- ⬜ WHAT IS OPEN: `⊢sPick`'s `rides` case and the two `⊢isubPay`
--   recursive cases.  ⚠ `rides` needs two premises the sketch above
--   does not yet thread — the IH's own type (`iinst (subTm σ j) q
--   subMotK`) and the EXTENSION's typing,
--
--       ⊢extN : Γ ⊢ sb ∷ SubTy d n → Γ ⊢ extN d n sb ∷ SubTy (nsuc d) (nsuc n)
--
--   which `⊢extSK` should supply.  Then the case is: apply the IH at
--   `(nsuc^k n, ext^k σ)`, landing at `K (pair (sortMap s) (nsuc^k n))`,
--   and convert to `K (pair s (nsuc^k n))` by ONE `muFwd*` along
--   `⟶*-pairˡ st` — `st` being precisely the witness `SubIx` was
--   refined to carry.
------------------------------------------------------------------------

