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
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; pair; snd; Nat; Π; IMu
        ; ICon; IDesc; _◂_; inil; nsuc; nzero; unit; natrec; renTm; renTy; εwkTy
        ; app; fst; jsub; ⌜IMu⌝; ielim; Σ'; isingle; ipayTy; εwk-ren; ipayTy-ren; ipayTy-cong
        ; ⌜Id⌝; ⌜Nat⌝; idrefl; El; _∈ID_; ilookupD )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢pair; ⊢unit; ⊢icon; ⊢lam; ⊢nsuc; ⊢nzero; ⊢natrec; wk-single; ty-Nat; ty-Π; ty-IMu; ty-Unit
        ; IConWf; imethTy; imethsTyFrom; ty-Σ; βsnd; βfst; ξ-pairʳ; ξ-pairˡ; ξ-nsuc; single
        ; _⟶*_; done; step; natrec-suc; natrec-zero; csymᵀ; iinst; iihTy
        ; ⊢app; ⊢jsub; ⊢fst; ⊢conv; ⊢⌜IMu⌝; ⊢⌜Id⌝; ⊢⌜Nat⌝; ty-El; ⊢ielim; imethsTy
        ; IDescWfFrom; idwf-nil; idwf-cons )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy; w; sub-w; ren-w; sub-w-single; towerA; towerJ )
open import DirectedHoTT.Lib.IMeths using ( CDesc; cd-stop; cd-cons; cdRest; cdPos; cdTake )
open import DirectedHoTT.Lib.IFold using ( eqℕ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )
import DirectedHoTT.Lib.ISub as IS
open import DirectedHoTT.Lib.IWk
  using ( Maybe; just; nothing )
open import DirectedHoTT.Lib.IPay
  using ( Split; spl-nil; spl-cons; spl-mem; spl-look; spl-step )
open import DirectedHoTT.Spec.Syntax using ( Sub; ipayTy; subTm; extS; extR )
open import DirectedHoTT.Lib.Monus using ( predTm; ⊢pred; pred-suc; pred-zero )
open import DirectedHoTT.Lib.ArithMonus using ( pred*; pred-snd-pair )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-natrecⁿ; ⟶*-natrecᶻ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-⌜Id⌝ˡ )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ; ⟶ᵀ*-IMu; ⟶ᵀ*-Πˡ; ⟶ᵀ*-El )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN; elIdN; ⊢reflN )
open import DirectedHoTT.Lib.IdSuc using ( predN; ⊢fordPredN )
open import DirectedHoTT.Lib.ICast
  using ( muFwd; muBwd*; fordAs; toMu; fromMu; ⟶*-castᵣ; ⟶*-castₗ )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢-cast; isingle-Sub⊢; iihTy-wf; ren-ty; ⊢wk; iihTy-ren; iihTy-cong )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf; ⊢methLam )
open import DirectedHoTT.Examples.Knot.Tags
  using ( memTm-nzero; memTm-var; memVar-vz; tagVar-vz; tagVar-vs; tagTm-var )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-nzeroK; Tm-varK )
open import DirectedHoTT.Examples.Knot.Terms using ( fordFst; fordSnd; tyFordFst; ixConv; SubTy )
open import DirectedHoTT.Examples.Knot.Build
  using ( Var-vzK; Var-vsK; ⊢Var-vzKv; ⊢Var-vzKt; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz )
open import DirectedHoTT.Examples.Knot.Desc using ( cVar-vz; cVar-vs; cTm-var )
open import DirectedHoTT.Examples.Knot.Wf using ( cVar-vzWf; cVar-vsWf; cTm-varWf )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; ⊢sTm; ⊢sVar; ⊢ixP; toI; fromI; num; ⊢num )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTmK; ⊢wkTmK )

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

-- ★★★ RE-EXPRESSED THROUGH `Lib/IPay.⊢methLam` 2026-08-30.  The three
--   generic binders — index, payload, IH tuple — and their `ipayTy-wf`/
--   `iihTy-wf`/retype obligations are the library's now; what is left
--   here is exactly what is `extMotK`-SPECIFIC: its own two Π binders
--   and the body that inhabits it.
-- ⚠ That split is the point.  A "constant method at an abstract motive"
--   cannot exist — an arbitrary motive may be uninhabited — so the
--   library gives the PROLOGUE and the customer gives the BODY.
⊢constMeth : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
             IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
             Γ ⊢ constMeth ∷ imethTy KnotD IPair k C extMotK
⊢constMeth k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢extMotK
    (⊢lam ty-Nat
      (⊢lam (ty-Π (ty-IMu KnotWf
                     (⊢ixP ⊢sVar (⊢pred (⊢snd (⊢var (there (there (there here))))))))
                  (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
        (⊢Tm-nzeroKv (⊢nsuc (⊢var (there here))))))

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
    (wkTmK (var (vs vz))
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
            -- ⚠⚠ `wkTmK`, NOT `wkK`.  `extS σ (vs x) = renTm vs (σ x)`
            --   (`Spec/Syntax:335`) and `σ x` is an arbitrary TERM, so
            --   this is exactly the case where the two weakenings differ.
            --   ★ THE FIX WAS BLOCKED UNTIL `Knot/RenTm` EXISTED: the
            --     first attempt expressed `renTm vs` as `subTm`, which
            --     put `Knot/WkSub` above this module and closed a cycle.
            --     Renaming had to be built BEFORE substitution, as it is
            --     in `Spec`.  `PLAN-RENAMING.md` §8.
            -- ★ And it drops the two β-steps: `wkK` lands at `sh (pair
            --   sTm n)`, `wkTmK n` lands at `pair sTm (nsuc n)`.
            (⊢wkTmK (⊢var (there here)) (⊢app (⊢var here) tx))))))
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

-- ⚠ INDEXED BY THE VALUE `k`, NOT BY A TERM, and the witness is
--   Γ-GENERIC — see `Lib/ISub`'s `IsNum`.  The typing needs this proof
--   of `subTm σ s`, which lives in a DIFFERENT CONTEXT from `s`, and
--   only a value crosses that boundary.  ★ It costs nothing: the six
--   chains were already stated for an arbitrary `Γ`, and `sTy … sICon`
--   are `num 0 … num 5` DEFINITIONALLY (`Knot/Sorts`), so the clauses
--   are the same six.
decStableK : (k : ℕ) → Maybe ({Δ : Cx} → sortMap {Δ} (num k) ⟶* num k)
decStableK zero                               = just sortMap-ty
decStableK (suc zero)                         = just sortMap-tm
decStableK (suc (suc zero))                   = just sortMap-desc
decStableK (suc (suc (suc zero)))             = just sortMap-dcon
decStableK (suc (suc (suc (suc zero))))       = just sortMap-idesc
decStableK (suc (suc (suc (suc (suc zero))))) = just sortMap-icon
decStableK _                                  = nothing

------------------------------------------------------------------------
-- ★★★ THE SORT FORD'S ACTION — the third place weakening and
-- substitution part company, and the only one that changes the TERM.
--
-- ⚠ `Lib/IWk` COPIES a tag ford through a method, because at the
--   weakened index the constraint reads `fst (sh ⟨i⟩) ≡ b` and `βfst`
--   takes that to `fst ⟨i⟩ ≡ b` — the very witness the method holds.
--   ★ Under substitution the output index reads `sortMap (fst ⟨i⟩)`,
--   and NOTHING reduces that to `fst ⟨i⟩`: mapping the sort is what
--   `sortMap` is for.  ⇒ the witness has to be ACTED ON.
--
-- ★ AND THE ACTION IS `jsub` ONE MORE TIME, in the direction `sortConv`
--   does not go: `symN` turns `fi ≡ b` around, the motive
--   `λ z. sortMap z ≡ b` is transported to `fi`, and the base case
--   `sortMap b ≡ b` is the row's own stability chain read as an
--   identity.  ⇒ the SAME datum `s-rides` already carries.
------------------------------------------------------------------------

fordMapK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
fordMapK fi b p =
  jsub (⌜Id⌝ ⌜Nat⌝ (sortMap (var vz)) (w b)) (symN fi p) (idrefl ⌜Nat⌝ b)

-- ⚠ ONE CAST, and it is the round trip every `jsub` here pays: the
--   motive carries the TAG weakened past its own binder, so instantiating
--   it at `fi` leaves `subTm (single fi) (w (num k))`.  ★ The MOTIVE's
--   own `sortMap (var vz)` needs NO cast — `sortMap` is substitution
--   transparent, which is the same fact `sortConv` relies on.
⊢fordMapK : {Γ : Ctx} {fi t : RTm ⌊ Γ ⌋} (k : ℕ) →
            ({Δ : Cx} → sortMap {Δ} (num k) ⟶* num k) →
            Γ ⊢ fi ∷ Nat → Γ ⊢ t ∷ El (⌜Id⌝ ⌜Nat⌝ fi (num k)) →
            Γ ⊢ fordMapK fi (num k) t ∷ El (⌜Id⌝ ⌜Nat⌝ (sortMap fi) (num k))
⊢fordMapK {fi = fi} k st dfi dt =
  ⊢-cast (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ (sortMap fi) z))
               (wk-single {v = fi} (num k)))
    (⊢jsub (⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢sortMap (elAsNat (⊢var here))))
                         (natAsEl (⊢wk (⊢num k))))
           (natAsEl (⊢num k)) (natAsEl dfi)
           (⊢symN dfi (⊢num k) (⊢conv dt (elIdN fi (num k))))
           -- ★ THE BASE CASE IS THE ROW'S OWN STABILITY CHAIN, read as
           --   an identity: `idrefl` proves `num k ≡ num k`, and `st`
           --   moves the left endpoint back to `sortMap (num k)`.
           (⊢-cast (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ (sortMap (num k)) z))
                         (sym (wk-single {v = num k} (num k))))
             (⊢conv (⊢conv (⊢reflN (⊢num k)) (csymᵀ (elIdN (num k) (num k))))
                    (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-⌜Id⌝ˡ st)))))))

-- ⚠ the module now takes the SORT MAP, its stability decider, and the
--   ford action.
open IS.Sub extNK sortMap decStableK fordMapK

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

------------------------------------------------------------------------
-- ★★★ STEP 1 OF THE REMAINING SIX: the EXTENSION's typing.  ✅ CLOSED.
--
-- `⊢isubPay`'s `rides` case pushes `σ` under `k` binders, so `extN` must
-- be type-preserving:
--
--     ⊢extNK : Γ ⊢ sb ∷ SubTy d n → Γ ⊢ extNK d n sb ∷ SubTy (nsuc d) (nsuc n)
--     SubTy d n = Π (K (pair sVar d)) (K (pair sTm (renTm vs n)))
--
-- ⚠⚠ FOUR CASTS WERE GUESSED AT THE RESULT AND ALL FOUR WERE BACKED
--   OUT.  What finally closed it was NOT a fifth cast but dropping the
--   assumption the four shared — that the body gets BUILT first and
--   CONVERTED second.  Listing them made the shared premise visible;
--   `SUBTM-ATTEMPTS.md` has the table, and this is the second time the
--   list-the-attempts move has paid (`poc/OCP0009/GAP-A-ATTEMPTS.md` was
--   the first, at 51).
--
-- ★ CONVERT THE INPUT AT ITS SOURCE.  At the result the mismatch sits
--   inside a Π DOMAIN, where a `⊢-cast` cannot reach it.  At the
--   argument the type is still concrete, and it takes TWO conversions
--   OF DIFFERENT KINDS, which is why no single cast was ever going to
--   work:
--
--     · the CODOMAIN differs by a RENAMING — `ren-w`, an `≡`, so a
--       `⊢-cast`;
--     · the DOMAIN differs by a REDUCTION — `predSndSub`, a `⟶*`
--       lifted through the `Π` by `⟶ᵀ*-Πˡ`, so a `⊢conv`.
--
-- ★ AND BOTH TOOLS ALREADY EXISTED: `ξ-Πˡ` (`Spec/Typing`) and
--   `⟶ᵀ*-Πˡ` (`Metatheory/Injectivity`) were proved long before this
--   file.  The four attempts never looked for them because, under the
--   dropped assumption, a Π-domain congruence had no place to be used.
------------------------------------------------------------------------

-- ⚠ `SubTy` MOVED to `Knot/Terms` — `Knot/Single` had re-defined it
--   character for character.  Imported above.

-- ★ the domain conversion needs: one `βsnd`, then one `pred-suc`.
-- ⚠ LIFTED.  The body is `Lib/ArithMonus`'s `pred-snd-pair`, which takes
--   the first component as a PARAMETER; this is the `sVar` instance and
--   nothing more.  `Knot/Single` uses the general one.
predSndPair : {Γ : Cx} (d : RTm Γ) →
              predTm (snd (pair sVar (nsuc d))) ⟶* d
predSndPair d = pred-snd-pair sVar d

-- ⚠ AND IT IS NEEDED UNDER A SUBSTITUTION, which is NOT the same
--   statement.  `⊢extSK`'s domain is instantiated to `predTm (snd (w i))`
--   with `i` the SUBSTITUTED pair, so the `nsuc`'s argument arrives as
--   `subTm (single v) (w (w d))` rather than as `w d`.  `predSndPair`
--   still does all the reducing — only its right ENDPOINT has to be
--   moved, and an endpoint is an `≡`, so it moves by a cast and not by
--   another reduction.
--
-- ⬜ GENERALISATION CANDIDATE (with the two families in
--   HANDOFF-2026-08-27 §"THE PENDING GENERALISATION"): `⟶*-castᵣ` is
--   carrier-generic plumbing with nothing knot-specific in it.  It is
--   local only because this is its first customer; a second one moves
--   it down to a reduction lib.
-- ⚠ `⟶*-castᵣ` now lives in `Lib/ICast` beside its mirror
--   `⟶*-castₗ`, which `Lib/ISub` had written independently.

predSndSub : {Γ : Cx} (v D : RTm Γ) →
             subTm (single v) (predTm (snd (w (pair sVar (nsuc D))))) ⟶* D
predSndSub v D =
  ⟶*-castᵣ (wk-single {v = v} D)
           (predSndPair (subTm (single v) (w D)))

------------------------------------------------------------------------
-- ★★★ AND THE INPUT IS CONVERTED AT ITS SOURCE, NOT THE RESULT AFTER.
--
-- ⚠⚠ FOUR EARLIER ATTEMPTS ALL SHARED ONE ASSUMPTION — that the body is
--   BUILT first and CAST second — and each time the goal moved rather
--   than closed.  Dropping that assumption is what closes it, and it is
--   `build-dont-transport` (which closed gap A's `⊢S3s` after 51
--   attempts) applied one level down.  See `SUBTM-ATTEMPTS.md`.
--
-- ★ The tool was in the codebase already: `⟶ᵀ*-Πˡ` lifts a domain
--   reduction through a `Π`, so `predSndPair` reaches the place it is
--   needed.  Nothing new had to be proved — only stated in the right
--   position, where the type is still CONCRETE and the congruence is
--   writable.
------------------------------------------------------------------------

⊢extNK : {Γ : Ctx} {d n sb : RTm ⌊ Γ ⌋} →
         Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ sb ∷ SubTy d n →
         Γ ⊢ extNK d n sb ∷ SubTy (nsuc d) (nsuc n)
⊢extNK {d = d} {n = n} {sb = sb} dd dn dsb =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢nsuc dd)))
    (⊢-cast (cong (λ z → K (pair sTm (nsuc z)))
                  (wk-single {v = renTm vs sb} (renTm vs n)))
      (⊢app (⊢app (⊢extSK (⊢ixP ⊢sVar (⊢nsuc (⊢wk dd))) (⊢var here))
                  (⊢wk dn))
            -- ⚠ TWO CONVERSIONS ON THE INPUT, of DIFFERENT KINDS: the
            --   codomain differs by a RENAMING (`ren-w`, an `≡`), the
            --   domain by a REDUCTION (`predSndPair`, a `⟶*` lifted
            --   through `Π` by `⟶ᵀ*-Πˡ`).  Neither is reachable from
            --   the result end, which is why four casts there failed.
            (⊢conv (⊢-cast (cong (λ z → Π (K (pair sVar (renTm vs d)))
                                          (K (pair sTm z)))
                                 (ren-w {ρ = vs} n))
                           (⊢wk dsb))
                   (csymᵀ (red→≅ᵀ (⟶ᵀ*-Πˡ
                     (⟶ᵀ*-IMu (⟶*-pairʳ (predSndSub (renTm vs n) (renTm vs d))))))))))

------------------------------------------------------------------------
------------------------------------------------------------------------
-- ★★★ THE IH, ELIMINATED — `Lib/ISub`'s second obligation.
--
-- ★ THE TWO `⊢app`s GO THROUGH UNAIDED.  What the motive owes is only
--   its RESULT INDEX, and it owes it in the two currencies this file
--   keeps separate:
--
--     · an `≡` — `iinst` leaves the index under FOUR nested
--       substitutions, and collapsing them is the `sub-w`/`wk-single`
--       round trip, three rungs of it.  ⚠ The DEPTH slot needs none:
--       a substitution applied to a VARIABLE computes, so only the last
--       `wk-single` survives.
--     · a `⟶*` — the index arrives as `sortMap (fst (pair s dd))` and
--       `βfst` is a REDUCTION.  ⇒ `⊢conv`, not `⊢-cast`.
--
-- ⚠ AND `sortMap` MENTIONS ITS ARGUMENT TWICE: `natrec s sTm (p5 s)`
--   puts it in the ZERO branch and inside the SCRUTINEE.  So lifting a
--   reduction through it takes both congruences, not one.
------------------------------------------------------------------------

sortMap-red : {Γ : Cx} {a b : RTm Γ} → a ⟶* b → sortMap a ⟶* sortMap b
sortMap-red r =
  ⟶*-trans (⟶*-natrecᶻ r)
           (⟶*-natrecⁿ (pred* (pred* (pred* (pred* (pred* r))))))

-- ★★★ `towerA`/`towerJ` MOVED TO `Lib/Wk` 2026-09-02, at their THIRD
--   customer (`subMotK`, `ipayTyMotK`, `ihTyMotK`).  They mention nothing
--   of any motive: they are statements about `subTm`/`extS`/`single` and
--   a de Bruijn index, so a motive whose `⟨i⟩` sits in the SECOND domain
--   and whose payload sits three binders up in the result uses them
--   UNCHANGED.  ⇒ the `Lib`/`Examples` inversion, once more.

-- ⚠ `⟶*-castₗ` comes from `Lib/ICast` now.  It had been written THREE
--   times independently — here, in `Lib/ISub`, and (as `⟶*-castᵣ`) once
--   more in this same file — which is what finally moved the pair down.

⊢motAppK : {Γ : Ctx} {s dd u h m sb : RTm ⌊ Γ ⌋} →
           Γ ⊢ h ∷ iinst (pair s dd) u subMotK → Γ ⊢ m ∷ Nat →
           Γ ⊢ sb ∷ SubTy dd m →
           Γ ⊢ app (app h m) sb ∷ K (pair (sortMap s) m)
⊢motAppK {s = s} {dd = dd} {u = u} {m = m} {sb = sb} dh dm dsb =
  ⊢conv (⊢-cast (cong₂ (λ a b → K (pair (sortMap (fst a)) b))
                       (towerJ sb m u (pair s dd)) (wk-single {v = sb} m))
                (⊢app (⊢app dh dm)
                  (⊢conv dsb
                    (csymᵀ (red→≅ᵀ (⟶ᵀ*-Πˡ (⟶ᵀ*-IMu
                      (⟶*-pairʳ (⟶*-castₗ (cong snd (towerA m u (pair s dd)))
                                          (step (βsnd s dd) done))))))))))
        (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairˡ (sortMap-red (step (βfst s dd) done)))))

------------------------------------------------------------------------
-- ★★★ AND THE TYPING MODULE IS INSTANTIATED — which is the real check
-- that steps 1–3 fit together.  ⚠ Each of the three obligations was
-- built against a signature written in `Lib`, so nothing here confirms
-- they COMPOSE until this line typechecks.
------------------------------------------------------------------------

open Typing KnotD IPair SubTy subMotK ⊢extNK ⊢motAppK ⊢fordMapK

------------------------------------------------------------------------
-- ★★★ STEP 4 OF SIX: ONE COMPUTED METHOD, TYPED.
--
-- ⚠ IT LIVES HERE AND NOT IN `Lib`, and that is not an accident.  The
--   method's last two binders are the MOTIVE's own, so typing them needs
--   `subMotK` to unfold — the one thing `Lib/ISub` cannot do.  ★ What
--   `Lib` owed was genericity in the ROW, and `⊢isubPay` delivers that;
--   genericity in the MOTIVE was never the customer's need.
--
-- ★★ AND A COMPUTED ROW NEEDS NO `sortConv`.  The three GIVEN rows build
--   at their own sort and transport; a computed row builds its `icon`
--   AT THE OUTPUT INDEX `pair (sortMap (fst ⟨i⟩)) n` directly, so the
--   method's result type is met on the nose.
--
-- ⚠ WHICH IS WHY `⊢isubPay`'s τ HYPOTHESES ARE REDUCTIONS.  `τ` is
--   `isingle (pair (sortMap (fst ⟨i⟩)) n)`, so `fst (τ vz)` and
--   `snd (τ vz)` are STUCK PROJECTIONS OF A LITERAL PAIR: one `βfst` and
--   one `βsnd`, not two `refl`s.  `σ` is `isingle ⟨i⟩` with `⟨i⟩` a
--   VARIABLE, and both of its hypotheses ARE `refl`.
------------------------------------------------------------------------

-- ★ ONE RENAMING OF THE PAYLOAD TYPE, stated once.  ⚠ `⊢subVarM` needs
--   no such lemma because its row is CONCRETE and `ipayTy` computes; at
--   an abstract `C` it is stuck, so the environment has to be pushed
--   through by hand.  Composed with itself it covers any depth.
payRenK : {Γ : Cx} (v : RTm Γ) (C : ICon (ε ∙)) →
          renTy vs (ipayTy KnotD IPair (isingle v) C) ≡
          ipayTy KnotD IPair (isingle (renTm vs v)) C
payRenK v C = trans (ipayTy-ren vs KnotD IPair (isingle v) C)
                    (ipayTy-cong KnotD IPair C (λ { vz → refl ; (vs ()) }))

-- ★ CONTROL: the motive mentions NOTHING of the ambient context — its
--   deepest variable is `vs³ vz`, and it sits under two Π binders of its
--   own, so both references land inside its own two slots.  ⇒ pushing a
--   renaming past those two slots is the IDENTITY, and `refl` proves it.
--   ⚠ Without this the `iihTy` casts below would carry five stacked
--   `renTy (extR (extR vs))`s with nothing to cancel them.
subMotK-ren : {Γ : Cx} → renTy (extR (extR (vs {Γ = Γ}))) subMotK ≡ subMotK
subMotK-ren = refl

-- ★ and the same, one level up, for the IH tuple's type.
ihRenK : {Γ : Cx} (v q : RTm Γ) (C : ICon (ε ∙)) (M : RTy ((Γ ∙) ∙)) →
         renTy vs (iihTy KnotD IPair (isingle v) C q M)
           ≡ iihTy KnotD IPair (isingle (renTm vs v)) C (renTm vs q)
                   (renTy (extR (extR vs)) M)
ihRenK v q C M =
  trans (iihTy-ren vs KnotD IPair (isingle v) C q M)
        (iihTy-cong KnotD IPair C (renTm vs q) (renTy (extR (extR vs)) M)
                    (λ { vz → refl ; (vs ()) }))

⊢isubMethodK : {Γ : Ctx} (k : ℕ) {C : ICon (ε ∙)}
               (w : SubCon vz C) → IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
               k ∈ID KnotD → ilookupD KnotD k ≡ C →
               Γ ⊢ isubMethod k w ∷ imethTy KnotD IPair k C subMotK
⊢isubMethodK {Γ = Γ} k {C = C} w wC mem look =
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
                      (⊢-cast (payRenK (var vz) C) (⊢var here)))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf
                         (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
            (⊢icon KnotWf mem
                   (⊢ixP (⊢sortMap (⊢fst (⊢var (there (there (there (there here))))))) (⊢var (there here)))
                   (⊢-cast (cong (ipayTy KnotD IPair
                                    (isingle (pair (sortMap (fst (var (vs (vs (vs (vs vz)))))))
                                                   (var (vs vz)))))
                                 (sym look))
                     (⊢isubPay w wC KnotWf
                       (isingle-Sub⊢ (⊢var (there (there (there (there here))))))
                       (isingle-Sub⊢ (⊢ixP (⊢sortMap (⊢fst (⊢var (there (there (there (there here)))))))
                                           (⊢var (there here))))
                       refl (step (βfst _ _) done) refl (step (βsnd _ _) done)
                       (⊢fst (⊢var (there (there (there (there here)))))) (⊢snd (⊢var (there (there (there (there here)))))) (⊢var (there here))
                       (⊢var here)
                       (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                       -- ⚠ FOUR RENAMINGS, not three: a binder's TYPE
                       --   lives in the context BEFORE it, so the payload
                       --   is weakened past ITSELF as well as past `ih`,
                       --   `n` and `σ`.
                       (⊢-cast (trans (cong (renTy vs)
                                 (trans (cong (renTy vs)
                                   (trans (cong (renTy vs) (payRenK (var vz) C))
                                          (payRenK (var (vs vz)) C)))
                                   (payRenK (var (vs (vs vz))) C)))
                                 (payRenK (var (vs (vs (vs vz)))) C))
                               (⊢var (there (there (there here)))))
                       -- ⚠ THREE, for the same reason the payload took
                       --   four: `ih` is weakened past itself, `n` and
                       --   `σ`.  ★ And the MOTIVE cancels by `refl` —
                       --   see `subMotK-ren`.
                       (⊢-cast (trans (cong (renTy vs)
                                 (trans (cong (renTy vs)
                                          (ihRenK (var (vs vz)) (var vz) C subMotK))
                                        (ihRenK (var (vs (vs vz))) (var (vs vz)) C subMotK)))
                                 (ihRenK (var (vs (vs (vs vz)))) (var (vs (vs vz))) C subMotK))
                               (⊢var (there (there here)))))))))))

------------------------------------------------------------------------
-- ★★★ STEP 5 OF SIX: THE TUPLE, AT THE MASK.
--
-- ⚠ `Lib/IWk`'s tuple walks a PREFIX and stops with a caller-supplied
--   tail.  This one is TOTAL and INTERLEAVED — `subTm`'s three given
--   rows sit at 11, 51 and 52 of 53 — so the walk cannot end early and
--   the obligations cannot be a suffix.
--
-- ★ SO THE OBLIGATIONS ARE COMPUTED FROM THE MASK, exactly as the term
--   is: `GiveOK` has one node per row and asks for a derivation at
--   precisely the `sd-give` positions.  ⇒ the caller owes three
--   derivations, not 53, and never has to say WHERE they go.
------------------------------------------------------------------------

-- ★ the method type's own well-formedness, at THIS motive.  ⚠ It is
--   `Lib/IWk`'s `imethTyMot-wf` with the two motive-dependent places
--   replaced: `iihTy-wf`'s motive argument, and the RESULT, which for a
--   Π-motive is a `ty-Π` chain rather than one `ty-IMu`.
imethTySubK-wf : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
                 IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
                 Γ ⊢ty imethTy KnotD IPair k C subMotK
imethTySubK-wf {Γ = Γ} k C wC =
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
                      (⊢-cast (payRenK (var vz) C) (⊢var here)))
            (ty-Π ty-Nat
              (ty-Π (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                          (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
                    (ty-IMu KnotWf
                       (⊢ixP (⊢sortMap (⊢fst (⊢var (there (there (there (there here))))))) (⊢var (there here))))))))

imethsTyFromSubK-wf : {Γ : Ctx} (j : ℕ) (E : IDesc) →
                      IDescWfFrom KnotD IPair E →
                      Γ ⊢ty imethsTyFrom KnotD IPair subMotK j E
imethsTyFromSubK-wf j inil    idwf-nil          = ty-Unit
imethsTyFromSubK-wf j (C ◂ E) (idwf-cons wC wE) =
  ty-Σ (imethTySubK-wf j C wC)
       (ren-ty (imethsTyFromSubK-wf (suc j) E wE) there)

-- ★★★ THE OBLIGATIONS — COMPUTED, not a datatype.
--
-- ⚠⚠ AS A DATATYPE THIS COSTS 53 CONSTRUCTORS.  A `data GiveOK` with a
--   node per row is the obvious encoding, and its inhabitant would be
--   `gv-comp` applied 53 times with three `gv-give`s buried in it —
--   generated, checked, and carrying nothing at 50 of those positions.
--
-- ★ AS A RECURSIVE `Set` IT COSTS THREE.  `GiveOK` walks the mask and
--   emits an obligation only at `sd-give`, so over `KnotD` it REDUCES to
--   `Pr _ (Pr _ (Pr _ OK))` — and the caller writes exactly the three
--   derivations, in order, with no positions mentioned anywhere.
--   ⇒ the same reason the mask is computed rather than enumerated, one
--     level up.
data OKg : Set where
  okg : OKg

data Pr (A B : Set) : Set where
  pr : A → B → Pr A B

GiveOK : (Γ : Ctx) (give : (k : ℕ) → RTm ⌊ Γ ⌋) → ℕ → {E : IDesc} → SubDesc E → Set
GiveOK Γ give j sd-nil        = OKg
GiveOK Γ give j (sd-comp _ W) = GiveOK Γ give (suc j) W
GiveOK Γ give j (sd-give {C = C} W) =
  Pr (Γ ⊢ give j ∷ imethTy KnotD IPair j C subMotK) (GiveOK Γ give (suc j) W)

⊢isubMethsK : {Γ : Ctx} {j : ℕ} {E : IDesc} {give : (k : ℕ) → RTm ⌊ Γ ⌋}
              (W : SubDesc E) → Split KnotD j E → IDescWfFrom KnotD IPair E →
              GiveOK Γ give j W →
              Γ ⊢ isubMeths give j W ∷ imethsTyFrom KnotD IPair subMotK j E
⊢isubMethsK sd-nil        sp idwf-nil          okg      = ⊢unit
⊢isubMethsK {j = j} {give = give} (sd-comp w W) sp (idwf-cons wC wE) g =
  ⊢pair (ren-ty (imethsTyFromSubK-wf (suc j) _ wE) there)
        (⊢isubMethodK j w wC (spl-mem sp) (spl-look sp))
        (⊢-cast (sym (wk-singleTy {v = isubMethod j w} _))
                (⊢isubMethsK W (spl-step sp) wE g))
⊢isubMethsK {j = j} {give = give} (sd-give W) sp (idwf-cons wC wE) (pr dg g) =
  ⊢pair (ren-ty (imethsTyFromSubK-wf (suc j) _ wE) there)
        dg
        (⊢-cast (sym (wk-singleTy {v = give j} _))
                (⊢isubMethsK W (spl-step sp) wE g))

------------------------------------------------------------------------
-- ★★★ STEP 6 OF SIX: `subTm`, ASSEMBLED.
--
-- ⚠ `giveK` DISPATCHES BY `eqℕ`, NOT BY A LITERAL PATTERN.  `giveK 51 =
--   …` is a numeric literal in a PATTERN, which Agda desugars to 51
--   `suc`s and rejects as `LiteralTooBig`; the same numbers are fine in
--   an EXPRESSION.  `isLookup` above already had to be written this way.
------------------------------------------------------------------------

pickTm : {Γ : Cx} → 𝔹 → RTm Γ → RTm Γ → RTm Γ
pickTm true  a b = a
pickTm false a b = b

giveK : {Γ : Cx} (k : ℕ) → RTm Γ
giveK k = pickTm (eqℕ k 11) subVarM
            (pickTm (eqℕ k 51) subVzM
              (pickTm (eqℕ k 52) subVsM unit))

subDescK : SubDesc KnotD
subDescK = decSub isLookup 0 KnotD

-- ★★★ AND THE OBLIGATIONS ARE THREE DERIVATIONS IN A ROW.  ⚠ No
--   positions appear here: `GiveOK` reduced the mask to exactly the
--   `sd-give` slots, so a wrong `isLookup` would show up as a type
--   error, not as a silently misplaced method.
giveOKK : {Γ : Ctx} → GiveOK Γ giveK 0 subDescK
giveOKK = pr ⊢subVarM (pr ⊢subVzM (pr ⊢subVsM okg))

subMethsK : {Γ : Cx} → RTm Γ
subMethsK = isubMeths giveK 0 subDescK

⊢subMethsK : {Γ : Ctx} → Γ ⊢ subMethsK ∷ imethsTy KnotD IPair subMotK KnotD
-- ⚠ `{give = giveK}` PINNED, and it must be.  `GiveOK` is a DEFINED
--   `Set`, so it is not injective: `GiveOK Γ give 0 subDescK` unfolds
--   and consumes its `give` argument, leaving nothing to solve the meta
--   from.  `pin-implicits-on-defined-set-types`, third customer.
⊢subMethsK = ⊢isubMethsK {give = giveK} subDescK spl-nil KnotWf giveOKK

subTmK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
subTmK i x = ielim KnotD i subMethsK x

-- ★ NO CAST.  `⊢ielim` already lands at `iinst i x M`, and `⊢motAppK`
--   takes its hypothesis in exactly that shape — so the eliminator and
--   the IH interface meet without a round trip between them.
⊢subTmK : {Γ : Ctx} {i x : RTm ⌊ Γ ⌋} →
          Γ ⊢ i ∷ εwkTy IPair → Γ ⊢ x ∷ K i →
          Γ ⊢ subTmK i x ∷ iinst i x subMotK
⊢subTmK di dx = ⊢ielim KnotWf ⊢subMotK di ⊢subMethsK dx
