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
        ; ICon; IDesc; _◂_; inil; nsuc; unit; renTm; renTy; εwkTy; app; fst; jsub; ⌜IMu⌝; ielim; Σ'; isingle; ipayTy; εwk-ren; ipayTy-ren; ipayTy-cong )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢pair; ⊢unit; ⊢icon; ⊢lam; ⊢nsuc; wk-single; ty-Nat; ty-Π; ty-IMu; ty-Unit
        ; IConWf; imethTy; imethsTyFrom; ty-Σ; βsnd; βfst; ξ-pairʳ; ξ-pairˡ; ξ-nsuc; single
        ; ⊢app; ⊢jsub; ⊢fst; ⊢conv; ⊢⌜IMu⌝; ⊢ielim; imethsTy
        ; IDescWfFrom; idwf-nil; idwf-cons )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy; w; sub-w )
open import DirectedHoTT.Lib.Monus using ( predTm; ⊢pred )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN )
open import DirectedHoTT.Lib.IdSuc using ( predN; ⊢fordPredN )
open import DirectedHoTT.Examples.Knot.JudgeLib using ( muFwd; fordAs; toMu; fromMu )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkK )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; isingle-Sub⊢; iihTy-wf; ren-ty; ⊢wk )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf )
open import DirectedHoTT.Examples.Knot.Tags using ( memTm-nzero; memTm-var; tagVar-vs )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-nzeroK; Tm-varK )
open import DirectedHoTT.Examples.Knot.Terms using ( fordFst; tyFordFst; ixConv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; ⊢Var-vzKv )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz )
open import DirectedHoTT.Examples.Knot.Desc using ( cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Wf using ( cVar-vzWf; cVar-vsWf )
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
