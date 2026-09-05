------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ THE TWO REFERENCE ROWS OF `ren-agree`, PROVED BY
-- HAND, WHICH IS WHAT `gen_renagree` MUST EMIT.
--
-- ⚠ THIS MODULE IS INPUT TO A GENERATOR, NOT A DELIVERABLE.  Delete it
--   when `tools/gen-knot.py` emits all 30 `RTm` rows; until then it is
--   the checked statement of the shape, and `Knot/SzAgree` is the
--   precedent (436 generated lines from ~40 lines of emitter).
--
-- ★ TWO SHAPES COVER THE TABLE:
--     `cTm-nzero`  [FORD_TM]                  — no recursive field
--     `cTm-lam`    [rec("sTm", sucD()), FORD] — one, ONE BINDER DEEPER
--   Every other row is a longer list of the same two kinds; `rec` at `D`
--   (no binder) is `rec` at `sucD()` with `depthOf = 0`.
--
-- ★★★ AND THE BINDER ROW IS THE ONE `Knot/SzAgree` HAS NO ANALOGUE FOR.
--   A fold never crosses a binder, so its IH is always at the same
--   algebra.  Here `sPick` at depth 1 produces
--
--       app (app <IH entry> (sucs 1 n)) (extsN 1 d n σ)
--
--   which IS `renTmAtK sTm (nsuc dd) (nsuc n) (extRNK d n r) (enTm b)` —
--   the IH's own statement at the EXTENDED renaming.  `extR-Represents`
--   supplies its hypothesis.
--
-- ⚠⚠ AND `extR-Represents` STAYS POLYMORPHIC IN `d` — BUT NOT BECAUSE THE
--   ALTERNATIVE IS IMPOSSIBLE.  An earlier version of this note said a
--   fixed `d` "would need a congruence through `extRNK`'s own `lam`,
--   which does not exist".  THE SECOND HALF WAS WRONG: it does not exist
--   YET, and it is ONE LINE, from pieces already in `Metatheory/RedCong`:
--
--       extRNK-congᵈ r = ⟶*-lam (⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ
--                          (⟶*-pairʳ (⟶*-nsuc (⟶*-ren vs r))))))
--
--   (checked, then deleted unused.)  ⇒ the real argument for the
--   polymorphic form is that it is FREE — the proof never touches `d` —
--   and it saves a reduction step at all 30 call sites.  That is a good
--   reason; "otherwise impossible" was not one.
--
-- ★ AND WHY IT IS FREE IS WORTH SAYING OUT LOUD.  `d` is load-bearing for
--   TYPING (`⊢extRNK` needs `Γ ⊢ rn ∷ RenTy d n`) and irrelevant to the
--   REDUCTION behaviour on encoded variables — neither `extRNK-vz` nor
--   `extRNK-vs` mentions it in its conclusion.  ⚠ A parameter that does
--   not affect reduction is exactly the shape that hid `wkK` for two
--   customers, so it earns an explicit reason rather than a shrug: here
--   the typing use is real and checked, and the reduction laws are stated
--   over an arbitrary `d`, which is the strongest form available.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenAgreeRows where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; Var; vz; vs; Ren; app; pair; icon; renTm; extR; ilookupD; nzero; idrefl; ⌜Nat⌝; unit; lam; snd; app )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; βfst; βsnd )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ; ⟶*-ielimⁱ; ⟶*-fst; ⟶*-snd; ⟶*-nsuc )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enVar )
open import DirectedHoTT.Examples.Knot.Sorts using ( num; len; sTm )
open import DirectedHoTT.Examples.Knot.RenTm using ( renTmAtK )
open import DirectedHoTT.Examples.Knot.RenRed using ( ren-head-red )
open import DirectedHoTT.Examples.Knot.SubAgree using ( RepresentsR; extR-Represents )
open import DirectedHoTT.Lib.ISub using ( ttsd )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Lib.IWk using ( IsSucs; is-snd; is-suc; just )
import DirectedHoTT.Lib.ISub as IS
open import DirectedHoTT.Examples.Knot.RenMot using ( extRNK )
open import DirectedHoTT.Examples.Knot.RenTm using ( renSmap; renDecStable; renFordMap )
open IS.Sub extRNK renSmap renDecStable renFordMap

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

-- ★ PROBE: state the row and prove `done` early, to READ the goal.
--   (Attempt 10 of `nrs` — the probe that makes an opaque mismatch
--   legible.  `SUBTM-ATTEMPTS.md` step 7.)
row-nzero : {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} →
            RepresentsR ρ r →
            renTmAtK sTm (num (len Γ)) (num (len Δ)) r (enTm {Γ} {Θ} nzero)
            ⟶* enTm {Δ} {Θ} (renTm ρ nzero)
row-nzero {Γ} {Δ} h =
  ren-head-red 30 ttsd (sc-κ (sk-fst (n-suc n-zero) done) sc-ι) 30 refl
               sTm (num (len Γ)) (num (len Δ)) _
               (pair (idrefl ⌜Nat⌝ sTm) unit) »
  ⟶*-icon (⟶*-pairˡ (step (βfst _ _) done))

------------------------------------------------------------------------
-- ★ THE BINDER ROW — `cTm-lam` is `[rec("sTm", sucD()), FORD_TM]`, so its
--   recursive field sits ONE binder deeper and the IH is needed at the
--   EXTENDED renaming.  This is the shape `Knot/SzAgree` has no analogue
--   for.  Probe with `done` to read the goal.
------------------------------------------------------------------------

row-lam : {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} →
          RepresentsR ρ r → (b : RTm (Γ ∙)) →
          -- the IH, at the extended renaming, as the generator will pass it
          (ih : {Θ' : Cx} {r' : RTm Θ'} → RepresentsR (extR ρ) r' →
                renTmAtK sTm (num (len (Γ ∙))) (num (len (Δ ∙))) r' (enTm b)
                ⟶* enTm (renTm (extR ρ) b)) →
          renTmAtK sTm (num (len Γ)) (num (len Δ)) r (enTm {Γ} {Θ} (lam b))
          ⟶* enTm {Δ} {Θ} (renTm ρ (lam b))
row-lam {Γ} {Δ} h b ih =
  ren-head-red 12 ttsd
    (sc-ρ (s-rides (n-suc n-zero) (is-suc is-snd) done)
          (sc-κ (sk-fst (n-suc n-zero) done) sc-ι)) 12 refl
    sTm (num (len Γ)) (num (len Δ)) _
    (pair (enTm b) (pair (idrefl ⌜Nat⌝ sTm) unit)) »
  -- ★ SLOT 0 — the recursive field.  ⚠ all of this happens INSIDE the
  --   `icon`'s payload, so every step is under `⟶*-icon ∘ ⟶*-pairˡ`.
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))) »
     -- ★ and the eliminator's INDEX: `subTm (isingle i) (var vz)` is `i`,
     --   so `snd i` is a `βsnd` away from the depth the IH is stated at.
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (step (βsnd _ _) done))))) »
     -- ★★★ THE IH, AT THE EXTENDED RENAMING.  ⚠ NO reduction is needed on
     --   `extsN`'s depth argument: `extR-Represents` is polymorphic in
     --   `d`, because neither `extRNK-vz` nor `extRNK-vs` mentions it in
     --   its conclusion.  ⇒ instantiate it at whatever the payload
     --   produced.  ⚠ A fixed `d` would need `extRNK-congᵈ` — which is
     --   ONE LINE and was checked, not impossible; see the header.  The
     --   polymorphic form is chosen because it is FREE, not because the
     --   alternative is blocked.
     ih (extR-Represents (snd (pair sTm (num (len Γ)))) h))) »
  -- ★ SLOT 1 — the ford.  `kaPick` is the identity at the renaming
  --   instance, so what is left is two projections out of the payload.
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (step (βsnd _ _) done) » step (βfst _ _) done)))

------------------------------------------------------------------------
-- ★ THE THIRD SHAPE — `cTm-app` is `[rec("sTm", D), rec("sTm", D),
--   FORD_TM]`: TWO recursive fields at depth ZERO.
--
-- ⚠ AT DEPTH 0 THE IH IS AT THE **SAME** RENAMING.  `sPick` gives
--   `app (app ih (sucs 0 n)) (extsN 0 d n σ)`, and `extsN 0 d n σ = σ` —
--   so `h` is passed straight through, with no `extR-Represents` at all.
--   ⇒ depth 0 and depth k are the SAME emitter with `k` extensions; they
--     are not two cases.
--
-- ⚠⚠ AND THE TWO PEELS RUN AT DIFFERENT DEPTHS, exactly as
--   `Knot/SzAgree`'s header warns: the IH TUPLE has a slot per RECURSIVE
--   field, the PAYLOAD has one per FIELD.  Here they happen to coincide
--   (fields 0,1 are both `rec`), which is why a row with a `NAT` or a
--   cross-sort field first is the one that will catch a wrong count.
------------------------------------------------------------------------

row-app : {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} →
          RepresentsR ρ r → (f a : RTm Γ) →
          ({Θ' : Cx} {r' : RTm Θ'} → RepresentsR ρ r' →
             renTmAtK sTm (num (len Γ)) (num (len Δ)) r' (enTm f)
             ⟶* enTm (renTm ρ f)) →
          ({Θ' : Cx} {r' : RTm Θ'} → RepresentsR ρ r' →
             renTmAtK sTm (num (len Γ)) (num (len Δ)) r' (enTm a)
             ⟶* enTm (renTm ρ a)) →
          renTmAtK sTm (num (len Γ)) (num (len Δ)) r (enTm {Γ} {Θ} (app f a))
          ⟶* enTm {Δ} {Θ} (renTm ρ (app f a))
row-app {Γ} {Δ} h f a ihf iha =
  ren-head-red 13 ttsd
    (sc-ρ (s-rides (n-suc n-zero) is-snd done)
    (sc-ρ (s-rides (n-suc n-zero) is-snd done)
    (sc-κ (sk-fst (n-suc n-zero) done) sc-ι))) 13 refl
    sTm (num (len Γ)) (num (len Δ)) _
    (pair (enTm f) (pair (enTm a) (pair (idrefl ⌜Nat⌝ sTm) unit))) »
  -- slot 0 — first recursive field, IH tuple entry 0, payload entry 0
  ⟶*-icon (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     ihf h)) »
  -- slot 1 — second recursive field: ONE peel further in BOTH tuples
  ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-appˡ (⟶*-appˡ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done)) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ (⟶*-fst (⟶*-snd done » step (βsnd _ _) done) » step (βfst _ _) done))) »
     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (step (βsnd _ _) done)))) »
     iha h))) »
  -- slot 2 — the ford
  ⟶*-icon (⟶*-pairʳ (⟶*-pairʳ (⟶*-pairˡ
    (⟶*-fst (⟶*-snd (⟶*-snd done » step (βsnd _ _) done) » step (βsnd _ _) done) » step (βfst _ _) done))))

------------------------------------------------------------------------
-- ⚠⚠⚠ A CONTROL THE ROWS THEMSELVES CANNOT PROVIDE — AND THE REASON IS
-- CATEGORY D′.
--
-- `ren-head-red` takes the row's `SubCon` as an argument, and at the
-- RENAMING instantiation that argument is **NOT PINNED BY THE ROW**:
--
--     renFordMap fi b p = p          -- ignores the tag `b`
--     fordMapK   fi b p = jsub (⌜Id⌝ ⌜Nat⌝ (sortMap (var vz)) (w b))
--                              (symN fi p) (idrefl ⌜Nat⌝ b)
--
--   `kaPick` feeds the tag to `fordMap`, so the renaming instance
--   DISCARDS it and the substitution instance USES it three times.
--
-- ★★★ MEASURED, NOT SUSPECTED: replacing `cTm-nzero`'s ford witness with
--   `n-zero` — the WRONG sort — left the row GREEN.  A generator emitting
--   a wrong tag would therefore produce a clean `ren-agree` and break only
--   at `sub-agree`, one instantiation later.  That is exactly the shape
--   `FUTURE.md` D′ records, and exactly how `wkK` survived.
--
-- ⇒ SO THE TAGS ARE PINNED HERE INSTEAD, against the DECIDER — which is
--   what actually builds the mask that `renDescK`/`subDescK` use.  This
--   `refl` fails if an emitted `SubCon` is not the computed one, at either
--   instantiation, for every row that carries it.
------------------------------------------------------------------------

subcon-nzero : decSubCon vz (ilookupD KnotD 30)
               ≡ just (sc-κ (sk-fst (n-suc n-zero) done) sc-ι)
subcon-nzero = refl
