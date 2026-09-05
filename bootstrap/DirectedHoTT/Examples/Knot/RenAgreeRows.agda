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
  using ( Cx; ε; _∙; RTm; Var; vz; vs; Ren; app; pair; icon; renTm; extR; nzero; idrefl; ⌜Nat⌝; unit; lam; snd )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; βfst; βsnd )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ; ⟶*-ielimⁱ; ⟶*-fst; ⟶*-nsuc )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enVar )
open import DirectedHoTT.Examples.Knot.Sorts using ( num; len; sTm )
open import DirectedHoTT.Examples.Knot.RenTm using ( renTmAtK )
open import DirectedHoTT.Examples.Knot.RenRed using ( ren-head-red )
open import DirectedHoTT.Examples.Knot.SubAgree using ( RepresentsR; extR-Represents )
open import DirectedHoTT.Lib.ISub using ( ttsd )
open import DirectedHoTT.Lib.IWk using ( IsSucs; is-snd; is-suc )
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
  ren-head-red 30 ttsd (sc-κ (sk-fst (n-suc (n-suc n-zero)) done) sc-ι) 30 refl
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
    (sc-ρ (s-rides (n-suc (n-suc n-zero)) (is-suc is-snd) done)
          (sc-κ (sk-fst (n-suc (n-suc n-zero)) done) sc-ι)) 12 refl
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
