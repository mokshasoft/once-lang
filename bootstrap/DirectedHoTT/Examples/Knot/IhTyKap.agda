------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `ihTy`'s `dκ` ROW, ALONE IN A MODULE.
-- ★★★ AND IT IS PURE IH: `ihTy D (dκ A C) q M = ihTy D C (snd q) M`.
--   No `Σ'`, no weakening, no substitution — the `κ` field is SKIPPED,
--   because a non-recursive field carries no induction hypothesis.  ⇒ the
--   method is `⊢ihAppK` applied to the second field's IH and nothing
--   else, which is the smallest real row in the whole knot.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhTyKap where
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
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
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
open import DirectedHoTT.Examples.Knot.Single using ( singleK; ⊢singleK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTyAtK; ⊢subTyAtK )

open import DirectedHoTT.Examples.Knot.IhTyMot
  using ( ihTyMotK; ⊢ihTyMotK; ⊢ihAppK; ⊢ihRowρ )

ihTyKap : {Γ : Cx} → RTm Γ
ihTyKap =
  lam (lam (lam (lam (lam
    (app (app (fst (snd (var (vs (vs vz))))) (Tm-sndK (var (vs vz))))
         (var vz))))))

⊢ihTyKap : {Γ : Ctx} →
           Γ ⊢ ihTyKap ∷ imethTy KnotD IPair tagDCon-kap cDCon-kap ihTyMotK
⊢ihTyKap =
  ⊢methLam KnotD IPair tagDCon-kap cDCon-kap KnotWf cDCon-kapWf
           ⊢IPair ⊢ihTyMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢var (there (there here))))))
      (⊢lam (ty-IMu KnotWf
               (⊢ixP ⊢sTy (⊢nsuc (⊢snd (⊢var (there (there (there here))))))))
        (⊢ihAppK {dd = snd (var (vs (vs (vs (vs vz)))))}
                 {u = fst (snd (var (vs (vs (vs vz))))) }
                 dIH (⊢Tm-sndKv _ dn dq) dM)))
  where
    dn = ⊢snd (⊢var (there (there (there (there here)))))
    dq = ⊢var (there here)
    dM = ⊢var here
    dIH = ⊢ihHere
            {D = KnotD} {I = IPair}
            {σ = iext (isingle (var (vs (vs (vs (vs vz)))))) 
                      (fst (var (vs (vs (vs vz)))))}
            {j = pair sDCon (snd (var (vs vz)))}
            (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDCon) iι)
            {q = snd (var (vs (vs (vs vz))))} {M = ihTyMotK}
            (⊢ihSkipρ
               {D = KnotD} {I = IPair}
               {σ = isingle (var (vs (vs (vs (vs vz)))))}
               {j = pair sTy nzero}
               (iρ (pair sDCon (snd (var (vs vz))))
                 (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDCon) iι))
               {q = var (vs (vs (vs vz)))} {M = ihTyMotK}
               (⊢var (there (there here))))
