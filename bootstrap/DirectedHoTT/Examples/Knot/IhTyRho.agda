------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `ihTy`'s `dρ` ROW, ALONE IN A MODULE.
--   `Knot/IPayTyRho`'s header measures why: a concrete row with a real
--   body runs to ~4 GB, so two of them do not fit one process.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhTyRho where
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

open import DirectedHoTT.Examples.Knot.IhTyMot
  using ( ihTyMotK; ⊢ihTyMotK; ⊢ihAppK; ⊢ihRowρ )

ihTyRho : {Γ : Cx} → RTm Γ
ihTyRho =
  lam (lam (lam (lam (lam
    (Ty-SgK (subTyAtK (nsuc (snd (var (vs (vs (vs (vs vz)))))))
                      (snd (var (vs (vs (vs (vs vz))))))
                      (singleK (snd (var (vs (vs (vs (vs vz))))))
                               (Tm-fstK (var (vs vz))))
                      (var vz))
            (wkK (pair sTy (snd (var (vs (vs (vs (vs vz))))))) 
                 (app (app (fst (var (vs (vs vz)))) (Tm-sndK (var (vs vz))))
                      (var vz))))))))

⊢ihTyRho : {Γ : Ctx} →
           Γ ⊢ ihTyRho ∷ imethTy KnotD IPair tagDCon-rho cDCon-rho ihTyMotK
⊢ihTyRho =
  ⊢methLam KnotD IPair tagDCon-rho cDCon-rho KnotWf cDCon-rhoWf
           ⊢IPair ⊢ihTyMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢var (there (there here))))))
      (⊢lam (ty-IMu KnotWf
               (⊢ixP ⊢sTy (⊢nsuc (⊢snd (⊢var (there (there (there here))))))))
        (⊢ihRowρ dn dq dM
          (⊢wkKat ⊢sTy dn
            (⊢ihAppK {dd = snd (var (vs (vs (vs (vs vz))))) }
                     {u = fst (var (vs (vs (vs vz)))) }
                     dIH (⊢Tm-sndKv _ dn dq) dM)))))
  where
    dn = ⊢snd (⊢var (there (there (there (there here)))))
    dq = ⊢var (there here)
    dM = ⊢var here
    dIH = ⊢ihHere
            {D = KnotD} {I = IPair}
            {σ = isingle (var (vs (vs (vs (vs vz)))))}
            {j = pair sDCon (snd (var vz))}
            (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs vz))) sDCon) iι)
            {q = var (vs (vs (vs vz)))} {M = ihTyMotK}
            (⊢var (there (there here)))
