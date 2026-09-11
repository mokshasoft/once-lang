------------------------------------------------------------------------
-- OCP-0009 · KNOT — `ihsK` PART 2: the `dρ` row, ALONE IN ITS OWN MODULE.
--
-- ⚠⚠ SPLIT FOR SIZE, AND THE SPLIT IS MEASURED.  With `dι`+`dρ` together
--   this checked in 2:15 at 4.9 GB; adding `dκ` pushed it past the
--   5.5 GB cgroup cap and it was KILLED at 2:23.  `Knot/IhTyRho` and
--   `Knot/IhTyKap` are separate modules for exactly this reason — the
--   precedent, not an invention.
--
-- ⚠ NEEDS THE COMPACTING COLLECTOR (`sweep.sh`'s `needs_c` greps the
--   first 40 lines for "COMPACTING COLLECTOR").
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhsRho where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; var; vz; vs; pair; snd; Π; Nat; εwkTy; IMu )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢ty_; _⊢_∷_; ⊢var; here; there; ⊢snd; ty-Π; ty-IMu
        ; ⊢lam; imethTy; ty-Nat )
open import DirectedHoTT.Spec.Syntax using ( lam )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Examples.Knot.Desc using ( cDCon-i; cDCon-rho; cDCon-kap )
open import DirectedHoTT.Examples.Knot.Wf using ( cDCon-iWf; cDCon-rhoWf; cDCon-kapWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDCon-i; tagDCon-rho; tagDCon-kap )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-unitK; Tm-pairK; Tm-elimK; Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-unitKv; ⊢Tm-pairKv; ⊢Tm-elimKv; ⊢Tm-fstKv; ⊢Tm-sndKv )
open import DirectedHoTT.Spec.Syntax using ( app; fst; isingle; iext; iρ; iκ; iι; ⌜Id⌝; ⌜Nat⌝; nzero )
open import DirectedHoTT.Spec.Typing using ( ⊢app )
open import DirectedHoTT.Lib.IPay using ( ⊢ihHere; ⊢ihSkipρ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; sDesc; ⊢sDesc; sDCon; ⊢sDCon; sTy; ⊢sTy; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )

-- ★★★ THE DEPTH RIDES AS A PASSENGER — `Knot/IPayTyMot`'s idiom.
--
-- ⚠ MY FIRST VERSION READ THE AMBIENT INDEX FOUR TIMES, once per `Π`
--   level, at `vs¹`…`vs⁴`.  That does NOT survive `⊢methLam`'s
--   `renTy (extR (extR vs))`: `extR² vs` fixes only the top TWO
open import DirectedHoTT.Examples.Knot.IhsMot using ( ihsMotK; ⊢ihsMotK )

-- ★ the hoisted body, LOCAL rather than imported — see the measurement
--   note in the header.
⊢ihsStep : {Γ : Ctx} {n D ms p f : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ Nat →
           Γ ⊢ D ∷ K (pair sDesc n) → Γ ⊢ ms ∷ K (pair sTm n) →
           Γ ⊢ p ∷ K (pair sTm n) → Γ ⊢ f ∷ K (pair sTm n) →
           Γ ⊢ Tm-pairK (Tm-elimK D ms (Tm-fstK p)) f ∷ K (pair sTm n)
⊢ihsStep {n = n} dn dD dms dp df =
  ⊢Tm-pairKv n dn (⊢Tm-elimKv n dn dD dms (⊢Tm-fstKv n dn dp)) df

------------------------------------------------------------------------
-- ★ ROW `dρ` — `ihs D ms (dρ C) p = pair (elim D ms (fst p)) (ihs D ms C (snd p))`.
------------------------------------------------------------------------

ihsRho : {Γ : Cx} → RTm Γ
ihsRho = lam (lam (lam (lam (lam (lam (lam
  (Tm-pairK (Tm-elimK (var (vs (vs vz))) (var (vs vz)) (Tm-fstK (var vz)))
            (app (app (app (app (fst (var (vs (vs (vs (vs vz))))))
                                (var (vs (vs (vs vz)))))
                           (var (vs (vs vz))))
                      (var (vs vz)))
                 (Tm-sndK (var vz))))))))))

⊢ihsRho : {Γ : Ctx} →
          Γ ⊢ ihsRho ∷ imethTy KnotD IPair tagDCon-rho cDCon-rho ihsMotK
⊢ihsRho =
  ⊢methLam KnotD IPair tagDCon-rho cDCon-rho KnotWf cDCon-rhoWf ⊢IPair ⊢ihsMotK
    (⊢lam ty-Nat
      (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢var here)))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))
          (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there here)))))
            (⊢ihsStep (⊢var (there (there (there here))))
                      (⊢var (there (there here))) (⊢var (there here)) (⊢var here)
               (⊢app (⊢app (⊢app (⊢app
                        (⊢ihHere {D = KnotD} {I = IPair}
                          {σ = isingle (var (vs (vs (vs (vs (vs (vs vz)))))))}
                          {j = pair sDCon (snd (var vz))}
                          (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs vz))) sDCon) iι)
                          {q = var (vs (vs (vs (vs (vs vz)))))} {M = ihsMotK}
                          (⊢var (there (there (there (there here))))))
                        (⊢var (there (there (there here)))))
                        (⊢var (there (there here))))
                        (⊢var (there here)))
                     (⊢Tm-sndKv (var (vs (vs (vs vz)))) (⊢var (there (there (there here)))) (⊢var here)))))))) 

------------------------------------------------------------------------
