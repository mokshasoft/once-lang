------------------------------------------------------------------------
-- OCP-0009 · KNOT — `ihsK` PART 3: the `dκ` row, ALONE IN ITS OWN MODULE.
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
module DirectedHoTT.Examples.Knot.IhsKap where

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
-- ★ ROW `dκ` — `ihs D ms (dκ A C) p = ihs D ms C (snd p)`.
--
-- ⚠ `cDCon-kap` has TWO `iρ` fields: the `Ty` (which `ihs` SKIPS) and
--   the tail `DCon`.  So the IH is `fst (snd ihs)`, reached by
--   `⊢ihSkipρ` past the `Ty` then `⊢ihHere` — `⊢lookupCons`'s shape.
--   ⚠ AFTER A SKIP THE PAYLOAD STEPS TOO: `iihTy` recurses at `snd q`,
--     so σ and q move together, one field at a time.
------------------------------------------------------------------------

ihsKap : {Γ : Cx} → RTm Γ
ihsKap = lam (lam (lam (lam (lam (lam (lam
  (app (app (app (app (fst (snd (var (vs (vs (vs (vs vz)))))))
                      (var (vs (vs (vs vz)))))
                 (var (vs (vs vz))))
            (var (vs vz)))
       (Tm-sndK (var vz))))))))) 

⊢ihsKap : {Γ : Ctx} →
          Γ ⊢ ihsKap ∷ imethTy KnotD IPair tagDCon-kap cDCon-kap ihsMotK
⊢ihsKap =
  ⊢methLam KnotD IPair tagDCon-kap cDCon-kap KnotWf cDCon-kapWf ⊢IPair ⊢ihsMotK
    (⊢lam ty-Nat
      (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢var here)))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))
          (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there here)))))
            (⊢app (⊢app (⊢app (⊢app
                     (⊢ihHere {D = KnotD} {I = IPair}
                       {σ = iext (isingle (var (vs (vs (vs (vs (vs (vs vz))))))))
                                 (fst (var (vs (vs (vs (vs (vs vz)))))))}
                       {j = pair sDCon (snd (var (vs vz)))}
                       (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDCon) iι)
                       {q = snd (var (vs (vs (vs (vs (vs vz))))))} {M = ihsMotK}
                       (⊢ihSkipρ {D = KnotD} {I = IPair}
                         {σ = isingle (var (vs (vs (vs (vs (vs (vs vz)))))))}
                         {j = pair sTy nzero}
                         (iρ (pair sDCon (snd (var (vs vz))))
                          (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDCon) iι))
                         {q = var (vs (vs (vs (vs (vs vz)))))} {M = ihsMotK}
                         (⊢var (there (there (there (there here)))))))
                     (⊢var (there (there (there here)))))
                     (⊢var (there (there here))))
                     (⊢var (there here)))
                  (⊢Tm-sndKv (var (vs (vs (vs vz)))) (⊢var (there (there (there here)))) (⊢var here)))))))

