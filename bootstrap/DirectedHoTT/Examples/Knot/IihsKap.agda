------------------------------------------------------------------------
-- OCP-0009 · KNOT — `iihsK` PART 3: the `iκ` ROW, alone in its module.
--
--     iihs D ms σ (iκ κ C) p = iihs D ms (iext σ (fst p)) C (snd p)
--
-- ★★★ `cICon-kap` AND `cICon-rho` ARE THE **SAME** DESCRIPTION — both
--   are `iρ (pair sTm …) (iρ (pair sICon …) (iκ … iι))`.  The encoded
--   `ICon` has a Tm-sorted field and an ICon tail in BOTH constructors,
--   so this row's IH pick, its app spine and its casts are `iihsRho`'s
--   SECOND COMPONENT verbatim — `⊢iihsIH` and `⊢iihsAppK` are imported,
--   not restated.
--   ⇒ the ONLY difference from `iihsRho` is the missing `Tm-pairK
--     (Tm-ielimK …)` head: `iκ` skips the field instead of recursing
--     into it.
--
-- ⚠ ALONE IN ITS OWN MODULE, and the split is `Knot/IhsKap`'s
--   precedent, not an invention: on the NON-indexed side `dι`+`dρ`
--   together checked at 4.9 GB and adding `dκ` was KILLED at 2:23.
--
-- ⚠ NEEDS THE COMPACTING COLLECTOR.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IihsKap where

open import DirectedHoTT.Lib.Lkp using ( ∋lkp; vsⁿ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; var; vz; vs; pair; fst; snd; app; lam; Π; Nat
        ; εwkTy; IMu; ICon; IDesc; ε; isingle; iext; iρ; iκ; iι; ⌜Id⌝; ⌜Nat⌝
        ; nsuc; Σ'; renTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢ty_; _⊢_∷_; ⊢var; here; there; ⊢snd; ⊢fst; ⊢nsuc
        ; ty-Π; ty-Σ; ty-IMu; ty-Nat; ⊢lam; ⊢app; imethTy; IConWf )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; sICon; ⊢sICon; sIDesc; ⊢sIDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cICon-kap )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cICon-kapWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagICon-kap )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy; ty-SubTy )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-fstKv; ⊢Tm-sndKv )
open import DirectedHoTT.Examples.Knot.IExt using ( iextK; ⊢iextK )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Examples.Knot.IihsMot using ( iihsMotK; ⊢iihsMotK )
open import DirectedHoTT.Examples.Knot.IihsRho using ( ⊢iihsAppK; ⊢iihsIH )

iihsKap : {Γ : Cx} → RTm Γ
iihsKap = lam (lam (lam (lam (lam (lam (lam
  (app (app (app (app (fst (snd (var (vs (vs (vs (vs vz)))))))
                      (var (vs (vs (vs vz)))))
                 (iextK (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                        (var (vs (vs (vs vz))))
                        (var (vs (vs vz)))
                        (Tm-fstK (var vz))))
            (var (vs vz)))
       (Tm-sndK (var vz)))))))))

⊢iihsKap : {Γ : Ctx} →
           Γ ⊢ iihsKap ∷ imethTy KnotD IPair tagICon-kap cICon-kap iihsMotK
⊢iihsKap =
  ⊢methLam KnotD IPair tagICon-kap cICon-kap KnotWf cICon-kapWf ⊢IPair ⊢iihsMotK
    (⊢lam ty-Nat
      (⊢lam (ty-SubTy (⊢snd (⊢var (∋lkp _ (vsⁿ 3 vz)))) (⊢var here))
        (⊢lam (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var (there here))))
                    (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (∋lkp _ (vsⁿ 2 vz))))))
          (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (∋lkp _ (vsⁿ 2 vz)))))
            -- ⚠ `dd`/`u` PINNED: they occur only under `iinst`, which is
            --   DEFINED and not injective.  ⚠ `i`/`q` are `⊢iihsIH`'s
            --   EXPLICIT arguments for the same reason, one layer down.
            (⊢iihsAppK {dd = nsuc (snd (var (vs (vs (vs (vs (vs (vs vz))))))))}
                       {u = fst (snd (var (vs (vs (vs (vs (vs vz)))))))}
                       (⊢iihsIH (var (vs (vs (vs (vs (vs (vs vz)))))))
                                (var (vs (vs (vs (vs (vs vz))))))
                                (⊢var (∋lkp _ (vsⁿ 4 vz))))
                       dn (⊢nsuc dIdx)
                       (⊢iextK dIdx dn dσ
                               (⊢Tm-fstKv (var (vs (vs (vs vz)))) dn (⊢var here)))
                       dalg
                       (⊢Tm-sndKv (var (vs (vs (vs vz)))) dn (⊢var here)))))))
  where
    dn   = ⊢var (∋lkp _ (vsⁿ 3 vz))
    dσ   = ⊢var (∋lkp _ (vsⁿ 2 vz))
    dalg = ⊢var (there here)
    dIdx = ⊢snd (⊢var (∋lkp _ (vsⁿ 6 vz)))
