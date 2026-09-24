------------------------------------------------------------------------
-- OCP-0009 · KNOT — `iihsK` PART 2: the `iρ` ROW, at FOUR passengers.
--
--   iihs D ms σ (iρ j C) p =
--     pair (ielim D (subTm σ j) ms (fst p))
--          (iihs D ms (iext σ (fst p)) C (snd p))
--
-- ★ THE TYPES LINE UP, and that is the check that the motive is right:
--   σ : SubTy (snd ⟨i⟩) n, `iextK` returns SubTy (nsuc (snd ⟨i⟩)) n, and
--   `cICon-rho`'s tail field sits at `pair sICon (nsuc (snd ⟨i⟩))`.
--
-- ⚠ SEVEN LAMS — three from `⊢methLam` (index, payload, IH) plus the
--   motive's FOUR passengers.  From the body: p `vz`, alg `vs¹`,
--   σ `vs²`, n `vs³`, ihs `vs⁴`, payload `vs⁵`, index `vs⁶`.
--   ⚠ `j` is `fst <payload>` — a projection of the ICON's fields — while
--     `fst p` is `Tm-fstK <p>`, the RTm CONSTRUCTOR on the runtime
--     payload.  Two different `fst`s, one line apart.
--
-- ⚠ NEEDS THE COMPACTING COLLECTOR.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IihsRho where

open import DirectedHoTT.Lib.Lkp using ( ∋lkp; vsⁿ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; var; vz; vs; pair; fst; snd; app; lam; Π; Nat
        ; εwkTy; IMu; ICon; IDesc; ε; isingle; iext; iρ; iκ; iι; ⌜Id⌝; ⌜Nat⌝; nsuc; Σ'; renTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢ty_; _⊢_∷_; ⊢var; here; there; ⊢snd; ⊢fst; ⊢nsuc
        ; ty-Π; ty-Σ; ty-IMu; ty-Nat; ⊢lam; ⊢app; imethTy; IConWf )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; sICon; ⊢sICon; sIDesc; ⊢sIDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cICon-rho )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cICon-rhoWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagICon-rho )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy; ty-SubTy; subBwd )
open import DirectedHoTT.Spec.Typing using ( βsnd )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-pairK; Tm-ielimK; Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.CtorsV
  using ( ⊢Tm-pairKv; ⊢Tm-ielimKv; ⊢Tm-fstKv; ⊢Tm-sndKv )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK; ⊢subTmAtK )
open import DirectedHoTT.Examples.Knot.IExt using ( iextK; ⊢iextK )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import DirectedHoTT.Spec.Typing using ( iinst; wk-single; iihTy )
open import DirectedHoTT.Spec.Syntax using ( subTm )
open import DirectedHoTT.Lib.Wk using ( towerA; towerJ; sub-w²-single; sub-w-single )
open import normalizer.Syntax.Types using ( cong; cong₂; sym )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ )
open import DirectedHoTT.Examples.Knot.IihsMot using ( iihsMotK; ⊢iihsMotK )

iihsRho : {Γ : Cx} → RTm Γ
iihsRho = lam (lam (lam (lam (lam (lam (lam
  (Tm-pairK
     (Tm-ielimK (fst (var (vs vz)))
                (subTmAtK (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                          (var (vs (vs (vs vz))))
                          (var (vs (vs vz)))
                          (fst (var (vs (vs (vs (vs (vs vz))))))))
                (snd (var (vs vz)))
                (Tm-fstK (var vz)))
     (app (app (app (app (fst (snd (var (vs (vs (vs (vs vz)))))))
                         (var (vs (vs (vs vz)))))
                    (iextK (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                           (var (vs (vs (vs vz))))
                           (var (vs (vs vz)))
                           (Tm-fstK (var vz))))
               (var (vs vz)))
          (Tm-sndK (var vz))))))))))

------------------------------------------------------------------------
-- ★ THE FIRST COMPONENT, HOISTED — `ihsK` measured that this is what
--   makes a row of this size fit, and that the Def must stay in the
--   SAME module (imported from a sibling it did not help).
------------------------------------------------------------------------

⊢iihsStep : {Γ : Ctx} {n dd σ D j ms p f : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ dd ∷ Nat → Γ ⊢ σ ∷ SubTy dd n →
            Γ ⊢ D ∷ K (pair sIDesc n) → Γ ⊢ j ∷ K (pair sTm dd) →
            Γ ⊢ ms ∷ K (pair sTm n) → Γ ⊢ p ∷ K (pair sTm n) →
            Γ ⊢ f ∷ K (pair sTm n) →
            Γ ⊢ Tm-pairK (Tm-ielimK D (subTmAtK dd n σ j) ms (Tm-fstK p)) f
                ∷ K (pair sTm n)
⊢iihsStep {n = n} dn ddd dσ dD dj dms dp df =
  ⊢Tm-pairKv n dn
    (⊢Tm-ielimKv n dn dD (⊢subTmAtK ddd dn dσ dj) dms (⊢Tm-fstKv n dn dp)) df


------------------------------------------------------------------------
-- ★ THE FIVE-APP SPINE, HOISTED — `Knot/Ihs.⊢ihsAppK` one passenger up,
--   and `⊢ipayAppK`'s cast structure exactly.
--
-- ★ ONE CAST PER SLOT, and each is the rung count:
--     n    none            σ'   `towerA` + `subBwd` (it reads ⟨i⟩)
--     D    `wk-single`     ms   `sub-w²-single`
--     p    `sub-w³-single` result `towerJ⁵`
--   ⚠ `σ'` is the only slot whose domain reads the AMBIENT INDEX, which
--     is why it alone needs `towerA`; `ihsK`'s passengers all read a
--     motive-local binder and needed none.
------------------------------------------------------------------------

⊢iihsAppK : {Γ : Ctx} {dd u h n σ' alg p : RTm ⌊ Γ ⌋} →
            Γ ⊢ h ∷ iinst (pair sICon dd) u iihsMotK →
            Γ ⊢ n ∷ Nat → Γ ⊢ dd ∷ Nat → Γ ⊢ σ' ∷ SubTy dd n →
            Γ ⊢ alg ∷ Σ' (K (pair sIDesc n)) (K (pair sTm (renTm vs n))) →
            Γ ⊢ p ∷ K (pair sTm n) →
            Γ ⊢ app (app (app (app h n) σ') alg) p ∷ K (pair sTm n)
⊢iihsAppK {dd = dd} {u = u} {n = n} {σ' = σ'} {alg = alg} {p = p}
          dh dn ddd dσ dalg dp =
  ⊢-cast (cong (λ z → K (pair sTm z)) (towerJ p alg σ' n))
    (⊢app (⊢app (⊢app (⊢app dh dn)
             (⊢-cast (cong (λ z → SubTy (snd z) n)
                           (sym (towerA n u (pair sICon dd))))
                     (subBwd (βsnd sICon dd) dσ)))
             -- ⚠ the two `Σ'` components need DIFFERENT equalities: the
             --   first is `wk-single`, the second `sub-w-single` (= `peel¹`),
             --   because the codomain sits under the `Σ'`'s own binder.
             (⊢-cast (cong₂ (λ x y → Σ' (K (pair sIDesc x)) (K (pair sTm y)))
                            (sym (wk-single {v = σ'} n))
                            (sym (sub-w-single {v = σ'} n))) dalg))
          (⊢-cast (cong (λ z → K (pair sTm z))
                        (sym (sub-w²-single {a = alg} {b = σ'} n))) dp))

------------------------------------------------------------------------
-- ★ THE IH PICK, HOISTED.  `cICon-rho` has TWO `iρ` fields — the index
--   `Tm` and the tail `ICon` — so the IH is `fst (snd h)`: one
--   `⊢ihSkipρ` past the index, then `⊢ihHere`.
--
-- ⚠ THIS IS WHERE THE COST WAS.  With the row's other two components
--   already hoisted, removing `⊢iihsRho` dropped the module from 4:13
--   (killed) to 4.3s — so the row was the whole cost, and what remained
--   in it was this pick, whose pins force `iihTy … iihsMotK` to
--   normalise at a 5-`Π` motive.
------------------------------------------------------------------------

-- ★★★ `i` AND `q` ARE **EXPLICIT** — 2026-09-17.
--
-- ⚠ They occur ONLY inside `iihTy KnotD IPair (isingle i) cICon-rho q
--   iihsMotK`, and `iihTy` is a DEFINED RECURSIVE FUNCTION.  Agda cannot
--   invert a defined function against a meta, so left implicit they are
--   simply unsolvable — the module reported
--   `UnsolvedMetaVariables` at this call for the whole session.
--
-- ★ `Lib/IPay`'s own note already said so for the ICon: *"`iihTy` is a
--   FUNCTION, so unifying its application against a concrete IH type
--   cannot invert it … Pin the `ICon` and it unfolds."*  The same is true
--   of `i` and `q`; pinning ONE of the three was not enough.
--   ⇒ `pin-implicits-on-defined-set-types`, third instance.
⊢iihsIH : {Γ : Ctx} (i q : RTm ⌊ Γ ⌋) {h : RTm ⌊ Γ ⌋} →
          Γ ⊢ h ∷ iihTy KnotD IPair (isingle i) cICon-rho q iihsMotK →
          Γ ⊢ fst (snd h)
              ∷ iinst (subTm (iext (isingle i) (fst q))
                             (pair sICon (nsuc (snd (var (vs vz))))))
                      (fst (snd q)) iihsMotK
⊢iihsIH i q dh =
  ⊢ihHere {D = KnotD} {I = IPair}
    {σ = iext (isingle i) (fst q)}
    {j = pair sICon (nsuc (snd (var (vs vz))))}
    (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sICon) iι)
    {q = snd q} {M = iihsMotK}
    (⊢ihSkipρ {D = KnotD} {I = IPair} {σ = isingle i}
      {j = pair sTm (snd (var vz))}
      (iρ (pair sICon (nsuc (snd (var (vs vz)))))
       (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sICon) iι))
      {q = q} {M = iihsMotK} dh)

⊢iihsRho : {Γ : Ctx} →
           Γ ⊢ iihsRho ∷ imethTy KnotD IPair tagICon-rho cICon-rho iihsMotK
⊢iihsRho =
  ⊢methLam KnotD IPair tagICon-rho cICon-rho KnotWf cICon-rhoWf ⊢IPair ⊢iihsMotK
    (⊢lam ty-Nat
      (⊢lam (ty-SubTy (⊢snd (⊢var (∋lkp _ (vsⁿ 3 vz)))) (⊢var here))
        (⊢lam (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var (there here))))
                    (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (∋lkp _ (vsⁿ 2 vz))))))
          (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (∋lkp _ (vsⁿ 2 vz)))))
            (⊢iihsStep dn dIdx dσ (⊢fst dalg)
               (⊢fst (⊢var (∋lkp _ (vsⁿ 5 vz))))
               dms (⊢var here)
               -- ⚠ `dd`/`u` PINNED: they occur only under `iinst`, which
               --   is DEFINED and not injective.
               (⊢iihsAppK {dd = nsuc (snd (var (vs (vs (vs (vs (vs (vs vz))))))))}
                          {u = fst (snd (var (vs (vs (vs (vs (vs vz)))))))}
                          -- ★★★ PINNED, and they must be.  ⚠ AN EARLIER
                          --   NOTE HERE READ "NOT PINNED … pinning made
                          --   it WORSE (a KILL at 2:56)".  That was
                          --   `exit-143-is-not-evidence-about-cost`: a
                          --   kill is a MEMORY event and says nothing
                          --   about solvability.  `i`/`q` occur only
                          --   inside `iihTy`, a DEFINED function, so
                          --   unpinned they are simply unsolvable.
                          (⊢iihsIH (var (vs (vs (vs (vs (vs (vs vz)))))))
                                   (var (vs (vs (vs (vs (vs vz))))))
                                   (⊢var (∋lkp _ (vsⁿ 4 vz))))
                          dn (⊢nsuc dIdx)
                          (⊢iextK dIdx dn dσ
                                  (⊢Tm-fstKv (var (vs (vs (vs vz)))) dn (⊢var here)))
                          dalg
                          (⊢Tm-sndKv (var (vs (vs (vs vz)))) dn (⊢var here))))))))
  where
    dn   = ⊢var (∋lkp _ (vsⁿ 3 vz))
    dσ   = ⊢var (∋lkp _ (vsⁿ 2 vz))
    dalg = ⊢var (there here)
    dIdx = ⊢snd (⊢var (∋lkp _ (vsⁿ 6 vz)))
    -- ⚠ `⊢snd` instantiates the `Σ'`'s codomain at `fst alg`; the
    --   codomain is CONSTANT, so `wk-single` cancels the round trip.
    dms  = ⊢-cast (cong (λ z → K (pair sTm z))
                        (wk-single {v = fst (var (vs vz))} (var (vs (vs (vs vz))))))
                  (⊢snd dalg)
