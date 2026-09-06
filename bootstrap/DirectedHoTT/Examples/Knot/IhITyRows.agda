------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `iihTy`'s TWO REAL ROWS.
--
--     iρ j C  ↦  Σ' (iinst (subTm σ j) (fst q) M) (renTy vs <IH>)
--     iκ κ C  ↦  <IH>                                    ★ NO `Σ'`
--
-- ⚠ `cICon-rho` AND `cICon-kap` HAVE THE **SAME** SHAPE — both are
--   `iρ (sTm) (iρ (sICon) (iκ ford iι))` — so both select their IH the
--   same way: `⊢ihSkipρ` past the INDEX field (an `sTm`, cross-sort and
--   useless as an IH), then `⊢ihHere` on the sub-`ICon`.  What differs is
--   only the answer, and `iκ` contributes NOTHING to the IH tuple's type,
--   which is why its row is the bare recursive call.
--
-- ⚠⚠ `fst q` IS THE **OBJECT-LEVEL** `fst` (`Tm-fstK`), not the kernel's.
--   `q` is an encoded TERM — the payload of the constructor being
--   eliminated one layer OUT — where the method's own payload is a kernel
--   tuple read with the kernel's `fst`.  Both appear in this file, three
--   lines apart.  `Knot/IhTyMot` flags the same trap.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhITyRows where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IDesc; εwkTy; IMu; app; fst; iρ; iκ; iι
        ; ⌜Id⌝; ⌜Nat⌝; isingle; iext; unit; nsuc )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; ⊢var; here; there
        ; ⊢snd; ⊢fst; ⊢lam; ⊢nsuc; ty-Nat; ty-IMu; imethTy )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sTm; ⊢sTm; sICon; ⊢sICon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cICon-rho; cICon-kap )
open import DirectedHoTT.Examples.Knot.Wf
  using ( KnotWf; cICon-rhoWf; cICon-kapWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagICon-rho; tagICon-kap )
open import DirectedHoTT.Examples.Knot.Ctors
  using ( Ty-SgK; Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-fstKv; ⊢Tm-sndKv )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy; ty-SubTy )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK; ⊢wkTyK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK; ⊢subTmAtK )
open import DirectedHoTT.Examples.Knot.IExt
  using ( iextK; ⊢iextK; iinstK; ⊢iinstK )
open import DirectedHoTT.Examples.Knot.IhITyMot
  using ( iihTyMotK; ⊢iihTyMotK; ⊢iihAppK; ⊢iihRowρ )

-- ★ the IH APPLICATION, shared by both rows: `iihTy … (iext σ (fst q))
--   C (snd q) M`, at the SAME `n` (an `iext` conses, it does not raise).
-- ⚠ ITS CONTEXT IS THE ONE THE SEVEN `lam`s BUILD, spelled out.  At a
--   general `Γ` the de Bruijn indices below (up to `vs⁶ vz`) do not even
--   scope — which is why `Knot/IPayTyRho` inlines its copy instead of
--   naming it.  Naming it is worth the seven `∙`s: the two rows differ
--   ONLY in what they wrap around this.
ihApp : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
ihApp =
  app (app (app (app (fst (snd (var (vs (vs (vs (vs vz)))))))
                     (var (vs (vs (vs vz)))))
                (iextK (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                       (var (vs (vs (vs vz))))
                       (var (vs (vs vz)))
                       (Tm-fstK (var (vs vz)))))
           (Tm-sndK (var (vs vz))))
      (var vz)

------------------------------------------------------------------------
-- ★ `iρ` — the one row that builds anything.
------------------------------------------------------------------------

iihTyRho : {Γ : Cx} → RTm Γ
iihTyRho =
  lam (lam (lam (lam (lam (lam (lam
    (Ty-SgK (iinstK (var (vs (vs (vs vz))))
                    (subTmAtK (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                              (var (vs (vs (vs vz))))
                              (var (vs (vs vz)))
                              (fst (var (vs (vs (vs (vs (vs vz)))))))) 
                    (Tm-fstK (var (vs vz)))
                    (var vz))
            (wkTyK (var (vs (vs (vs vz)))) ihApp))))))))

⊢iihTyRho : {Γ : Ctx} →
            Γ ⊢ iihTyRho ∷ imethTy KnotD IPair tagICon-rho cICon-rho iihTyMotK
⊢iihTyRho =
  ⊢methLam KnotD IPair tagICon-rho cICon-rho KnotWf cICon-rhoWf
           ⊢IPair ⊢iihTyMotK
    (⊢lam ty-Nat
      (⊢lam (ty-SubTy (⊢snd (⊢var (there (there (there here))))) (⊢var here))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))
          (⊢lam (ty-IMu KnotWf
                   (⊢ixP ⊢sTy (⊢nsuc (⊢nsuc (⊢var (there (there here)))))))
            (⊢iihRowρ dn ddd dsb dj (⊢Tm-fstKv _ dn dq) dM
              (⊢iihAppK {dd = nsuc (snd (var (vs (vs (vs (vs (vs (vs vz)))))))) }
                        {u = fst (snd (var (vs (vs (vs (vs (vs vz))))))) }
                        dIH dn (⊢iextK ddd dn dsb (⊢Tm-fstKv _ dn dq))
                        (⊢Tm-sndKv _ dn dq) dM))))))
  where
    dn  = ⊢var (there (there (there here)))
    dsb = ⊢var (there (there here))
    dq  = ⊢var (there here)
    dM  = ⊢var here
    ddd = ⊢snd (⊢var (there (there (there (there (there (there here)))))))
    dj  = ⊢fst (⊢var (there (there (there (there (there here))))))
    dIH = ⊢ihHere
            {D = KnotD} {I = IPair}
            {σ = iext (isingle (var (vs (vs (vs (vs (vs (vs vz))))))))
                      (fst (var (vs (vs (vs (vs (vs vz)))))))}
            {j = pair sICon (nsuc (snd (var (vs vz))))}
            (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sICon) iι)
            {q = snd (var (vs (vs (vs (vs (vs vz))))))} {M = iihTyMotK}
            (⊢ihSkipρ
               {D = KnotD} {I = IPair}
               {σ = isingle (var (vs (vs (vs (vs (vs (vs vz)))))))}
               {j = pair sTm (snd (var vz))}
               (iρ (pair sICon (nsuc (snd (var (vs vz)))))
                 (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sICon) iι))
               {q = var (vs (vs (vs (vs (vs vz)))))} {M = iihTyMotK}
               (⊢var (there (there (there (there here))))))

------------------------------------------------------------------------
-- ★ `iκ` — the IH and nothing else.
------------------------------------------------------------------------

iihTyKap : {Γ : Cx} → RTm Γ
iihTyKap = lam (lam (lam (lam (lam (lam (lam ihApp))))))

⊢iihTyKap : {Γ : Ctx} →
            Γ ⊢ iihTyKap ∷ imethTy KnotD IPair tagICon-kap cICon-kap iihTyMotK
⊢iihTyKap =
  ⊢methLam KnotD IPair tagICon-kap cICon-kap KnotWf cICon-kapWf
           ⊢IPair ⊢iihTyMotK
    (⊢lam ty-Nat
      (⊢lam (ty-SubTy (⊢snd (⊢var (there (there (there here))))) (⊢var here))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))
          (⊢lam (ty-IMu KnotWf
                   (⊢ixP ⊢sTy (⊢nsuc (⊢nsuc (⊢var (there (there here)))))))
            (⊢iihAppK {dd = nsuc (snd (var (vs (vs (vs (vs (vs (vs vz)))))))) }
                      {u = fst (snd (var (vs (vs (vs (vs (vs vz))))))) }
                      dIH dn (⊢iextK ddd dn dsb (⊢Tm-fstKv _ dn dq))
                      (⊢Tm-sndKv _ dn dq) dM)))))
  where
    dn  = ⊢var (there (there (there here)))
    dsb = ⊢var (there (there here))
    dq  = ⊢var (there here)
    dM  = ⊢var here
    ddd = ⊢snd (⊢var (there (there (there (there (there (there here)))))))
    dIH = ⊢ihHere
            {D = KnotD} {I = IPair}
            {σ = iext (isingle (var (vs (vs (vs (vs (vs (vs vz))))))))
                      (fst (var (vs (vs (vs (vs (vs vz)))))))}
            {j = pair sICon (nsuc (snd (var (vs vz))))}
            (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sICon) iι)
            {q = snd (var (vs (vs (vs (vs (vs vz))))))} {M = iihTyMotK}
            (⊢ihSkipρ
               {D = KnotD} {I = IPair}
               {σ = isingle (var (vs (vs (vs (vs (vs (vs vz)))))))}
               {j = pair sTm (snd (var vz))}
               (iρ (pair sICon (nsuc (snd (var (vs vz)))))
                 (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sICon) iι))
               {q = var (vs (vs (vs (vs (vs vz)))))} {M = iihTyMotK}
               (⊢var (there (there (there (there here))))))
