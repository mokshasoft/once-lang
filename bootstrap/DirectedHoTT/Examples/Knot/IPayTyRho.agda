------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `ipayTy`'s `iρ` ROW, ALONE IN A MODULE.
--
-- ⚠⚠ IT IS ALONE BECAUSE IT MUST BE.  MEASURED:
--
--     row structure only (junk body)      9.7s /  0.8 GB
--     + `Ty-IMuK D I (subTmAtK …)`       20.6s /  2.5 GB
--     + the recursive call as well       OOM at 5.5 GB (with `-c` too)
--     the same, behind abstract lemmas   48.3s /  4.5 GB
--
--   The abstract lemmas of `Knot/IPayTyMot` are what brought it under
--   the cap at all — but 4.5 GB for ONE row leaves no room for a second,
--   so the two rows live in two modules.  This is the shape the merge
--   spike measured for the judgement rows (`JUDGEMENT-ATTEMPTS.md` §11):
--   viable at ONE row per module.
--
-- ⚠ AND NAMING THE BIG SUBTERMS BOUGHT NOTHING.  `subTmAtK`, `extNK`
--   and `wkK` each expand to an `ielim` over a 53-method tuple; pulling
--   them out as `Def`s measured 48.3s / 4.56 GB against 48.3s / 4.53 GB.
--   ⇒ `agda-cost-is-elaborated-term-size` cuts the other way here: the
--     cost is in the CONVERSION CHECK, which unfolds a `Def` anyway.
--     What did pay was moving the DERIVATION behind abstract arguments.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IPayTyRho where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IDesc; εwkTy; IMu; app; fst; iρ; iκ; iι
        ; ⌜Id⌝; ⌜Nat⌝; isingle; iext; unit; _◂_; ielim; nzero; nsuc; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢fst; ⊢lam; ⊢app; ⊢unit; ⊢nzero; ⊢nsuc
        ; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim
        ; ξ-pairʳ; βsnd; done; step; single; wk-single; iinst )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast )
open import normalizer.Syntax.Types using ( cong; trans; sym )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ; ⊢methsFrom; ⊢methsCons
        ; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Lib.ICast using ( muFwd; muBwd* )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sTm; ⊢sTm; sICon; ⊢sICon
        ; sIDesc; ⊢sIDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cICon-rho; cICon-kap )
open import DirectedHoTT.Examples.Knot.Wf
  using ( KnotWf; cICon-rhoWf; cICon-kapWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagICon-rho; tagICon-kap )
open import DirectedHoTT.Examples.Knot.Ctors
  using ( Ty-UnitK; Ty-SgK; Ty-IMuK; Ty-ElK )
open import DirectedHoTT.Examples.Knot.CtorsV
  using ( ⊢Ty-UnitKv; ⊢Ty-SgKv; ⊢Ty-IMuKv; ⊢Ty-ElKv )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy; ty-SubTy; subBwd )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkKat )
open import DirectedHoTT.Examples.Knot.SubMot
  using ( extNK; ⊢extNK; towerA; towerJ )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK; ⊢subTmAtK )

open import DirectedHoTT.Examples.Knot.IPayTyMot
  using ( ipayTyMotK; ⊢ipayTyMotK; ⊢ipayAppK; ⊢ipayRowρ; ⊢ipayRowκ )

------------------------------------------------------------------------
-- ★★★ `iρ` AND `iκ` — AND THE TWO CODES ARE CHARACTER-IDENTICAL.
--
--   cICon-rho = cICon-kap
--     = iρ (pair sTm (snd ⟨i⟩))
--        (iρ (pair sICon (nsuc (snd ⟨i⟩))) (iκ <ford> iι))
--
--   ⇒ the two methods differ in ONE constructor — `Ty-IMuK D I …` vs
--     `Ty-ElK …` — and in nothing else, pins included.
--
-- ★★ AND THE RECURSIVE ANSWER NEEDS NO WEAKENING.  It comes back at
--   `pair sTy (nsuc n)` because `extS` moved the TARGET depth too, which
--   is exactly `⊢Ty-SgKv`'s second premise.  Contrast `Knot/PayTy`,
--   where every recursive answer costs a `⊢wkKat`.
--
-- ⚠ `⊢ipayAppK`'s `dd`/`u` ARE PINNED.  They sit under `iinst`, which is
--   two `subTy`s and so not injective; left as metas they leave a stuck
--   constraint (`pin-implicits-on-defined-set-types`, one layer up).
------------------------------------------------------------------------

ipayTyRho : {Γ : Cx} → RTm Γ
ipayTyRho =
  lam (lam (lam (lam (lam (lam (lam
    (Ty-SgK (Ty-IMuK (var (vs vz)) (var vz)
                     (subTmAtK (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                               (var (vs (vs (vs vz))))
                               (var (vs (vs vz)))
                               (fst (var (vs (vs (vs (vs (vs vz)))))))))
            (app (app (app (app (fst (snd (var (vs (vs (vs (vs vz)))))))
                                (nsuc (var (vs (vs (vs vz))))))
                           (extNK (snd (var (vs (vs (vs (vs (vs (vs vz))))))))
                                  (var (vs (vs (vs vz))))
                                  (var (vs (vs vz)))))
                      (wkK (pair sIDesc (var (vs (vs (vs vz))))) (var (vs vz))))
                 (var vz)))))))))

⊢ipayTyRho : {Γ : Ctx} →
             Γ ⊢ ipayTyRho
               ∷ imethTy KnotD IPair tagICon-rho cICon-rho ipayTyMotK
⊢ipayTyRho =
  ⊢methLam KnotD IPair tagICon-rho cICon-rho KnotWf cICon-rhoWf
           ⊢IPair ⊢ipayTyMotK
    (⊢lam ty-Nat
      (⊢lam (ty-SubTy (⊢snd (⊢var (there (there (there here))))) (⊢var here))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var (there here))))
          (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTy ⊢nzero))
            (⊢ipayRowρ dn ddd dsb dD dI
              (⊢fst (⊢var (there (there (there (there (there here)))))))
              (⊢ipayAppK
                 {dd = nsuc (snd (var (vs (vs (vs (vs (vs (vs vz)))))))) }
                 {u = fst (snd (var (vs (vs (vs (vs (vs vz))))))) }
                 dIH (⊢nsuc dn) (⊢extNK ddd dn dsb)
                 (⊢wkKat ⊢sIDesc dn dD) dI))))))
  where
    dn  = ⊢var (there (there (there here)))
    dsb = ⊢var (there (there here))
    dD  = ⊢var (there here)
    dI  = ⊢var here
    ddd = ⊢snd (⊢var (there (there (there (there (there (there here)))))))
    dIH = ⊢ihHere
            {D = KnotD} {I = IPair}
            {σ = iext (isingle (var (vs (vs (vs (vs (vs (vs vz))))))))
                      (fst (var (vs (vs (vs (vs (vs vz)))))))}
            {j = pair sICon (nsuc (snd (var (vs vz))))}
            (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sICon) iι)
            {q = snd (var (vs (vs (vs (vs (vs vz))))))} {M = ipayTyMotK}
            (⊢ihSkipρ
               {D = KnotD} {I = IPair}
               {σ = isingle (var (vs (vs (vs (vs (vs (vs vz)))))))}
               {j = pair sTm (snd (var vz))}
               (iρ (pair sICon (nsuc (snd (var (vs vz)))))
                 (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sICon) iι))
               {q = var (vs (vs (vs (vs (vs vz)))))} {M = ipayTyMotK}
               (⊢var (there (there (there (there here))))))
