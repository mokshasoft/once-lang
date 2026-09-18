------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `iconSK` AND `iatConK`.  TWO ENTRIES, ONE PROOF.
--
--   iconS k i vz          = icon k (var vz)
--   iconS k i (vs vz)     = renTm vs i
--   iconS k i (vs (vs x)) = var (vs x)
--   iatCon k i M          = subTy (iconS k i) M
--
-- ★★★ THE FACTORISATION the ledger names:  `iconS k i = icS k ∘ extS
--   (single i)`, where `icS k` is the ONE-LEVEL part that `icSK`
--   represents (`Knot/IConSAgree.icSK-vz`/`-vs`).  Check it:
--     vz        ↦ var vz       ↦ icon k (var vz)    ✓
--     vs vz     ↦ w i          ↦ w i   (icS is the identity off `vz`) ✓
--     vs (vs x) ↦ var (vs x)   ↦ var (vs x)         ✓
--
-- ★ AND `iconSK` IS `iextK`'s SHAPE — a composition under its own `lam`
--   — so `Knot/IExtRep` is the template: one β law stated ONCE, generic
--   in the variable, then the clauses are its packaging.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IConSRep where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; Sub; Var; vz; vs; var; app; lam; pair; subTm
        ; renTm; extS; nsuc; icon; subTm-renTm; subTm-cong; subTm-id )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; single; wk-single; iconS; iatCon )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ; ⟶*-castᵣ )
open import DirectedHoTT.Lib.Wk using ( w; sub-w; cong₃; cong₄; ren-sub )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ; ⟶*-ielimᵗ )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans; sym )
open import DirectedHoTT.Examples.Knot.Sorts using ( len; sVar )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enVar; enTy )
open import DirectedHoTT.Examples.Knot.IConS using ( iconSK; icSK; iconSMeths; iconSSK; iconSTail )
open import DirectedHoTT.Examples.Knot.ConS using ( conSJunk )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK )
open import DirectedHoTT.Examples.Knot.Single using ( singleK )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK )
open import DirectedHoTT.Examples.Knot.SubNat using ( extNK-sub )
open import DirectedHoTT.Examples.Knot.SubAgree using ( Represents; single-Represents )
open import DirectedHoTT.Examples.Knot.SubExt using ( extS-Represents )
open import DirectedHoTT.Examples.Knot.SubAgreeTie using ( sub-agree )
open import DirectedHoTT.Examples.Knot.IExtRep
  using ( singleK-sub; subTmAtK-sub; ⟶*-subTmAtK )
open import DirectedHoTT.Examples.Knot.IConSAgree using ( icSK-vz; icSK-vs )
open import DirectedHoTT.Lib.IMeths using ( cdTake; methsFrom-sub )

------------------------------------------------------------------------
-- ★ `icSK`'s NATURALITY — `singleK-sub`'s shape, one tuple over.
------------------------------------------------------------------------

iconSMeths-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) →
                 subTm τ (iconSMeths {Γ}) ≡ iconSMeths {Δ}
iconSMeths-sub τ = methsFrom-sub (cdTake 51 KnotD) τ conSJunk iconSTail

iconSSK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (i x k : RTm Γ) →
              subTm τ (iconSSK i x k)
              ≡ iconSSK (subTm τ i) (subTm τ x) (subTm τ k)
iconSSK-sub τ i x k =
  cong (λ z → app (DirectedHoTT.Spec.Syntax.ielim KnotD (subTm τ i) z (subTm τ x))
                  (subTm τ k))
       (iconSMeths-sub τ)

icSK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n k : RTm Γ) →
           subTm τ (icSK n k) ≡ icSK (subTm τ n) (subTm τ k)
icSK-sub τ n k = cong lam (trans (iconSSK-sub (extS τ) (pair sVar (nsuc (w n))) (var vz) (w k))
                                 (cong₂ (λ a b → iconSSK (pair sVar (nsuc a)) (var vz) b)
                                        (sub-w {σ = τ} n) (sub-w {σ = τ} k)))

------------------------------------------------------------------------
-- ★★★ THE β LAW, ONCE — `Knot/IExtRep.iextK-app`'s shape exactly.
------------------------------------------------------------------------

iconSK-app : {Γ : Cx} (n k i a : RTm Γ) →
             app (iconSK n k i) a
             ⟶* subTmAtK (nsuc n) (nsuc n) (icSK n k)
                         (app (extNK (nsuc n) n (singleK n i)) a)
iconSK-app n k i a = step (β _ _) (⟶*-castₗ eq done)
  where
    eIc : subTm (single a) (icSK (w n) (w k)) ≡ icSK n k
    eIc = trans (icSK-sub (single a) (w n) (w k))
                (cong₂ icSK (wk-single {v = a} n) (wk-single {v = a} k))
    eS : subTm (single a) (singleK (w n) (w i)) ≡ singleK n i
    eS = trans (singleK-sub (single a) (w n) (w i))
               (cong₂ singleK (wk-single {v = a} n) (wk-single {v = a} i))
    eE : subTm (single a) (extNK (nsuc (w n)) (w n) (singleK (w n) (w i)))
         ≡ extNK (nsuc n) n (singleK n i)
    eE = trans (extNK-sub (single a) (nsuc (w n)) (w n) (singleK (w n) (w i)))
               (cong₃ extNK (cong nsuc (wk-single {v = a} n))
                            (wk-single {v = a} n) eS)
    eq : subTm (single a)
           (subTmAtK (nsuc (w n)) (nsuc (w n)) (icSK (w n) (w k))
                     (app (extNK (nsuc (w n)) (w n) (singleK (w n) (w i))) (var vz)))
         ≡ subTmAtK (nsuc n) (nsuc n) (icSK n k)
                    (app (extNK (nsuc n) n (singleK n i)) a)
    eq = trans (subTmAtK-sub (single a) (nsuc (w n)) (nsuc (w n))
                             (icSK (w n) (w k))
                             (app (extNK (nsuc (w n)) (w n) (singleK (w n) (w i)))
                                  (var vz)))
               (cong₄ (λ d m s x → subTmAtK d m s (app x a))
                      (cong nsuc (wk-single {v = a} n))
                      (cong nsuc (wk-single {v = a} n)) eIc eE)

------------------------------------------------------------------------
-- ★ THE ONE-LEVEL PART, which is what `icSK` represents.
------------------------------------------------------------------------

icS : {Γ : Cx} → ℕ → Sub (Γ ∙) (Γ ∙)
icS k vz     = icon k (var vz)
icS k (vs x) = var (vs x)

icS-Represents : {Γ Θ : Cx} (n : RTm Θ) (k : ℕ) →
                 Represents {Γ = Γ ∙} {Δ = Γ ∙} (icS k) (icSK n (num k))
icS-Represents {Γ} n k vz     = icSK-vz n (num k) (num (len Γ))
icS-Represents {Γ} n k (vs x) = icSK-vs n (num k) (num (len Γ)) (enVar x)

-- ★★ THE FACTORISATION.  ⚠ The MIDDLE clause is the only one with
--   content: `extS (single i) (vs vz)` is `w i`, and `icS k` is the
--   IDENTITY off `vz`, so substituting it into a weakened term does
--   nothing.
iconS-fact : {Γ : Cx} (k : ℕ) (i : RTm Γ) (x : Var ((Γ ∙) ∙)) →
             subTm (icS k) (extS (single i) x) ≡ iconS k i x
iconS-fact k i vz          = refl
iconS-fact k i (vs vz)     = trans (subTm-renTm i) (sym (ren-sub {ρ = vs} i))
iconS-fact k i (vs (vs x)) = refl

------------------------------------------------------------------------
-- ★★★ THE TWO LEDGER ENTRIES.
------------------------------------------------------------------------

-- ⚠ THE DEPTH IS FORCED to `⌈|Γ|⌉` and is NOT free, exactly as
--   `Knot/ConSAgree.atCon-agree` records: `extS-Represents` reads the
--   target depth off the ENCODING, so `n` may only be stated where the
--   encoding uses it.
iconS-Represents : {Γ Θ : Cx} (k : ℕ) (i : RTm Γ) →
                   Represents {Γ = (Γ ∙) ∙} {Δ = Γ ∙}
                              (iconS k i)
                              (iconSK {Θ} (num (len Γ)) (num k) (enTm i))
iconS-Represents {Γ} k i x =
  ⟶*-castᵣ (cong enTm (iconS-fact k i x))
    (iconSK-app (num (len Γ)) (num k) (enTm i) (enVar x)
     » ⟶*-subTmAtK (extS-Represents (nsuc (num (len Γ)))
                                    (single-Represents (num (len Γ))) x)
     » sub-agree (icS-Represents (num (len Γ)) k) (extS (single i) x))

------------------------------------------------------------------------
-- ★★★ AND `iatConK` IS THE ONE-LINE COROLLARY its entry predicted:
--   *"a corollary of `iconSK`'s and `subTyAtK`'s"*.
--
--     iatCon k i M  = subTy (iconS k i) M
--     iatConK n k i = subTyAtK (nsuc (nsuc n)) (nsuc n) (iconSK n k i)
------------------------------------------------------------------------

open import DirectedHoTT.Examples.Knot.IConS using ( iatConK )
open import DirectedHoTT.Examples.Knot.SubAgreeTyTie using ( sub-agree-ty )

iatCon-agree : {Γ Θ : Cx} (k : ℕ) (i : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
               iatConK (num (len Γ)) (num k) (enTm {Γ} {Θ} i)
                       (enTy {(Γ ∙) ∙} {Θ} M)
               ⟶* enTy {Γ ∙} {Θ} (iatCon k i M)
iatCon-agree {Γ} k i M = sub-agree-ty (iconS-Represents k i) M
