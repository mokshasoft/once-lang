------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES, WF-AXIS STAGE E: ★★ DOGFOODING.
--
-- THE MOST PERSUASIVE EXHIBIT, because it is OUR OWN PAIN.
--
-- This POC's own metatheory hand-rolls measure recursion everywhere:
--
--     prog    : (n : ℕ) {t : RTm ε} → ◇ ⊢ t ∷ T → sz t ≤ n → Prog t
--     usplit  : (n : ℕ) {c : RTm ε} → ◇ ⊢ c ∷ U → sz c ≤ n → UProg c
--     trS     : (m : ℕ) …                        → sz p ≤ m → …
--     ordtrS  : (m : ℕ) …  → sz a + sz t + sz u + sz p + sz q ≤ m → …
--
-- Every one threads an explicit `ℕ` bound and a `≤` premise, then peels
-- the bound with `un≤` and re-derives the sub-bounds by hand (`ordtr-bᵃ`
-- and friends).  That plumbing IS the pain the WF axis exists to kill.
--
-- ★ `⊢mrec` below is the combinator that replaces it: recursion along a
--   MEASURE `μ`, derived from ordinary `natrec` inside the kernel.
--
--     mrec : ((x : Nat) → ((y : Nat) → μ y < μ x → P y) → P x)
--          → (x : Nat) → P x
--
--   The bound and the `≤` premise are still there — but they are now
--   INTERNAL to `mrec`, generated once, instead of appearing in the
--   signature of every single recursive definition.
--
-- ⚠ NO `Acc`, NO fuel, NO `TERMINATING`, no measure argument in the
--   user-facing signature.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesDogfood where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; ⌜Hom⌝; ⌜Nat⌝
        ; Π; lam; app; renTy; subTy )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶ᵀ_; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢absurd; ⊢ordtr
        ; _⊢ty_; ty-El; ty-Nat; ty-U; ty-Π; ty-Hom )
open import poc.OCP0009.NbEPDirDBInj
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong
  using ( El-homNat; ⊢le-refl; reflTm )

------------------------------------------------------------------------
-- 1. THE THREE HYPOTHESES, AS CONTEXT VARIABLES.
--
--    `cP : Π Nat U`   the motive code family, `P x = El (app cP x)`
--    `μ  : Π Nat Nat` the MEASURE
--    `stp`            the step function
--
--    ★ context variables, not Agda parameters — the `⊢sind` trick: every
--      substitution `natrec`/`app` generates then COMPUTES.
------------------------------------------------------------------------

-- `(y : Nat) → μ y < μ x → P y`, with vz = x, vs vz = μ, vs² vz = cP.
MIHT : RTy (ε ∙ ∙ ∙)
MIHT = Π Nat (Π (Hom Nat (nsuc (app (var (vs (vs vz))) (var vz)))
                         (app (var (vs (vs vz))) (var (vs vz))))
                (El (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))))

-- `(x : Nat) → ((y : Nat) → μ y < μ x → P y) → P x`, vz = μ, vs vz = cP.
MStepT : RTy (ε ∙ ∙)
MStepT = Π Nat (Π MIHT (El (app (var (vs (vs (vs vz)))) (var (vs vz)))))

Γ₂ : Ctx
Γ₂ = ((◇ ▹ Π Nat U) ▹ Π Nat Nat) ▹ MStepT

-- ── the `natrec` motive: `(x : Nat) → μ x ≤ n → P x`, with vz = n ────
mAuxMot : RTy (ε ∙ ∙ ∙ ∙)
mAuxMot =
  Π Nat (Π (Hom Nat (app (var (vs (vs (vs vz)))) (var vz)) (var (vs vz)))
           (El (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz)))))

------------------------------------------------------------------------
-- 2. THE TWO BRANCHES.  Identical in shape to `⊢aux`, with `μ y` / `μ x`
--    in the order positions instead of `y` / `x`.
------------------------------------------------------------------------

-- n = 0: `μ x ≤ 0` and `μ y < μ x` compose to `μ y < 0`, which COMPUTES
-- to `base`; ex falso inhabits `P y`.
mZBr : RTm (ε ∙ ∙ ∙)
mZBr =
  lam (lam (app (app (var (vs (vs vz))) (var (vs vz)))
                (lam (lam (absurd
                  (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs vz)))
                  (ordtr (nsuc (app (var (vs (vs (vs (vs (vs vz))))))
                                    (var (vs vz))))
                         (app (var (vs (vs (vs (vs (vs vz))))))
                              (var (vs (vs (vs vz)))))
                         nzero (var vz) (var (vs (vs vz)))))))))

-- n = suc n': `μ y < μ x` and `μ x ≤ suc n'` give `μ y < suc n'`, i.e.
-- `suc (μ y) ≤ suc n'`, which the ORDER computes to `μ y ≤ n'` — exactly
-- what the IH wants.
mSBr : RTm (ε ∙ ∙ ∙ ∙ ∙)
mSBr =
  lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))
                (lam (lam (app
                  (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))
                  (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
                                    (var (vs vz))))
                         (app (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
                              (var (vs (vs (vs vz)))))
                         (nsuc (var (vs (vs (vs (vs (vs vz)))))))
                         (var vz) (var (vs (vs vz)))))))))

mAuxTm : RTm (ε ∙ ∙ ∙) → RTm (ε ∙ ∙ ∙)
mAuxTm n = natrec mZBr mSBr n

------------------------------------------------------------------------
-- 3. THE DERIVATIONS.
------------------------------------------------------------------------

⊢mAuxMot : (Γ₂ ▹ Nat) ⊢ty mAuxMot
⊢mAuxMot =
  ty-Π ty-Nat
    (ty-Π (ty-Hom ty-Nat
             (⊢app (⊢var (there (there (there here)))) (⊢var here))
             (⊢var (there here)))
          (ty-El (⊢app (⊢var (there (there (there (there (there here))))))
                       (⊢var (there here)))))

⊢mZBr : Γ₂ ⊢ mZBr ∷ subTy (single nzero) mAuxMot
⊢mZBr =
  ⊢lam ty-Nat
    (⊢lam (ty-Hom ty-Nat
             (⊢app (⊢var (there (there here))) (⊢var here))
             ⊢nzero)
      (⊢app (⊢app (⊢var (there (there here))) (⊢var (there here)))
            (⊢lam ty-Nat
              (⊢lam (ty-Hom ty-Nat
                       (⊢nsuc (⊢app (⊢var (there (there (there (there here)))))
                                    (⊢var here)))
                       (⊢app (⊢var (there (there (there (there here)))))
                             (⊢var (there (there here)))))
                (⊢absurd
                  (⊢app (⊢var (there (there (there (there (there (there here)))))))
                        (⊢var (there here)))
                  (⊢conv (⊢ordtr
                           (⊢nsuc (⊢app (⊢var (there (there (there (there (there here))))))
                                        (⊢var (there here))))
                           (⊢app (⊢var (there (there (there (there (there here))))))
                                 (⊢var (there (there (there here)))))
                           ⊢nzero
                           (⊢var here)
                           (⊢var (there (there here))))
                         (red→≅ᵀ (stepᵀ (Hom-Nat-sz _) doneᵀ))))))))

⊢mSBr : ((Γ₂ ▹ Nat) ▹ mAuxMot) ⊢ mSBr ∷ subTy nrs mAuxMot
⊢mSBr =
  ⊢lam ty-Nat
    (⊢lam (ty-Hom ty-Nat
             (⊢app (⊢var (there (there (there (there here))))) (⊢var here))
             (⊢nsuc (⊢var (there (there here)))))
      (⊢app (⊢app (⊢var (there (there (there (there here)))))
                  (⊢var (there here)))
            (⊢lam ty-Nat
              (⊢lam (ty-Hom ty-Nat
                       (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there here)))))))
                                    (⊢var here)))
                       (⊢app (⊢var (there (there (there (there (there (there here)))))))
                             (⊢var (there (there here)))))
                (⊢app (⊢app (⊢var (there (there (there (there here)))))
                            (⊢var (there here)))
                      (⊢conv (⊢ordtr
                               (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there here))))))))
                                            (⊢var (there here))))
                               (⊢app (⊢var (there (there (there (there (there (there (there here))))))))
                                     (⊢var (there (there (there here)))))
                               (⊢nsuc (⊢var (there (there (there (there (there here)))))))
                               (⊢var here)
                               (⊢var (there (there here))))
                             (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ))))))))

-- ★★ the bounded auxiliary, ON THE MEASURE.
⊢mAux : {n : RTm ⌊ Γ₂ ⌋} → Γ₂ ⊢ n ∷ Nat →
        Γ₂ ⊢ mAuxTm n ∷ subTy (single n) mAuxMot
⊢mAux dn = ⊢natrec ⊢mAuxMot ⊢mZBr ⊢mSBr dn

------------------------------------------------------------------------
-- ★★★★ 4. MEASURE RECURSION.
--
--        mrec x = mAux (μ x) x (le-refl (μ x))  :  P x
--
--   `prog`, `usplit`, `trS` and `ordtrS` each carry an `ℕ` bound and a
--   `≤` premise through their whole signature and peel them by hand.
--   Here that bookkeeping happens ONCE, inside `mrec`, and never appears
--   in a user-facing type again.
------------------------------------------------------------------------

mrecTm : RTm ⌊ Γ₂ ⌋ → RTm ⌊ Γ₂ ⌋
mrecTm x = app (app (mAuxTm (app (var (vs vz)) x)) x)
               (reflTm (app (var (vs vz)) x))

⊢mrec : {x : RTm ⌊ Γ₂ ⌋} → Γ₂ ⊢ x ∷ Nat →
        Γ₂ ⊢ mrecTm x ∷ El (app (var (vs (vs vz))) x)
-- ⚠ the same TWO `wk-single` casts as `⊢sind`, and for the same reason:
-- Agda computes every substitution `natrec`/`app` generates except
-- `subTm (single v) (renTm vs ·)`.
⊢mrec {x = x} dx =
  subst (λ z → Γ₂ ⊢ mrecTm x ∷ El (app (var (vs (vs vz))) z))
        (wk-single x)
   (⊢app (⊢app (⊢mAux dμx) dx)
       (subst (λ z → Γ₂ ⊢ reflTm (app (var (vs vz)) x) ∷ Hom Nat (app (var (vs vz)) x) z)
              (sym (wk-single (app (var (vs vz)) x)))
              (⊢le-refl dμx)))
  where
    dμx : Γ₂ ⊢ app (var (vs vz)) x ∷ Nat
    dμx = ⊢app (⊢var (there here)) dx
