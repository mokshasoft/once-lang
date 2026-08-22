------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — gap B layer 2, SPLIT 3's `a > b` LEAF.
--
-- ⚠⚠ ITS OWN MODULE, EVERY PIECE A `Def` — same measurement as the `a ≤ b`
--   leaf, one context slot DEEPER (the successor branch adds the
--   predecessor and the inner motive, so this sits at depth 10).
--
-- ★ `a ∸ b` is `suc p`, so `gcd (a,b) = gcd (a ∸ b , b)`.  The IH gives
--   `v ∣ (a ∸ b)` and `v ∣ b`; `gcdLeaf-gt` turns those into
--   `v ∣ a ∧ v ∣ b` using `monusPlus`.  ⚠ The mirror image of the `a ≤ b`
--   leaf in EVERY respect — which conjunct is immediate, which
--   cancellation applies, and which component the recursion changes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Gcd.DvdLs where
open import DirectedHoTT.Examples.Gcd.Dvd public

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs; RTy; RTm; El; Nat; Hom
        ; var; nzero; nsuc; fst; snd; app; subTm; subTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢lam; ⊢conv
        ; csymᵀ; _⟶*_; step; done; βfst; βsnd; natrec-suc )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Wk using ( w )
open import DirectedHoTT.Lib.Pair using ( asN; PairT ; msrPair)
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Monus using ( monusTm; ⊢monus )
open import DirectedHoTT.Lib.ArithComm using ( IdN; ⊢tyIdN )
open import DirectedHoTT.Lib.Amrec using ( Prv; prv; prvOk )
open import DirectedHoTT.Lib.DvdArith
  using ( QCode; QCode-conv; QCode-convU; ⊢Q-fst; ⊢Q-snd )
open import DirectedHoTT.Examples.Gcd.Step
  using ( PAIRˢ; CERTˢ; KS; NS; gcdIH; ⊢gcdIH; msr; G3s )
open import DirectedHoTT.Spec.Typing using ( ⊢pair; ty-Nat )
open import DirectedHoTT.Lib.ArithMonus using ( ⊢desc-left )
open import DirectedHoTT.Examples.Gcd.StepExt
  using ( f₃; gcdIH-w; gcdIH-w²; appGcdIH )
open import DirectedHoTT.Examples.Gcd.StepExtLs using ( red₃s )

private

  -- ★ the branch's bound and step function, at `(Θ₃ ▹ Nat) ▹ MI₃`
  B₄ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  B₄ = plusTm (nsuc (var (vs (vs (vs vz)))))
              (nsuc (var (vs (vs (vs (vs (vs vz)))))))

  F₄ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  F₄ = subTm nrs f₃

  ⊢B₄ : {Γ : Ctx} → ((ΘI₃ Γ ▹ Nat) ▹ MI₃) ⊢ B₄ ∷ Nat
  ⊢B₄ = ⊢plus (⊢nsuc (⊢var (there (there (there here)))))
              (⊢nsuc (⊢var (there (there (there (there (there here)))))))

  rr₄ : {Γ : Cx} → subTm nrs (f₃ {Γ}) ⟶* G3s
  rr₄ = step (natrec-suc _ _ _) done

  -- the scrutinee equation this branch is entered WITH
  EqT : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  EqT = IdN (monusTm (nsuc (var (vs (vs (vs vz)))))
                     (nsuc (var (vs (vs (vs (vs (vs vz)))))))) 
            (nsuc (var (vs vz)))

  ⊢EqT : {Γ : Ctx} → ((ΘI₃ Γ ▹ Nat) ▹ MI₃) ⊢ty EqT
  ⊢EqT = ⊢tyIdN (⊢monus (⊢nsuc (⊢var (there (there (there here)))))
                        (⊢nsuc (⊢var (there (there (there (there (there here))))))))
                (⊢nsuc (⊢var (there here)))

  -- the branch's context up to (and including) the equation binder — this
  -- is `CΓs`'s shape with the last slot being `EqT`, not `gcdIH`.
  Θ₄E : Ctx → Ctx
  Θ₄E Γ = (((ΘI₃ Γ ▹ Nat) ▹ MI₃) ▹ EqT)

  Θ₄ : Ctx → Ctx
  Θ₄ Γ = ((Θ₄E Γ) ▹ gcdIH (w B₄)) ▹ indPWT (w (w B₄)) (var vz)

  A₁₀ B₁₀ P₁₀ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  A₁₀ = nsuc (var (vs (vs (vs (vs (vs (vs vz)))))))
  B₁₀ = nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) 
  P₁₀ = var (vs (vs (vs (vs vz))))

  dA₁₀ : {Γ : Ctx} → Θ₄ Γ ⊢ A₁₀ ∷ Nat
  dA₁₀ = ⊢nsuc (⊢var (there (there (there (there (there (there here)))))))

  dB₁₀ : {Γ : Ctx} → Θ₄ Γ ⊢ B₁₀ ∷ Nat
  dB₁₀ = ⊢nsuc (⊢var (there (there (there (there (there (there (there (there here)))))))))

  dP₁₀ : {Γ : Ctx} → Θ₄ Γ ⊢ P₁₀ ∷ Nat
  dP₁₀ = ⊢var (there (there (there (there here))))

  -- ⚠⚠ `⊢PAIRˢ`/`⊢CERTˢ` ARE RE-DERIVED HERE, NOT IMPORTED, AND THAT IS A
  --   MEASUREMENT.  `…GcdStep` states them at `CΓs Γ B C D`, whose LAST
  --   slot is hard-wired to `gcdIH …`; this branch binds the SCRUTINEE
  --   EQUATION there instead.  Generalising `CΓs` over that slot — the
  --   obvious fix, and the one `CΓz` got — **OOM-KILLED
  --   `…ExamplesGcdLeEq` and `…ExamplesGcdLeMid`** (exit 143, uncontended;
  --   both were green before and are green again after reverting).
  --
  -- ⭐ Same mechanism `…LibAmrecRen`'s header records: PARAMETERISING A
  --   SHARED DEFINITION IS NOT FREE — it moves the parameter into every
  --   use site, and only the modules already at the ceiling notice.  Those
  --   two sit at ~6m24s.  ⇒ six lines of duplication here, rather than a
  --   regression there.
  dksL : {Γ : Ctx} → Θ₄E Γ ⊢ KS ∷ Nat
  dksL = ⊢var (there (there (there (there here))))

  dnsL : {Γ : Ctx} → Θ₄E Γ ⊢ NS ∷ Nat
  dnsL = ⊢var (there (there (there (there (there (there here))))))

  ⊢PAIRˢL : {Γ : Ctx} → Θ₄E Γ ⊢ PAIRˢ ∷ PairT
  ⊢PAIRˢL = ⊢pair ty-Nat (⊢monus (⊢nsuc dksL) (⊢nsuc dnsL)) (⊢nsuc dnsL)

  ⊢CERTˢL : {Γ : Ctx} → Θ₄E Γ ⊢ CERTˢ
              ∷ Hom Nat (nsuc (plusTm (fst PAIRˢ) (snd PAIRˢ)))
                        (plusTm (nsuc KS) (nsuc NS))
  ⊢CERTˢL =
    ⊢conv (⊢desc-left dksL dnsL)
          (csymᵀ (msrPair (monusTm (nsuc KS) (nsuc NS)) (nsuc NS)
                           (plusTm (nsuc KS) (nsuc NS))))

  dPAIR : {Γ : Ctx} → Θ₄ Γ ⊢ w (w PAIRˢ) ∷ PairT
  dPAIR = ⊢wk (⊢wk ⊢PAIRˢL)

  dCERT : {Γ : Ctx} → Θ₄ Γ ⊢ w (w CERTˢ)
            ∷ Hom Nat (nsuc (subTm (single (w (w PAIRˢ))) msr)) (w (w (w B₄)))
  dCERT = ⊢wk (⊢wk ⊢CERTˢL)

  dIH : {Γ : Ctx} → Θ₄ Γ ⊢ var (vs vz) ∷ gcdIH (w (w (w B₄)))
  dIH = ⊢-cast (gcdIH-w² (w B₄)) (⊢var (there here))

  dV : {Γ : Ctx} → Θ₄ Γ ⊢ app (app (var (vs vz)) (w (w PAIRˢ))) (w (w CERTˢ)) ∷ Nat
  dV = asN (appGcdIH dIH dPAIR dCERT)

  dcall : {Γ : Ctx} →
          Θ₄ Γ ⊢ app (app (var vz) (w (w PAIRˢ))) (w (w CERTˢ))
            ∷ El (QCode (monusTm A₁₀ B₁₀) B₁₀
                    (app (app (var (vs vz)) (w (w PAIRˢ))) (w (w CERTˢ))))
  dcall =
    ⊢conv (indPWElim (⊢-cast (indPWT-w (w (w B₄)) (var vz)) (⊢var here))
                     dPAIR dCERT)
          (QCode-convU _ (step (βfst _ _) done) (step (βsnd _ _) done))

  dEq : {Γ : Ctx} → Θ₄ Γ ⊢ var (vs (vs vz)) ∷ IdN (monusTm A₁₀ B₁₀) (nsuc P₁₀)
  dEq = ⊢var (there (there here))

  inner : {Γ : Ctx} → Prv (Θ₄ Γ) (El (QCode A₁₀ B₁₀
                                       (app (w (w (w F₄))) (var (vs vz)))))
  inner =
    prv _ (⊢conv (prvOk (gcdLeaf-gt dA₁₀ dB₁₀ dV dP₁₀ dEq
                                    (⊢Q-fst dcall) (⊢Q-snd dcall)))
                 (csymᵀ (QCode-conv A₁₀ B₁₀ (red₃s rr₄ (var (vs vz))))))

leafI₃s : {Γ : Ctx} → Prv ((ΘI₃ Γ ▹ Nat) ▹ MI₃) (subTy nrs MI₃)
leafI₃s =
  prv _ (⊢lam ⊢EqT
          (⊢lam (⊢gcdIH (⊢wk ⊢B₄))
            (⊢lam (⊢indPWT (⊢wk (⊢wk ⊢B₄))
                           (⊢-cast (gcdIH-w (w B₄)) (⊢var here)))
                  (prvOk inner))))
