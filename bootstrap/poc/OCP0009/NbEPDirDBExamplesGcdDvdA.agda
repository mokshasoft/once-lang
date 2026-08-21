------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — gap B layer 2, THE WHOLE ASSEMBLY, ONE MODULE.
--
-- ⚠⚠ THIS MODULE NEEDS THE COMPACTING COLLECTOR.  Check it with
--
--       ./check.sh poc/OCP0009/NbEPDirDBExamplesGcdDvdA.agda +RTS -c -RTS
--
--   (`sweep.sh` reads that phrase from these first 40 lines and passes
--    `-A64m -c` on the FIRST attempt, so the 339s failed copying-GC
--    attempt never happens.  Its exit-143 retry is the safety net for
--    machine variation, not the mechanism.)
--
-- ★ WAS SIX MODULES (`…GcdDvdA1`…`A5`, `…GcdDvdA`), MERGED 2026-08-21.
--   MEASURED (`PERF-2026-08-21.md` §3): the six built individually cost
--   7+51+13+21+21+34 = 147s; merged, this module costs 147s.  Identical.
--   ⇒ Splitting was COST-NEUTRAL — purely a memory device, needed only
--     because the default COPYING collector wants ~2x the live heap.
--     Under `-c` (~1x, in-place compaction) one module fits.
--
-- ⚠ `-c` IS A CONSTANT FACTOR AGAINST A SUPERLINEAR CURVE — it buys one
--   doubling, exactly as `check.sh`'s header says of `-A64m`.  Do not
--   read this merge as headroom; it is a tidier arrangement at the same
--   price.  ⇒ Granularity is still right for LIBRARIES, where a small
--   module can cut a client's dependency CLOSURE.  It bought nothing
--   here because these six shared one closure anyway.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdDvdA where

open import poc.OCP0009.NbEPDirDBExamplesGcdDvdL public
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdLs public
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs; RTy; RTm; El; Nat; Hom; Π
        ; var; nzero; nsuc; fst; snd; app; natrec; ⌜Nat⌝; Sub; subTm; subTy; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nsuc; ⊢fst; ⊢snd; ⊢app; ⊢natrec
        ; ⊢conv; _≅ᵀ_; csymᵀ; ty-Π )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; ⊢[]; Ren⊢ )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; sub-w; sub-w²; cong₃; cong₄ )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm; ⊢monus )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN; ⊢tyIdN; reflN; ⊢reflN )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( Prv; prv; prvTm; prvOk; prv-cast )
open import poc.OCP0009.NbEPDirDBLibAmrecInd using ( IndStep )
open import poc.OCP0009.NbEPDirDBLibNatrec using ( ⊢natrec-var )
open import poc.OCP0009.NbEPDirDBLibDvdArith using ( QCode; QCode-sub; QCode-conv )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdStp; gcdBody; msr; gcdIH; ⊢gcdIH
        ; G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExt
  using ( μ₁; f₁; μ₂; f₂; μ₃; f₃; probe₁-s; probe₂-s
        ; red-β; gcdAt )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtE using ( gcdIH-sub )


-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdDvdA1
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 · EXAMPLES — gap B layer 2, ASSEMBLY PART A1.
-- ⚠⚠ SPLIT ACROSS SIX MODULES FOR COST, AND IT IS A MEASUREMENT.  As ONE
--   module the assembly OOM-KILLED (exit 143, uncontended) — the same wall
--   `…GcdStepExtA1` records for `StepExt`, and for the same reason: split
--   3's leaves sit at context depth 10 and cost is ~1.7x per slot, so the
--   three `natrec`s elaborated together do not fit.  `Def`-splitting alone
--   was not enough there either; the FILE had to split.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

-- ★ the substitution laws `indG` needs — mirrors of `pwT-sub`/`eqG-sub`
------------------------------------------------------------------------

indPWT-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ i : RTm Γ) →
             subTy σ (indPWT μ i) ≡ indPWT (subTm σ μ) (subTm σ i)
indPWT-sub {σ = σ} μ i =
  cong₂ (λ u c → Π PairT (Π (Hom Nat (nsuc msr) u) (El c)))
        (sub-w {σ = σ} μ)
        (trans (QCode-sub {σ = extS (extS σ)}
                  (fst (var (vs vz))) (snd (var (vs vz)))
                  (app (app (w (w i)) (var (vs vz))) (var vz)))
               (cong (λ z → QCode (fst (var (vs vz))) (snd (var (vs vz)))
                                  (app (app z (var (vs vz))) (var vz)))
                     (sub-w² {σ = σ} i)))

indG-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ f u₁ u₂ : RTm Γ) →
           subTy σ (indG μ f u₁ u₂)
         ≡ indG (subTm σ μ) (subTm σ f) (subTm σ u₁) (subTm σ u₂)
indG-sub {σ = σ} μ f u₁ u₂ =
  cong₂ Π (gcdIH-sub μ)
    (cong₂ Π (trans (indPWT-sub (w μ) (var vz))
                    (cong (λ u → indPWT u (var vz)) (sub-w {σ = σ} μ)))
             (cong El
                (trans (QCode-sub {σ = extS (extS σ)}
                          (w (w u₁)) (w (w u₂)) (app (w (w f)) (var (vs vz))))
                       (cong₃ (λ a b z → QCode a b (app z (var (vs vz))))
                              (sub-w² {σ = σ} u₁) (sub-w² {σ = σ} u₂)
                              (sub-w² {σ = σ} f)))))

------------------------------------------------------------------------
-- ★ …and the elimination.
------------------------------------------------------------------------

indGElim : {Γ : Ctx} {μ f u₁ u₂ e i h : RTm ⌊ Γ ⌋} →
           Γ ⊢ e ∷ indG μ f u₁ u₂ → Γ ⊢ i ∷ gcdIH μ → Γ ⊢ h ∷ indPWT μ i →
           Γ ⊢ app (app e i) h ∷ El (QCode u₁ u₂ (app f i))
indGElim {μ = μ} {f = f} {u₁ = u₁} {u₂ = u₂} {i = i} {h = h} de di dh =
  ⊢-cast (cong El eq2) (⊢app (⊢-cast eq1 (⊢app de di)) dh)
  where
    p₁ : (t : RTm ⌊ _ ⌋) → subTm (extS (single i)) (w (w t)) ≡ w t
    p₁ t = trans (sub-w {σ = single i} (w t)) (cong w (wk-single {v = i} t))

    eq1 = cong₂ Π (trans (indPWT-sub (w μ) (var vz))
                         (cong (λ u → indPWT u i) (wk-single {v = i} μ)))
                  (cong El
                     (trans (QCode-sub {σ = extS (single i)}
                               (w (w u₁)) (w (w u₂)) (app (w (w f)) (var (vs vz))))
                            (cong₃ (λ a b z → QCode a b (app z (w i)))
                                   (p₁ u₁) (p₁ u₂) (p₁ f))))

    -- ⚠ FOUR slots, not three: the handle `i` is weakened here too.
    eq2 = trans (QCode-sub {σ = single h} (w u₁) (w u₂) (app (w f) (w i)))
                (cong₄ (λ a b z u → QCode a b (app z u))
                       (wk-single {v = h} u₁) (wk-single {v = h} u₂)
                       (wk-single {v = h} f) (wk-single {v = h} i))

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdDvdA2
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 · EXAMPLES — gap B layer 2, ASSEMBLY PART A2.
-- ⚠⚠ SPLIT ACROSS SIX MODULES FOR COST, AND IT IS A MEASUREMENT.  As ONE
--   module the assembly OOM-KILLED (exit 143, uncontended) — the same wall
--   `…GcdStepExtA1` records for `StepExt`, and for the same reason: split
--   3's leaves sit at context depth 10 and cost is ~1.7x per slot, so the
--   three `natrec`s elaborated together do not fit.  `Def`-splitting alone
--   was not enough there either; the FILE had to split.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

-- ★★ the three motives, typed
------------------------------------------------------------------------

⊢MI₁ : {Γ : Ctx} → ((Γ ▹ PairT) ▹ Nat) ⊢ty MI₁
⊢MI₁ = ⊢indG (⊢plus (⊢fst (⊢var (there here))) (⊢var here))
             (⊢natrec-var ⊢G1 ⊢G1z ⊢gcdInn1)
             (⊢fst (⊢var (there here))) (⊢var here)

⊢MI₂ : {Γ : Ctx} → (ΘI₂ Γ ▹ Nat) ⊢ty MI₂
⊢MI₂ = ⊢indG (⊢plus (⊢var here) (⊢nsuc (⊢var (there (there here)))))
             (⊢natrec-var ⊢G2 ⊢G2z ⊢gcdInn2)
             (⊢var here) (⊢nsuc (⊢var (there (there here))))

⊢MI₃ : {Γ : Ctx} → (ΘI₃ Γ ▹ Nat) ⊢ty MI₃
⊢MI₃ =
  ty-Π (⊢tyIdN (⊢monus (⊢nsuc (⊢var (there (there here))))
                       (⊢nsuc (⊢var (there (there (there (there here)))))))
               (⊢var here))
       (⊢indG (⊢wk (⊢plus (⊢nsuc (⊢var (there (there here))))
                          (⊢nsuc (⊢var (there (there (there (there here))))))))
              (⊢wk (⊢natrec-var ⊢G3 ⊢G3z ⊢G3s))
              (⊢wk (⊢nsuc (⊢var (there (there here)))))
              (⊢wk (⊢nsuc (⊢var (there (there (there (there here))))))))

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdDvdA3
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 · EXAMPLES — gap B layer 2, ASSEMBLY PART A3.
-- ⚠⚠ SPLIT ACROSS SIX MODULES FOR COST, AND IT IS A MEASUREMENT.  As ONE
--   module the assembly OOM-KILLED (exit 143, uncontended) — the same wall
--   `…GcdStepExtA1` records for `StepExt`, and for the same reason: split
--   3's leaves sit at context depth 10 and cost is ~1.7x per slot, so the
--   three `natrec`s elaborated together do not fit.  `Def`-splitting alone
--   was not enough there either; the FILE had to split.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

-- ★★★ the three splits
------------------------------------------------------------------------

split3 : {Γ : Ctx} → Prv (ΘI₃ Γ) (subTy (single μAB) MI₃)
split3 = prv _ (⊢natrec ⊢MI₃ (prvOk leafI₃z) (prvOk leafI₃s)
                        (⊢monus (⊢nsuc (⊢var (there here)))
                                (⊢nsuc (⊢var (there (there (there here)))))))

-- ⚠ THE STEP `StepExt` DOES NOT HAVE: discharge the equation with `reflN`.
split3app : {Γ : Ctx} →
            Prv (ΘI₃ Γ) (indG (plusTm uA₃ uB₃) (subTm (single μAB) f₃) uA₃ uB₃)
split3app =
  prv _ (⊢-cast peel
          (⊢app (⊢-cast probeI₃-at (prvOk split3))
                (⊢reflN (⊢monus (⊢nsuc (⊢var (there here)))
                                (⊢nsuc (⊢var (there (there (there here)))))))))
  where
    R = reflN (μAB {Γ = _})
    peel = trans (indG-sub {σ = single R}
                    (w (plusTm uA₃ uB₃)) (w (natrec G3z G3s μAB))
                    (w uA₃) (w uB₃))
                 (cong₄ indG (wk-single {v = R} (plusTm uA₃ uB₃))
                             (wk-single {v = R} (natrec G3z G3s μAB))
                             (wk-single {v = R} uA₃)
                             (wk-single {v = R} uB₃))

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdDvdA4
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 · EXAMPLES — gap B layer 2, ASSEMBLY PART A4.
-- ⚠⚠ SPLIT ACROSS SIX MODULES FOR COST, AND IT IS A MEASUREMENT.  As ONE
--   module the assembly OOM-KILLED (exit 143, uncontended) — the same wall
--   `…GcdStepExtA1` records for `StepExt`, and for the same reason: split
--   3's leaves sit at context depth 10 and cost is ~1.7x per slot, so the
--   three `natrec`s elaborated together do not fit.  `Def`-splitting alone
--   was not enough there either; the FILE had to split.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

conv₂I : {Γ : Cx} →
         subTy nrs (MI₂ {Γ})
       ≅ᵀ indG (plusTm uA₃ uB₃) (subTm (single μAB) f₃) uA₃ uB₃
conv₂I = indG-red probe₂-s

-- ⚠ `{⌊ Γ ⌋}` PINNED on the conversion: `MI₂` is a DEFINED function and
--   `⌊_⌋` is not injective, so the raw context never solves from the
--   expected type.  Same trap as `PAtR-gcd` at `Ctx`.
split2 : {Γ : Ctx} →
         Prv (ΘI₂ Γ) (subTy (single (fst (var (vs (vs vz))))) MI₂)
split2 {Γ} = prv _ (⊢natrec ⊢MI₂ (prvOk leafI₂z)
                            (⊢conv (prvOk split3app) (csymᵀ (conv₂I {⌊ Γ ⌋})))
                            (⊢fst (⊢var (there (there here)))))

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdDvdA5
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 · EXAMPLES — gap B layer 2, ASSEMBLY PART A5.
-- ⚠⚠ SPLIT ACROSS SIX MODULES FOR COST, AND IT IS A MEASUREMENT.  As ONE
--   module the assembly OOM-KILLED (exit 143, uncontended) — the same wall
--   `…GcdStepExtA1` records for `StepExt`, and for the same reason: split
--   3's leaves sit at context depth 10 and cost is ~1.7x per slot, so the
--   three `natrec`s elaborated together do not fit.  `Def`-splitting alone
--   was not enough there either; the FILE had to split.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

conv₁I : {Γ : Cx} →
         subTy nrs (MI₁ {Γ}) ≅ᵀ subTy (single (fst (var (vs (vs vz))))) MI₂
conv₁I = indG-red probe₁-s

------------------------------------------------------------------------
-- ★★★★★ THE STATEMENT AT THE GENERIC CARRIER…
------------------------------------------------------------------------

gcdInd : {Γ : Ctx} →
         Prv (Γ ▹ PairT) (indG msr gcdBody (fst (var vz)) (snd (var vz)))
gcdInd {Γ} = prv _ (⊢natrec ⊢MI₁ (prvOk leafI₁z)
                            (⊢conv (prvOk split2) (csymᵀ (conv₁I {⌊ Γ ⌋})))
                            (⊢snd (⊢var here)))

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdDvdA
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 · EXAMPLES — gap B layer 2, ASSEMBLY PART A.
-- ⚠⚠ SPLIT ACROSS SIX MODULES FOR COST, AND IT IS A MEASUREMENT.  As ONE
--   module the assembly OOM-KILLED (exit 143, uncontended) — the same wall
--   `…GcdStepExtA1` records for `StepExt`, and for the same reason: split
--   3's leaves sit at context depth 10 and cost is ~1.7x per slot, so the
--   three `natrec`s elaborated together do not fit.  `Def`-splitting alone
--   was not enough there either; the FILE had to split.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

-- ★★★★★★ …AND `IndStep`, DISCHARGED.
------------------------------------------------------------------------

gcdIndStep : {Δ : Ctx} → IndStep Δ PairT ⌜Nat⌝ msr gcdStp gcdP
-- ⚠ `ρ` is BOUND and PASSED: `PAtR` is a defined function, so the ambient
--   renaming never solves from the goal.
gcdIndStep {Δ} {Θ} {ρ} hρ a ih da dih pw =
  prv-cast (cong El (sym (PAtR-gcd ρ a (app (app gcdStp a) ih))))
    (prv _ (⊢conv (indGElim (⊢-cast (indG-sub {σ = single a}
                                       msr gcdBody (fst (var vz)) (snd (var vz)))
                                    (⊢[] (prvOk gcdInd) da))
                            dih
                            (prvOk (indPWIntro (⊢plus (⊢fst da) (⊢snd da)) pw)))
                  (csymᵀ (QCode-conv (fst a) (snd a) (red-β a ih)))))
