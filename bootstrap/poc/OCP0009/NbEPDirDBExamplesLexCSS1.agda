------------------------------------------------------------------------
-- ⚠⚠⚠ THIS MODULE IS **RED**.  IT DOES NOT TYPECHECK — IT RUNS OUT OF
--     MEMORY.  Do not read it as a verified derivation; it is a MEASURED
--     NEGATIVE RESULT, kept so the next session does not redo it.
--
--     LexCSS1  OOM after 105 s   LexCSS2  OOM after 147-151 s
--     (5.5 GB cgroup cap; `+RTS -c` retried on SS2, still OOM.)
--
--     Only the DATA module (LexCSSData, 3.6 s / 0.39 GB) is green, and
--     the assembly (LexCSS) cannot be checked while its inputs are red.
--
-- ★ WHAT THAT MEASURES.  Branch (S,S) does NOT fit under option C, and
--   under option B it did — as four modules at 4.37 / 5.05 GB peak.  The
--   full option-C series:
--       (0,0)   2.2× faster, 2.3× lighter than B      one module
--       (0,S)   1.2× / 1.1×                           one module
--       (S,0)   needs a 4-way split B did not need    peak 4.19 GB
--       (S,S)   DOES NOT FIT AT ALL                   both halves OOM
--
-- ★★ AND IT REFUTES THE DEPTH MODEL FOR THIS SETTING.  ΓSS is 8 slots
--   under C against 12 under B, so ~1.7×/slot predicts C should be ~8×
--   CHEAPER.  It is instead too big to finish.  So context depth is NOT
--   what drives cost once the data are ABSTRACT: what drives it is the
--   `w`-tower depth on opaque terms — `renTm vs` iterated 11-14 times
--   around `cP`/`μ₁`/`μ₂` — which every conversion check must traverse.
--   Under Γ₅ those were VARIABLES, and `var (vs^k vz)` is cheap.
--
--   ⚠ SO DO NOT "FIX" THIS BY SPLITTING FURTHER.  Splitting helps when a
--     MODULE is too big; here a SINGLE DERIVATION is.  The lever, if
--     there is one, is shortening the towers — hoisting `w^k cP` into
--     `Def`s so conversion can hit a name instead of walking a chain.
--     UNTESTED.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- BRANCH (S,S), rec₁ — THE OUTER DESCENT, under option C.
--
-- (S,0)'s rec₁ at two more context slots: the OUTER IH is `lexAuxMot`, so
-- the reassociation is `auxMotB-w⁹`, and the spine is again FOUR ⊢apps
-- with one fitting lemma each.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexCSS1 where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd
  using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLexC
open import poc.OCP0009.NbEPDirDBExamplesLexCMot
open import poc.OCP0009.NbEPDirDBExamplesLexCSSData using ( module SSD )

module SS1 (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂) where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SSD Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  IH1-w⁹ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (lexAuxMot)))))))))
         ≡ auxMotB (w (w (w (w (w (w (w (w (w (w cA)))))))))) (w (w (w (w (w (w (w (w (w (w cP)))))))))) (w (w (w (w (w (w (w (w (w (w μ₁)))))))))) (w (w (w (w (w (w (w (w (w (w μ₂)))))))))) (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))
  IH1-w⁹ = auxMotB-w⁹ (w cA) (w cP) (w μ₁) (w μ₂) (var vz)

  cA-fit : subTm (single nSS) (w (w (w (w (w (w (w (w (w (w (w cA))))))))))) ≡ (w (w (w (w (w (w (w (w (w (w cA))))))))))
  cA-fit = wk-single {v = nSS} (w (w (w (w (w (w (w (w (w (w cA))))))))))

  μ₁-fit : subTm (single (var (vs vz))) (subTm (extS (single nSS)) (w (w (w (w (w (w (w (w (w (w (w (w μ₁))))))))))))) ≡ (w (w (w (w (w (w (w (w (w (w μ₁))))))))))
  μ₁-fit =
    trans (cong (subTm (single (var (vs vz))))
                (trans (sub-w {σ = single nSS} (w (w (w (w (w (w (w (w (w (w (w μ₁))))))))))))
                       (cong w (wk-single {v = nSS} (w (w (w (w (w (w (w (w (w (w μ₁))))))))))))))
          (wk-single {v = (var (vs vz))} (w (w (w (w (w (w (w (w (w (w μ₁)))))))))))

  μ₂-fit : subTm (single ltSS)
             (subTm (extS (single (var (vs vz))))
               (subTm (extS (extS (single nSS))) (w (w (w (w (w (w (w (w (w (w (w (w (w μ₂)))))))))))))))
         ≡ (w (w (w (w (w (w (w (w (w (w μ₂))))))))))
  μ₂-fit =
    trans (cong (λ z → subTm (single ltSS) (subTm (extS (single (var (vs vz)))) z))
                (trans (sub-w² {σ = single nSS} (w (w (w (w (w (w (w (w (w (w (w μ₂))))))))))))
                       (cong (λ z → w (w z)) (wk-single {v = nSS} (w (w (w (w (w (w (w (w (w (w μ₂))))))))))))))
    (trans (cong (subTm (single ltSS))
                 (trans (sub-w {σ = single (var (vs vz))} (w (w (w (w (w (w (w (w (w (w (w μ₂))))))))))))
                        (cong w (wk-single {v = (var (vs vz))} (w (w (w (w (w (w (w (w (w (w μ₂))))))))))))))
           (wk-single {v = ltSS} (w (w (w (w (w (w (w (w (w (w μ₂))))))))))))

  n-fit : subTm (single ltSS) (subTm (extS (single (var (vs vz)))) (w (w nSS))) ≡ nSS
  n-fit =
    trans (cong (subTm (single ltSS))
                (trans (sub-w {σ = single (var (vs vz))} (w nSS))
                       (cong w (wk-single {v = (var (vs vz))} nSS))))
          (wk-single {v = ltSS} nSS)

  ihPcancel : subTm (single (reflTm nSS))
                (subTm (extS (single ltSS))
                  (subTm (extS (extS (single (var (vs vz)))))
                    (subTm (extS (extS (extS (single nSS)))) (w (w (w (w (w (w (w (w (w (w (w (w (w (w cP)))))))))))))))))
            ≡ (w (w (w (w (w (w (w (w (w (w cP))))))))))
  ihPcancel =
    trans (cong (λ z → subTm (single (reflTm nSS)) (subTm (extS (single ltSS)) (subTm (extS (extS (single (var (vs vz))))) z)))
                (trans (sub-w³ {σ = single nSS} (w (w (w (w (w (w (w (w (w (w (w cP))))))))))))
                       (cong (λ z → w (w (w z))) (wk-single {v = nSS} (w (w (w (w (w (w (w (w (w (w cP))))))))))))))
    (trans (cong (λ z → subTm (single (reflTm nSS)) (subTm (extS (single ltSS)) z))
                 (trans (sub-w² {σ = single (var (vs vz))} (w (w (w (w (w (w (w (w (w (w (w cP))))))))))))
                        (cong (λ z → w (w z)) (wk-single {v = (var (vs vz))} (w (w (w (w (w (w (w (w (w (w cP))))))))))))))
    (trans (cong (subTm (single (reflTm nSS)))
                 (trans (sub-w {σ = single ltSS} (w (w (w (w (w (w (w (w (w (w (w cP))))))))))))
                        (cong w (wk-single {v = ltSS} (w (w (w (w (w (w (w (w (w (w cP))))))))))))))
           (wk-single {v = reflTm nSS} (w (w (w (w (w (w (w (w (w (w cP)))))))))))))

  ⊢lexSSrec1 : ΓSS ⊢ lexSSrec1
             ∷ rec1T (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (var (vs (vs vz)))
  ⊢lexSSrec1 =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcA))))))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))))) (⊢var here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))))) (⊢var (there (there (there here)))))) (⊢-cast (cong (λ z → El (app z (var (vs vz)))) ihPcancel) (⊢app (⊢app (⊢app (⊢app (⊢-cast IH1-w⁹ (⊢var (there (there (there (there (there (there (there (there here)))))))))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))))) (⊢var (there here)))) (⊢-cast (sym (cong El cA-fit)) (⊢var (there here)))) (⊢-cast (sym (cong (λ z → Hom Nat (app z (var (vs vz))) (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) μ₁-fit)) (⊢strong-step (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))))))))) (⊢var (there here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))))))))) (⊢var (there (there (there (there here)))))) (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var here) (⊢var (there (there (there here))))))) (⊢-cast (sym (cong₂ (λ z z' → Hom Nat (app z (var (vs vz))) z') μ₂-fit n-fit)) (⊢le-refl (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))))) (⊢var (there here))))))))
