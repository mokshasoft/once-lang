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
-- BRANCH (S,S), rec₂ — THE INNER DESCENT, under option C.
--
-- (0,S)'s rec₂ at two more context slots, with one difference that
-- matters: the μ₁ obligation is `μ₁ y ≤ nsuc n₁'`, not `μ₁ y ≤ 0`, so it
-- is a plain ⊢ordtr rather than a collapse.  n₁ is HELD; n₂ goes strictly
-- down, and THAT is `⊢strong-step`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexCSS2 where

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
        ; ty-Nat; ty-Hom; ty-El; wk-single )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibOrd
  using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLexC
open import poc.OCP0009.NbEPDirDBExamplesLexCSSData using ( module SSD )

module SS2 (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂) where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SSD Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  -- the INNER IH, reassociated: `M1lex` is an `auxBody`, so this is
  -- `auxBody-w⁷` — NOT the `auxMotB` ladder rec₁ needs.
  IH2-w⁷ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (M1lex)))))))
         ≡ auxBody (w (w (w (w (w (w (w (w (w (w (w cA))))))))))) (w (w (w (w (w (w (w (w (w (w (w cP))))))))))) (w (w (w (w (w (w (w (w (w (w (w μ₁))))))))))) (w (w (w (w (w (w (w (w (w (w (w μ₂))))))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
  IH2-w⁷ = auxBody-w⁷ (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ₁)))) (w (w (w (w μ₂)))) (nsuc (var (vs (vs (vs vz))))) (var vz)

  μ₁-fit : subTm (single (var (vs (vs vz)))) (w (w (w (w (w (w (w (w (w (w (w (w μ₁)))))))))))) ≡ (w (w (w (w (w (w (w (w (w (w (w μ₁)))))))))))
  μ₁-fit = wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w (w (w μ₁)))))))))))

  μ₂-fit : subTm (single leSS₂) (subTm (extS (single (var (vs (vs vz))))) (w (w (w (w (w (w (w (w (w (w (w (w (w μ₂)))))))))))))) ≡ (w (w (w (w (w (w (w (w (w (w (w μ₂)))))))))))
  μ₂-fit =
    trans (cong (subTm (single leSS₂))
                (trans (sub-w {σ = single (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w (w (w (w μ₂)))))))))))))
                       (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w (w (w μ₂)))))))))))))))
          (wk-single {v = leSS₂} (w (w (w (w (w (w (w (w (w (w (w μ₂))))))))))))

  ihPcancel : subTm (single ltSS₂)
                (subTm (extS (single leSS₂))
                  (subTm (extS (extS (single (var (vs (vs vz)))))) (w (w (w (w (w (w (w (w (w (w (w (w (w (w cP))))))))))))))))
            ≡ (w (w (w (w (w (w (w (w (w (w (w cP)))))))))))
  ihPcancel =
    trans (cong (λ z → subTm (single ltSS₂) (subTm (extS (single leSS₂)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w (w (w (w cP)))))))))))))
                       (cong (λ z → w (w z)) (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w (w (w cP)))))))))))))))
    (trans (cong (subTm (single ltSS₂))
                 (trans (sub-w {σ = single leSS₂} (w (w (w (w (w (w (w (w (w (w (w (w cP)))))))))))))
                        (cong w (wk-single {v = leSS₂} (w (w (w (w (w (w (w (w (w (w (w cP)))))))))))))))
           (wk-single {v = ltSS₂} (w (w (w (w (w (w (w (w (w (w (w cP)))))))))))))

  ⊢lexSSrec2 : ΓSS ⊢ lexSSrec2
             ∷ rec2T (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂)))))))) (var (vs (vs vz)))
  ⊢lexSSrec2 =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcA))))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))))) (⊢var here)) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))))) (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))))) (⊢var (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))))) (⊢var (there (there (there (there here))))))) (⊢-cast (cong (λ z → El (app z (var (vs (vs vz))))) ihPcancel) (⊢app (⊢app (⊢app (⊢-cast IH2-w⁷ (⊢var (there (there (there (there (there (there here)))))))) (⊢var (there (there here)))) (⊢-cast (sym (cong (λ z → Hom Nat (app z (var (vs (vs vz)))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) μ₁-fit)) (⊢ordtr (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))))))) (⊢var (there (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))))))) (⊢var (there (there (there (there (there here))))))) (⊢nsuc (⊢var (there (there (there (there (there (there (there (there (there (there here)))))))))))) (⊢var (there here)) (⊢var (there (there (there (there here)))))))) (⊢-cast (sym (cong (λ z → Hom Nat (app z (var (vs (vs vz)))) (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) μ₂-fit)) (⊢strong-step (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂))))))))))) (⊢var (there (there here)))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂))))))))))) (⊢var (there (there (there (there (there here))))))) (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var here) (⊢var (there (there (there here))))))))))
