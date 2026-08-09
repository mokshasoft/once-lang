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
-- OCP-0009 — LEXREC BRANCH (S,S) ASSEMBLED, at an ABSTRACT AMBIENT
-- CONTEXT.  Option C: there is no Γ₅.  See NbEPDirDBExamplesLexC.
--
-- ★ THE ONLY BRANCH WHERE BOTH RECURSOR ARGUMENTS ARE LIVE — the case the
--   whole development exists to reach.  Both are `Def`s from LexCSS1 and
--   LexCSS2, so this module is small.
--
-- The motive boundary is `subTy nrs M1lex`: the STEP instance of the
-- inner recursor at the SUCCESSOR outer motive, so BOTH bounds move —
-- μ₁'s to `nsuc n₁'` and μ₂'s to `nsuc m`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexCSS where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
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
open import poc.OCP0009.NbEPDirDBExamplesLexCSS1 using ( module SS1 )
open import poc.OCP0009.NbEPDirDBExamplesLexCSS2 using ( module SS2 )

module _ (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂) where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SSD Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SS1 Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SS2 Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  M1lex-nrs : subTy nrs M1lex
            ≡ auxBody (w (w (w (w (w cA))))) (w (w (w (w (w cP))))) (w (w (w (w (w μ₁))))) (w (w (w (w (w μ₂))))) (nsuc (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs vz)))
  M1lex-nrs =
    trans (auxBody-sub {σ = nrs} (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ₁)))) (w (w (w (w μ₂)))) (nsuc (var (vs (vs (vs vz))))) (var vz))
          (cong₆ auxBody (nrs-w (w (w (w cA)))) (nrs-w (w (w (w cP))))
                         (nrs-w (w (w (w μ₁)))) (nrs-w (w (w (w μ₂)))) refl refl)

  stp-w⁸ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (lStepT cA cP μ₁ μ₂))))))))
         ≡ lStepT (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂))))))))
  stp-w⁸ = lStepT-w⁸ cA cP μ₁ μ₂

  cPcancel : subTm (single lexSSrec2)
               (subTm (extS (single lexSSrec1))
                 (subTm (extS (extS (single (var (vs (vs vz)))))) (w (w (w (w (w (w (w (w (w (w (w cP)))))))))))))
           ≡ (w (w (w (w (w (w (w (w cP))))))))
  cPcancel =
    trans (cong (λ z → subTm (single lexSSrec2) (subTm (extS (single lexSSrec1)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (w (w (w (w (w (w (w (w (w cP))))))))))
                       (cong (λ z → w (w z)) (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w cP))))))))))))
    (trans (cong (subTm (single lexSSrec2))
                 (trans (sub-w {σ = single lexSSrec1} (w (w (w (w (w (w (w (w (w cP))))))))))
                        (cong w (wk-single {v = lexSSrec1} (w (w (w (w (w (w (w (w cP))))))))))))
           (wk-single {v = lexSSrec2} (w (w (w (w (w (w (w (w cP))))))))))

  rec1-fit : subTy (single (var (vs (vs vz)))) (rec1T (w (w (w (w (w (w (w (w (w cA))))))))) (w (w (w (w (w (w (w (w (w cP))))))))) (w (w (w (w (w (w (w (w (w μ₁))))))))) (var vz))
           ≡ rec1T (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (var (vs (vs vz)))
  rec1-fit =
    trans (rec1T-sub (w (w (w (w (w (w (w (w (w cA))))))))) (w (w (w (w (w (w (w (w (w cP))))))))) (w (w (w (w (w (w (w (w (w μ₁))))))))) (var vz))
          (cong₄ rec1T (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w cA))))))))) (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w cP)))))))))
                       (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w μ₁))))))))) refl)

  rec2-fit : subTy (single lexSSrec1)
               (subTy (extS (single (var (vs (vs vz)))))
                 (rec2T (w (w (w (w (w (w (w (w (w (w cA)))))))))) (w (w (w (w (w (w (w (w (w (w cP)))))))))) (w (w (w (w (w (w (w (w (w (w μ₁)))))))))) (w (w (w (w (w (w (w (w (w (w μ₂)))))))))) (var (vs vz))))
           ≡ rec2T (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂)))))))) (var (vs (vs vz)))
  rec2-fit =
    trans (cong (subTy (single lexSSrec1))
            (trans (rec2T-sub (w (w (w (w (w (w (w (w (w (w cA)))))))))) (w (w (w (w (w (w (w (w (w (w cP)))))))))) (w (w (w (w (w (w (w (w (w (w μ₁)))))))))) (w (w (w (w (w (w (w (w (w (w μ₂)))))))))) (var (vs vz)))
                   (cong₅ rec2T (trans (sub-w (w (w (w (w (w (w (w (w (w cA)))))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w cA)))))))))))
                                (trans (sub-w (w (w (w (w (w (w (w (w (w cP)))))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w cP)))))))))))
                                (trans (sub-w (w (w (w (w (w (w (w (w (w μ₁)))))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w μ₁)))))))))))
                                (trans (sub-w (w (w (w (w (w (w (w (w (w μ₂)))))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w (w (w μ₂)))))))))))
                                refl)))
          (trans (rec2T-sub (w (w (w (w (w (w (w (w (w cA))))))))) (w (w (w (w (w (w (w (w (w cP))))))))) (w (w (w (w (w (w (w (w (w μ₁))))))))) (w (w (w (w (w (w (w (w (w μ₂))))))))) (w (var (vs (vs vz)))))
                 (cong₅ rec2T (wk-single {v = lexSSrec1} (w (w (w (w (w (w (w (w cA))))))))) (wk-single {v = lexSSrec1} (w (w (w (w (w (w (w (w cP)))))))))
                              (wk-single {v = lexSSrec1} (w (w (w (w (w (w (w (w μ₁))))))))) (wk-single {v = lexSSrec1} (w (w (w (w (w (w (w (w μ₂)))))))))
                              (wk-single {v = lexSSrec1} (var (vs (vs vz))))))

  ⊢lexSS : (((((Δ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ▹ Nat) ▹ M1lex) ⊢ lexSS ∷ subTy nrs M1lex
  ⊢lexSS =
    ⊢-cast (sym M1lex-nrs)
      (⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcA)))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))))) (⊢var here)) (⊢nsuc (⊢var (there (there (there (there (there here)))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂))))))) (⊢var (there here))) (⊢nsuc (⊢var (there (there (there here)))))) (⊢-cast (cong (λ z → El (app z (var (vs (vs vz))))) cPcancel) (⊢app (⊢app (⊢app (⊢-cast stp-w⁸ (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dstp))))))))) (⊢var (there (there here)))) (⊢-cast (sym rec1-fit) ⊢lexSSrec1)) (⊢-cast (sym rec2-fit) ⊢lexSSrec2))))))
