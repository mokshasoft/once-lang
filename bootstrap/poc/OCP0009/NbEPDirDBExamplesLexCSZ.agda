------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (S,0) ASSEMBLED, at an ABSTRACT AMBIENT
-- CONTEXT.  Option C: there is no Γ₅.  See NbEPDirDBExamplesLexC.
--
-- ⚠⚠ THIS BRANCH IS WHERE OPTION C STOPS PAYING.  Option B fit (S,0) in
--   ONE module at 70.5 s / 5.16 GB.  Option C needs FOUR — as one module
--   it OOMs at the 5.5 GB cap.  Split it is 69.2 s all told (data 3.1,
--   rec₁ 35.2, rec₂ 24.6, this 6.2) with a 4.19 GB peak: the same wall
--   clock as B, a lower PEAK, but a strictly larger TOTAL.
--
--   The trend across the branches ported so far:
--       (0,0)  2.2× faster, 2.3× lighter   ΓZZ = 4 slots, no IH applied
--       (0,S)  1.2× / 1.1×                 ΓZS = 6, inner IH applied
--       (S,0)  WORSE — needs a 4-way split ΓSZ = 6, OUTER IH applied
--
--   The saving is linear-ish in slots removed; the naturality kit's cost
--   grows with how DEEPLY the IH is applied — `auxMotB-w⁷` plus one
--   fitting lemma per ⊢app argument, four of them here.  Past (0,S) the
--   second term wins.  Under Γ₅ these were free: the data were context
--   VARIABLES, so instantiating a motive COMPUTED.
--
-- Both recursor arguments are `Def`s from LexCSZ1/LexCSZ2, so this module
-- is small — the outer spine is (0,S)'s verbatim.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexCSZ where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd
  using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLexC
open import poc.OCP0009.NbEPDirDBExamplesLexCSZData using ( module SZD )
open import poc.OCP0009.NbEPDirDBExamplesLexCSZ1 using ( module SZ1 )
open import poc.OCP0009.NbEPDirDBExamplesLexCSZ2 using ( module SZ2 )

module _ (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂) where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SZD Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SZ1 Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SZ2 Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  -- ★ THE MOTIVE BOUNDARY — the ZERO instance, `M1lex` at n₂ := 0.  The
  --   μ₁-bound `nsuc n₁'` rides through untouched.
  M1lex-sub : subTy (single nzero) M1lex
            ≡ auxBody (w (w (w cA))) (w (w (w cP))) (w (w (w μ₁))) (w (w (w μ₂))) (nsuc (var (vs (vs vz)))) nzero
  M1lex-sub =
    trans (auxBody-sub {σ = single nzero} (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ₁)))) (w (w (w (w μ₂)))) (nsuc (var (vs (vs (vs vz))))) (var vz))
          (cong₆ auxBody (wk-single {v = nzero} (w (w (w cA)))) (wk-single {v = nzero} (w (w (w cP))))
                         (wk-single {v = nzero} (w (w (w μ₁)))) (wk-single {v = nzero} (w (w (w μ₂))))
                         refl refl)

  stp-w⁶ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (lStepT cA cP μ₁ μ₂))))))
         ≡ lStepT (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (w (w (w (w (w (w μ₂))))))
  stp-w⁶ = lStepT-w⁶ cA cP μ₁ μ₂

  cPcancel : subTm (single lexSZrec2)
               (subTm (extS (single lexSZrec1))
                 (subTm (extS (extS (single (var (vs (vs vz)))))) (w (w (w (w (w (w (w (w (w cP)))))))))))
           ≡ (w (w (w (w (w (w cP))))))
  cPcancel =
    trans (cong (λ z → subTm (single lexSZrec2) (subTm (extS (single lexSZrec1)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (w (w (w (w (w (w (w cP))))))))
                       (cong (λ z → w (w z)) (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cP))))))))))
    (trans (cong (subTm (single lexSZrec2))
                 (trans (sub-w {σ = single lexSZrec1} (w (w (w (w (w (w (w cP))))))))
                        (cong w (wk-single {v = lexSZrec1} (w (w (w (w (w (w cP))))))))))
           (wk-single {v = lexSZrec2} (w (w (w (w (w (w cP))))))))

  rec1-fit : subTy (single (var (vs (vs vz)))) (rec1T (w (w (w (w (w (w (w cA))))))) (w (w (w (w (w (w (w cP))))))) (w (w (w (w (w (w (w μ₁))))))) (var vz))
           ≡ rec1T (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (var (vs (vs vz)))
  rec1-fit =
    trans (rec1T-sub (w (w (w (w (w (w (w cA))))))) (w (w (w (w (w (w (w cP))))))) (w (w (w (w (w (w (w μ₁))))))) (var vz))
          (cong₄ rec1T (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cA))))))) (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cP)))))))
                       (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w μ₁))))))) refl)

  rec2-fit : subTy (single lexSZrec1)
               (subTy (extS (single (var (vs (vs vz)))))
                 (rec2T (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂)))))))) (var (vs vz))))
           ≡ rec2T (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (w (w (w (w (w (w μ₂)))))) (var (vs (vs vz)))
  rec2-fit =
    trans (cong (subTy (single lexSZrec1))
            (trans (rec2T-sub (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂)))))))) (var (vs vz)))
                   (cong₅ rec2T (trans (sub-w (w (w (w (w (w (w (w cA)))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cA)))))))))
                                (trans (sub-w (w (w (w (w (w (w (w cP)))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w cP)))))))))
                                (trans (sub-w (w (w (w (w (w (w (w μ₁)))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w μ₁)))))))))
                                (trans (sub-w (w (w (w (w (w (w (w μ₂)))))))) (cong w (wk-single {v = (var (vs (vs vz)))} (w (w (w (w (w (w μ₂)))))))))
                                refl)))
          (trans (rec2T-sub (w (w (w (w (w (w (w cA))))))) (w (w (w (w (w (w (w cP))))))) (w (w (w (w (w (w (w μ₁))))))) (w (w (w (w (w (w (w μ₂))))))) (w (var (vs (vs vz)))))
                 (cong₅ rec2T (wk-single {v = lexSZrec1} (w (w (w (w (w (w cA))))))) (wk-single {v = lexSZrec1} (w (w (w (w (w (w cP)))))))
                              (wk-single {v = lexSZrec1} (w (w (w (w (w (w μ₁))))))) (wk-single {v = lexSZrec1} (w (w (w (w (w (w μ₂)))))))
                              (wk-single {v = lexSZrec1} (var (vs (vs vz))))))

  ⊢lexSZ : (((Δ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ⊢ lexSZ ∷ subTy (single nzero) M1lex
  ⊢lexSZ =
    ⊢-cast (sym M1lex-sub)
      (⊢lam (ty-El (⊢wk (⊢wk (⊢wk dcA)))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))) (⊢var here)) (⊢nsuc (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂))))) (⊢var (there here))) ⊢nzero) (⊢-cast (cong (λ z → El (app z (var (vs (vs vz))))) cPcancel) (⊢app (⊢app (⊢app (⊢-cast stp-w⁶ (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dstp))))))) (⊢var (there (there here)))) (⊢-cast (sym rec1-fit) ⊢lexSZrec1)) (⊢-cast (sym rec2-fit) ⊢lexSZrec2))))))
