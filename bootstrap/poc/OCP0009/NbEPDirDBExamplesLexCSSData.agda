------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (S,S) under option C, SHARED DATA: the
-- context and the two recursor arguments as raw terms.
--
-- ★ THE BRANCH THE WHOLE FILE EXISTS TO REACH: the only one where BOTH
--   recursor arguments are LIVE.  rec₁ calls the OUTER IH (n₁ down, n₂
--   reset); rec₂ calls the INNER one (n₁ held, n₂ down).
--
-- ⚠⚠ THIS MODULE IS GREEN (3.6 s / 0.39 GB) BUT ITS CONSUMERS ARE NOT.
--   `LexCSS1` and `LexCSS2` both OOM at the 5.5 GB cap, so branch (S,S)
--   is NOT ported under option C — see their headers for the measurement
--   and for why splitting further is not the answer.
--
-- ctx: vz = lt, vs = le, vs² = x, vs³ = IH₂, vs⁴ = m, vs⁵ = n₂,
--      vs⁶ = IH₁, vs⁷ = n₁', then Δ
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexCSSData where

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
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibOrd
  using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesLexC

module SSD (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂) where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  ΓSS : Ctx
  ΓSS =
    (((((((Δ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ▹ Nat) ▹ M1lex) ▹ El (w (w (w (w (w cA))))))
       ▹ Hom Nat (app (w (w (w (w (w (w μ₁)))))) (var vz)) (nsuc (var (vs (vs (vs (vs (vs vz))))))))
       ▹ Hom Nat (app (w (w (w (w (w (w (w μ₂))))))) (var (vs vz))) (nsuc (var (vs (vs (vs vz)))))

  -- rec₁: the OUTER descent — n₂ := μ₂ y (the RESET), then y, then
  -- μ₁ y ≤ n₁' by ⊢strong-step, then μ₂ y ≤ μ₂ y by ⊢le-refl.
  nSS : RTm (⌊ ΓSS ⌋ ∙ ∙)
  nSS = app (w (w (w (w (w (w (w (w (w (w μ₂)))))))))) (var (vs vz))

  ltSS : RTm (⌊ ΓSS ⌋ ∙ ∙)
  ltSS = ordtr (nsuc (app (w (w (w (w (w (w (w (w (w (w μ₁)))))))))) (var (vs vz)))) (app (w (w (w (w (w (w (w (w (w (w μ₁)))))))))) (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var vz) (var (vs (vs (vs vz))))

  lexSSrec1 : RTm ⌊ ΓSS ⌋
  lexSSrec1 =
    lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) nSS) (var (vs vz))) ltSS) (reflTm nSS)))

  -- rec₂: the INNER descent — n₁ HELD (μ₁ y ≤ nsuc n₁' by plain ⊢ordtr),
  -- n₂ strictly down (μ₂ y ≤ m by ⊢strong-step).
  leSS₂ : RTm (⌊ ΓSS ⌋ ∙ ∙ ∙)
  leSS₂ = ordtr (app (w (w (w (w (w (w (w (w (w (w (w μ₁))))))))))) (var (vs (vs vz)))) (app (w (w (w (w (w (w (w (w (w (w (w μ₁))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz)) (var (vs (vs (vs (vs vz)))))

  ltSS₂ : RTm (⌊ ΓSS ⌋ ∙ ∙ ∙)
  ltSS₂ = ordtr (nsuc (app (w (w (w (w (w (w (w (w (w (w (w μ₂))))))))))) (var (vs (vs vz))))) (app (w (w (w (w (w (w (w (w (w (w (w μ₂))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))

  lexSSrec2 : RTm ⌊ ΓSS ⌋
  lexSSrec2 =
    lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) leSS₂) ltSS₂)))
