------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (0,0) UNDER FAMILIES.
--
-- ★ THE SHALLOW BRANCH, and the only one where BOTH recursor arguments
--   are VACUOUS: n₁ = 0 kills every μ₁-descent and n₂ = 0 every
--   μ₂-descent, so rec₁ and rec₂ are both `⊢strong-base'` — ex falso
--   through `Hom Nat (nsuc k) nzero ⟶ᵀ* base`.
--
-- ⚠ NOT the gate, and not evidence about it.  (0,0) applies no IH at
--   all, which is exactly why option C looked good here (2.2× / 2.3×)
--   and then died at (S,S).  It is included because `⊢lexrec` needs four
--   branches, not because it measures anything.
--
-- ctx: vz = lt, vs = le, vs² = x, vs³ = n₂, then Δ
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibLexrecZZ where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; lam; app; absurd; ordtr
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El; ty-Π )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; ren-ty )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base' )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; cong₆; sub-w; sub-w²; wk-singleTy; wᶠ-single
        ; wᶠ³-single; w^; wTy^; wᶠ^; ⊢wkᶠ; sub-wTy )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat; aIHT; aIHT-fit )
open import poc.OCP0009.NbEPDirDBLibLexrecT
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )

module ZZ (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m₁ m₂ : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
          (dA   : Δ ⊢ty A)
          (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
          (dm₁  : (Δ ▹ A) ⊢ m₁ ∷ Nat)
          (dm₂  : (Δ ▹ A) ⊢ m₂ ∷ Nat)
          (dstp : Δ ⊢ stp ∷ lStepT A cM m₁ m₂)
          where

  -- ⚠ THE SAME `mot` as `SpikeLexT.ZS` — written out rather than reached
  --   into, so the two branches are provably about one inner recursor.
  mot : RTy ((⌊ Δ ⌋ ∙) ∙)
  mot = M0lex (wTy^ 1 A) (wᶠ^ 1 cM) (wᶠ^ 1 m₁) (wᶠ^ 1 m₂)

  -- the ZERO instance of that motive: both bounds land on `nzero`.
  mot-z : subTy (single nzero) mot
        ≡ auxB (wTy^ 1 A) (wᶠ^ 1 cM) (wᶠ^ 1 m₁) (wᶠ^ 1 m₂) nzero nzero
  mot-z =
    trans (auxB-sub {σ = single nzero} (wTy^ 2 A) (wᶠ^ 2 cM) (wᶠ^ 2 m₁)
                    (wᶠ^ 2 m₂) nzero (var vz))
          (cong₆ auxB (wk-singleTy {v = nzero} (wTy^ 1 A))
                      (wᶠ-single {v = nzero} (wᶠ^ 1 cM))
                      (wᶠ-single {v = nzero} (wᶠ^ 1 m₁))
                      (wᶠ-single {v = nzero} (wᶠ^ 1 m₂)) refl refl)

  ZZCtx : Ctx
  ZZCtx =
    (((Δ ▹ Nat) ▹ wTy^ 1 A) ▹ Hom Nat (wᶠ^ 1 m₁) nzero)
       ▹ Hom Nat (w (wᶠ^ 1 m₂)) nzero

  ------------------------------------------------------------------------
  -- the shared premises.  ★ `dmX` is the depth-independent shape again:
  --   THREE ordinary weakenings above the carrier slot, `⊢wkᶠ` for the
  --   one slot below it.
  ------------------------------------------------------------------------

  tyA₄ : ZZCtx ⊢ty wTy^ 4 A
  tyA₄ = ren-ty (ren-ty (ren-ty (ren-ty dA there) there) there) there

  dk₁ : (ZZCtx ▹ wTy^ 4 A) ⊢ wᶠ^ 4 m₁ ∷ Nat
  dk₁ = ⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁)))

  dk₂ : (ZZCtx ▹ wTy^ 4 A) ⊢ wᶠ^ 4 m₂ ∷ Nat
  dk₂ = ⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂)))

  dmX : (ZZCtx ▹ wTy^ 4 A) ⊢ w (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₁)) ∷ Nat
  dmX = subst (λ z → (ZZCtx ▹ wTy^ 4 A) ⊢ z ∷ Nat)
              (sym (cong w (wᶠ³-single (wᶠ^ 1 m₁))))
              (⊢wk (⊢wk (⊢wk (⊢wkᶠ dm₁))))

  dmX₂ : (ZZCtx ▹ wTy^ 4 A) ⊢ w (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₂)) ∷ Nat
  dmX₂ = subst (λ z → (ZZCtx ▹ wTy^ 4 A) ⊢ z ∷ Nat)
               (sym (cong w (wᶠ³-single (wᶠ^ 1 m₂))))
               (⊢wk (⊢wk (⊢wk (⊢wkᶠ dm₂))))

  ------------------------------------------------------------------------
  -- rec₁ — VACUOUS on μ₁: μ₁ y < μ₁ x ≤ 0.
  ------------------------------------------------------------------------

  rec1tm : RTm ⌊ ZZCtx ⌋
  rec1tm =
    lam (lam (absurd (w (wᶠ^ 4 cM))
                     (ordtr (nsuc (w (wᶠ^ 4 m₁)))
                            (w (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₁))))
                            nzero (var vz) (var (vs (vs (vs vz)))))))

  ⊢rec1 : ZZCtx ⊢ rec1tm
        ∷ aIHTat (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁)
                 (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₁))
  ⊢rec1 =
    ⊢lam tyA₄
      (⊢lam (ty-Hom ty-Nat (⊢nsuc dk₁) dmX)
        (⊢strong-base' (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dcM)))))
                       (⊢wk dk₁) (⊢wk dmX) (⊢var here)
                       (⊢-cast (cong (λ z → Hom Nat (w (w z)) nzero)
                                     (sym (wᶠ³-single (wᶠ^ 1 m₁))))
                               (⊢var (there (there (there here)))))))

  ------------------------------------------------------------------------
  -- rec₂ — VACUOUS on μ₂ this time: μ₂ y < μ₂ x ≤ 0.  ★ Same lemma, the
  --   OTHER measure; the μ₁ hypothesis is simply never used.
  ------------------------------------------------------------------------

  rec2tm : RTm ⌊ ZZCtx ⌋
  rec2tm =
    lam (lam (lam (absurd (w (w (wᶠ^ 4 cM)))
                          (ordtr (nsuc (w (w (wᶠ^ 4 m₂))))
                                 (w (w (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₂)))))
                                 nzero (var vz) (var (vs (vs (vs vz))))))))

  ⊢rec2 : ZZCtx ⊢ rec2tm
        ∷ rec2Tat (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁) (wᶠ^ 4 m₂)
                  (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₁))
                  (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₂))
  ⊢rec2 =
    ⊢lam tyA₄
      (⊢lam (ty-Hom ty-Nat dk₁ dmX)
        (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢wk dk₂)) (⊢wk dmX₂))
          (⊢strong-base' (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dcM))))))
                         (⊢wk (⊢wk dk₂)) (⊢wk (⊢wk dmX₂)) (⊢var here)
                         (⊢-cast (cong (λ z → Hom Nat (w (w (w z))) nzero)
                                       (sym (wᶠ³-single (wᶠ^ 1 m₂))))
                                 (⊢var (there (there (there here))))))))

  ------------------------------------------------------------------------
  -- BRANCH (0,0), ASSEMBLED.
  ------------------------------------------------------------------------

  lexZZ : RTm (⌊ Δ ⌋ ∙)
  lexZZ =
    lam (lam (lam (app (app (app (w^ 4 stp) (var (vs (vs vz)))) rec1tm) rec2tm)))

  stp-w⁴ : wTy^ 4 (lStepT A cM m₁ m₂)
         ≡ lStepT (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁) (wᶠ^ 4 m₂)
  stp-w⁴ = lStepT-w^ 4 A cM m₁ m₂

  rec1-fit : subTy (single (var (vs (vs vz))))
                   (rec1T (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁))
           ≡ aIHTat (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁)
                    (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₁))
  rec1-fit = aIHT-fit (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁)

  rec2-fit : subTy (single rec1tm)
               (subTy (extS (single (var (vs (vs vz)))))
                      (renTy vs (rec2T (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁) (wᶠ^ 4 m₂))))
           ≡ rec2Tat (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁) (wᶠ^ 4 m₂)
                     (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₁))
                     (subTm (single (var (vs (vs vz)))) (wᶠ^ 4 m₂))
  rec2-fit =
    trans (cong (subTy (single rec1tm))
                (sub-wTy {σ = single (var (vs (vs vz)))}
                         (rec2T (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁) (wᶠ^ 4 m₂))))
          (trans (wk-singleTy {v = rec1tm}
                    (subTy (single (var (vs (vs vz))))
                           (rec2T (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁) (wᶠ^ 4 m₂))))
                 (rec2T-fit (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁) (wᶠ^ 4 m₂)))

  cMcancel : subTm (single rec2tm)
               (subTm (extS (single rec1tm))
                 (subTm (extS (extS (single (var (vs (vs vz))))))
                        (w (w (wᶠ^ 4 cM)))))
           ≡ w (w (wᶠ^ 1 cM))
  cMcancel =
    trans (cong (λ z → subTm (single rec2tm) (subTm (extS (single rec1tm)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (wᶠ^ 4 cM))
                       (cong (λ z → w (w z)) (wᶠ³-single (wᶠ^ 1 cM)))))
          (trans (cong (subTm (single rec2tm))
                       (trans (sub-w {σ = single rec1tm} (w (w (w (wᶠ^ 1 cM)))))
                              (cong w (wk-single {v = rec1tm} (w (w (wᶠ^ 1 cM)))))))
                 (wk-single {v = rec2tm} (w (w (wᶠ^ 1 cM)))))

  ⊢lexZZ : (Δ ▹ Nat) ⊢ lexZZ ∷ subTy (single nzero) mot
  ⊢lexZZ =
    ⊢-cast (sym mot-z)
      (⊢lam (ren-ty dA there)
        (⊢lam (ty-Hom ty-Nat (⊢wkᶠ dm₁) ⊢nzero)
          (⊢lam (ty-Hom ty-Nat (⊢wk (⊢wkᶠ dm₂)) ⊢nzero)
            (⊢-cast (cong El cMcancel)
              (⊢app (⊢app (⊢app (⊢-cast stp-w⁴ (⊢wk (⊢wk (⊢wk (⊢wk dstp)))))
                                 (⊢var (there (there here))))
                          (⊢-cast (sym rec1-fit) ⊢rec1))
                    (⊢-cast (sym rec2-fit) ⊢rec2))))))
