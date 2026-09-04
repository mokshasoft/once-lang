------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (S,0) UNDER FAMILIES.  The fourth and last.
--
-- ★ THE MIXED BRANCH, and it is exactly the two halves already built,
--   recombined:
--
--     rec₁  REAL — `SpikeLexSS.SS.⊢rec1` two slots shallower.  The outer
--           IH, the n₂ RESET at μ₂ y, `⊢strong-step` for μ₁ y ≤ n₁' and
--           `⊢le-refl` for the reset μ₂ obligation.
--     rec₂  VACUOUS — `SpikeLexZZ.ZZ.⊢rec2` verbatim in shape: n₂ = 0, so
--           μ₂ y < μ₂ x ≤ 0 and `⊢strong-base'` finishes it.  ⚠ The μ₁
--           hypothesis is live here (its bound is `suc n₁'`) and simply
--           goes unused — vacuity is on the μ₂ axis alone.
--
-- ⚠ Under codes-and-functions this branch "needed a 4-way split where
--   option B needed ONE module" (peak 4.19 GB).  It is one module here.
--
-- ctx: vz = lt, vs = le, vs² = x, vs³ = n₂, vs⁴ = IH₁, vs⁵ = n₁', then Δ
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexrecSZ where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; lam; app; absurd; ordtr
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El; ty-Π; wk-single )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; ren-ty )
open import DirectedHoTT.Lib.Ord using ( ⊢strong-base'; ⊢strong-step )
open import DirectedHoTT.Lib.Strong using ( ⊢le-refl; reflTm )
open import DirectedHoTT.Lib.Wk
  using ( w; wᶠ; cong₆; sub-w; sub-w²; wk-singleTy; wᶠ-single
        ; wᶠ²-single; wᶠ³-single; w^; wTy^; wᶠ^; ⊢wkᶠ; sub-wTy )
open import DirectedHoTT.Lib.Rec using ( aIHTat; aIHT; aIHT-fit )
open import DirectedHoTT.Negative.LexrecT
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )

module SZ (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m₁ m₂ : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
          (dA   : Δ ⊢ty A)
          (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
          (dm₁  : (Δ ▹ A) ⊢ m₁ ∷ Nat)
          (dm₂  : (Δ ▹ A) ⊢ m₂ ∷ Nat)
          (dstp : Δ ⊢ stp ∷ lStepT A cM m₁ m₂)
          where

  -- ⚠ SPELLED IDENTICALLY to `SpikeLexSS.SS` — the assembly needs these
  --   to be the same terms, not merely equal ones.
  omot : RTy (⌊ Δ ⌋ ∙)
  omot = lexMot (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) (var vz)

  imot : RTy (⌊ Δ ⌋ ∙ ∙ ∙ ∙)
  imot = M1lex (wTy^ 3 A) (wᶠ^ 3 cM) (wᶠ^ 3 m₁) (wᶠ^ 3 m₂) (var (vs (vs vz)))

  -- the ZERO instance: the μ₂-bound collapses to `nzero`, the μ₁-bound
  -- keeps its `suc n₁'` and just loses one slot.
  imot-z : subTy (single nzero) imot
         ≡ auxB (wTy^ 3 A) (wᶠ^ 3 cM) (wᶠ^ 3 m₁) (wᶠ^ 3 m₂)
                (nsuc (var (vs (vs vz)))) nzero
  imot-z =
    trans (auxB-sub {σ = single nzero} (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁)
                    (wᶠ^ 4 m₂) (nsuc (var (vs (vs (vs vz))))) (var vz))
          (cong₆ auxB (wk-singleTy {v = nzero} (wTy^ 3 A))
                      (wᶠ-single {v = nzero} (wᶠ^ 3 cM))
                      (wᶠ-single {v = nzero} (wᶠ^ 3 m₁))
                      (wᶠ-single {v = nzero} (wᶠ^ 3 m₂)) refl refl)

  SZCtx : Ctx
  SZCtx =
    (((((Δ ▹ Nat) ▹ omot) ▹ Nat) ▹ wTy^ 3 A)
       ▹ Hom Nat (wᶠ^ 3 m₁) (nsuc (var (vs (vs (vs vz))))))
       ▹ Hom Nat (w (wᶠ^ 3 m₂)) nzero

  ------------------------------------------------------------------------
  -- shared premises — `dmX`'s depth-independent shape once more
  ------------------------------------------------------------------------

  tyA₆ : SZCtx ⊢ty wTy^ 6 A
  tyA₆ = ren-ty (ren-ty (ren-ty (ren-ty (ren-ty (ren-ty dA there) there)
                                        there) there) there) there

  dk₁ : (SZCtx ▹ wTy^ 6 A) ⊢ wᶠ^ 6 m₁ ∷ Nat
  dk₁ = ⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁)))))

  dk₂ : (SZCtx ▹ wTy^ 6 A) ⊢ wᶠ^ 6 m₂ ∷ Nat
  dk₂ = ⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂)))))

  dmX : (SZCtx ▹ wTy^ 6 A) ⊢ w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁)) ∷ Nat
  dmX = subst (λ z → (SZCtx ▹ wTy^ 6 A) ⊢ z ∷ Nat)
              (sym (cong w (wᶠ³-single (wᶠ^ 3 m₁))))
              (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁))))))

  dmX₂ : (SZCtx ▹ wTy^ 6 A) ⊢ w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₂)) ∷ Nat
  dmX₂ = subst (λ z → (SZCtx ▹ wTy^ 6 A) ⊢ z ∷ Nat)
               (sym (cong w (wᶠ³-single (wᶠ^ 3 m₂))))
               (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂))))))

  ------------------------------------------------------------------------
  -- rec₁ — REAL: the outer descent with the n₂ reset.
  ------------------------------------------------------------------------

  nSZ : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  nSZ = w (wᶠ^ 6 m₂)

  ltSZ : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  ltSZ = ordtr (nsuc (w (wᶠ^ 6 m₁))) (w (w (w (w (wᶠ^ 3 m₁)))))
               (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz)))))))))
               (var vz) (var (vs (vs (vs vz))))

  rec1tm : RTm ⌊ SZCtx ⌋
  rec1tm =
    lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs vz)))))))
                                 nSZ)
                            (var (vs vz)))
                       ltSZ)
                  (reflTm nSZ)))

  IH₁-w⁷ : wTy^ 7 omot
         ≡ lexMot (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁) (wᶠ^ 8 m₂)
                  (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
  IH₁-w⁷ = lexMot-w^ 7 (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) (var vz)

  IH₁-fit : subTy (single nSZ)
              (auxB (wTy^ 9 A) (wᶠ^ 9 cM) (wᶠ^ 9 m₁) (wᶠ^ 9 m₂)
                    (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz))
          ≡ auxB (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁) (wᶠ^ 8 m₂)
                 (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) nSZ
  IH₁-fit =
    trans (auxB-sub {σ = single nSZ} (wTy^ 9 A) (wᶠ^ 9 cM) (wᶠ^ 9 m₁) (wᶠ^ 9 m₂)
                    (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz))
          (cong₆ auxB (wk-singleTy {v = nSZ} (wTy^ 8 A))
                      (wᶠ-single {v = nSZ} (wᶠ^ 8 cM))
                      (wᶠ-single {v = nSZ} (wᶠ^ 8 m₁))
                      (wᶠ-single {v = nSZ} (wᶠ^ 8 m₂)) refl refl)

  μ₁SZ-fit : subTm (single (var (vs vz))) (wᶠ^ 8 m₁) ≡ w (wᶠ^ 6 m₁)
  μ₁SZ-fit = wᶠ²-single (wᶠ^ 6 m₁)

  refl-fitˡ : subTm (single ltSZ)
                (subTm (extS (single (var (vs vz)))) (w (wᶠ^ 8 m₂)))
            ≡ nSZ
  refl-fitˡ =
    trans (cong (subTm (single ltSZ))
                (trans (sub-w {σ = single (var (vs vz))} (wᶠ^ 8 m₂))
                       (cong w (wᶠ²-single (wᶠ^ 6 m₂)))))
          (wk-single {v = ltSZ} (w (wᶠ^ 6 m₂)))

  refl-fitʳ : subTm (single ltSZ)
                (subTm (extS (single (var (vs vz)))) (w (w nSZ)))
            ≡ nSZ
  refl-fitʳ =
    trans (cong (subTm (single ltSZ))
                (trans (sub-w {σ = single (var (vs vz))} (w nSZ))
                       (cong w (wk-single {v = var (vs vz)} nSZ))))
          (wk-single {v = ltSZ} nSZ)

  cancel₁ : subTm (single (reflTm nSZ))
              (subTm (extS (single ltSZ))
                (subTm (extS (extS (single (var (vs vz)))))
                       (w (w (wᶠ^ 8 cM)))))
          ≡ w (wᶠ^ 6 cM)
  cancel₁ =
    trans (cong (λ z → subTm (single (reflTm nSZ)) (subTm (extS (single ltSZ)) z))
                (trans (sub-w² {σ = single (var (vs vz))} (wᶠ^ 8 cM))
                       (cong (λ z → w (w z)) (wᶠ²-single (wᶠ^ 6 cM)))))
          (trans (cong (subTm (single (reflTm nSZ)))
                       (trans (sub-w {σ = single ltSZ} (w (w (wᶠ^ 6 cM))))
                              (cong w (wk-single {v = ltSZ} (w (wᶠ^ 6 cM))))))
                 (wk-single {v = reflTm nSZ} (w (wᶠ^ 6 cM))))

  dnSZ : ((SZCtx ▹ wTy^ 6 A)
            ▹ Hom Nat (nsuc (wᶠ^ 6 m₁))
                      (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))))
         ⊢ nSZ ∷ Nat
  dnSZ = ⊢wk dk₂

  ⊢ltSZ : ((SZCtx ▹ wTy^ 6 A)
             ▹ Hom Nat (nsuc (wᶠ^ 6 m₁))
                       (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))))
          ⊢ ltSZ
          ∷ Hom Nat (w (wᶠ^ 6 m₁)) (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
  ⊢ltSZ =
    ⊢strong-step (⊢wk dk₁)
                 (⊢wk (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁)))))))
                 (⊢var (there (there (there (there (there (there (there here))))))))
                 (⊢-cast (cong (λ z → Hom Nat (nsuc (w (wᶠ^ 6 m₁))) (w (w z)))
                               (wᶠ³-single (wᶠ^ 3 m₁)))
                         (⊢var here))
                 (⊢var (there (there (there here))))

  ⊢rec1 : SZCtx ⊢ rec1tm
        ∷ aIHTat (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁)
                 (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))
  ⊢rec1 =
    ⊢lam tyA₆
      (⊢lam (ty-Hom ty-Nat (⊢nsuc dk₁) dmX)
        (⊢-cast (cong El cancel₁)
          (⊢app (⊢app (⊢app (⊢-cast IH₁-fit
                               (⊢app (⊢-cast IH₁-w⁷
                                        (⊢var (there (there (there (there (there
                                               (there here))))))))
                                     dnSZ))
                             (⊢var (there here)))
                      (⊢-cast (sym (cong (λ z → Hom Nat z
                                     (var (vs (vs (vs (vs (vs (vs (vs vz)))))))))
                                         μ₁SZ-fit))
                              ⊢ltSZ))
                (⊢-cast (sym (cong₂ (λ a b → Hom Nat a b) refl-fitˡ refl-fitʳ))
                        (⊢le-refl dnSZ)))))

  ------------------------------------------------------------------------
  -- rec₂ — VACUOUS on μ₂: μ₂ y < μ₂ x ≤ 0.
  ------------------------------------------------------------------------

  rec2tm : RTm ⌊ SZCtx ⌋
  rec2tm =
    lam (lam (lam (absurd (w (w (wᶠ^ 6 cM)))
                          (ordtr (nsuc (w (w (wᶠ^ 6 m₂))))
                                 (w (w (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₂)))))
                                 nzero (var vz) (var (vs (vs (vs vz))))))))

  ⊢rec2 : SZCtx ⊢ rec2tm
        ∷ rec2Tat (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂)
                  (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))
                  (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₂))
  ⊢rec2 =
    ⊢lam tyA₆
      (⊢lam (ty-Hom ty-Nat dk₁ dmX)
        (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢wk dk₂)) (⊢wk dmX₂))
          (⊢strong-base' (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dcM))))))))
                         (⊢wk (⊢wk dk₂)) (⊢wk (⊢wk dmX₂)) (⊢var here)
                         (⊢-cast (cong (λ z → Hom Nat (w (w (w z))) nzero)
                                       (sym (wᶠ³-single (wᶠ^ 3 m₂))))
                                 (⊢var (there (there (there here))))))))

  ------------------------------------------------------------------------
  -- BRANCH (S,0), ASSEMBLED.
  ------------------------------------------------------------------------

  lexSZ : RTm (⌊ Δ ⌋ ∙ ∙ ∙)
  lexSZ =
    lam (lam (lam (app (app (app (w^ 6 stp) (var (vs (vs vz)))) rec1tm) rec2tm)))

  stp-w⁶ : wTy^ 6 (lStepT A cM m₁ m₂)
         ≡ lStepT (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂)
  stp-w⁶ = lStepT-w^ 6 A cM m₁ m₂

  rec1-fit : subTy (single (var (vs (vs vz))))
                   (rec1T (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁))
           ≡ aIHTat (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁)
                    (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))
  rec1-fit = aIHT-fit (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁)

  rec2-fit : subTy (single rec1tm)
               (subTy (extS (single (var (vs (vs vz)))))
                      (renTy vs (rec2T (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂))))
           ≡ rec2Tat (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂)
                     (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))
                     (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₂))
  rec2-fit =
    trans (cong (subTy (single rec1tm))
                (sub-wTy {σ = single (var (vs (vs vz)))}
                         (rec2T (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂))))
          (trans (wk-singleTy {v = rec1tm}
                    (subTy (single (var (vs (vs vz))))
                           (rec2T (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂))))
                 (rec2T-fit (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂)))

  cMcancel : subTm (single rec2tm)
               (subTm (extS (single rec1tm))
                 (subTm (extS (extS (single (var (vs (vs vz))))))
                        (w (w (wᶠ^ 6 cM)))))
           ≡ w (w (wᶠ^ 3 cM))
  cMcancel =
    trans (cong (λ z → subTm (single rec2tm) (subTm (extS (single rec1tm)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (wᶠ^ 6 cM))
                       (cong (λ z → w (w z)) (wᶠ³-single (wᶠ^ 3 cM)))))
          (trans (cong (subTm (single rec2tm))
                       (trans (sub-w {σ = single rec1tm} (w (w (w (wᶠ^ 3 cM)))))
                              (cong w (wk-single {v = rec1tm} (w (w (wᶠ^ 3 cM)))))))
                 (wk-single {v = rec2tm} (w (w (wᶠ^ 3 cM)))))

  ⊢lexSZ : (((Δ ▹ Nat) ▹ omot) ▹ Nat) ⊢ lexSZ ∷ subTy (single nzero) imot
  ⊢lexSZ =
    ⊢-cast (sym imot-z)
      (⊢lam (ren-ty (ren-ty (ren-ty dA there) there) there)
        (⊢lam (ty-Hom ty-Nat (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁)))
                      (⊢nsuc (⊢var (there (there (there here))))))
          (⊢lam (ty-Hom ty-Nat (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂)))) ⊢nzero)
            (⊢-cast (cong El cMcancel)
              (⊢app (⊢app (⊢app (⊢-cast stp-w⁶
                                   (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dstp)))))))
                                 (⊢var (there (there here))))
                          (⊢-cast (sym rec1-fit) ⊢rec1))
                    (⊢-cast (sym rec2-fit) ⊢rec2))))))
