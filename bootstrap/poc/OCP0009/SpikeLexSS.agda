------------------------------------------------------------------------
-- OCP-0009 — ★★★ THE GATE: LEXREC BRANCH (S,S) UNDER FAMILIES.
--
-- ⚠ THE QUESTION THIS MODULE EXISTS TO ANSWER, and nothing else.  Under
--   codes-and-functions this branch DOES NOT FIT: `…ExamplesLexCSS1` and
--   `…ExamplesLexCSS2` each OOM at the 5.5 GB cap — both halves, even
--   under `+RTS -c` — so option C's lexrec was never completed.  See
--   `…ExamplesLexCSS`'s header for that measurement; those modules are a
--   deliberate RED and must not be cited as derivations.
--
-- ★ WHY IT MIGHT FIT HERE.  Families removes every `app` from the types,
--   so `μᵢ y` is a term rather than a β-redex, and the fitting collapses
--   to ONE lemma per spine instead of one per argument.  Branch (0,S),
--   the one branch that exists in both worlds, measured 48.7 s / 4.35 GB
--   under codes-and-functions against 8.8 s / 0.71 GB here (SpikeLexT).
--
-- ★★ THE BRANCH ITSELF — the only one where BOTH recursor arguments are
--   LIVE, and the reason the whole development exists:
--
--     rec₁  the OUTER descent.  μ₁ y < μ₁ x ≤ suc n₁' gives μ₁ y ≤ n₁',
--           and n₂ RESETS — the outer IH is `Π Nat …`, so it is
--           instantiated at μ₂ y itself and the μ₂ obligation is
--           REFLEXIVITY.  ★ Under families that reset is `w (wᶠ⁸ m₂)`,
--           the measure family, not an application.
--     rec₂  the INNER descent.  n₁ is HELD (μ₁ y ≤ suc n₁' by plain
--           `⊢ordtr`) and n₂ drops (μ₂ y ≤ n₂' by `⊢strong-step`).
--
--   Together those two ARE the lexicographic order.
--
-- ctx: vz = lt, vs = le, vs² = x, vs³ = IH₂, vs⁴ = n₂', vs⁵ = n₂,
--      vs⁶ = IH₁, vs⁷ = n₁', then Δ
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeLexSS where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; lam; app; absurd; ordtr
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El; ty-Π )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; ren-ty )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; cong₄; cong₆; sub-w; sub-w²; wk-singleTy; wᶠ-single
        ; wᶠ²-single; wᶠ³-single; nrs-wTy; wᶠ-nrs
        ; w^; wTy^; wᶠ^; ⊢wkᶠ )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat; aIHT; aIHT-fit )
open import poc.OCP0009.SpikeLexT
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )

module SS (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m₁ m₂ : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
          (dA   : Δ ⊢ty A)
          (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
          (dm₁  : (Δ ▹ A) ⊢ m₁ ∷ Nat)
          (dm₂  : (Δ ▹ A) ⊢ m₂ ∷ Nat)
          (dstp : Δ ⊢ stp ∷ lStepT A cM m₁ m₂)
          where

  ------------------------------------------------------------------------
  -- THE TWO MOTIVES AND THE BRANCH CONTEXT
  ------------------------------------------------------------------------

  -- the OUTER motive, at the outer natrec's own variable
  omot : RTy (⌊ Δ ⌋ ∙)
  omot = lexMot (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) (var vz)

  -- the INNER motive at n₁ = suc n₁'
  imot : RTy (⌊ Δ ⌋ ∙ ∙ ∙ ∙)
  imot = M1lex (wTy^ 3 A) (wᶠ^ 3 cM) (wᶠ^ 3 m₁) (wᶠ^ 3 m₂) (var (vs (vs vz)))

  -- ★ the boundary.  BOTH bounds move this time — μ₁'s is `suc n₁'` and
  --   `nrs` carries it one slot further, μ₂'s becomes `suc n₂'`.  Still
  --   only the bounds: A/cM/m₁/m₂ are already at depth.
  imot-s : subTy nrs imot
         ≡ auxB (wTy^ 5 A) (wᶠ^ 5 cM) (wᶠ^ 5 m₁) (wᶠ^ 5 m₂)
                (nsuc (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs vz)))
  imot-s =
    trans (auxB-sub {σ = nrs} (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁) (wᶠ^ 4 m₂)
                    (nsuc (var (vs (vs (vs vz))))) (var vz))
          (cong₆ auxB (nrs-wTy (wTy^ 3 A)) (wᶠ-nrs (wᶠ^ 3 cM))
                      (wᶠ-nrs (wᶠ^ 3 m₁)) (wᶠ-nrs (wᶠ^ 3 m₂)) refl refl)

  SSCtx : Ctx
  SSCtx =
    (((((((Δ ▹ Nat) ▹ omot) ▹ Nat) ▹ Nat) ▹ imot)
        ▹ wTy^ 5 A)
        ▹ Hom Nat (wᶠ^ 5 m₁) (nsuc (var (vs (vs (vs (vs (vs vz))))))))
        ▹ Hom Nat (w (wᶠ^ 5 m₂)) (nsuc (var (vs (vs (vs vz)))))

  ------------------------------------------------------------------------
  -- the shared premises.  ★ `dmX`/`dmX₂` are (0,S)'s verbatim at depth 5
  --   rather than 3: `⊢wk³ (⊢wkᶠ⁵ dm)`, bridged by `wᶠ³-single`.  The
  --   three ordinary weakenings are always the same three — `le`, `lt`
  --   and the `y` binder sitting above the carrier slot.
  ------------------------------------------------------------------------

  tyA₈ : SSCtx ⊢ty wTy^ 8 A
  tyA₈ = ren-ty (ren-ty (ren-ty (ren-ty (ren-ty (ren-ty (ren-ty (ren-ty dA
           there) there) there) there) there) there) there) there

  dk₁ : (SSCtx ▹ wTy^ 8 A) ⊢ wᶠ^ 8 m₁ ∷ Nat
  dk₁ = ⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁)))))))

  dk₂ : (SSCtx ▹ wTy^ 8 A) ⊢ wᶠ^ 8 m₂ ∷ Nat
  dk₂ = ⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂)))))))

  dmX : (SSCtx ▹ wTy^ 8 A) ⊢ w (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₁)) ∷ Nat
  dmX = subst (λ z → (SSCtx ▹ wTy^ 8 A) ⊢ z ∷ Nat)
              (sym (cong w (wᶠ³-single (wᶠ^ 5 m₁))))
              (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁))))))))

  dmX₂ : (SSCtx ▹ wTy^ 8 A) ⊢ w (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₂)) ∷ Nat
  dmX₂ = subst (λ z → (SSCtx ▹ wTy^ 8 A) ⊢ z ∷ Nat)
               (sym (cong w (wᶠ³-single (wᶠ^ 5 m₂))))
               (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂))))))))

  ------------------------------------------------------------------------
  -- ★★ rec₁ — THE OUTER DESCENT, WITH THE n₂ RESET.
  ------------------------------------------------------------------------

  -- ★ the reset.  Under codes-and-functions this was `app (w¹⁰ μ₂) (var (vs vz))`,
  --   a β-redex that never reduces; under families it is the measure.
  nSS : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  nSS = w (wᶠ^ 8 m₂)

  ltSS : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  ltSS = ordtr (nsuc (w (wᶠ^ 8 m₁))) (w (w (w (w (wᶠ^ 5 m₁)))))
               (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))
               (var vz) (var (vs (vs (vs vz))))

  rec1tm : RTm ⌊ SSCtx ⌋
  rec1tm =
    lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))
                                 nSS)
                            (var (vs vz)))
                       ltSS)
                  (reflTm nSS)))

  -- the outer IH's own type, out from under nine ⊢wks
  IH₁-w⁹ : wTy^ 9 omot
         ≡ lexMot (wTy^ 10 A) (wᶠ^ 10 cM) (wᶠ^ 10 m₁) (wᶠ^ 10 m₂)
                  (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))
  IH₁-w⁹ = lexMot-w^ 9 (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) (var vz)

  -- ★ …and the RESET itself, as a fit: instantiating the outer IH's `Π Nat`
  --   at μ₂ y leaves the μ₁-bound alone and plants μ₂ y as the μ₂-bound.
  IH₁-fit : subTy (single nSS)
              (auxB (wTy^ 11 A) (wᶠ^ 11 cM) (wᶠ^ 11 m₁) (wᶠ^ 11 m₂)
                    (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))
                    (var vz))
          ≡ auxB (wTy^ 10 A) (wᶠ^ 10 cM) (wᶠ^ 10 m₁) (wᶠ^ 10 m₂)
                 (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) nSS
  IH₁-fit =
    trans (auxB-sub {σ = single nSS} (wTy^ 11 A) (wᶠ^ 11 cM) (wᶠ^ 11 m₁)
                    (wᶠ^ 11 m₂)
                    (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))
                    (var vz))
          (cong₆ auxB (wk-singleTy {v = nSS} (wTy^ 10 A))
                      (wᶠ-single {v = nSS} (wᶠ^ 10 cM))
                      (wᶠ-single {v = nSS} (wᶠ^ 10 m₁))
                      (wᶠ-single {v = nSS} (wᶠ^ 10 m₂)) refl refl)

  μ₁SS-fit : subTm (single (var (vs vz))) (wᶠ^ 10 m₁) ≡ w (wᶠ^ 8 m₁)
  μ₁SS-fit = wᶠ²-single (wᶠ^ 8 m₁)

  -- the reflexivity slot's two endpoints
  refl-fitˡ : subTm (single ltSS)
                (subTm (extS (single (var (vs vz)))) (w (wᶠ^ 10 m₂)))
            ≡ nSS
  refl-fitˡ =
    trans (cong (subTm (single ltSS))
                (trans (sub-w {σ = single (var (vs vz))} (wᶠ^ 10 m₂))
                       (cong w (wᶠ²-single (wᶠ^ 8 m₂)))))
          (wk-single {v = ltSS} (w (wᶠ^ 8 m₂)))

  refl-fitʳ : subTm (single ltSS)
                (subTm (extS (single (var (vs vz)))) (w (w nSS)))
            ≡ nSS
  refl-fitʳ =
    trans (cong (subTm (single ltSS))
                (trans (sub-w {σ = single (var (vs vz))} (w nSS))
                       (cong w (wk-single {v = var (vs vz)} nSS))))
          (wk-single {v = ltSS} nSS)

  -- the motive's cancellation down rec₁'s four-argument spine
  cancel₁ : subTm (single (reflTm nSS))
              (subTm (extS (single ltSS))
                (subTm (extS (extS (single (var (vs vz)))))
                       (w (w (wᶠ^ 10 cM)))))
          ≡ w (wᶠ^ 8 cM)
  cancel₁ =
    trans (cong (λ z → subTm (single (reflTm nSS)) (subTm (extS (single ltSS)) z))
                (trans (sub-w² {σ = single (var (vs vz))} (wᶠ^ 10 cM))
                       (cong (λ z → w (w z)) (wᶠ²-single (wᶠ^ 8 cM)))))
          (trans (cong (subTm (single (reflTm nSS)))
                       (trans (sub-w {σ = single ltSS} (w (w (wᶠ^ 8 cM))))
                              (cong w (wk-single {v = ltSS} (w (wᶠ^ 8 cM))))))
                 (wk-single {v = reflTm nSS} (w (wᶠ^ 8 cM))))

  dnSS : ((SSCtx ▹ wTy^ 8 A)
            ▹ Hom Nat (nsuc (wᶠ^ 8 m₁))
                      (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₁))))
         ⊢ nSS ∷ Nat
  dnSS = ⊢wk dk₂

  ⊢ltSS : ((SSCtx ▹ wTy^ 8 A)
             ▹ Hom Nat (nsuc (wᶠ^ 8 m₁))
                       (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₁))))
          ⊢ ltSS
          ∷ Hom Nat (w (wᶠ^ 8 m₁))
                    (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))
  ⊢ltSS =
    ⊢strong-step (⊢wk dk₁)
                 (⊢wk (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁)))))))))
                 (⊢var (there (there (there (there (there (there (there
                        (there (there here))))))))))
                 (⊢-cast (cong (λ z → Hom Nat (nsuc (w (wᶠ^ 8 m₁))) (w (w z)))
                               (wᶠ³-single (wᶠ^ 5 m₁)))
                         (⊢var here))
                 (⊢var (there (there (there here))))

  ⊢rec1 : SSCtx ⊢ rec1tm
        ∷ aIHTat (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁)
                 (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₁))
  ⊢rec1 =
    ⊢lam tyA₈
      (⊢lam (ty-Hom ty-Nat (⊢nsuc dk₁) dmX)
        (⊢-cast (cong El cancel₁)
          (⊢app (⊢app (⊢app (⊢-cast IH₁-fit
                               (⊢app (⊢-cast IH₁-w⁹
                                        (⊢var (there (there (there (there (there
                                               (there (there (there here))))))))))
                                     dnSS))
                             (⊢var (there here)))
                      (⊢-cast (sym (cong (λ z → Hom Nat z
                                     (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))
                                         μ₁SS-fit))
                              ⊢ltSS))
                (⊢-cast (sym (cong₂ (λ a b → Hom Nat a b) refl-fitˡ refl-fitʳ))
                        (⊢le-refl dnSS)))))

  ------------------------------------------------------------------------
  -- ★★ rec₂ — THE INNER DESCENT.  (0,S)'s rec₂ verbatim, two slots
  --    deeper, with the μ₁ obligation landing at `suc n₁'` instead of 0 —
  --    so it is a plain `⊢ordtr` there and a plain `⊢ordtr` here.
  ------------------------------------------------------------------------

  lt₁SS : RTm (⌊ SSCtx ⌋ ∙ ∙ ∙)
  lt₁SS = ordtr (w (w (wᶠ^ 8 m₁))) (w (w (w (w (w (wᶠ^ 5 m₁))))))
                (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))
                (var (vs vz)) (var (vs (vs (vs (vs vz)))))

  lt₂SS : RTm (⌊ SSCtx ⌋ ∙ ∙ ∙)
  lt₂SS = ordtr (nsuc (w (w (wᶠ^ 8 m₂)))) (w (w (w (w (w (wᶠ^ 5 m₂))))))
                (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz)))))))))
                (var vz) (var (vs (vs (vs vz))))

  rec2tm : RTm ⌊ SSCtx ⌋
  rec2tm =
    lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz)))))))
                                 (var (vs (vs vz))))
                            lt₁SS)
                       lt₂SS)))

  IH₂-w⁷ : wTy^ 7 imot
         ≡ auxB (wTy^ 11 A) (wᶠ^ 11 cM) (wᶠ^ 11 m₁) (wᶠ^ 11 m₂)
                (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))
                (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
  IH₂-w⁷ = auxB-w^ 7 (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁) (wᶠ^ 4 m₂)
                     (nsuc (var (vs (vs (vs vz))))) (var vz)

  μ₁-fit₂ : subTm (single (var (vs (vs vz)))) (wᶠ^ 11 m₁) ≡ w (w (wᶠ^ 8 m₁))
  μ₁-fit₂ = wᶠ³-single (wᶠ^ 8 m₁)

  μ₂-fit₂ : subTm (single lt₁SS)
              (subTm (extS (single (var (vs (vs vz))))) (w (wᶠ^ 11 m₂)))
          ≡ w (w (wᶠ^ 8 m₂))
  μ₂-fit₂ =
    trans (cong (subTm (single lt₁SS))
                (trans (sub-w {σ = single (var (vs (vs vz)))} (wᶠ^ 11 m₂))
                       (cong w (wᶠ³-single (wᶠ^ 8 m₂)))))
          (wk-single {v = lt₁SS} (w (w (wᶠ^ 8 m₂))))

  cancel₂ : subTm (single lt₂SS)
              (subTm (extS (single lt₁SS))
                (subTm (extS (extS (single (var (vs (vs vz))))))
                       (w (w (wᶠ^ 11 cM)))))
          ≡ w (w (wᶠ^ 8 cM))
  cancel₂ =
    trans (cong (λ z → subTm (single lt₂SS) (subTm (extS (single lt₁SS)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (wᶠ^ 11 cM))
                       (cong (λ z → w (w z)) (wᶠ³-single (wᶠ^ 8 cM)))))
          (trans (cong (subTm (single lt₂SS))
                       (trans (sub-w {σ = single lt₁SS} (w (w (w (wᶠ^ 8 cM)))))
                              (cong w (wk-single {v = lt₁SS} (w (w (wᶠ^ 8 cM)))))))
                 (wk-single {v = lt₂SS} (w (w (wᶠ^ 8 cM)))))

  ⊢lt₁SS : ((((SSCtx ▹ wTy^ 8 A)
                ▹ Hom Nat (wᶠ^ 8 m₁)
                          (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₁))))
                ▹ Hom Nat (nsuc (w (wᶠ^ 8 m₂)))
                          (w (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₂))))))
           ⊢ lt₁SS
           ∷ Hom Nat (w (w (wᶠ^ 8 m₁)))
                     (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))
  ⊢lt₁SS =
    ⊢ordtr (⊢wk (⊢wk dk₁))
           (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁))))))))))
           (⊢nsuc (⊢var (there (there (there (there (there (there (there
                          (there (there (there here))))))))))))
           (⊢-cast (cong (λ z → Hom Nat (w (w (wᶠ^ 8 m₁))) (w (w (w z))))
                         (wᶠ³-single (wᶠ^ 5 m₁)))
                   (⊢var (there here)))
           (⊢var (there (there (there (there here)))))

  ⊢lt₂SS : ((((SSCtx ▹ wTy^ 8 A)
                ▹ Hom Nat (wᶠ^ 8 m₁)
                          (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₁))))
                ▹ Hom Nat (nsuc (w (wᶠ^ 8 m₂)))
                          (w (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₂))))))
           ⊢ lt₂SS
           ∷ Hom Nat (w (w (wᶠ^ 8 m₂)))
                     (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
  ⊢lt₂SS =
    ⊢strong-step (⊢wk (⊢wk dk₂))
                 (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂))))))))))
                 (⊢var (there (there (there (there (there (there (there here))))))))
                 (⊢-cast (cong (λ z → Hom Nat (nsuc (w (w (wᶠ^ 8 m₂)))) (w (w (w z))))
                               (wᶠ³-single (wᶠ^ 5 m₂)))
                         (⊢var here))
                 (⊢var (there (there (there here))))

  ⊢rec2 : SSCtx ⊢ rec2tm
        ∷ rec2Tat (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁) (wᶠ^ 8 m₂)
                  (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₁))
                  (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₂))
  ⊢rec2 =
    ⊢lam tyA₈
      (⊢lam (ty-Hom ty-Nat dk₁ dmX)
        (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢wk dk₂)) (⊢wk dmX₂))
          (⊢-cast (cong El cancel₂)
            (⊢app (⊢app (⊢app (⊢-cast IH₂-w⁷
                                 (⊢var (there (there (there (there (there
                                        (there here))))))))
                               (⊢var (there (there here))))
                        (⊢-cast (sym (cong (λ z → Hom Nat z
                                       (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))))
                                           μ₁-fit₂))
                                ⊢lt₁SS))
                  (⊢-cast (sym (cong (λ z → Hom Nat z
                                 (var (vs (vs (vs (vs (vs (vs (vs vz)))))))))
                                     μ₂-fit₂))
                          ⊢lt₂SS)))))

  ------------------------------------------------------------------------
  -- ★★★ BRANCH (S,S), ASSEMBLED.  ⚠ THIS IS THE ANSWER TO THE GATE.
  ------------------------------------------------------------------------

  lexSS : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙)
  lexSS =
    lam (lam (lam (app (app (app (w^ 8 stp) (var (vs (vs vz)))) rec1tm) rec2tm)))

  stp-w⁸ : wTy^ 8 (lStepT A cM m₁ m₂)
         ≡ lStepT (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁) (wᶠ^ 8 m₂)
  stp-w⁸ = lStepT-w^ 8 A cM m₁ m₂

  rec1-fit : subTy (single (var (vs (vs vz))))
                   (rec1T (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁))
           ≡ aIHTat (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁)
                    (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₁))
  rec1-fit = aIHT-fit (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁)

  rec2-fit : subTy (single rec1tm)
               (subTy (extS (single (var (vs (vs vz)))))
                      (renTy vs (rec2T (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁) (wᶠ^ 8 m₂))))
           ≡ rec2Tat (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁) (wᶠ^ 8 m₂)
                     (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₁))
                     (subTm (single (var (vs (vs vz)))) (wᶠ^ 8 m₂))
  rec2-fit =
    trans (cong (subTy (single rec1tm))
                (sub-wTy {σ = single (var (vs (vs vz)))}
                         (rec2T (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁) (wᶠ^ 8 m₂))))
          (trans (wk-singleTy {v = rec1tm}
                    (subTy (single (var (vs (vs vz))))
                           (rec2T (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁) (wᶠ^ 8 m₂))))
                 (rec2T-fit (wTy^ 8 A) (wᶠ^ 8 cM) (wᶠ^ 8 m₁) (wᶠ^ 8 m₂)))

  cMcancel : subTm (single rec2tm)
               (subTm (extS (single rec1tm))
                 (subTm (extS (extS (single (var (vs (vs vz))))))
                        (w (w (wᶠ^ 8 cM)))))
           ≡ w (w (wᶠ^ 5 cM))
  cMcancel =
    trans (cong (λ z → subTm (single rec2tm) (subTm (extS (single rec1tm)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (wᶠ^ 8 cM))
                       (cong (λ z → w (w z)) (wᶠ³-single (wᶠ^ 5 cM)))))
          (trans (cong (subTm (single rec2tm))
                       (trans (sub-w {σ = single rec1tm} (w (w (w (wᶠ^ 5 cM)))))
                              (cong w (wk-single {v = rec1tm} (w (w (wᶠ^ 5 cM)))))))
                 (wk-single {v = rec2tm} (w (w (wᶠ^ 5 cM)))))

  ⊢lexSS : ((((Δ ▹ Nat) ▹ omot) ▹ Nat) ▹ Nat) ▹ imot ⊢ lexSS ∷ subTy nrs imot
  ⊢lexSS =
    ⊢-cast (sym imot-s)
      (⊢lam (ren-ty (ren-ty (ren-ty (ren-ty (ren-ty dA there) there) there)
                            there) there)
        (⊢lam (ty-Hom ty-Nat (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁)))))
                      (⊢nsuc (⊢var (there (there (there (there (there here))))))))
          (⊢lam (ty-Hom ty-Nat (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂))))))
                        (⊢nsuc (⊢var (there (there (there here))))))
            (⊢-cast (cong El cMcancel)
              (⊢app (⊢app (⊢app (⊢-cast stp-w⁸
                                   (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dstp)))))))))
                                 (⊢var (there (there here))))
                          (⊢-cast (sym rec1-fit) ⊢rec1))
                    (⊢-cast (sym rec2-fit) ⊢rec2))))))
