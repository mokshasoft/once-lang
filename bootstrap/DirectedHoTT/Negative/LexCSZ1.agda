------------------------------------------------------------------------
-- BRANCH (S,0), rec₁ — THE OUTER DESCENT, under option C.
--
-- ★ THE OUTER IH IS A DIFFERENT SHAPE from (0,S)'s inner one.  That was an
--   `auxBody`; this is `lexAuxMot`, i.e. `Π Nat (auxBody …)`, so the
--   reassociation is `auxMotB-w⁷`.  ⚠ The μ₁-bound has to be a PARAMETER
--   of that combinator — `renTy vs` does NOT preserve the `var (vs vz)`
--   that `lexAuxMot` writes inline.
--
-- ★★ FOUR arguments, not three: n₂ := μ₂ y comes FIRST, so every later
--   argument's expected type carries that substitution too.  The fitting
--   lemmas are one level deeper than (0,S)'s — `μ₂-fit` peels `sub-w²`,
--   then `sub-w`, then `wk-single`, and `ihPcancel` peels all four.
--
-- ⚠ 35.2 s / 4.19 GB on its own.  This is why the branch is split.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexCSZ1 where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; wk-single )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Strong using ( ⊢le-refl; reflTm )
open import DirectedHoTT.Lib.Ord
  using ( ⊢strong-base'; ⊢strong-step )
open import DirectedHoTT.Negative.LexC
open import DirectedHoTT.Negative.LexCMot
open import DirectedHoTT.Negative.LexCSZData using ( module SZD )

module SZ1 (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
         (dcA  : Δ ⊢ cA  ∷ U)
         (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
         (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
         (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
         (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂) where

  open Lx Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp
  open SZD Δ cA cP μ₁ μ₂ stp dcA dcP dμ₁ dμ₂ dstp

  -- ★ THE OUTER IH, REASSOCIATED: seven ⊢wk's worth of `renTy` sitting
  --   outside a `Π Nat (auxBody …)`; `auxMotB-w⁷` puts them back inside.
  IH1-w⁷ : renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (lexAuxMot)))))))
         ≡ auxMotB (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂)))))))) (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
  IH1-w⁷ = auxMotB-w⁷ (w cA) (w cP) (w μ₁) (w μ₂) (var vz)

  cA-fit : subTm (single nSZ) (w (w (w (w (w (w (w (w (w cA))))))))) ≡ (w (w (w (w (w (w (w (w cA))))))))
  cA-fit = wk-single {v = nSZ} (w (w (w (w (w (w (w (w cA))))))))

  μ₁-fit : subTm (single (var (vs vz))) (subTm (extS (single nSZ)) (w (w (w (w (w (w (w (w (w (w μ₁))))))))))) ≡ (w (w (w (w (w (w (w (w μ₁))))))))
  μ₁-fit =
    trans (cong (subTm (single (var (vs vz))))
                (trans (sub-w {σ = single nSZ} (w (w (w (w (w (w (w (w (w μ₁))))))))))
                       (cong w (wk-single {v = nSZ} (w (w (w (w (w (w (w (w μ₁))))))))))))
          (wk-single {v = (var (vs vz))} (w (w (w (w (w (w (w (w μ₁)))))))))

  μ₂-fit : subTm (single ltSZ)
             (subTm (extS (single (var (vs vz))))
               (subTm (extS (extS (single nSZ))) (w (w (w (w (w (w (w (w (w (w (w μ₂)))))))))))))
         ≡ (w (w (w (w (w (w (w (w μ₂))))))))
  μ₂-fit =
    trans (cong (λ z → subTm (single ltSZ) (subTm (extS (single (var (vs vz)))) z))
                (trans (sub-w² {σ = single nSZ} (w (w (w (w (w (w (w (w (w μ₂))))))))))
                       (cong (λ z → w (w z)) (wk-single {v = nSZ} (w (w (w (w (w (w (w (w μ₂))))))))))))
    (trans (cong (subTm (single ltSZ))
                 (trans (sub-w {σ = single (var (vs vz))} (w (w (w (w (w (w (w (w (w μ₂))))))))))
                        (cong w (wk-single {v = (var (vs vz))} (w (w (w (w (w (w (w (w μ₂))))))))))))
           (wk-single {v = ltSZ} (w (w (w (w (w (w (w (w μ₂))))))))))

  -- ★ THE RESET, surviving the spine: the μ₂-bound the IH is applied at is
  --   the very term `nSZ`, so `⊢le-refl` really does discharge it.
  n-fit : subTm (single ltSZ) (subTm (extS (single (var (vs vz)))) (w (w nSZ))) ≡ nSZ
  n-fit =
    trans (cong (subTm (single ltSZ))
                (trans (sub-w {σ = single (var (vs vz))} (w nSZ))
                       (cong w (wk-single {v = (var (vs vz))} nSZ))))
          (wk-single {v = ltSZ} nSZ)

  -- the IH spine's FOUR substitutions, w¹² cP → w⁸ cP
  ihPcancel : subTm (single (reflTm nSZ))
                (subTm (extS (single ltSZ))
                  (subTm (extS (extS (single (var (vs vz)))))
                    (subTm (extS (extS (extS (single nSZ)))) (w (w (w (w (w (w (w (w (w (w (w (w cP)))))))))))))))
            ≡ (w (w (w (w (w (w (w (w cP))))))))
  ihPcancel =
    trans (cong (λ z → subTm (single (reflTm nSZ)) (subTm (extS (single ltSZ)) (subTm (extS (extS (single (var (vs vz))))) z)))
                (trans (sub-w³ {σ = single nSZ} (w (w (w (w (w (w (w (w (w cP))))))))))
                       (cong (λ z → w (w (w z))) (wk-single {v = nSZ} (w (w (w (w (w (w (w (w cP))))))))))))
    (trans (cong (λ z → subTm (single (reflTm nSZ)) (subTm (extS (single ltSZ)) z))
                 (trans (sub-w² {σ = single (var (vs vz))} (w (w (w (w (w (w (w (w (w cP))))))))))
                        (cong (λ z → w (w z)) (wk-single {v = (var (vs vz))} (w (w (w (w (w (w (w (w cP))))))))))))
    (trans (cong (subTm (single (reflTm nSZ)))
                 (trans (sub-w {σ = single ltSZ} (w (w (w (w (w (w (w (w (w cP))))))))))
                        (cong w (wk-single {v = ltSZ} (w (w (w (w (w (w (w (w cP))))))))))))
           (wk-single {v = reflTm nSZ} (w (w (w (w (w (w (w (w cP)))))))))))

  ⊢lexSZrec1 : ΓSZ ⊢ lexSZrec1
             ∷ rec1T (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (var (vs (vs vz)))
  ⊢lexSZrec1 =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcA))))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))) (⊢var here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))))) (⊢var (there (there (there here)))))) (⊢-cast (cong (λ z → El (app z (var (vs vz)))) ihPcancel) (⊢app (⊢app (⊢app (⊢app (⊢-cast IH1-w⁷ (⊢var (there (there (there (there (there (there here)))))))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))) (⊢var (there here)))) (⊢-cast (sym (cong El cA-fit)) (⊢var (there here)))) (⊢-cast (sym (cong (λ z → Hom Nat (app z (var (vs vz))) (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) μ₁-fit)) (⊢strong-step (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))))))) (⊢var (there here))) (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))))))) (⊢var (there (there (there (there here)))))) (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var here) (⊢var (there (there (there here))))))) (⊢-cast (sym (cong₂ (λ z z' → Hom Nat (app z (var (vs vz))) z') μ₂-fit n-fit)) (⊢le-refl (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₂)))))))) (⊢var (there here))))))))
