------------------------------------------------------------------------
-- OCP-0009 — THE OUTER-MOTIVE COMBINATOR AND THE DEEP LADDERS.
--
-- ⚠ SPLIT OUT OF `LexC` DEFENSIVELY, not on a clean measurement.  Branch
--   (0,S) uses NONE of these and sits within ~0.5 GB of the 5.5 GB cap, so
--   it should not deserialise them.  ⛔ BUT DO NOT QUOTE A SAVING: (0,S)
--   read 4.43 GB, then 5.19 GB with these in `LexC`, then 4.96 GB with
--   them out — against a `LexC` that is byte-identical to the 4.43 run.
--   So run-to-run variance here is ±12%, which swamps the effect, and the
--   attribution is NOT established.  The split is hygiene: only the
--   SUCCESSOR branches apply the outer IH, so only they should carry it.
--
-- ⚠ AND TAKE THE ±12% AS THE REAL LESSON.  Every RSS number in these
--   headers is one sample.  Differences under ~15% between modules are
--   not evidence of anything.
--
-- ★ `auxMotB` is the outer motive `lexAuxMot` as a combinator:
--   `Π Nat (auxBody …)` with the μ₁-bound from the ambient context and
--   the μ₂-bound the Π's own variable.  ⚠ The μ₁-bound MUST be a
--   parameter — `renTy vs` does not preserve the `var (vs vz)` that
--   `lexAuxMot` writes inline, so a combinator with the bound written in
--   cannot have a `-ren` lemma at all.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexCMot where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs; Ren
        ; RTy; El; Hom; Nat
        ; RTm; var; Π; renTy; renTm )
open import DirectedHoTT.Negative.LexC

-- ★ THE OUTER MOTIVE, as a combinator.  `lexAuxMot` is `Π Nat (auxBody …)`
--   with the μ₁-bound coming from the AMBIENT context and the μ₂-bound
--   being the Π's own variable.  Both successor branches APPLY this IH,
--   so they need its `renTy` pushed in — and `renTy vs` does not preserve
--   `var (vs vz)`, which is why the μ₁-bound must be a PARAMETER here
--   rather than written into the body the way `lexAuxMot` writes it.
auxMotB : {Γ : Cx} (cA cP μ₁ μ₂ b₁ : RTm Γ) → RTy Γ
auxMotB cA cP μ₁ μ₂ b₁ =
  Π Nat (auxBody (w cA) (w cP) (w μ₁) (w μ₂) (w b₁) (var vz))

auxMotB-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cA cP μ₁ μ₂ b₁ : RTm Γ) →
              renTy ρ (auxMotB cA cP μ₁ μ₂ b₁)
            ≡ auxMotB (renTm ρ cA) (renTm ρ cP) (renTm ρ μ₁) (renTm ρ μ₂) (renTm ρ b₁)
auxMotB-ren a b c d e =
  cong (Π Nat)
    (trans (auxBody-ren (w a) (w b) (w c) (w d) (w e) (var vz))
           (cong₆ auxBody (ren-w a) (ren-w b) (ren-w c) (ren-w d) (ren-w e) refl))


lStepT-w⁷ : {Γ : Cx} (cA cP μ₁ μ₂ : RTm Γ) →
            renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (lStepT cA cP μ₁ μ₂)))))))
          ≡ lStepT (w (w (w (w (w (w (w cA))))))) (w (w (w (w (w (w (w cP))))))) (w (w (w (w (w (w (w μ₁))))))) (w (w (w (w (w (w (w μ₂)))))))
lStepT-w⁷ a b c d =
  trans (cong (renTy vs) (lStepT-w⁶ a b c d))
        (lStepT-ren (w (w (w (w (w (w a)))))) (w (w (w (w (w (w b)))))) (w (w (w (w (w (w c)))))) (w (w (w (w (w (w d)))))))

lStepT-w⁸ : {Γ : Cx} (cA cP μ₁ μ₂ : RTm Γ) →
            renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (lStepT cA cP μ₁ μ₂))))))))
          ≡ lStepT (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂))))))))
lStepT-w⁸ a b c d =
  trans (cong (renTy vs) (lStepT-w⁷ a b c d))
        (lStepT-ren (w (w (w (w (w (w (w a))))))) (w (w (w (w (w (w (w b))))))) (w (w (w (w (w (w (w c))))))) (w (w (w (w (w (w (w d))))))))

auxMotB-w² : {Γ : Cx} (cA cP μ₁ μ₂ b₁ : RTm Γ) →
              renTy vs (renTy vs (auxMotB cA cP μ₁ μ₂ b₁))
            ≡ auxMotB (w (w cA)) (w (w cP)) (w (w μ₁)) (w (w μ₂)) (w (w b₁))
auxMotB-w² a b c d e =
  trans (cong (renTy vs) (auxMotB-ren a b c d e))
        (auxMotB-ren (w a) (w b) (w c) (w d) (w e))

auxMotB-w³ : {Γ : Cx} (cA cP μ₁ μ₂ b₁ : RTm Γ) →
              renTy vs (renTy vs (renTy vs (auxMotB cA cP μ₁ μ₂ b₁)))
            ≡ auxMotB (w (w (w cA))) (w (w (w cP))) (w (w (w μ₁))) (w (w (w μ₂))) (w (w (w b₁)))
auxMotB-w³ a b c d e =
  trans (cong (renTy vs) (auxMotB-w² a b c d e))
        (auxMotB-ren (w (w a)) (w (w b)) (w (w c)) (w (w d)) (w (w e)))

auxMotB-w⁴ : {Γ : Cx} (cA cP μ₁ μ₂ b₁ : RTm Γ) →
              renTy vs (renTy vs (renTy vs (renTy vs (auxMotB cA cP μ₁ μ₂ b₁))))
            ≡ auxMotB (w (w (w (w cA)))) (w (w (w (w cP)))) (w (w (w (w μ₁)))) (w (w (w (w μ₂)))) (w (w (w (w b₁))))
auxMotB-w⁴ a b c d e =
  trans (cong (renTy vs) (auxMotB-w³ a b c d e))
        (auxMotB-ren (w (w (w a))) (w (w (w b))) (w (w (w c))) (w (w (w d))) (w (w (w e))))

auxMotB-w⁵ : {Γ : Cx} (cA cP μ₁ μ₂ b₁ : RTm Γ) →
              renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (auxMotB cA cP μ₁ μ₂ b₁)))))
            ≡ auxMotB (w (w (w (w (w cA))))) (w (w (w (w (w cP))))) (w (w (w (w (w μ₁))))) (w (w (w (w (w μ₂))))) (w (w (w (w (w b₁)))))
auxMotB-w⁵ a b c d e =
  trans (cong (renTy vs) (auxMotB-w⁴ a b c d e))
        (auxMotB-ren (w (w (w (w a)))) (w (w (w (w b)))) (w (w (w (w c)))) (w (w (w (w d)))) (w (w (w (w e)))))

auxMotB-w⁶ : {Γ : Cx} (cA cP μ₁ μ₂ b₁ : RTm Γ) →
              renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (auxMotB cA cP μ₁ μ₂ b₁))))))
            ≡ auxMotB (w (w (w (w (w (w cA)))))) (w (w (w (w (w (w cP)))))) (w (w (w (w (w (w μ₁)))))) (w (w (w (w (w (w μ₂)))))) (w (w (w (w (w (w b₁))))))
auxMotB-w⁶ a b c d e =
  trans (cong (renTy vs) (auxMotB-w⁵ a b c d e))
        (auxMotB-ren (w (w (w (w (w a))))) (w (w (w (w (w b))))) (w (w (w (w (w c))))) (w (w (w (w (w d))))) (w (w (w (w (w e))))))

auxMotB-w⁷ : {Γ : Cx} (cA cP μ₁ μ₂ b₁ : RTm Γ) →
              renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (auxMotB cA cP μ₁ μ₂ b₁)))))))
            ≡ auxMotB (w (w (w (w (w (w (w cA))))))) (w (w (w (w (w (w (w cP))))))) (w (w (w (w (w (w (w μ₁))))))) (w (w (w (w (w (w (w μ₂))))))) (w (w (w (w (w (w (w b₁)))))))
auxMotB-w⁷ a b c d e =
  trans (cong (renTy vs) (auxMotB-w⁶ a b c d e))
        (auxMotB-ren (w (w (w (w (w (w a)))))) (w (w (w (w (w (w b)))))) (w (w (w (w (w (w c)))))) (w (w (w (w (w (w d)))))) (w (w (w (w (w (w e)))))))

auxMotB-w⁸ : {Γ : Cx} (cA cP μ₁ μ₂ b₁ : RTm Γ) →
              renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (auxMotB cA cP μ₁ μ₂ b₁))))))))
            ≡ auxMotB (w (w (w (w (w (w (w (w cA)))))))) (w (w (w (w (w (w (w (w cP)))))))) (w (w (w (w (w (w (w (w μ₁)))))))) (w (w (w (w (w (w (w (w μ₂)))))))) (w (w (w (w (w (w (w (w b₁))))))))
auxMotB-w⁸ a b c d e =
  trans (cong (renTy vs) (auxMotB-w⁷ a b c d e))
        (auxMotB-ren (w (w (w (w (w (w (w a))))))) (w (w (w (w (w (w (w b))))))) (w (w (w (w (w (w (w c))))))) (w (w (w (w (w (w (w d))))))) (w (w (w (w (w (w (w e))))))))

auxMotB-w⁹ : {Γ : Cx} (cA cP μ₁ μ₂ b₁ : RTm Γ) →
              renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (auxMotB cA cP μ₁ μ₂ b₁)))))))))
            ≡ auxMotB (w (w (w (w (w (w (w (w (w cA))))))))) (w (w (w (w (w (w (w (w (w cP))))))))) (w (w (w (w (w (w (w (w (w μ₁))))))))) (w (w (w (w (w (w (w (w (w μ₂))))))))) (w (w (w (w (w (w (w (w (w b₁)))))))))
auxMotB-w⁹ a b c d e =
  trans (cong (renTy vs) (auxMotB-w⁸ a b c d e))
        (auxMotB-ren (w (w (w (w (w (w (w (w a)))))))) (w (w (w (w (w (w (w (w b)))))))) (w (w (w (w (w (w (w (w c)))))))) (w (w (w (w (w (w (w (w d)))))))) (w (w (w (w (w (w (w (w e)))))))))


