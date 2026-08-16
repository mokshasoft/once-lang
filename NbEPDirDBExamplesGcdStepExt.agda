
μ₂ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙)
μ₂ = plusTm (var vz) (nsuc (var (vs (vs vz))))

M₂ : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙)
M₂ = eqG μ₂ f₂

-- split 1's successor context, which is split 2's base
Θ₂ : Ctx → Ctx
Θ₂ Γ = ((Γ ▹ PairT) ▹ Nat) ▹ M₁

probe₂-z : {Γ : Cx} →
           subTy (single nzero) (M₂ {Γ})
         ≡ eqG (plusTm nzero (nsuc (var (vs vz))))
               (natrec G2z (subTm (extS (extS (single nzero)))
                                  (renTm (extR (extR vs)) gcdInn2)) nzero)
probe₂-z = refl

------------------------------------------------------------------------
-- ★ LEAF 2 — `fst x = 0`, so `gcd (0 , b) = b`.  IH-FREE, same shape as
--   leaf 1: `G2z`'s body is `nsuc n'`, which does not mention the bound
--   `ih`, so both sides land on the same term.
------------------------------------------------------------------------

red₂z : {Γ : Cx} (sb : RTm (Γ ∙ ∙ ∙ ∙ ∙)) (i : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)) →
        app (w (w (w (natrec (G2z {Γ}) sb nzero)))) i
      ⟶* nsuc (var (vs (vs (vs (vs vz)))))
red₂z sb i = ⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done)) (step (β _ i) done)

leaf₂z : {Γ : Ctx} → Prv (Θ₂ Γ) (subTy (single nzero) M₂)
leaf₂z =
  prv _ (⊢lam (⊢gcdIH dμ)
          (⊢lam (⊢gcdIH (⊢wk dμ))
            (⊢lam (⊢pwT (⊢wk (⊢wk dμ))
                        (⊢-cast (gcdIH-w² _) (⊢var (there here)))
                        (⊢-cast (gcdIH-w (w _)) (⊢var here)))
                  (prvOk idPrf))))
  where
    dμ = ⊢plus ⊢nzero (⊢nsuc (⊢var (there here)))
    idPrf = idOfRed (red₂z _ (var (vs (vs vz)))) (red₂z _ (var (vs vz)))
              (prv _ (⊢idrefl ⊢⌜Nat⌝
                        (asP (⊢nsuc (⊢var (there (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★★★ ELIMINATING THE INTERNAL POINTWISE HYPOTHESIS.
--
-- The mirror of `pwIntro`: two `⊢app`s and the peels they leave.  ⚠ The
-- `w`s are the whole cost — `pwT` states its body at the two binders'
-- depth, so every slot arrives under one or two weakenings that
-- `sub-w`/`wk-single` have to strip.  Both recursive leaves use this once.
------------------------------------------------------------------------

pwElim : {Γ : Ctx} {μ i₁ i₂ h y q : RTm ⌊ Γ ⌋} →
         Γ ⊢ h ∷ pwT μ i₁ i₂ → Γ ⊢ y ∷ PairT →
         Γ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) msr)) μ →
         Γ ⊢ app (app h y) q
           ∷ Id (El ⌜Nat⌝) (app (app i₁ y) q) (app (app i₂ y) q)
pwElim {μ = μ} {i₁ = i₁} {i₂ = i₂} {y = y} {q = q} dh dy dq =
  ⊢-cast eq2 (⊢app (⊢-cast eq1 (⊢app dh dy)) dq)
  where
    -- one binder in: the two IHs lose one `w`, the bound loses its `w`
    peel₁ : (t : RTm ⌊ _ ⌋) → subTm (extS (single y)) (w (w t)) ≡ w t
    peel₁ t = trans (sub-w {σ = single y} (w t))
                    (cong w (wk-single {v = y} t))

    eq1 = cong₂ (λ u f → Π (Hom Nat (nsuc (subTm (single y) msr)) u) f)
                (wk-single {v = y} μ)
                (Id-cong₃ refl
                  (cong (λ z → app (app z (w y)) (var vz)) (peel₁ i₁))
                  (cong (λ z → app (app z (w y)) (var vz)) (peel₁ i₂)))

    -- the second binder: both `w`s go
    peel₂ : (t : RTm ⌊ _ ⌋) → subTm (single q) (w t) ≡ t
    peel₂ t = wk-single {v = q} t

    eq2 = Id-cong₃ refl
            (cong₂ (λ z u → app (app z u) q) (peel₂ i₁) (peel₂ y))
            (cong₂ (λ z u → app (app z u) q) (peel₂ i₂) (peel₂ y))
