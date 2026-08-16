
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

-- ★ `pwT` past a weakening — needed because the hypothesis reaches each
--   leaf as a Π-BOUND VARIABLE, and `here` hands it back under a `renTy vs`.
pwT-w : {Γ : Cx} (μ i₁ i₂ : RTm Γ) →
        renTy vs (pwT μ i₁ i₂) ≡ pwT (w μ) (w i₁) (w i₂)
pwT-w μ i₁ i₂ =
  cong₂ (λ u f → Π PairT (Π (Hom Nat (nsuc msr) u) f))
        (ren-w μ)
        (Id-cong₃ refl (atv (wwr i₁)) (atv (wwr i₂)))
  where
    wwr : (t : RTm _) → renTm (extR (extR vs)) (w (w t)) ≡ w (w (w t))
    wwr t = trans (ren-w {ρ = extR vs} (w t)) (cong w (ren-w t))

    atv : {u u' : RTm _} → u ≡ u' →
          app (app u (var (vs vz))) (var vz) ≡ app (app u' (var (vs vz))) (var vz)
    atv e = cong (λ z → app (app z (var (vs vz))) (var vz)) e

------------------------------------------------------------------------
-- ★★ SPLIT 3 — the COMPARISON, on `a ∸ b`.  ctx: [0]=M₂ [1]=k' [2]=M₁ [3]=n' [4]=x
--
-- ⚠ CONSTANT MOTIVE, exactly as `G3` is: the branch needs to know only
--   WHETHER `a ∸ b` is zero, never its value.  So `μ₃` does not mention the
--   recursion variable and the two leaves get their IHs at the SAME bound,
--   `plusTm (nsuc k') (nsuc n')` — which is precisely the bound `⊢CERTᶻ`
--   and `⊢CERTˢ` are stated at.
------------------------------------------------------------------------

Θ₃ : Ctx → Ctx
Θ₃ Γ = (Θ₂ Γ ▹ Nat) ▹ M₂

μ₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)
μ₃ = plusTm (nsuc (var (vs (vs vz)))) (nsuc (var (vs (vs (vs (vs vz))))))

f₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)
f₃ = natrec (w G3z) (renTm (extR (extR vs)) G3s) (var vz)

M₃ : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙ ∙ ∙)
M₃ = eqG μ₃ f₃

-- ⭐ splits 2 and 3 meet in one `natrec-suc` step too
probe₂-s : {Γ : Cx} →
           subTm nrs (f₂ {Γ})
         ⟶* subTm (single (monusTm (nsuc (var (vs vz)))
                                   (nsuc (var (vs (vs (vs vz))))))) (f₃ {Γ})
probe₂-s = step (natrec-suc _ _ _) done

------------------------------------------------------------------------
-- ★★★★ LEAF 3 — `a ∸ b = 0`, i.e. `a ≤ b`: recurse at `(a , b ∸ a)`.
--       THE FIRST LEAF THAT USES THE HYPOTHESIS.
--
-- ⭐ AND IT IS ONE APPLICATION.  `G3z` reduces to `ih (PAIRᶻ) (CERTᶻ)`, the
--   Π-bound hypothesis is about the two IHs at the bound
--   `plusTm (nsuc k') (nsuc n')`, and `⊢CERTᶻ` is stated at EXACTLY that
--   bound.  Nothing is transported.  This is what carrying the IHs in the
--   motive bought — under the 2026-08-15 design the certificate would have
--   had to be rebuilt at `μ a` first.
------------------------------------------------------------------------

red₃z : {Γ : Cx} (sb : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)) (i : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)) →
        app (w (w (w (natrec (G3z {Γ}) sb nzero)))) i
      ⟶* app (app i (w (w PAIRᶻ))) (w (w CERTᶻ))
red₃z sb i = ⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done)) (step (β _ i) done)

leaf₃z : {Γ : Ctx} → Prv (Θ₃ Γ) (subTy (single nzero) M₃)
leaf₃z =
  prv _ (⊢lam (⊢gcdIH dμ)
          (⊢lam (⊢gcdIH (⊢wk dμ))
            (⊢lam (⊢pwT (⊢wk (⊢wk dμ))
                        (⊢-cast (gcdIH-w² _) (⊢var (there here)))
                        (⊢-cast (gcdIH-w (w _)) (⊢var here)))
                  (prvOk idPrf))))
  where
    dμ = ⊢plus (⊢nsuc (⊢var (there here)))
               (⊢nsuc (⊢var (there (there (there here)))))
    idPrf = idOfRed (red₃z _ (var (vs (vs vz)))) (red₃z _ (var (vs vz)))
              (prv _ (pwElim (⊢-cast (pwT-w _ _ _) (⊢var here))
                             (⊢wk (⊢wk ⊢PAIRᶻ))
                             (⊢wk (⊢wk ⊢CERTᶻ))))

------------------------------------------------------------------------
-- ★★★★ LEAF 4 — `a ∸ b = suc d`, i.e. `a > b`: recurse at `(a ∸ b , b)`.
--
-- ⭐ `natrec-suc` HANDS BACK `G3s` UNCHANGED.  The step substitutes the
--   natrec's predecessor and its IH into the successor branch, and `G3s`
--   uses NEITHER — its two free variables are `k'` and `n'`, three and five
--   slots further out.  So the branch is reached in one step and the leaf
--   is `β` plus one application of the hypothesis, exactly like leaf 3.
------------------------------------------------------------------------

red₃s : {Γ : Cx} {F : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)} → F ⟶* G3s →
        (i : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)) →
        app (w (w (w F))) i ⟶* app (app i (w (w PAIRˢ))) (w (w CERTˢ))
red₃s r i =
  ⟶*-trans (⟶*-appˡ (⟶*-ren vs (⟶*-ren vs (⟶*-ren vs r))))
           (step (β _ i) done)

leaf₃s : {Γ : Ctx} → Prv ((Θ₃ Γ ▹ Nat) ▹ M₃) (subTy nrs M₃)
leaf₃s =
  prv _ (⊢lam (⊢gcdIH dμ)
          (⊢lam (⊢gcdIH (⊢wk dμ))
            (⊢lam (⊢pwT (⊢wk (⊢wk dμ))
                        (⊢-cast (gcdIH-w² _) (⊢var (there here)))
                        (⊢-cast (gcdIH-w (w _)) (⊢var here)))
                  (prvOk idPrf))))
  where
    dμ = ⊢plus (⊢nsuc (⊢var (there (there (there here)))))
               (⊢nsuc (⊢var (there (there (there (there (there here)))))))
    rr : subTm nrs f₃ ⟶* G3s
    rr = step (natrec-suc _ _ _) done
    idPrf = idOfRed (red₃s rr (var (vs (vs vz)))) (red₃s rr (var (vs vz)))
              (prv _ (pwElim (⊢-cast (pwT-w _ _ _) (⊢var here))
                             (⊢wk (⊢wk ⊢PAIRˢ))
                             (⊢wk (⊢wk ⊢CERTˢ))))

------------------------------------------------------------------------
-- ★★ THE SUBSTITUTION TWINS, and `eqG`'s eliminator.
------------------------------------------------------------------------

gcdIH-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ : RTm Γ) →
            subTy σ (gcdIH μ) ≡ gcdIH (subTm σ μ)
gcdIH-sub μ = aIHTat-sub PairT ⌜Nat⌝ msr μ

pwT-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ i₁ i₂ : RTm Γ) →
          subTy σ (pwT μ i₁ i₂) ≡ pwT (subTm σ μ) (subTm σ i₁) (subTm σ i₂)
pwT-sub {σ = σ} μ i₁ i₂ =
  cong₂ (λ u f → Π PairT (Π (Hom Nat (nsuc msr) u) f))
        (sub-w {σ = σ} μ)
        (Id-cong₃ refl (atv (sub-w² {σ = σ} i₁)) (atv (sub-w² {σ = σ} i₂)))
  where
    atv : {u u' : RTm _} → u ≡ u' →
          app (app u (var (vs vz))) (var vz) ≡ app (app u' (var (vs vz))) (var vz)
    atv e = cong (λ z → app (app z (var (vs vz))) (var vz)) e

-- ★ …and the eliminator: feed `eqG` its two IHs and the hypothesis.
--   Three `⊢app`s, three casts, and every cast is `wk-single`/`sub-w`.
eqGElim : {Γ : Ctx} {μ f e i₁ i₂ h : RTm ⌊ Γ ⌋} →
          Γ ⊢ e ∷ eqG μ f → Γ ⊢ i₁ ∷ gcdIH μ → Γ ⊢ i₂ ∷ gcdIH μ →
          Γ ⊢ h ∷ pwT μ i₁ i₂ →
          Γ ⊢ app (app (app e i₁) i₂) h
            ∷ Id (El ⌜Nat⌝) (app f i₁) (app f i₂)
eqGElim {μ = μ} {f = f} {i₁ = i₁} {i₂ = i₂} {h = h} de d₁ d₂ dh =
  ⊢-cast eq3 (⊢app (⊢-cast eq2 (⊢app (⊢-cast eq1 (⊢app de d₁)) d₂)) dh)
  where
    eq1 = cong₂ Π (trans (gcdIH-sub (w μ)) (cong gcdIH (wk-single {v = i₁} μ)))
                  (cong₂ Π (trans (pwT-sub (w (w μ)) (var (vs vz)) (var vz))
                                  (cong (λ u → pwT u (w i₁) (var vz))
                                        (trans (sub-w {σ = single i₁} (w μ))
                                               (cong w (wk-single {v = i₁} μ)))))
                           (Id-cong₃ refl
                             (cong₂ (λ z u → app z u)
                                    (trans (sub-w² {σ = single i₁} (w f))
                                           (cong (λ t → w (w t)) (wk-single {v = i₁} f)))
                                    refl)
                             (cong₂ (λ z u → app z u)
                                    (trans (sub-w² {σ = single i₁} (w f))
                                           (cong (λ t → w (w t)) (wk-single {v = i₁} f)))
                                    refl)))

    eq2 = cong₂ Π (trans (pwT-sub (w μ) (w i₁) (var vz))
                         (cong₃' (wk-single {v = i₂} μ) (wk-single {v = i₂} i₁)))
                  (Id-cong₃ refl
                    (cong₂ (λ z u → app z u) (wk-single {v = i₂} (w f))
                                             (wk-single {v = i₂} (w i₁)))
                    (cong₂ (λ z u → app z u) (wk-single {v = i₂} (w f)) refl))
      where
        cong₃' : {a a' b b' : RTm _} → a ≡ a' → b ≡ b' →
                 pwT a b i₂ ≡ pwT a' b' i₂
        cong₃' refl refl = refl

    eq3 = Id-cong₃ refl
            (cong₂ (λ z u → app z u) (wk-single {v = h} f) (wk-single {v = h} i₁))
            (cong₂ (λ z u → app z u) (wk-single {v = h} f) (wk-single {v = h} i₂))

------------------------------------------------------------------------
-- ★★★★★ THE ASSEMBLY — three nested `natrec`s, mirroring `⊢gcdStp` step
--        for step, with `gcdG` replaced by `eqG` throughout.
------------------------------------------------------------------------

gcdExt : {Γ : Ctx} → Prv (Γ ▹ PairT) (eqG msr gcdBody)
gcdExt =
  prv _ (⊢natrec (⊢eqG dμ₁ (⊢natrec-var ⊢G1 ⊢G1z ⊢gcdInn1))
                 (prvOk leaf₁z)
                 (⊢conv split2 (csymᵀ (eqG-red probe₁-s)))
                 (⊢snd (⊢var here)))
  where
    dμ₁ = ⊢plus (⊢fst (⊢var (there here))) (⊢var here)
    dμ₂ = ⊢plus (⊢var here) (⊢nsuc (⊢var (there (there here))))
    dμ₃ = ⊢plus (⊢nsuc (⊢var (there (there here))))
                (⊢nsuc (⊢var (there (there (there (there here))))))

    split3 = ⊢natrec (⊢eqG dμ₃ (⊢natrec-var ⊢G3 ⊢G3z ⊢G3s))
                     (prvOk leaf₃z) (prvOk leaf₃s)
                     (⊢monus (⊢nsuc (⊢var (there here)))
                             (⊢nsuc (⊢var (there (there (there here))))))

    split2 = ⊢natrec (⊢eqG dμ₂ (⊢natrec-var ⊢G2 ⊢G2z ⊢gcdInn2))
                     (prvOk leaf₂z)
                     (⊢conv split3 (csymᵀ (eqG-red probe₂-s)))
                     (⊢fst (⊢var (there (there here))))

------------------------------------------------------------------------
-- ★★★★★★ AND THE HYPOTHESIS ITSELF.  Gap A's caller-side half, DONE.
--
-- Instantiate `gcdExt` at the carrier, feed it the two IHs and the
-- internalised hypothesis, and bridge the one β-step to `app (app stp a) ih`.
------------------------------------------------------------------------

gcdStepExt : {Δ : Ctx} → StepExt Δ PairT ⌜Nat⌝ msr gcdStp
gcdStepExt hρ a ih₁ ih₂ da d₁ d₂ pw =
  idOfRed (red-β a ih₁) (red-β a ih₂)
          (prv _ (eqGElim (⊢[] (prvOk gcdExt) da) d₁ d₂
                          (prvOk (pwIntro (⊢plus (⊢fst da) (⊢snd da)) pw))))
