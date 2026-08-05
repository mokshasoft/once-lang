------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 24 — (ii) TOWARD SUBJECT REDUCTION: reduction and
--                            conversion are SUBSTITUTION-STABLE
--
-- Subject reduction (`Γ ⊢ t ∷ A → t ⟶ u → Γ ⊢ u ∷ A`) for the kernel of
-- dHoTT-21 rests on two things: (a) the substitution machinery — reduction and
-- conversion survive substitution — and (b) inversion of the typing rules
-- through `⊢conv`. Part (a) is confluence-free and is proven here, reusing the
-- strict substitution laws of `NbEPDirDBPi`. Part (b) is the genuine
-- obstruction and is scoped honestly below.
--
--   * `sub-comm` — the β substitution lemma for single substitution
--     (`σ (t[s]) = (σ↑ t)[σ s]`), from `NbEPDirDBPi.subTm-subTm` + a bridge.
--   * `⟶-sub` / `⟶ᵀ-sub` — REDUCTION is substitution-stable: `t ⟶ u →
--     (t[σ]) ⟶ (u[σ])`, on terms and (through `El`/`Π`/`Σ`) on types. The β
--     case is where `sub-comm` earns its keep.
--   * `≅ᵀ-sub` — hence CONVERSION is substitution-stable: `A ≅ᵀ B →
--     (A[σ]) ≅ᵀ (B[σ])`. This is exactly what the `⊢conv` case of the typed
--     substitution lemma needs.
--   * `sr-β-concrete` — subject reduction for the concrete redex `(λx.x) y`:
--     it reduces to `y`, and both are typed at `base`.
--
-- HONEST CEILING (the real obstruction, not a gap): general subject reduction
-- needs to INVERT `⊢ lam t ∷ Π A B` — but a derivation may end in `⊢conv`, so
-- inversion needs Π-INJECTIVITY of conversion (`Π A B ≅ᵀ Π A' B' → A ≅ᵀ A' ×
-- B ≅ᵀ B'`), which follows from CONFLUENCE (Church–Rosser). Confluence for βη
-- is the next metatheoretic slice; the substitution-stability proven here is
-- the confluence-free half that every version of SR reuses. `--safe`, ZERO
-- axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBSR where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; subst; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam; app
        ; ⌜Π⌝; ⌜Hom⌝; hrefl; tr; ap; ⌜Id⌝; idrefl; jsub
        ; nzero; nsuc; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝
        ; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃; ⌜Id⌝-cong₃; jsub-cong₃
        ; Ren; extR; Sub; subTy; subTm; extS; _∘ₛ_; _ₛ∘ᵣ_; _ᵣ∘ₛ_; renTm
        ; subTm-subTm; subTm-cong; subTm-renTm; subTm-id; renTm-subTm
        ; renTm-renTm; renTm-cong )
open import poc.OCP0009.NbEPDirDBVar using ( ren-as-sub )
open import poc.OCP0009.NbEPDirDBVar
  using ( pw?; stkC?; stkA?; pwBody; pwShift
        ; pw?-sub; stkC?-sub; stkA?-sub; pwBody-sub )
open import poc.OCP0009.NbEPDirDBType
  using ( single; swp; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; tr-J-base; tr-J-Σ; tr-J-Id; tr-taut; hrefl-pw; tr-J-Hom; tr-pw
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ
        ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ; ξ-idreflᵃ
        ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; El-⌜Id⌝; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ
        ; natrec-zero; natrec-suc; ξ-nsuc; ξ-natrecᶻ; ξ-natrecˢ; ξ-natrecⁿ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; El-⌜Nat⌝; El-⌜Unit⌝; tr-J-Unit
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; _⊢_∷_; ⊢var; ⊢lam; ⊢app; here
        ; _⊢ty_; ty-base )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- The β substitution lemma (single substitution commutes with a parallel
-- substitution). Same shape as `NbEPDirDB.sub-comm`, over this calculus.
------------------------------------------------------------------------

sub-comm : (σ : Sub Γ Δ) (t : RTm (Γ ∙)) (u : RTm Γ) →
           subTm σ (subTm (single u) t) ≡
           subTm (single (subTm σ u)) (subTm (extS σ) t)
sub-comm {Γ} σ t u =
  trans (subTm-subTm {τ = σ} {σ = single u} t)
        (trans (subTm-cong bridge t)
               (sym (subTm-subTm {τ = single (subTm σ u)} {σ = extS σ} t)))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           (σ ∘ₛ single u) x ≡ (single (subTm σ u) ∘ₛ extS σ) x
  bridge vz     = refl
  bridge (vs x) = sym (trans (subTm-renTm (σ x)) (subTm-id (σ x)))

------------------------------------------------------------------------
-- Weakening/renaming vs substitution commutation — the bridges the
-- `Hom-U`/`Hom-Π`/`hrefl-Π`/`tr-pw` cases need.  All three are pointwise
-- arguments in the RENAMING fragment (no new substitution machinery —
-- exactly the shape SpikeTr priced).
------------------------------------------------------------------------

wk-sub : (σ : Sub Γ Δ) (t : RTm Γ) →
         subTm (extS σ) (renTm vs t) ≡ renTm vs (subTm σ t)
wk-sub σ t = trans (subTm-renTm t) (sym (renTm-subTm t))

-- ★ WF stage A: `sub-comm` one binder down — commuting a substitution
-- past the recursor's outer-binder instantiation (the number), keeping
-- the inner (IH) binder.
sub-comm-ext : (σ : Sub Γ Δ) (s : RTm ((Γ ∙) ∙)) (n : RTm Γ) →
               subTm (extS σ) (subTm (extS (single n)) s) ≡
               subTm (extS (single (subTm σ n))) (subTm (extS (extS σ)) s)
sub-comm-ext {Γ} σ s n =
  trans (subTm-subTm {τ = extS σ} {σ = extS (single n)} s)
        (trans (subTm-cong bridge s)
               (sym (subTm-subTm {τ = extS (single (subTm σ n))} {σ = extS (extS σ)} s)))
  where
  bridge : ∀ (x : Var ((Γ ∙) ∙)) →
           subTm (extS σ) (extS (single n) x) ≡
           subTm (extS (single (subTm σ n))) (extS (extS σ) x)
  bridge vz          = refl
  bridge (vs vz)     = wk-sub σ n
  bridge (vs (vs w)) =
    sym (trans (cong (subTm (extS (single (subTm σ n)))) (renTm-renTm (σ w)))
               (trans (subTm-renTm (σ w)) (sym (ren-as-sub vs (σ w)))))

-- the same commutation one binder down: `extR vs` against `extS (extS σ)`
wk₁-sub : (σ : Sub Γ Δ) (t : RTm (Γ ∙)) →
          subTm (extS (extS σ)) (renTm (extR vs) t) ≡
          renTm (extR vs) (subTm (extS σ) t)
wk₁-sub σ t =
  trans (subTm-renTm t) (trans (subTm-cong ptw t) (sym (renTm-subTm t)))
  where
  ptw : ∀ x → (extS (extS σ) ₛ∘ᵣ extR vs) x ≡ (extR vs ᵣ∘ₛ extS σ) x
  ptw vz     = refl
  ptw (vs z) =
    trans (renTm-renTm (σ z))
          (trans (renTm-cong (λ _ → refl) (σ z)) (sym (renTm-renTm (σ z))))

-- the top-two-variable swap against `extS (extS σ)`
swp-sub : (σ : Sub Γ Δ) (t : RTm ((Γ ∙) ∙)) →
          subTm (extS (extS σ)) (renTm swp t) ≡
          renTm swp (subTm (extS (extS σ)) t)
swp-sub σ t =
  trans (subTm-renTm t) (trans (subTm-cong ptw t) (sym (renTm-subTm t)))
  where
  ptw : ∀ x → (extS (extS σ) ₛ∘ᵣ swp) x ≡ (swp ᵣ∘ₛ extS (extS σ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs z)) =
    trans (renTm-renTm (σ z))
          (trans (renTm-cong (λ _ → refl) (σ z))
                 (sym (trans (renTm-renTm (renTm vs (σ z)))
                             (renTm-renTm (σ z)))))

-- ...and the same against `pwShift` (W2b's binder retarget: Πb ↦ x,
-- end ↦ junk).  Both composites send Γ-variables through vs∘vs.
pwShift-sub : (σ : Sub Γ Δ) (t : RTm ((Γ ∙) ∙)) →
              subTm (extS (extS σ)) (renTm pwShift t) ≡
              renTm pwShift (subTm (extS (extS σ)) t)
pwShift-sub σ t =
  trans (subTm-renTm t) (trans (subTm-cong ptw t) (sym (renTm-subTm t)))
  where
  ptw : ∀ x → (extS (extS σ) ₛ∘ᵣ pwShift) x ≡
              (pwShift ᵣ∘ₛ extS (extS σ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs z)) =
    trans (renTm-renTm (σ z))
          (trans (renTm-cong (λ _ → refl) (σ z))
                 (sym (trans (renTm-renTm (renTm vs (σ z)))
                             (renTm-renTm (σ z)))))

------------------------------------------------------------------------
-- Reduction is substitution-stable — terms, then types.
------------------------------------------------------------------------

⟶-sub : (σ : Sub Γ Δ) {t u : RTm Γ} → t ⟶ u → subTm σ t ⟶ subTm σ u
⟶-sub σ (β t s)    =
  subst (λ z → app (lam (subTm (extS σ) t)) (subTm σ s) ⟶ z)
        (sym (sub-comm σ t s))
        (β (subTm (extS σ) t) (subTm σ s))
⟶-sub σ (βfst a b)  = βfst (subTm σ a) (subTm σ b)
⟶-sub σ (βsnd a b)  = βsnd (subTm σ a) (subTm σ b)
⟶-sub σ (ξ-lam r)   = ξ-lam (⟶-sub (extS σ) r)
⟶-sub σ (ξ-appˡ r)  = ξ-appˡ (⟶-sub σ r)
⟶-sub σ (ξ-appʳ r)  = ξ-appʳ (⟶-sub σ r)
⟶-sub σ (ξ-pairˡ r) = ξ-pairˡ (⟶-sub σ r)
⟶-sub σ (ξ-pairʳ r) = ξ-pairʳ (⟶-sub σ r)
⟶-sub σ (ξ-absurdᵉ r)   = ξ-absurdᵉ (⟶-sub σ r)
⟶-sub σ (ξ-fst r)   = ξ-fst (⟶-sub σ r)
⟶-sub σ (ξ-snd r)   = ξ-snd (⟶-sub σ r)
⟶-sub σ (ξ-⌜Π⌝ˡ r) = ξ-⌜Π⌝ˡ (⟶-sub σ r)
⟶-sub σ (ξ-⌜Π⌝ʳ r) = ξ-⌜Π⌝ʳ (⟶-sub (extS σ) r)
⟶-sub σ (ξ-⌜Σ⌝ˡ r) = ξ-⌜Σ⌝ˡ (⟶-sub σ r)
⟶-sub σ (ξ-⌜Σ⌝ʳ r) = ξ-⌜Σ⌝ʳ (⟶-sub (extS σ) r)
-- W2 eliminator: the two J rules and `tr-taut` are direct.
⟶-sub σ (tr-J-Unit c a m s e) =
  tr-J-Unit (subTm (extS σ) c) (subTm (extS σ) a) (subTm (extS σ) m)
            (subTm σ s) (subTm σ e)
⟶-sub σ (tr-J-base c a m s e) =
  tr-J-base (subTm (extS σ) c) (subTm (extS σ) a) (subTm (extS σ) m)
            (subTm σ s) (subTm σ e)
⟶-sub σ (tr-J-Σ c a m c₁ c₂ s e) =
  tr-J-Σ (subTm (extS σ) c) (subTm (extS σ) a) (subTm (extS σ) m)
         (subTm σ c₁) (subTm (extS σ) c₂)
         (subTm σ s) (subTm σ e)
⟶-sub σ (tr-J-Id c a m c₁ a₁ b₁ s e) =
  tr-J-Id (subTm (extS σ) c) (subTm (extS σ) a) (subTm (extS σ) m)
          (subTm σ c₁) (subTm σ a₁) (subTm σ b₁)
          (subTm σ s) (subTm σ e)
⟶-sub σ (tr-taut f e) = tr-taut (subTm (extS σ) f) (subTm σ e)
⟶-sub σ (hrefl-pw C t key) =
  subst (λ z → hrefl (subTm σ C) (subTm σ t) ⟶ z)
        (cong₂ (λ x y → lam (hrefl x (app y (var vz))))
               (pwBody-sub σ C key) (sym (wk-sub σ t)))
        (hrefl-pw (subTm σ C) (subTm σ t) (pw?-sub σ C key))
⟶-sub σ (tr-J-Hom c a m c₁ a₁ b₁ t e key) =
  tr-J-Hom (subTm (extS σ) c) (subTm (extS σ) a) (subTm (extS σ) m)
           (subTm σ c₁) (subTm σ a₁) (subTm σ b₁)
           (subTm σ t) (subTm σ e) (stkA?-sub σ c₁ key)
⟶-sub σ (tr-pw c a f e key) =
  subst (λ z → tr (⌜Hom⌝ (subTm (extS σ) c) (subTm (extS σ) a) (var vz))
                  (lam (subTm (extS σ) f)) (subTm σ e) ⟶ z)
        (cong lam
          (tr-cong₃
            (⌜Hom⌝-cong₃
              (trans (cong (renTm pwShift) (pwBody-sub (extS σ) c key))
                     (sym (pwShift-sub σ (pwBody c))))
              (cong (λ z → app z (var (vs vz))) (sym (wk-sub (extS σ) a)))
              refl)
            refl
            (cong (λ z → app z (var vz)) (sym (wk-sub σ e)))))
        (tr-pw (subTm (extS σ) c) (subTm (extS σ) a) (subTm (extS σ) f)
               (subTm σ e) (pw?-sub (extS σ) c key))
⟶-sub σ (ξ-⌜Hom⌝ᶜ r) = ξ-⌜Hom⌝ᶜ (⟶-sub σ r)
⟶-sub σ (ξ-⌜Hom⌝ˡ r) = ξ-⌜Hom⌝ˡ (⟶-sub σ r)
⟶-sub σ (ξ-⌜Hom⌝ʳ r) = ξ-⌜Hom⌝ʳ (⟶-sub σ r)
⟶-sub σ (ξ-hreflᶜ r) = ξ-hreflᶜ (⟶-sub σ r)
⟶-sub σ (ξ-hreflᵃ r) = ξ-hreflᵃ (⟶-sub σ r)
⟶-sub σ (ξ-trᵈ r)    = ξ-trᵈ (⟶-sub (extS σ) r)
⟶-sub σ (ξ-trᵖ r)    = ξ-trᵖ (⟶-sub σ r)
⟶-sub σ (ξ-trᵉ r)    = ξ-trᵉ (⟶-sub σ r)
⟶-sub σ (ap-J cB b c₁ s key) =
  subst (λ z → ap (subTm σ cB) (subTm (extS σ) b)
                  (hrefl (subTm σ c₁) (subTm σ s))
               ⟶ hrefl (subTm σ cB) z)
        (sym (sub-comm σ b s))
        (ap-J (subTm σ cB) (subTm (extS σ) b) (subTm σ c₁) (subTm σ s)
              (stkC?-sub σ c₁ key))
⟶-sub σ (ξ-apᶜ r) = ξ-apᶜ (⟶-sub σ r)
⟶-sub σ (ξ-apᵇ r) = ξ-apᵇ (⟶-sub (extS σ) r)
⟶-sub σ (ξ-apᵖ r) = ξ-apᵖ (⟶-sub σ r)
⟶-sub σ (jsub-refl d c s e) =
  subst (λ z → jsub (subTm (extS σ) d)
                    (idrefl (subTm σ c) (subTm σ s)) (subTm σ e) ⟶ z)
        refl
        (jsub-refl (subTm (extS σ) d) (subTm σ c) (subTm σ s) (subTm σ e))
⟶-sub σ (ξ-⌜Id⌝ᶜ r) = ξ-⌜Id⌝ᶜ (⟶-sub σ r)
⟶-sub σ (ξ-⌜Id⌝ˡ r) = ξ-⌜Id⌝ˡ (⟶-sub σ r)
⟶-sub σ (ξ-⌜Id⌝ʳ r) = ξ-⌜Id⌝ʳ (⟶-sub σ r)
⟶-sub σ (ξ-idreflᶜ r) = ξ-idreflᶜ (⟶-sub σ r)
⟶-sub σ (ξ-idreflᵃ r) = ξ-idreflᵃ (⟶-sub σ r)
⟶-sub σ (natrec-zero z s) =
  natrec-zero (subTm σ z) (subTm (extS (extS σ)) s)
⟶-sub σ (natrec-suc z s n) =
  subst (λ w → natrec (subTm σ z) (subTm (extS (extS σ)) s)
                      (nsuc (subTm σ n)) ⟶ w)
        (sym (trans (sub-comm σ (subTm (extS (single n)) s) (natrec z s n))
                    (cong (subTm (single (natrec (subTm σ z)
                                                 (subTm (extS (extS σ)) s)
                                                 (subTm σ n))))
                          (sub-comm-ext σ s n))))
        (natrec-suc (subTm σ z) (subTm (extS (extS σ)) s) (subTm σ n))
⟶-sub σ (ξ-nsuc r)    = ξ-nsuc (⟶-sub σ r)
⟶-sub σ (ξ-natrecᶻ r) = ξ-natrecᶻ (⟶-sub σ r)
⟶-sub σ (ξ-natrecˢ r) = ξ-natrecˢ (⟶-sub (extS (extS σ)) r)
⟶-sub σ (ξ-natrecⁿ r) = ξ-natrecⁿ (⟶-sub σ r)
⟶-sub σ (ξ-jsubᵈ r) = ξ-jsubᵈ (⟶-sub (extS σ) r)
⟶-sub σ (ξ-jsubᵖ r) = ξ-jsubᵖ (⟶-sub σ r)
⟶-sub σ (ξ-jsubᵉ r) = ξ-jsubᵉ (⟶-sub σ r)

⟶ᵀ-sub : (σ : Sub Γ Δ) {A B : RTy Γ} → A ⟶ᵀ B → subTy σ A ⟶ᵀ subTy σ B
⟶ᵀ-sub σ (El-⌜base⌝)  = El-⌜base⌝
⟶ᵀ-sub σ (El-⌜Π⌝ c d) = El-⌜Π⌝ (subTm σ c) (subTm (extS σ) d)
⟶ᵀ-sub σ (El-⌜Σ⌝ c d) = El-⌜Σ⌝ (subTm σ c) (subTm (extS σ) d)
⟶ᵀ-sub σ (El-⌜Hom⌝ c a b) = El-⌜Hom⌝ (subTm σ c) (subTm σ a) (subTm σ b)
⟶ᵀ-sub σ (ξ-El r) = ξ-El (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-Πˡ r) = ξ-Πˡ (⟶ᵀ-sub σ r)
⟶ᵀ-sub σ (ξ-Πʳ r) = ξ-Πʳ (⟶ᵀ-sub (extS σ) r)
⟶ᵀ-sub σ (ξ-Σˡ r) = ξ-Σˡ (⟶ᵀ-sub σ r)
⟶ᵀ-sub σ (ξ-Σʳ r) = ξ-Σʳ (⟶ᵀ-sub (extS σ) r)
⟶ᵀ-sub σ El-⌜Nat⌝         = El-⌜Nat⌝
⟶ᵀ-sub σ El-⌜Unit⌝        = El-⌜Unit⌝
⟶ᵀ-sub σ (Hom-Nat-z n)    = Hom-Nat-z (subTm σ n)
⟶ᵀ-sub σ (Hom-Nat-sz m)   = Hom-Nat-sz (subTm σ m)
⟶ᵀ-sub σ (Hom-Nat-ss m n) = Hom-Nat-ss (subTm σ m) (subTm σ n)
⟶ᵀ-sub σ (Hom-U c d) =
  subst (λ z → Hom U (subTm σ c) (subTm σ d) ⟶ᵀ Π (El (subTm σ c)) (El z))
        (sym (wk-sub σ d))
        (Hom-U (subTm σ c) (subTm σ d))
⟶ᵀ-sub σ (Hom-Π A B f g) =
  subst (λ Z → Hom (Π (subTy σ A) (subTy (extS σ) B)) (subTm σ f) (subTm σ g) ⟶ᵀ Z)
        (cong₂ (λ x y → Π (subTy σ A)
                          (Hom (subTy (extS σ) B) (app x (var vz)) (app y (var vz))))
               (sym (wk-sub σ f)) (sym (wk-sub σ g)))
        (Hom-Π (subTy σ A) (subTy (extS σ) B) (subTm σ f) (subTm σ g))
⟶ᵀ-sub σ (ξ-Homᵀ r) = ξ-Homᵀ (⟶ᵀ-sub σ r)
⟶ᵀ-sub σ (ξ-Homˡ r) = ξ-Homˡ (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-Homʳ r) = ξ-Homʳ (⟶-sub σ r)
⟶ᵀ-sub σ (El-⌜Id⌝ c a b) = El-⌜Id⌝ (subTm σ c) (subTm σ a) (subTm σ b)
⟶ᵀ-sub σ (ξ-Idᵀ r) = ξ-Idᵀ (⟶ᵀ-sub σ r)
⟶ᵀ-sub σ (ξ-Idˡ r) = ξ-Idˡ (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-Idʳ r) = ξ-Idʳ (⟶-sub σ r)

------------------------------------------------------------------------
-- Hence conversion is substitution-stable — the `⊢conv`-case ingredient.
------------------------------------------------------------------------

≅ᵀ-sub : (σ : Sub Γ Δ) {A B : RTy Γ} → A ≅ᵀ B → subTy σ A ≅ᵀ subTy σ B
≅ᵀ-sub σ (credᵀ r)   = credᵀ (⟶ᵀ-sub σ r)
≅ᵀ-sub σ crflᵀ       = crflᵀ
≅ᵀ-sub σ (csymᵀ c)   = csymᵀ (≅ᵀ-sub σ c)
≅ᵀ-sub σ (ctrnᵀ c d) = ctrnᵀ (≅ᵀ-sub σ c) (≅ᵀ-sub σ d)

------------------------------------------------------------------------
-- Concrete subject reduction: the redex `(λx.x) y` in context `◇ ▹ base`
-- reduces to `y`, and both the redex and the reduct are typed at `base`.
------------------------------------------------------------------------

-- the redex is well-typed (dHoTT-21's `⊢appex`)
sr-redex : (◇ ▹ base) ⊢ app (lam (var vz)) (var vz) ∷ base
sr-redex = ⊢app (⊢lam ty-base (⊢var here)) (⊢var here)

-- it β-reduces to `y = var vz`
sr-step : app (lam (var vz)) (var vz) ⟶ var (vz {ε})
sr-step = β (var vz) (var vz)

-- and the reduct is typed at the SAME type — subject reduction, concretely.
sr-reduct : (◇ ▹ base) ⊢ var vz ∷ base
sr-reduct = ⊢var here
