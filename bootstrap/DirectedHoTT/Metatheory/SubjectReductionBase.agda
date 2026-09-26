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
module DirectedHoTT.Metatheory.SubjectReductionBase where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; subst; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam
        ; app; ⌜Π⌝; ⌜Hom⌝; hrefl; tr; ap; ⌜Id⌝; idrefl; jsub; nzero; nsuc
        ; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃
        ; ⌜Id⌝-cong₃; jsub-cong₃; Ren; extR; Sub; subTy; subTm; extS; _∘ₛ_
        ; _ₛ∘ᵣ_; _ᵣ∘ₛ_; renTm; subTm-subTm; subTm-cong; subTm-renTm; subTm-id
        ; renTm-subTm; renTm-renTm; renTm-cong; Desc; con; IMu; ielim; ⌜IMu⌝
        ; εwkTm; ⌜Σ⌝; ⌜Fin⌝; dι; dσ; dρ; dpay; dih; fzero; fsuc; fcase; fcase0
        ; psplit; DIh; Fin; pair; fst; snd; unit; renTy; subTy-subTy
        ; subTy-cong; subTy-renTy; renTy-subTy; subTy-id; cong₄ )
open import DirectedHoTT.Spec.Variance
  using ( ren-as-sub )
open import DirectedHoTT.Spec.Variance
  using ( pw?; stkC?; stkA?; pwBody; pwShift; pw?-sub; stkC?-sub; stkA?-sub
        ; pwBody-sub )
open import DirectedHoTT.Spec.Typing
  using ( single; swp; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ
        ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ordtr-z; ordtr-szz; ordtr-ssz
        ; ordtr-szs; ordtr-sss; ξ-ordtrᵃ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ
        ; ξ-ordtrq; ξ-fst; ξ-snd; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; tr-J-base
        ; tr-J-Σ; tr-J-Id; tr-taut; hrefl-pw; tr-J-Hom; tr-pw; ξ-⌜Hom⌝ᶜ
        ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ; ap-J
        ; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ
        ; ξ-idreflᵃ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; El-⌜Id⌝; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ
        ; natrec-zero; natrec-suc; ξ-nsuc; ξ-natrecᶻ; ξ-natrecˢ; ξ-natrecⁿ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss; El-⌜Nat⌝; El-⌜Unit⌝; tr-J-Unit
        ; tr-J-IMu; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El; ξ-Πˡ
        ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; _≅ᵀ_; credᵀ
        ; crflᵀ; csymᵀ; ctrnᵀ; Ctx; ◇; _▹_; _⊢_∷_; ⊢var; ⊢lam; ⊢app; here
        ; _⊢ty_; ty-base; ξ-con; ξ-ielimⁱ; ξ-ielimᵗ; El-⌜IMu⌝; ι; dpay-ι
        ; dpay-σ; dpay-ρ; dih-ι; dih-σ; dih-ρ; fcase-z; fcase-s; psplit-β
        ; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ; ξ-⌜IMu⌝ⁱ; ξ-ielimᴰ; ξ-ielimᵉ; ξ-dι; ξ-dσˢ; ξ-dσᶠ
        ; ξ-dρʲ; ξ-dρᶜ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dpayⁱ; ξ-dihᴰ; ξ-dihᵉ
        ; ξ-dihᶜ; ξ-dihᵖ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0
        ; ξ-psplitᵇ; ξ-psplitᵍ; tr-J-Fin; El-⌜Fin⌝; DIh-ι; DIh-σ; DIh-ρ
        ; ξ-IMuᴵ; ξ-IMuᴰ; ξ-IMuⁱ; ξ-Desc; ξ-DIhᴰ; ξ-DIhᴹ; ξ-DIhᶜ; ξ-DIhᵖ
        ; single2; iinst; wk-single )

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

-- ★ LEVITATION: the substitution lemmas the levitated rules need.  (The
--   `iinst` pair moved here from `TySub`: it is SYNTAX, and `⟶ᵀ-sub`'s
--   `DIh-ρ` case needs it below `TySub`.)
subTy-comm : (σ : Sub Γ Δ) (B : RTy (Γ ∙)) (u : RTm Γ) →
             subTy σ (subTy (single u) B) ≡
             subTy (single (subTm σ u)) (subTy (extS σ) B)
subTy-comm {Γ} σ B u =
  trans (subTy-subTy B) (trans (subTy-cong bridge B) (sym (subTy-subTy B)))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           (σ ∘ₛ single u) x ≡ (single (subTm σ u) ∘ₛ extS σ) x
  bridge vz     = refl
  bridge (vs x) = sym (trans (subTm-renTm (σ x)) (subTm-id (σ x)))

sub-comm-ty-ext : (σ : Sub Γ Δ) (M : RTy ((Γ ∙) ∙)) (j : RTm Γ) →
                  subTy (extS σ) (subTy (extS (single j)) M)
                    ≡ subTy (extS (single (subTm σ j))) (subTy (extS (extS σ)) M)
sub-comm-ty-ext {Γ} σ M j =
  trans (subTy-subTy M) (trans (subTy-cong bridge M) (sym (subTy-subTy M)))
  where
  bridge : ∀ (x : Var ((Γ ∙) ∙)) →
           (extS σ ∘ₛ extS (single j)) x
             ≡ (extS (single (subTm σ j)) ∘ₛ extS (extS σ)) x
  bridge vz          = refl
  bridge (vs vz)     = wk-sub σ j
  bridge (vs (vs x)) =
    sym (trans (wk-sub (single (subTm σ j)) (renTm vs (σ x)))
               (cong (renTm vs) (wk-single (σ x))))

iinst-sub : (σ : Sub Γ Δ) (M : RTy ((Γ ∙) ∙)) (j t : RTm Γ) →
            subTy σ (iinst j t M)
              ≡ iinst (subTm σ j) (subTm σ t) (subTy (extS (extS σ)) M)
iinst-sub σ M j t =
  trans (subTy-comm σ (subTy (extS (single j)) M) t)
        (cong (subTy (single (subTm σ t))) (sub-comm-ty-ext σ M j))

-- the motive weakened past ONE more binder (its own two kept) commutes
wk2-subTy : (σ : Sub Γ Δ) (M : RTy ((Γ ∙) ∙)) →
            subTy (extS (extS (extS σ))) (renTy (extR (extR vs)) M)
              ≡ renTy (extR (extR vs)) (subTy (extS (extS σ)) M)
wk2-subTy σ M = trans (subTy-renTy M) (trans (subTy-cong ptw M) (sym (renTy-subTy M)))
  where
  ptw : ∀ x → (extS (extS (extS σ)) ₛ∘ᵣ extR (extR vs)) x ≡ (extR (extR vs) ᵣ∘ₛ extS (extS σ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs z)) =
    trans (trans (cong (renTm vs) (renTm-renTm (σ z))) (renTm-renTm (σ z)))
          (sym (trans (cong (renTm (extR (extR vs))) (renTm-renTm (σ z))) (renTm-renTm (σ z))))

-- `psplit-β`'s two-binder instantiation commutes
sub-comm2 : (σ : Sub Γ Δ) (b : RTm ((Γ ∙) ∙)) (x y : RTm Γ) →
            subTm σ (subTm (single2 x y) b) ≡
            subTm (single2 (subTm σ x) (subTm σ y)) (subTm (extS (extS σ)) b)
sub-comm2 {Γ} σ b x y =
  trans (subTm-subTm b) (trans (subTm-cong bridge b) (sym (subTm-subTm b)))
  where
  bridge : ∀ (z : Var ((Γ ∙) ∙)) →
           (σ ∘ₛ single2 x y) z ≡ (single2 (subTm σ x) (subTm σ y) ∘ₛ extS (extS σ)) z
  bridge vz          = refl
  bridge (vs vz)     = refl
  bridge (vs (vs z)) =
    sym (trans (subTm-renTm (renTm vs (σ z))) (trans (subTm-renTm (σ z)) (subTm-id (σ z))))

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
⟶-sub σ (ξ-absurdᶜ r)   = ξ-absurdᶜ (⟶-sub σ r)
⟶-sub σ (ξ-absurdᵉ r)   = ξ-absurdᵉ (⟶-sub σ r)
⟶-sub σ (ordtr-z t u p q) = ordtr-z _ _ _ _
⟶-sub σ (ordtr-szz a p q) = ordtr-szz _ _ _
⟶-sub σ (ordtr-ssz a t p q) = ordtr-ssz _ _ _ _
⟶-sub σ (ordtr-szs a u p q) = ordtr-szs _ _ _ _
⟶-sub σ (ordtr-sss a t u p q) = ordtr-sss _ _ _ _ _
⟶-sub σ (ξ-ordtrᵃ r) = ξ-ordtrᵃ (⟶-sub σ r)
⟶-sub σ (ξ-ordtrᵗ r) = ξ-ordtrᵗ (⟶-sub σ r)
⟶-sub σ (ξ-ordtrᵘ r) = ξ-ordtrᵘ (⟶-sub σ r)
⟶-sub σ (ξ-ordtrᵖ r) = ξ-ordtrᵖ (⟶-sub σ r)
⟶-sub σ (ξ-ordtrq r) = ξ-ordtrq (⟶-sub σ r)
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
⟶-sub σ (tr-J-IMu c a m s e) =
  tr-J-IMu (subTm (extS σ) c) (subTm (extS σ) a) (subTm (extS σ) m)
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
-- ★ LEVITATION
⟶-sub σ (ι D i e p) = ι _ _ _ _
⟶-sub σ (dpay-ι I D j i) = dpay-ι _ _ _ _
⟶-sub σ (dpay-σ I D S f i) =
  subst (λ z → dpay (subTm σ I) (subTm σ D) (dσ (subTm σ S) (subTm σ f)) (subTm σ i) ⟶ z)
        (sym (cong₄ (λ a b c d → ⌜Σ⌝ (subTm σ S) (dpay a b (app c (var vz)) d))
                    (wk-sub σ I) (wk-sub σ D) (wk-sub σ f) (wk-sub σ i)))
        (dpay-σ _ _ _ _ _)
⟶-sub σ (dpay-ρ I D j C i) =
  subst (λ z → dpay (subTm σ I) (subTm σ D) (dρ (subTm σ j) (subTm σ C)) (subTm σ i) ⟶ z)
        (sym (cong₄ (λ a b c d → ⌜Σ⌝ (⌜IMu⌝ (subTm σ I) (subTm σ D) (subTm σ j)) (dpay a b c d))
                    (wk-sub σ I) (wk-sub σ D) (wk-sub σ C) (wk-sub σ i)))
        (dpay-ρ _ _ _ _ _)
⟶-sub σ (dih-ι D e j p) = dih-ι _ _ _ _
⟶-sub σ (dih-σ D e S f p) = dih-σ _ _ _ _ _
⟶-sub σ (dih-ρ D e j C p) = dih-ρ _ _ _ _ _
⟶-sub σ (fcase-z a b) = fcase-z _ _
⟶-sub σ (fcase-s t a b) =
  subst (λ z → fcase (fsuc (subTm σ t)) (subTm σ a) (subTm (extS σ) b) ⟶ z)
        (sym (sub-comm σ b t))
        (fcase-s _ _ _)
⟶-sub σ (psplit-β b x y) =
  subst (λ z → psplit (subTm (extS (extS σ)) b) (pair (subTm σ x) (subTm σ y)) ⟶ z)
        (sym (sub-comm2 σ b x y))
        (psplit-β _ _ _)
⟶-sub σ (tr-J-Fin c a m s e) =
  tr-J-Fin (subTm (extS σ) c) (subTm (extS σ) a) (subTm (extS σ) m) (subTm σ s) (subTm σ e)
⟶-sub σ (ξ-⌜IMu⌝ᴵ r) = ξ-⌜IMu⌝ᴵ (⟶-sub σ r)
⟶-sub σ (ξ-⌜IMu⌝ᴰ r) = ξ-⌜IMu⌝ᴰ (⟶-sub σ r)
⟶-sub σ (ξ-⌜IMu⌝ⁱ r) = ξ-⌜IMu⌝ⁱ (⟶-sub σ r)
⟶-sub σ (ξ-con r)    = ξ-con (⟶-sub σ r)
⟶-sub σ (ξ-ielimᴰ r) = ξ-ielimᴰ (⟶-sub σ r)
⟶-sub σ (ξ-ielimⁱ r) = ξ-ielimⁱ (⟶-sub σ r)
⟶-sub σ (ξ-ielimᵉ r) = ξ-ielimᵉ (⟶-sub σ r)
⟶-sub σ (ξ-ielimᵗ r) = ξ-ielimᵗ (⟶-sub σ r)
⟶-sub σ (ξ-dι r)     = ξ-dι (⟶-sub σ r)
⟶-sub σ (ξ-dσˢ r)    = ξ-dσˢ (⟶-sub σ r)
⟶-sub σ (ξ-dσᶠ r)    = ξ-dσᶠ (⟶-sub σ r)
⟶-sub σ (ξ-dρʲ r)    = ξ-dρʲ (⟶-sub σ r)
⟶-sub σ (ξ-dρᶜ r)    = ξ-dρᶜ (⟶-sub σ r)
⟶-sub σ (ξ-dpayᴵ r)  = ξ-dpayᴵ (⟶-sub σ r)
⟶-sub σ (ξ-dpayᴰ r)  = ξ-dpayᴰ (⟶-sub σ r)
⟶-sub σ (ξ-dpayᶜ r)  = ξ-dpayᶜ (⟶-sub σ r)
⟶-sub σ (ξ-dpayⁱ r)  = ξ-dpayⁱ (⟶-sub σ r)
⟶-sub σ (ξ-dihᴰ r)   = ξ-dihᴰ (⟶-sub σ r)
⟶-sub σ (ξ-dihᵉ r)   = ξ-dihᵉ (⟶-sub σ r)
⟶-sub σ (ξ-dihᶜ r)   = ξ-dihᶜ (⟶-sub σ r)
⟶-sub σ (ξ-dihᵖ r)   = ξ-dihᵖ (⟶-sub σ r)
⟶-sub σ (ξ-fsuc r)   = ξ-fsuc (⟶-sub σ r)
⟶-sub σ (ξ-fcaseᵗ r) = ξ-fcaseᵗ (⟶-sub σ r)
⟶-sub σ (ξ-fcaseᵃ r) = ξ-fcaseᵃ (⟶-sub σ r)
⟶-sub σ (ξ-fcaseᵇ r) = ξ-fcaseᵇ (⟶-sub (extS σ) r)
⟶-sub σ (ξ-fcase0 r) = ξ-fcase0 (⟶-sub σ r)
⟶-sub σ (ξ-psplitᵇ r) = ξ-psplitᵇ (⟶-sub (extS (extS σ)) r)
⟶-sub σ (ξ-psplitᵍ r) = ξ-psplitᵍ (⟶-sub σ r)
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
⟶ᵀ-sub σ El-⌜IMu⌝ = El-⌜IMu⌝
⟶ᵀ-sub σ El-⌜Fin⌝ = El-⌜Fin⌝
⟶ᵀ-sub σ (DIh-ι D M j p) = DIh-ι _ _ _ _
⟶ᵀ-sub σ (DIh-σ D M S f p) = DIh-σ _ _ _ _ _
⟶ᵀ-sub σ (DIh-ρ D M j C p) =
  subst (λ Z → DIh (subTm σ D) (subTy (extS (extS σ)) M) (dρ (subTm σ j) (subTm σ C)) (subTm σ p) ⟶ᵀ Z)
        (sym (cong₂ Σ' (iinst-sub σ M j (fst p))
                        (cong₄ (λ a b c d → DIh a b c (snd d))
                               (wk-sub σ D) (wk2-subTy σ M) (wk-sub σ C) (wk-sub σ p))))
        (DIh-ρ _ _ _ _ _)
⟶ᵀ-sub σ (ξ-IMuᴵ r) = ξ-IMuᴵ (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-IMuᴰ r) = ξ-IMuᴰ (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-IMuⁱ r) = ξ-IMuⁱ (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-Desc r) = ξ-Desc (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-DIhᴰ r) = ξ-DIhᴰ (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-DIhᴹ r) = ξ-DIhᴹ (⟶ᵀ-sub (extS (extS σ)) r)
⟶ᵀ-sub σ (ξ-DIhᶜ r) = ξ-DIhᶜ (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-DIhᵖ r) = ξ-DIhᵖ (⟶-sub σ r)
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
