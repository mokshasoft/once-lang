------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 28 — (B2, part 2) SUBJECT REDUCTION, completed
--
-- The mechanical closing of subject reduction, on the Π-injectivity of
-- `NbEPDirDBInj` (dHoTT-26). Everything here is confluence-free and reuses the
-- strict substitution laws of `NbEPDirDBPi`/`NbEPDirDBSR`/`NbEPDirDBConf`.
--
--   * Type-level commute/cancel lemmas (`wk-cancel`, `subTy-comm`,
--     `ren-wk-comm`, `ren-comm-ty`, `exts-wk-ty`) — all via the type fusion
--     lemmas + refl/`sub-comm` bridges.
--   * `⟶ᵀ-ren`/`≅ᵀ-ren` — conversion survives renaming; `subTy-monoˢ` — types
--     are monotone in the substitution.
--   * `ren-lemma` / `sub-lemma` — TYPED renaming and substitution preserve
--     typing (the `⊢ˢ`/`Ren⊢` judgments + the ext-lemmas), and `⊢[]` — single
--     substitution preserves typing (what β needs).
--   * `gen-lam` / `gen-app` — generation (inversion through `⊢conv`).
--   * **`sr`** — SUBJECT REDUCTION: `Γ ⊢ t ∷ A → t ⟶ u → Γ ⊢ u ∷ A`. The β case
--     converts the argument to the λ's domain and the result type (via
--     `Π-inj`), sidestepping context conversion entirely.
--
-- With this, dHoTT-24's scoped ceiling is fully lifted: the kernel enjoys
-- subject reduction. `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBSubj where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; Σ; _,_; _×_ ; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam; app
        ; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr
        ; Ren; extR; renTm; renTy; Sub; extS; subTm; subTy; idₛ
        ; _∘ᵣ_; _ₛ∘ᵣ_; _ᵣ∘ₛ_; _∘ₛ_
        ; subTy-renTy; renTy-subTy; subTy-subTy; renTy-renTy
        ; subTy-cong; renTy-cong; subTy-id; subTm-renTm; subTm-id; subTm-cong
        ; renTm-renTm )
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; false; _∨_; occTm; ∨-false; ∨-false₁; ∨-false₂
        ; occ-ren-eq; occ-sub; eqv
        ; PosC; posc-var; posc-Hom; posc-ren; posc-sub )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝
        ; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; tr-J-base; tr-J-Σ; tr-taut
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; _⟶*_; done; step
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd
        ; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢conv
        ; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom
        ; ⊢ctx_; c-◇; c-▹ )
open import poc.OCP0009.NbEPDirDBSR using ( ≅ᵀ-sub; ⟶-sub )
open import poc.OCP0009.NbEPDirDBConf
  using ( ⟶-ren; ⟶*-ren; ren-comm; subTm-monoˢ; extS-mono; single-mono )
open import poc.OCP0009.NbEPDirDBSR using ( sub-comm )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans
        ; ⟶ᵀ*-El; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ
        ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ; red→≅ᵀ; Π-inj; Σ-inj
        ; church-rosserᵀ; Π-reduct; ΠRed; mkΠRed )

private
  variable
    Γ Δ : Cx

-- Transport a judgment along a type equality (fixed motive — avoids the
-- higher-order motive inference of a bare `subst`).
∋-cast : {Γ : Ctx} {x : Var ⌊ Γ ⌋} {A A' : RTy ⌊ Γ ⌋} →
         A ≡ A' → Γ ∋ x ∷ A → Γ ∋ x ∷ A'
∋-cast refl v = v

⊢-cast : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {A A' : RTy ⌊ Γ ⌋} →
         A ≡ A' → Γ ⊢ t ∷ A → Γ ⊢ t ∷ A'
⊢-cast refl d = d

------------------------------------------------------------------------
-- Type-level commute / cancel lemmas.
------------------------------------------------------------------------

wk-cancel : (a : RTm Γ) (A : RTy Γ) → subTy (single a) (renTy vs A) ≡ A
wk-cancel a A =
  trans (subTy-renTy A) (trans (subTy-cong (λ _ → refl) A) (subTy-id A))

ren-wk-comm : (ρ : Ren Γ Δ) (C : RTy Γ) →
              renTy (extR ρ) (renTy vs C) ≡ renTy vs (renTy ρ C)
ren-wk-comm ρ C =
  trans (renTy-renTy C) (trans (renTy-cong (λ _ → refl) C) (sym (renTy-renTy C)))

ren-comm-ty : (ρ : Ren Γ Δ) (D : RTy (Γ ∙)) (u : RTm Γ) →
              renTy ρ (subTy (single u) D) ≡
              subTy (single (renTm ρ u)) (renTy (extR ρ) D)
ren-comm-ty {Γ} ρ D u =
  trans (renTy-subTy D) (trans (subTy-cong bridge D) (sym (subTy-renTy D)))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           (ρ ᵣ∘ₛ single u) x ≡ (single (renTm ρ u) ₛ∘ᵣ extR ρ) x
  bridge vz     = refl
  bridge (vs x) = refl

exts-wk-ty : (σ : Sub Γ Δ) (C : RTy Γ) →
             subTy (extS σ) (renTy vs C) ≡ renTy vs (subTy σ C)
exts-wk-ty σ C =
  trans (subTy-renTy C) (trans (subTy-cong (λ _ → refl) C) (sym (renTy-subTy C)))

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

------------------------------------------------------------------------
-- Conversion survives renaming; types are monotone in the substitution.
------------------------------------------------------------------------

-- Weakening commutes with a renaming, at TERMS — both composites are
-- definitionally `x ↦ vs (ρ x)`.  The `Hom-U`/`Hom-Π` cases need it.
wk-ren : (ρ : Ren Γ Δ) (t : RTm Γ) →
         renTm (extR ρ) (renTm vs t) ≡ renTm vs (renTm ρ t)
wk-ren ρ t = trans (renTm-renTm t) (sym (renTm-renTm t))

⟶ᵀ-ren : (ρ : Ren Γ Δ) {A B : RTy Γ} → A ⟶ᵀ B → renTy ρ A ⟶ᵀ renTy ρ B
⟶ᵀ-ren ρ El-⌜base⌝    = El-⌜base⌝
⟶ᵀ-ren ρ (El-⌜Π⌝ c d) = El-⌜Π⌝ (renTm ρ c) (renTm (extR ρ) d)
⟶ᵀ-ren ρ (El-⌜Σ⌝ c d) = El-⌜Σ⌝ (renTm ρ c) (renTm (extR ρ) d)
⟶ᵀ-ren ρ (El-⌜Hom⌝ c a b) = El-⌜Hom⌝ (renTm ρ c) (renTm ρ a) (renTm ρ b)
⟶ᵀ-ren ρ (ξ-El r) = ξ-El (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-Πˡ r) = ξ-Πˡ (⟶ᵀ-ren ρ r)
⟶ᵀ-ren ρ (ξ-Πʳ r) = ξ-Πʳ (⟶ᵀ-ren (extR ρ) r)
⟶ᵀ-ren ρ (ξ-Σˡ r) = ξ-Σˡ (⟶ᵀ-ren ρ r)
⟶ᵀ-ren ρ (ξ-Σʳ r) = ξ-Σʳ (⟶ᵀ-ren (extR ρ) r)
⟶ᵀ-ren ρ (Hom-U c d) =
  subst (λ z → Hom U (renTm ρ c) (renTm ρ d) ⟶ᵀ Π (El (renTm ρ c)) (El z))
        (sym (wk-ren ρ d))
        (Hom-U (renTm ρ c) (renTm ρ d))
⟶ᵀ-ren ρ (Hom-Π A B f g) =
  subst (λ Z → Hom (Π (renTy ρ A) (renTy (extR ρ) B)) (renTm ρ f) (renTm ρ g) ⟶ᵀ Z)
        (cong₂ (λ x y → Π (renTy ρ A)
                          (Hom (renTy (extR ρ) B) (app x (var vz)) (app y (var vz))))
               (sym (wk-ren ρ f)) (sym (wk-ren ρ g)))
        (Hom-Π (renTy ρ A) (renTy (extR ρ) B) (renTm ρ f) (renTm ρ g))
⟶ᵀ-ren ρ (ξ-Homᵀ r) = ξ-Homᵀ (⟶ᵀ-ren ρ r)
⟶ᵀ-ren ρ (ξ-Homˡ r) = ξ-Homˡ (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-Homʳ r) = ξ-Homʳ (⟶-ren ρ r)

≅ᵀ-ren : (ρ : Ren Γ Δ) {A B : RTy Γ} → A ≅ᵀ B → renTy ρ A ≅ᵀ renTy ρ B
≅ᵀ-ren ρ (credᵀ r)   = credᵀ (⟶ᵀ-ren ρ r)
≅ᵀ-ren ρ crflᵀ       = crflᵀ
≅ᵀ-ren ρ (csymᵀ c)   = csymᵀ (≅ᵀ-ren ρ c)
≅ᵀ-ren ρ (ctrnᵀ c d) = ctrnᵀ (≅ᵀ-ren ρ c) (≅ᵀ-ren ρ d)

subTy-monoˢ : {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟶* σ' x) →
              (A : RTy Γ) → subTy σ A ⟶ᵀ* subTy σ' A
subTy-monoˢ h base     = doneᵀ
subTy-monoˢ h U        = doneᵀ
subTy-monoˢ h (El t)   = ⟶ᵀ*-El (subTm-monoˢ h t)
subTy-monoˢ h (Π A B)  =
  ⟶ᵀ*-trans (⟶ᵀ*-Πˡ (subTy-monoˢ h A)) (⟶ᵀ*-Πʳ (subTy-monoˢ (extS-mono h) B))
subTy-monoˢ h (Σ' A B) =
  ⟶ᵀ*-trans (⟶ᵀ*-Σˡ (subTy-monoˢ h A)) (⟶ᵀ*-Σʳ (subTy-monoˢ (extS-mono h) B))
subTy-monoˢ h (Hom A t u) =
  ⟶ᵀ*-trans (⟶ᵀ*-Homᵀ (subTy-monoˢ h A))
    (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (subTm-monoˢ h t)) (⟶ᵀ*-Homʳ (subTm-monoˢ h u)))

------------------------------------------------------------------------
-- W2 eliminator support: term-level cancels, type reduction under
-- renaming (star), occurrence preservation under reduction (`PosC`
-- survives `ξ-trᵈ`), and the reduct analyses `sr`'s new root cases need.
------------------------------------------------------------------------

wk-cancel-tm : (a t : RTm Γ) → subTm (single a) (renTm vs t) ≡ t
wk-cancel-tm a t =
  trans (subTm-renTm t) (trans (subTm-cong (λ _ → refl) t) (subTm-id t))

wk-inst : (d : RTm (Γ ∙)) → subTm (single (var vz)) (renTm (extR vs) d) ≡ d
wk-inst d =
  trans (subTm-renTm d) (trans (subTm-cong ptw d) (subTm-id d))
  where
  ptw : ∀ x → (single (var vz) ₛ∘ᵣ extR vs) x ≡ idₛ x
  ptw vz     = refl
  ptw (vs y) = refl

⟶ᵀ*-ren : (ρ : Ren Γ Δ) {A B : RTy Γ} → A ⟶ᵀ* B → renTy ρ A ⟶ᵀ* renTy ρ B
⟶ᵀ*-ren ρ doneᵀ       = doneᵀ
⟶ᵀ*-ren ρ (stepᵀ r p) = stepᵀ (⟶ᵀ-ren ρ r) (⟶ᵀ*-ren ρ p)

-- Reduction never INTRODUCES a free variable — so `PosC` (whose content
-- is vz-freeness of the motive's frozen components) survives `ξ-trᵈ`.
occ-red : {x : Var Γ} {t t' : RTm Γ} →
          t ⟶ t' → occTm x t ≡ false → occTm x t' ≡ false
occ-red {x = x} (β t u) e = occ-sub h t (∨-false₁ (occTm (vs x) t) e)
  where
  h : ∀ y → eqv (vs x) y ≡ false → occTm x (single u y) ≡ false
  h vz     _ = ∨-false₂ (occTm (vs x) t) e
  h (vs z) q = q
occ-red {x = x} (βfst a b) e = ∨-false₁ (occTm x a) e
occ-red {x = x} (βsnd a b) e = ∨-false₂ (occTm x a) e
occ-red (ξ-lam r) e = occ-red r e
occ-red {x = x} (ξ-appˡ {t = t} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x t) e)) (∨-false₂ (occTm x t) e)
occ-red {x = x} (ξ-appʳ {t = t} r) e =
  ∨-false (∨-false₁ (occTm x t) e) (occ-red r (∨-false₂ (occTm x t) e))
occ-red {x = x} (ξ-pairˡ {a = a} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x a) e)) (∨-false₂ (occTm x a) e)
occ-red {x = x} (ξ-pairʳ {a = a} r) e =
  ∨-false (∨-false₁ (occTm x a) e) (occ-red r (∨-false₂ (occTm x a) e))
occ-red (ξ-fst r) e = occ-red r e
occ-red (ξ-snd r) e = occ-red r e
occ-red {x = x} (ξ-⌜Π⌝ˡ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-⌜Π⌝ʳ {c = c} r) e =
  ∨-false (∨-false₁ (occTm x c) e) (occ-red r (∨-false₂ (occTm x c) e))
occ-red {x = x} (ξ-⌜Σ⌝ˡ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-⌜Σ⌝ʳ {c = c} r) e =
  ∨-false (∨-false₁ (occTm x c) e) (occ-red r (∨-false₂ (occTm x c) e))
occ-red {x = x} (tr-J-base d s e₀) e =
  ∨-false₂ (occTm x (hrefl ⌜base⌝ s)) (∨-false₂ (occTm (vs x) d) e)
occ-red {x = x} (tr-J-Σ d c₁ c₂ s e₀) e =
  ∨-false₂ (occTm x (hrefl (⌜Σ⌝ c₁ c₂) s)) (∨-false₂ (occTm (vs x) d) e)
occ-red (tr-taut f e₀) e = e
occ-red {x = x} (ξ-⌜Hom⌝ᶜ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-⌜Hom⌝ˡ {c = c} {a = a} r) e =
  ∨-false (∨-false₁ (occTm x c) e)
          (∨-false (occ-red r (∨-false₁ (occTm x a) (∨-false₂ (occTm x c) e)))
                   (∨-false₂ (occTm x a) (∨-false₂ (occTm x c) e)))
occ-red {x = x} (ξ-⌜Hom⌝ʳ {c = c} {a = a} r) e =
  ∨-false (∨-false₁ (occTm x c) e)
          (∨-false (∨-false₁ (occTm x a) (∨-false₂ (occTm x c) e))
                   (occ-red r (∨-false₂ (occTm x a) (∨-false₂ (occTm x c) e))))
occ-red {x = x} (ξ-hreflᶜ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-hreflᵃ {c = c} r) e =
  ∨-false (∨-false₁ (occTm x c) e) (occ-red r (∨-false₂ (occTm x c) e))
occ-red {x = x} (ξ-trᵈ {d = d} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm (vs x) d) e)) (∨-false₂ (occTm (vs x) d) e)
occ-red {x = x} (ξ-trᵖ {d = d} {p = p} r) e =
  ∨-false (∨-false₁ (occTm (vs x) d) e)
          (∨-false (occ-red r (∨-false₁ (occTm x p) (∨-false₂ (occTm (vs x) d) e)))
                   (∨-false₂ (occTm x p) (∨-false₂ (occTm (vs x) d) e)))
occ-red {x = x} (ξ-trᵉ {d = d} {p = p} r) e =
  ∨-false (∨-false₁ (occTm (vs x) d) e)
          (∨-false (∨-false₁ (occTm x p) (∨-false₂ (occTm (vs x) d) e))
                   (occ-red r (∨-false₂ (occTm x p) (∨-false₂ (occTm (vs x) d) e))))

posc-red : {d d' : RTm (Γ ∙)} → PosC vz d → d ⟶ d' → PosC vz d'
posc-red posc-var ()
posc-red (posc-Hom hc ha) (ξ-⌜Hom⌝ᶜ r) = posc-Hom (occ-red r hc) ha
posc-red (posc-Hom hc ha) (ξ-⌜Hom⌝ˡ r) = posc-Hom hc (occ-red r ha)
posc-red (posc-Hom hc ha) (ξ-⌜Hom⌝ʳ ())

------------------------------------------------------------------------
-- Reduct analyses for `sr`'s J and taut cases.  A `Hom` whose ambient
-- satisfies a reduction-closed, U/Π-free predicate never unfolds, so its
-- reducts are `Hom`s with componentwise reductions; a `Hom` that reduces
-- to a `Π` did unfold exactly once, via `Hom-U` or `Hom-Π`.
------------------------------------------------------------------------

record HomRed {Γ} (A : RTy Γ) (t u : RTm Γ)
              (A' : RTy Γ) (t' u' : RTm Γ) : Set where
  constructor mkHomRed
  field
    rA : A ⟶ᵀ* A'
    rt : t ⟶* t'
    ru : u ⟶* u'

Hom-to-Hom : {A A' : RTy Γ} {t u t' u' : RTm Γ} →
             Hom A t u ⟶ᵀ* Hom A' t' u' → HomRed A t u A' t' u'
Hom-to-Hom doneᵀ = mkHomRed doneᵀ done done
Hom-to-Hom (stepᵀ (ξ-Homᵀ r) rest) with Hom-to-Hom rest
... | mkHomRed rA rt ru = mkHomRed (stepᵀ r rA) rt ru
Hom-to-Hom (stepᵀ (ξ-Homˡ r) rest) with Hom-to-Hom rest
... | mkHomRed rA rt ru = mkHomRed rA (step r rt) ru
Hom-to-Hom (stepᵀ (ξ-Homʳ r) rest) with Hom-to-Hom rest
... | mkHomRed rA rt ru = mkHomRed rA rt (step r ru)
Hom-to-Hom (stepᵀ (Hom-U c d) rest) with Π-reduct rest
... | mkΠRed _ _ () _ _
Hom-to-Hom (stepᵀ (Hom-Π A B f g) rest) with Π-reduct rest
... | mkΠRed _ _ () _ _

homred-inv : {P : RTy Γ → Set} →
             (∀ {X Y : RTy Γ} → P X → X ⟶ᵀ Y → P Y) →
             (P U → ⊥) →
             (∀ {F : RTy Γ} {G : RTy (Γ ∙)} → P (Π F G) → ⊥) →
             {A : RTy Γ} {t u : RTm Γ} {C : RTy Γ} →
             P A → Hom A t u ⟶ᵀ* C →
             Σ (RTy Γ) (λ A' → Σ (RTm Γ) (λ t' → Σ (RTm Γ) (λ u' →
               (C ≡ Hom A' t' u') × ((t ⟶* t') × (u ⟶* u')))))
homred-inv pres noU noΠ pA doneᵀ = _ , (_ , (_ , (refl , (done , done))))
homred-inv pres noU noΠ pA (stepᵀ (ξ-Homᵀ r) rest) =
  homred-inv pres noU noΠ (pres pA r) rest
homred-inv pres noU noΠ pA (stepᵀ (ξ-Homˡ r) rest)
  with homred-inv pres noU noΠ pA rest
... | A' , (t' , (u' , (eq , (rt , ru)))) =
      A' , (t' , (u' , (eq , (step r rt , ru))))
homred-inv pres noU noΠ pA (stepᵀ (ξ-Homʳ r) rest)
  with homred-inv pres noU noΠ pA rest
... | A' , (t' , (u' , (eq , (rt , ru)))) =
      A' , (t' , (u' , (eq , (rt , step r ru))))
homred-inv pres noU noΠ pA (stepᵀ (Hom-U c d) rest) with noU pA
... | ()
homred-inv pres noU noΠ pA (stepᵀ (Hom-Π A B f g) rest) with noΠ pA
... | ()

data BaseAmb {Γ} : RTy Γ → Set where
  ba-el   : BaseAmb (El (⌜base⌝ {Γ}))
  ba-base : BaseAmb (base {Γ})

baseamb-red : {X Y : RTy Γ} → BaseAmb X → X ⟶ᵀ Y → BaseAmb Y
baseamb-red ba-el El-⌜base⌝ = ba-base
baseamb-red ba-el (ξ-El ())
baseamb-red ba-base ()

data ΣAmb {Γ} : RTy Γ → Set where
  sa-el : {c : RTm Γ} {d : RTm (Γ ∙)} → ΣAmb (El (⌜Σ⌝ c d))
  sa-Σ  : {A : RTy Γ} {B : RTy (Γ ∙)} → ΣAmb (Σ' A B)

σamb-red : {X Y : RTy Γ} → ΣAmb X → X ⟶ᵀ Y → ΣAmb Y
σamb-red sa-el (El-⌜Σ⌝ c d)      = sa-Σ
σamb-red sa-el (ξ-El (ξ-⌜Σ⌝ˡ r)) = sa-el
σamb-red sa-el (ξ-El (ξ-⌜Σ⌝ʳ r)) = sa-el
σamb-red sa-Σ  (ξ-Σˡ r)          = sa-Σ
σamb-red sa-Σ  (ξ-Σʳ r)          = sa-Σ

U-reduct : {C : RTy Γ} → U ⟶ᵀ* C → C ≡ U
U-reduct doneᵀ        = refl
U-reduct (stepᵀ () _)

data HomToΠ {Γ} (A : RTy Γ) (t u : RTm Γ)
            (P : RTy Γ) (Q : RTy (Γ ∙)) : Set where
  via-U : {t₁ u₁ : RTm Γ} →
          A ⟶ᵀ* U → t ⟶* t₁ → u ⟶* u₁ →
          El t₁ ⟶ᵀ* P → El (renTm vs u₁) ⟶ᵀ* Q →
          HomToΠ A t u P Q
  via-Π : {F : RTy Γ} {G : RTy (Γ ∙)} →
          A ⟶ᵀ* Π F G →
          HomToΠ A t u P Q

hom-to-Π : {A : RTy Γ} {t u : RTm Γ} {P : RTy Γ} {Q : RTy (Γ ∙)} →
           Hom A t u ⟶ᵀ* Π P Q → HomToΠ A t u P Q
hom-to-Π (stepᵀ (ξ-Homᵀ r) rest) with hom-to-Π rest
... | via-U rA rt ru rP rQ = via-U (stepᵀ r rA) rt ru rP rQ
... | via-Π rA             = via-Π (stepᵀ r rA)
hom-to-Π (stepᵀ (ξ-Homˡ r) rest) with hom-to-Π rest
... | via-U rA rt ru rP rQ = via-U rA (step r rt) ru rP rQ
... | via-Π rA             = via-Π rA
hom-to-Π (stepᵀ (ξ-Homʳ r) rest) with hom-to-Π rest
... | via-U rA rt ru rP rQ = via-U rA rt (step r ru) rP rQ
... | via-Π rA             = via-Π rA
hom-to-Π (stepᵀ (Hom-U c d) rest) with Π-reduct rest
... | mkΠRed _ _ refl rP rQ = via-U doneᵀ done done rP rQ
hom-to-Π (stepᵀ (Hom-Π A B f g) rest) = via-Π doneᵀ

-- transporting the payload's type across convertible endpoints
mono-El[] : (d₀ : RTm (Γ ∙)) {t w : RTm Γ} → t ⟶* w →
            El (subTm (single t) d₀) ≅ᵀ El (subTm (single w) d₀)
mono-El[] d₀ r = red→≅ᵀ (⟶ᵀ*-El (subTm-monoˢ (single-mono r) d₀))

-- inversion of a step on a `⌜Hom⌝`-headed term
data HomStep {Γ} (c a m : RTm Γ) : RTm Γ → Set where
  hsᶜ : {c' : RTm Γ} → c ⟶ c' → HomStep c a m (⌜Hom⌝ c' a m)
  hsˡ : {a' : RTm Γ} → a ⟶ a' → HomStep c a m (⌜Hom⌝ c a' m)
  hsʳ : {m' : RTm Γ} → m ⟶ m' → HomStep c a m (⌜Hom⌝ c a m')

hom-step : {c a m x : RTm Γ} → ⌜Hom⌝ c a m ⟶ x → HomStep c a m x
hom-step (ξ-⌜Hom⌝ᶜ r) = hsᶜ r
hom-step (ξ-⌜Hom⌝ˡ r) = hsˡ r
hom-step (ξ-⌜Hom⌝ʳ r) = hsʳ r

------------------------------------------------------------------------
-- Typed renaming preserves typing.
------------------------------------------------------------------------

Ren⊢ : (Γ Δ : Ctx) → Ren ⌊ Γ ⌋ ⌊ Δ ⌋ → Set
Ren⊢ Γ Δ ρ = ∀ {x A} → Γ ∋ x ∷ A → Δ ∋ ρ x ∷ renTy ρ A

Ren⊢-ext : {Γ Δ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Δ ⌋} {C : RTy ⌊ Γ ⌋} →
           Ren⊢ Γ Δ ρ → Ren⊢ (Γ ▹ C) (Δ ▹ renTy ρ C) (extR ρ)
Ren⊢-ext {ρ = ρ} {C = C} h here =
  ∋-cast (sym (ren-wk-comm ρ C)) here
Ren⊢-ext {ρ = ρ} h (there {A = A₀} v) =
  ∋-cast (sym (ren-wk-comm ρ A₀)) (there (h v))

-- Typed renaming, now MUTUAL with renaming for TYPE FORMATION: `⊢lam`/`⊢pair`
-- carry `⊢ty` premises (2026-07-30, option A), so the two must move together.
ren-lemma : {Γ Δ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Δ ⌋} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
            Γ ⊢ t ∷ A → Ren⊢ Γ Δ ρ → Δ ⊢ renTm ρ t ∷ renTy ρ A
ren-ty : {Γ Δ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Δ ⌋} {A : RTy ⌊ Γ ⌋} →
         Γ ⊢ty A → Ren⊢ Γ Δ ρ → Δ ⊢ty renTy ρ A

ren-ty ty-base       h = ty-base
ren-ty ty-U          h = ty-U
ren-ty (ty-Π dA dB)  h = ty-Π (ren-ty dA h) (ren-ty dB (Ren⊢-ext h))
ren-ty (ty-Σ dA dB)  h = ty-Σ (ren-ty dA h) (ren-ty dB (Ren⊢-ext h))
ren-ty (ty-El dc)    h = ty-El (ren-lemma dc h)
ren-ty (ty-Hom dA dt du) h =
  ty-Hom (ren-ty dA h) (ren-lemma dt h) (ren-lemma du h)

ren-lemma (⊢var v) h = ⊢var (h v)
ren-lemma (⊢lam dA d) h = ⊢lam (ren-ty dA h) (ren-lemma d (Ren⊢-ext h))
ren-lemma {ρ = ρ} (⊢app {B = D} {u = u} d₁ d₂) h =
  ⊢-cast (sym (ren-comm-ty ρ D u)) (⊢app (ren-lemma d₁ h) (ren-lemma d₂ h))
ren-lemma {ρ = ρ} (⊢pair {B = B} {a = a} dB d₁ d₂) h =
  ⊢pair (ren-ty dB (Ren⊢-ext h))
        (ren-lemma d₁ h) (⊢-cast (ren-comm-ty ρ B a) (ren-lemma d₂ h))
ren-lemma (⊢fst d) h = ⊢fst (ren-lemma d h)
ren-lemma {ρ = ρ} (⊢snd {B = B} {p = p} d) h =
  ⊢-cast (sym (ren-comm-ty ρ B (fst p))) (⊢snd (ren-lemma d h))
ren-lemma ⊢⌜base⌝ h = ⊢⌜base⌝
ren-lemma (⊢⌜Π⌝ dc dd) h = ⊢⌜Π⌝ (ren-lemma dc h) (ren-lemma dd (Ren⊢-ext h))
ren-lemma (⊢⌜Σ⌝ dc dd) h = ⊢⌜Σ⌝ (ren-lemma dc h) (ren-lemma dd (Ren⊢-ext h))
ren-lemma (⊢⌜Hom⌝ dc da db) h =
  ⊢⌜Hom⌝ (ren-lemma dc h) (ren-lemma da h) (ren-lemma db h)
ren-lemma (⊢hrefl dc dt) h = ⊢hrefl (ren-lemma dc h) (ren-lemma dt h)
ren-lemma {ρ = ρ} (⊢tr {c = cM} {a = aM} {t = t} {u = u} dc da dv hc ha dt du dp de) h
  with posc-ren {ρ = ρ} (posc-Hom {c = cM} {a = aM} hc ha)
... | posc-Hom hc' ha' =
      ⊢-cast (cong El (sym (ren-comm ρ (⌜Hom⌝ cM aM (var vz)) u)))
        (⊢tr {c = renTm (extR ρ) cM} {a = renTm (extR ρ) aM}
             {t = renTm ρ t} {u = renTm ρ u}
             (ren-lemma dc (Ren⊢-ext h)) (ren-lemma da (Ren⊢-ext h))
             (ren-lemma dv (Ren⊢-ext h)) hc' ha'
             (ren-lemma dt h) (ren-lemma du h) (ren-lemma dp h)
             (⊢-cast (cong El (ren-comm ρ (⌜Hom⌝ cM aM (var vz)) t))
                     (ren-lemma de h)))
ren-lemma {ρ = ρ} (⊢conv d c) h = ⊢conv (ren-lemma d h) (≅ᵀ-ren ρ c)

⊢wk : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
      Γ ⊢ t ∷ A → (Γ ▹ B) ⊢ renTm vs t ∷ renTy vs A
⊢wk d = ren-lemma d there

------------------------------------------------------------------------
-- Typed substitution preserves typing, and single substitution.
------------------------------------------------------------------------

Sub⊢ : (Γ Δ : Ctx) → Sub ⌊ Γ ⌋ ⌊ Δ ⌋ → Set
Sub⊢ Γ Δ σ = ∀ {x A} → Γ ∋ x ∷ A → Δ ⊢ subTm σ (var x) ∷ subTy σ A

Sub⊢-ext : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {C : RTy ⌊ Γ ⌋} →
           Sub⊢ Γ Δ σ → Sub⊢ (Γ ▹ C) (Δ ▹ subTy σ C) (extS σ)
Sub⊢-ext {σ = σ} {C = C} h here =
  ⊢-cast (sym (exts-wk-ty σ C)) (⊢var here)
Sub⊢-ext {σ = σ} h (there {A = A₀} v) =
  ⊢-cast (sym (exts-wk-ty σ A₀)) (⊢wk (h v))

sub-lemma : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
            Γ ⊢ t ∷ A → Sub⊢ Γ Δ σ → Δ ⊢ subTm σ t ∷ subTy σ A
sub-ty : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {A : RTy ⌊ Γ ⌋} →
         Γ ⊢ty A → Sub⊢ Γ Δ σ → Δ ⊢ty subTy σ A

sub-ty ty-base      h = ty-base
sub-ty ty-U         h = ty-U
sub-ty (ty-Π dA dB) h = ty-Π (sub-ty dA h) (sub-ty dB (Sub⊢-ext h))
sub-ty (ty-Σ dA dB) h = ty-Σ (sub-ty dA h) (sub-ty dB (Sub⊢-ext h))
sub-ty (ty-El dc)   h = ty-El (sub-lemma dc h)
sub-ty (ty-Hom dA dt du) h =
  ty-Hom (sub-ty dA h) (sub-lemma dt h) (sub-lemma du h)

sub-lemma (⊢var v) h = h v
sub-lemma (⊢lam dA d) h = ⊢lam (sub-ty dA h) (sub-lemma d (Sub⊢-ext h))
sub-lemma {σ = σ} (⊢app {B = D} {u = u} d₁ d₂) h =
  ⊢-cast (sym (subTy-comm σ D u)) (⊢app (sub-lemma d₁ h) (sub-lemma d₂ h))
sub-lemma {σ = σ} (⊢pair {B = B} {a = a} dB d₁ d₂) h =
  ⊢pair (sub-ty dB (Sub⊢-ext h))
        (sub-lemma d₁ h) (⊢-cast (subTy-comm σ B a) (sub-lemma d₂ h))
sub-lemma (⊢fst d) h = ⊢fst (sub-lemma d h)
sub-lemma {σ = σ} (⊢snd {B = B} {p = p} d) h =
  ⊢-cast (sym (subTy-comm σ B (fst p))) (⊢snd (sub-lemma d h))
sub-lemma ⊢⌜base⌝ h = ⊢⌜base⌝
sub-lemma (⊢⌜Π⌝ dc dd) h = ⊢⌜Π⌝ (sub-lemma dc h) (sub-lemma dd (Sub⊢-ext h))
sub-lemma (⊢⌜Σ⌝ dc dd) h = ⊢⌜Σ⌝ (sub-lemma dc h) (sub-lemma dd (Sub⊢-ext h))
sub-lemma (⊢⌜Hom⌝ dc da db) h =
  ⊢⌜Hom⌝ (sub-lemma dc h) (sub-lemma da h) (sub-lemma db h)
sub-lemma (⊢hrefl dc dt) h = ⊢hrefl (sub-lemma dc h) (sub-lemma dt h)
sub-lemma {σ = σ} (⊢tr {c = cM} {a = aM} {t = t} {u = u} dc da dv hc ha dt du dp de) h
  with posc-sub {σ = σ} (posc-Hom {c = cM} {a = aM} hc ha)
... | posc-Hom hc' ha' =
      ⊢-cast (cong El (sym (sub-comm σ (⌜Hom⌝ cM aM (var vz)) u)))
        (⊢tr {c = subTm (extS σ) cM} {a = subTm (extS σ) aM}
             {t = subTm σ t} {u = subTm σ u}
             (sub-lemma dc (Sub⊢-ext h)) (sub-lemma da (Sub⊢-ext h))
             (sub-lemma dv (Sub⊢-ext h)) hc' ha'
             (sub-lemma dt h) (sub-lemma du h) (sub-lemma dp h)
             (⊢-cast (cong El (sub-comm σ (⌜Hom⌝ cM aM (var vz)) t))
                     (sub-lemma de h)))
sub-lemma {σ = σ} (⊢conv d c) h = ⊢conv (sub-lemma d h) (≅ᵀ-sub σ c)

⊢[] : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {t : RTm (⌊ Γ ⌋ ∙)} {B : RTy (⌊ Γ ⌋ ∙)}
      {a : RTm ⌊ Γ ⌋} →
      (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ a ∷ A → Γ ⊢ subTm (single a) t ∷ subTy (single a) B
⊢[] {A = A} {a = a} dt da = sub-lemma dt single⊢
  where
  single⊢ : Sub⊢ _ _ (single a)
  single⊢ here          = ⊢-cast (sym (wk-cancel a A)) da
  single⊢ (there {A = A₀} v) = ⊢-cast (sym (wk-cancel a A₀)) (⊢var v)

-- Context conversion: converting the LAST context entry along `≅ᵀ`. Derived
-- from the substitution lemma (identity substitution, with `⊢conv` at `vz`),
-- sidestepping the induction-on-derivation obstruction.
conv-ctx : {Γ : Ctx} {A A' : RTy ⌊ Γ ⌋} → A ≅ᵀ A' →
           {t : RTm (⌊ Γ ⌋ ∙)} {B : RTy (⌊ Γ ⌋ ∙)} →
           (Γ ▹ A) ⊢ t ∷ B → (Γ ▹ A') ⊢ t ∷ B
conv-ctx {Γ} {A} {A'} c {t} {B} d =
  ⊢-cast (subTy-id B)
    (subst (λ z → (Γ ▹ A') ⊢ z ∷ subTy idₛ B) (subTm-id t) (sub-lemma d idₛ⊢))
  where
  idₛ⊢ : Sub⊢ (Γ ▹ A) (Γ ▹ A') idₛ
  idₛ⊢ here =
    ⊢-cast (sym (subTy-id (renTy vs A))) (⊢conv (⊢var here) (csymᵀ (≅ᵀ-ren vs c)))
  idₛ⊢ (there {A = A₀} v) =
    ⊢-cast (sym (subTy-id (renTy vs A₀))) (⊢var (there v))

------------------------------------------------------------------------
-- Generation (inversion through `⊢conv`).
------------------------------------------------------------------------

gen-lam : {Γ : Ctx} {s : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} → Γ ⊢ lam s ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (C ≅ᵀ Π A B) × ((Γ ⊢ty A) × ((Γ ▹ A) ⊢ s ∷ B))))
-- ⚠ now also returns the DOMAIN's well-formedness: `sr`'s `ξ-lam` case
-- reconstructs a `⊢lam`, which needs it (2026-07-30, option A).
gen-lam (⊢lam dA d) = _ , (_ , (crflᵀ , (dA , d)))
gen-lam (⊢conv d c) with gen-lam d
... | A , (B , (c' , (dA , ds))) = A , (B , (ctrnᵀ (csymᵀ c) c' , (dA , ds)))

gen-app : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ app t u ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (Γ ⊢ t ∷ Π A B) × ((Γ ⊢ u ∷ A) × (C ≅ᵀ subTy (single u) B))))
gen-app (⊢app d₁ d₂) = _ , (_ , (d₁ , (d₂ , crflᵀ)))
gen-app (⊢conv d c) with gen-app d
... | A , (B , (d₁ , (d₂ , c'))) = A , (B , (d₁ , (d₂ , ctrnᵀ (csymᵀ c) c')))

gen-pair : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ pair a b ∷ C →
           Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
             (C ≅ᵀ Σ' A B) ×
             (((Γ ▹ A) ⊢ty B) × ((Γ ⊢ a ∷ A) × (Γ ⊢ b ∷ subTy (single a) B)))))
-- ⚠ likewise returns the CODOMAIN's well-formedness, for `sr`'s `ξ-pair*`.
gen-pair (⊢pair dB da db) = _ , (_ , (crflᵀ , (dB , (da , db))))
gen-pair (⊢conv d c) with gen-pair d
... | A , (B , (c' , (dB , (da , db)))) =
      A , (B , (ctrnᵀ (csymᵀ c) c' , (dB , (da , db))))

gen-fst : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ fst p ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (Γ ⊢ p ∷ Σ' A B) × (C ≅ᵀ A)))
gen-fst (⊢fst d) = _ , (_ , (d , crflᵀ))
gen-fst (⊢conv d c) with gen-fst d
... | A , (B , (dp , c')) = A , (B , (dp , ctrnᵀ (csymᵀ c) c'))

gen-snd : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ snd p ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (Γ ⊢ p ∷ Σ' A B) × (C ≅ᵀ subTy (single (fst p)) B)))
gen-snd (⊢snd d) = _ , (_ , (d , crflᵀ))
gen-snd (⊢conv d c) with gen-snd d
... | A , (B , (dp , c')) = A , (B , (dp , ctrnᵀ (csymᵀ c) c'))

gen-⌜Π⌝ : {Γ : Ctx} {c : RTm ⌊ Γ ⌋} {d : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} →
          Γ ⊢ ⌜Π⌝ c d ∷ C →
          (Γ ⊢ c ∷ U) × (((Γ ▹ El c) ⊢ d ∷ U) × (C ≅ᵀ U))
gen-⌜Π⌝ (⊢⌜Π⌝ dc dd) = dc , (dd , crflᵀ)
gen-⌜Π⌝ (⊢conv d c) with gen-⌜Π⌝ d
... | (dc , (dd , c')) = dc , (dd , ctrnᵀ (csymᵀ c) c')

gen-⌜Σ⌝ : {Γ : Ctx} {c : RTm ⌊ Γ ⌋} {d : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} →
          Γ ⊢ ⌜Σ⌝ c d ∷ C →
          (Γ ⊢ c ∷ U) × (((Γ ▹ El c) ⊢ d ∷ U) × (C ≅ᵀ U))
gen-⌜Σ⌝ (⊢⌜Σ⌝ dc dd) = dc , (dd , crflᵀ)
gen-⌜Σ⌝ (⊢conv d c) with gen-⌜Σ⌝ d
... | (dc , (dd , c')) = dc , (dd , ctrnᵀ (csymᵀ c) c')

gen-var : {Γ : Ctx} {x : Var ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ var x ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → (Γ ∋ x ∷ A) × (C ≅ᵀ A))
gen-var (⊢var v) = _ , (v , crflᵀ)
gen-var (⊢conv d c) with gen-var d
... | A , (v , c') = A , (v , ctrnᵀ (csymᵀ c) c')

gen-⌜Hom⌝ : {Γ : Ctx} {c a b : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ ⌜Hom⌝ c a b ∷ C →
            (Γ ⊢ c ∷ U) × ((Γ ⊢ a ∷ El c) × ((Γ ⊢ b ∷ El c) × (C ≅ᵀ U)))
gen-⌜Hom⌝ (⊢⌜Hom⌝ dc da db) = dc , (da , (db , crflᵀ))
gen-⌜Hom⌝ (⊢conv d c) with gen-⌜Hom⌝ d
... | (dc , (da , (db , c'))) = dc , (da , (db , ctrnᵀ (csymᵀ c) c'))

gen-hrefl : {Γ : Ctx} {c t₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ hrefl c t₀ ∷ C →
            (Γ ⊢ c ∷ U) × ((Γ ⊢ t₀ ∷ El c) × (C ≅ᵀ Hom (El c) t₀ t₀))
gen-hrefl (⊢hrefl dc dt) = dc , (dt , crflᵀ)
gen-hrefl (⊢conv d c) with gen-hrefl d
... | (dc , (dt , c')) = dc , (dt , ctrnᵀ (csymᵀ c) c')

-- Inversion for `⊢tr` (stage 2: the composition motive, pinned in the
-- rule).  `deq` records that ANY typeable `tr`-motive has that shape.
record TrInv (Γ : Ctx) (d₀ : RTm (⌊ Γ ⌋ ∙)) (p e : RTm ⌊ Γ ⌋)
             (C : RTy ⌊ Γ ⌋) : Set where
  constructor mkTrInv
  field
    cM aM : RTm (⌊ Γ ⌋ ∙)
    deq  : d₀ ≡ ⌜Hom⌝ cM aM (var vz)
    A    : RTy ⌊ Γ ⌋
    t u  : RTm ⌊ Γ ⌋
    dcM  : (Γ ▹ A) ⊢ cM ∷ U
    daM  : (Γ ▹ A) ⊢ aM ∷ El cM
    dvM  : (Γ ▹ A) ⊢ var vz ∷ El cM
    hcM  : occTm vz cM ≡ false
    haM  : occTm vz aM ≡ false
    dt   : Γ ⊢ t ∷ A
    du   : Γ ⊢ u ∷ A
    dp   : Γ ⊢ p ∷ Hom A t u
    de   : Γ ⊢ e ∷ El (subTm (single t) (⌜Hom⌝ cM aM (var vz)))
    cC   : C ≅ᵀ El (subTm (single u) (⌜Hom⌝ cM aM (var vz)))

gen-tr : {Γ : Ctx} {d₀ : RTm (⌊ Γ ⌋ ∙)} {p e : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
         Γ ⊢ tr d₀ p e ∷ C → TrInv Γ d₀ p e C
gen-tr (⊢tr dc da dv hc ha dt du dp de) =
  mkTrInv _ _ refl _ _ _ dc da dv hc ha dt du dp de crflᵀ
gen-tr (⊢conv d c) with gen-tr d
... | mkTrInv cM aM deq A t u dc da dv hc ha dt du dp de cC =
      mkTrInv cM aM deq A t u dc da dv hc ha dt du dp de (ctrnᵀ (csymᵀ c) cC)

------------------------------------------------------------------------
-- ★ SUBJECT REDUCTION.
------------------------------------------------------------------------

sr : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ A → t ⟶ u → Γ ⊢ u ∷ A
sr d (β s a) with gen-app d
... | A₀ , (B₀ , (d-lam , (d-a , cC))) with gen-lam d-lam
...   | A₁ , (B₁ , (cΠ , (tyA₁ , d-s))) with Π-inj cΠ
...     | (cA , cB) =
          ⊢conv (⊢[] d-s (⊢conv d-a cA))
                (ctrnᵀ (≅ᵀ-sub (single a) (csymᵀ cB)) (csymᵀ cC))
sr d (ξ-lam r) with gen-lam d
... | A₀ , (B₀ , (cΠ , (tyA₀ , d-s))) =
      ⊢conv (⊢lam tyA₀ (sr d-s r)) (csymᵀ cΠ)
sr d (ξ-appˡ r) with gen-app d
... | A₀ , (B₀ , (d-t , (d-u , cC))) = ⊢conv (⊢app (sr d-t r) d-u) (csymᵀ cC)
sr d (ξ-appʳ {u = u} {u' = u'} r) with gen-app d
... | A₀ , (B₀ , (d-t , (d-u , cC))) =
      ⊢conv (⊢app d-t (sr d-u r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) B₀))))
sr d (βfst a b) with gen-fst d
... | A₀ , (B₀ , (d-pair , cC)) with gen-pair d-pair
...   | A₁ , (B₁ , (cΣ , (tyB₁ , (d-a , d-b)))) with Σ-inj cΣ
...     | (cA , cB) = ⊢conv d-a (csymᵀ (ctrnᵀ cC cA))
sr d (βsnd a b) with gen-snd d
... | A₀ , (B₀ , (d-pair , cC)) with gen-pair d-pair
...   | A₁ , (B₁ , (cΣ , (tyB₁ , (d-a , d-b)))) with Σ-inj cΣ
...     | (cA , cB) =
          ⊢conv d-b
            (csymᵀ (ctrnᵀ cC
              (ctrnᵀ (red→≅ᵀ (subTy-monoˢ (single-mono (step (βfst a b) done)) B₀))
                     (≅ᵀ-sub (single a) cB))))
sr d (ξ-pairˡ r) with gen-pair d
... | A₀ , (B₀ , (cΣ , (tyB₀ , (d-a , d-b)))) =
      ⊢conv (⊢pair tyB₀ (sr d-a r)
              (⊢conv d-b (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) B₀))))
            (csymᵀ cΣ)
sr d (ξ-pairʳ r) with gen-pair d
... | A₀ , (B₀ , (cΣ , (tyB₀ , (d-a , d-b)))) =
      ⊢conv (⊢pair tyB₀ d-a (sr d-b r)) (csymᵀ cΣ)
sr d (ξ-fst r) with gen-fst d
... | A₀ , (B₀ , (d-p , cC)) = ⊢conv (⊢fst (sr d-p r)) (csymᵀ cC)
sr d (ξ-snd r) with gen-snd d
... | A₀ , (B₀ , (d-p , cC)) =
      ⊢conv (⊢snd (sr d-p r))
        (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step (ξ-fst r) done)) B₀))))
sr d (ξ-⌜Π⌝ˡ r) with gen-⌜Π⌝ d
... | (dc , (dd , cU)) =
      ⊢conv (⊢⌜Π⌝ (sr dc r) (conv-ctx (credᵀ (ξ-El r)) dd)) (csymᵀ cU)
sr d (ξ-⌜Π⌝ʳ r) with gen-⌜Π⌝ d
... | (dc , (dd , cU)) = ⊢conv (⊢⌜Π⌝ dc (sr dd r)) (csymᵀ cU)
sr d (ξ-⌜Σ⌝ˡ r) with gen-⌜Σ⌝ d
... | (dc , (dd , cU)) =
      ⊢conv (⊢⌜Σ⌝ (sr dc r) (conv-ctx (credᵀ (ξ-El r)) dd)) (csymᵀ cU)
sr d (ξ-⌜Σ⌝ʳ r) with gen-⌜Σ⌝ d
... | (dc , (dd , cU)) = ⊢conv (⊢⌜Σ⌝ dc (sr dd r)) (csymᵀ cU)
-- `tr`-rule reductions (stage 2).  The J cases extract the endpoint
-- conversion a canonical identity path witnesses via confluence
-- (stuck-ambient `Hom`s never unfold, so reducts decompose
-- componentwise); the taut case is VACUOUS in the base judgment — the
-- rule pins the motive to a `⌜Hom⌝`, never `var vz`.
sr d (tr-J-base d₂ s e₀) with gen-tr d
... | mkTrInv cM aM refl A t u dcM daM dvM hcM haM dt du dp de cC with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR) with homred-inv baseamb-red (λ ()) (λ ()) ba-el rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] d₂ rt)
                         (ctrnᵀ (csymᵀ (mono-El[] d₂ rs₁))
                           (ctrnᵀ (mono-El[] d₂ rs₂)
                             (csymᵀ (mono-El[] d₂ ru)))))
                       (csymᵀ cC))
sr d (tr-J-Σ d₂ c₁ c₂ s e₀) with gen-tr d
... | mkTrInv cM aM refl A t u dcM daM dvM hcM haM dt du dp de cC with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR) with homred-inv σamb-red (λ ()) (λ ()) sa-el rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] d₂ rt)
                         (ctrnᵀ (csymᵀ (mono-El[] d₂ rs₁))
                           (ctrnᵀ (mono-El[] d₂ rs₂)
                             (csymᵀ (mono-El[] d₂ ru)))))
                       (csymᵀ cC))
sr d (tr-taut f e₀) with gen-tr d
... | mkTrInv cM aM () A t u dcM daM dvM hcM haM dt du dp de cC
-- congruence cases for the three new formers.
sr d (ξ-⌜Hom⌝ᶜ r) with gen-⌜Hom⌝ d
... | (dc , (da , (db , cU))) =
      ⊢conv (⊢⌜Hom⌝ (sr dc r) (⊢conv da (credᵀ (ξ-El r)))
                    (⊢conv db (credᵀ (ξ-El r))))
            (csymᵀ cU)
sr d (ξ-⌜Hom⌝ˡ r) with gen-⌜Hom⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Hom⌝ dc (sr da r) db) (csymᵀ cU)
sr d (ξ-⌜Hom⌝ʳ r) with gen-⌜Hom⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Hom⌝ dc da (sr db r)) (csymᵀ cU)
sr d (ξ-hreflᶜ r) with gen-hrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢hrefl (sr dc r) (⊢conv dt (credᵀ (ξ-El r))))
            (csymᵀ (ctrnᵀ cH (credᵀ (ξ-Homᵀ (ξ-El r)))))
sr d (ξ-hreflᵃ r) with gen-hrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢hrefl dc (sr dt r))
            (csymᵀ (ctrnᵀ cH (ctrnᵀ (credᵀ (ξ-Homˡ r)) (credᵀ (ξ-Homʳ r)))))
sr d (ξ-trᵈ r) with gen-tr d
... | mkTrInv cM aM refl A t u dcM daM dvM hcM haM dt du dp de cC with hom-step r
...   | hsᶜ rc =
        ⊢conv (⊢tr (sr dcM rc) (⊢conv daM (credᵀ (ξ-El rc)))
                   (⊢conv dvM (credᵀ (ξ-El rc)))
                   (occ-red rc hcM) haM dt du dp
                   (⊢conv de (credᵀ (ξ-El (⟶-sub (single t) r)))))
              (csymᵀ (ctrnᵀ cC (credᵀ (ξ-El (⟶-sub (single u) r)))))
...   | hsˡ ra =
        ⊢conv (⊢tr dcM (sr daM ra) dvM hcM (occ-red ra haM) dt du dp
                   (⊢conv de (credᵀ (ξ-El (⟶-sub (single t) r)))))
              (csymᵀ (ctrnᵀ cC (credᵀ (ξ-El (⟶-sub (single u) r)))))
...   | hsʳ ()
sr d (ξ-trᵖ r) with gen-tr d
... | mkTrInv cM aM refl A t u dcM daM dvM hcM haM dt du dp de cC =
      ⊢conv (⊢tr dcM daM dvM hcM haM dt du (sr dp r) de) (csymᵀ cC)
sr d (ξ-trᵉ r) with gen-tr d
... | mkTrInv cM aM refl A t u dcM daM dvM hcM haM dt du dp de cC =
      ⊢conv (⊢tr dcM daM dvM hcM haM dt du dp (sr de r)) (csymᵀ cC)

------------------------------------------------------------------------
-- Type preservation for MULTI-step reduction — the immediate corollary.
------------------------------------------------------------------------

sr* : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ A → t ⟶* u → Γ ⊢ u ∷ A
sr* d done       = d
sr* d (step r p) = sr* (sr d r) p
