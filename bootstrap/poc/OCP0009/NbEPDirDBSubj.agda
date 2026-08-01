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
  using ( _≡_; refl; sym; trans; subst; cong₂; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam; app
        ; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; Ren; extR; renTm; renTy; Sub; extS; subTm; subTy; idₛ
        ; _∘ᵣ_; _ₛ∘ᵣ_; _ᵣ∘ₛ_; _∘ₛ_
        ; subTy-renTy; renTy-subTy; subTy-subTy; renTy-renTy
        ; subTy-cong; renTy-cong; subTy-id; subTm-renTm; subTm-id
        ; renTm-renTm )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; _⟶*_; done; step
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd
        ; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢conv
        ; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom
        ; ⊢ctx_; c-◇; c-▹ )
open import poc.OCP0009.NbEPDirDBSR using ( ≅ᵀ-sub )
open import poc.OCP0009.NbEPDirDBConf
  using ( ⟶-ren; subTm-monoˢ; extS-mono; single-mono )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans
        ; ⟶ᵀ*-El; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ
        ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ; red→≅ᵀ; Π-inj; Σ-inj )

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

------------------------------------------------------------------------
-- Type preservation for MULTI-step reduction — the immediate corollary.
------------------------------------------------------------------------

sr* : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ A → t ⟶* u → Γ ⊢ u ∷ A
sr* d done       = d
sr* d (step r p) = sr* (sr d r) p
