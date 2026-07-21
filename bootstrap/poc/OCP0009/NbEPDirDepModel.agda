------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 41 (M1 raw route, milestone 3, part a) — the typed
--   RENAMING metatheory, toward the set-model interpretation → consistency.
--
-- M3 is the classical dependent-TT-soundness crux: the interpretation's `app`
-- case needs the semantic substitution lemma, which rests on the SYNTACTIC
-- substitution/renaming preservation lemmas.  This part: `renTy` fusion,
-- `ren-comm` (renaming commutes with single substitution), typed renamings, and
-- ★ RENAMING PRESERVES TYPING (`ren-⊢`).  `--safe`, zero axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDepModel where

open import Agda.Builtin.Equality using ( _≡_; refl )

open import poc.OCP0009.NbEPDirDep
  using ( Cx; ε; _∙; Var; vz; vs; Tm; var; lam; app; ⌜⊥⌝; ⌜Π⌝
        ; Ren; extR; ren; _∘ᵣ_; ren-ren
        ; Sub; sub; extS; single; sub-comm; _ᵣ∘ₛ_; _ₛ∘ᵣ_
        ; ren-sub; sub-ren; sub-cong )
open import poc.OCP0009.NbEPDirDepTy
  using ( RTy; U; El; renTy; subTy; Con; ε; _▷_; _∋_∷_; vz; vs; _⊢_∷_
        ; ⊢var; ⊢lam; ⊢app; ⊢⌜⊥⌝; ⊢⌜Π⌝ )

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl
sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q
subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

------------------------------------------------------------------------
-- `renTy` fusion, and `ren-comm` (renaming vs single substitution).
------------------------------------------------------------------------

renTy-wk : ∀ {Γ Δ} {ρ : Ren Γ Δ} (A : RTy Γ) →
           renTy (extR ρ) (renTy vs A) ≡ renTy vs (renTy ρ A)
renTy-wk U      = refl
renTy-wk (El t) = cong El (trans (ren-ren t) (sym (ren-ren t)))

ren-comm : ∀ {Γ Δ} (ρ : Ren Γ Δ) (d : Tm (Γ ∙)) (u : Tm Γ) →
           ren ρ (sub (single u) d) ≡ sub (single (ren ρ u)) (ren (extR ρ) d)
ren-comm ρ d u = trans (ren-sub d) (trans (sub-cong bridge d) (sym (sub-ren d)))
  where
  bridge : ∀ (x : Var (_ ∙)) → (ρ ᵣ∘ₛ single u) x ≡ (single (ren ρ u) ₛ∘ᵣ extR ρ) x
  bridge vz     = refl
  bridge (vs x) = refl

------------------------------------------------------------------------
-- Typed renamings, and RENAMING PRESERVES TYPING.
------------------------------------------------------------------------

_⊢ᵣ_∷_ : ∀ {Γ Δ} → Con Δ → Ren Γ Δ → Con Γ → Set
Θ ⊢ᵣ ρ ∷ Γ = ∀ {x A} → Γ ∋ x ∷ A → Θ ∋ ρ x ∷ renTy ρ A

⊢ᵣ-ext : ∀ {Γ Δ} {Θ : Con Δ} {Γc : Con Γ} {ρ : Ren Γ Δ} {A : RTy Γ} →
         Θ ⊢ᵣ ρ ∷ Γc → (Θ ▷ renTy ρ A) ⊢ᵣ extR ρ ∷ (Γc ▷ A)
⊢ᵣ-ext {Θ = Θ} {ρ = ρ} rρ (vz {A = A₀}) =
  subst (λ z → (Θ ▷ renTy ρ A₀) ∋ vz ∷ z) (sym (renTy-wk {ρ = ρ} A₀)) vz
⊢ᵣ-ext {Θ = Θ} {ρ = ρ} {A = A} rρ (vs {A = A₀} x) =
  subst (λ z → (Θ ▷ renTy ρ A) ∋ _ ∷ z) (sym (renTy-wk {ρ = ρ} A₀)) (vs (rρ x))

-- ★ RENAMING PRESERVES TYPING.
ren-⊢ : ∀ {Γ Δ} {Γc : Con Γ} {Θ : Con Δ} {t A} {ρ : Ren Γ Δ} →
        Γc ⊢ t ∷ A → Θ ⊢ᵣ ρ ∷ Γc → Θ ⊢ ren ρ t ∷ renTy ρ A
ren-⊢ (⊢var x)     rρ = ⊢var (rρ x)
ren-⊢ (⊢lam td)    rρ = ⊢lam (ren-⊢ td (⊢ᵣ-ext rρ))
ren-⊢ {ρ = ρ} (⊢app {d = d} {f = f} {u = u} tf tu) rρ =
  subst (λ z → _ ⊢ app (ren ρ f) (ren ρ u) ∷ El z) (sym (ren-comm ρ d u))
        (⊢app (ren-⊢ tf rρ) (ren-⊢ tu rρ))
ren-⊢ ⊢⌜⊥⌝         rρ = ⊢⌜⊥⌝
ren-⊢ (⊢⌜Π⌝ tc td) rρ = ⊢⌜Π⌝ (ren-⊢ tc rρ) (ren-⊢ td (⊢ᵣ-ext rρ))

------------------------------------------------------------------------
-- M3b — typed SUBSTITUTIONS, and SUBSTITUTION PRESERVES TYPING.
------------------------------------------------------------------------

-- `subTy` weakening commute (dual of `renTy-wk`).
subTy-wk : ∀ {Γ Δ} {σ : Sub Γ Δ} (A : RTy Γ) →
           subTy (extS σ) (renTy vs A) ≡ renTy vs (subTy σ A)
subTy-wk U      = refl
subTy-wk (El t) = cong El (trans (sub-ren t) (sym (ren-sub t)))

-- the weakening renaming is typed.
wk-⊢ᵣ : ∀ {Γ} {Θ : Con Γ} {B : RTy Γ} → (Θ ▷ B) ⊢ᵣ vs ∷ Θ
wk-⊢ᵣ x = vs x

-- `Θ ⊢ₛ σ ∷ Γ` — the substitution σ maps Γ's typed variables to Θ-terms.
_⊢ₛ_∷_ : ∀ {Γ Δ} → Con Δ → Sub Γ Δ → Con Γ → Set
Θ ⊢ₛ σ ∷ Γ = ∀ {x A} → Γ ∋ x ∷ A → Θ ⊢ σ x ∷ subTy σ A

⊢ₛ-ext : ∀ {Γ Δ} {Θ : Con Δ} {Γc : Con Γ} {σ : Sub Γ Δ} {A : RTy Γ} →
         Θ ⊢ₛ σ ∷ Γc → (Θ ▷ subTy σ A) ⊢ₛ extS σ ∷ (Γc ▷ A)
⊢ₛ-ext {Θ = Θ} {σ = σ} sσ (vz {A = A₀}) =
  subst (λ z → (Θ ▷ subTy σ A₀) ⊢ var vz ∷ z) (sym (subTy-wk {σ = σ} A₀)) (⊢var vz)
⊢ₛ-ext {Θ = Θ} {σ = σ} {A = A} sσ (vs {A = A₀} x) =
  subst (λ z → (Θ ▷ subTy σ A) ⊢ _ ∷ z) (sym (subTy-wk {σ = σ} A₀))
        (ren-⊢ (sσ x) wk-⊢ᵣ)

-- ★ SUBSTITUTION PRESERVES TYPING.
sub-⊢ : ∀ {Γ Δ} {Γc : Con Γ} {Θ : Con Δ} {t A} {σ : Sub Γ Δ} →
        Γc ⊢ t ∷ A → Θ ⊢ₛ σ ∷ Γc → Θ ⊢ sub σ t ∷ subTy σ A
sub-⊢ (⊢var x)     sσ = sσ x
sub-⊢ (⊢lam td)    sσ = ⊢lam (sub-⊢ td (⊢ₛ-ext sσ))
sub-⊢ {σ = σ} (⊢app {d = d} {f = f} {u = u} tf tu) sσ =
  subst (λ z → _ ⊢ app (sub σ f) (sub σ u) ∷ El z) (sym (sub-comm σ d u))
        (⊢app (sub-⊢ tf sσ) (sub-⊢ tu sσ))
sub-⊢ ⊢⌜⊥⌝         sσ = ⊢⌜⊥⌝
sub-⊢ (⊢⌜Π⌝ tc td) sσ = ⊢⌜Π⌝ (sub-⊢ tc sσ) (sub-⊢ td (⊢ₛ-ext sσ))
