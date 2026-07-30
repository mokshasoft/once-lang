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

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; RTm; var; lam; app
        ; Sub; subTy; subTm; extS; _∘ₛ_
        ; subTm-subTm; subTm-cong; subTm-renTm; subTm-id )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
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
⟶-sub σ (ξ-fst r)   = ξ-fst (⟶-sub σ r)
⟶-sub σ (ξ-snd r)   = ξ-snd (⟶-sub σ r)
⟶-sub σ (ξ-⌜Π⌝ˡ r) = ξ-⌜Π⌝ˡ (⟶-sub σ r)
⟶-sub σ (ξ-⌜Π⌝ʳ r) = ξ-⌜Π⌝ʳ (⟶-sub (extS σ) r)
⟶-sub σ (ξ-⌜Σ⌝ˡ r) = ξ-⌜Σ⌝ˡ (⟶-sub σ r)
⟶-sub σ (ξ-⌜Σ⌝ʳ r) = ξ-⌜Σ⌝ʳ (⟶-sub (extS σ) r)

⟶ᵀ-sub : (σ : Sub Γ Δ) {A B : RTy Γ} → A ⟶ᵀ B → subTy σ A ⟶ᵀ subTy σ B
⟶ᵀ-sub σ (El-⌜base⌝)  = El-⌜base⌝
⟶ᵀ-sub σ (El-⌜Π⌝ c d) = El-⌜Π⌝ (subTm σ c) (subTm (extS σ) d)
⟶ᵀ-sub σ (El-⌜Σ⌝ c d) = El-⌜Σ⌝ (subTm σ c) (subTm (extS σ) d)
⟶ᵀ-sub σ (ξ-El r) = ξ-El (⟶-sub σ r)
⟶ᵀ-sub σ (ξ-Πˡ r) = ξ-Πˡ (⟶ᵀ-sub σ r)
⟶ᵀ-sub σ (ξ-Πʳ r) = ξ-Πʳ (⟶ᵀ-sub (extS σ) r)
⟶ᵀ-sub σ (ξ-Σˡ r) = ξ-Σˡ (⟶ᵀ-sub σ r)
⟶ᵀ-sub σ (ξ-Σʳ r) = ξ-Σʳ (⟶ᵀ-sub (extS σ) r)

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
