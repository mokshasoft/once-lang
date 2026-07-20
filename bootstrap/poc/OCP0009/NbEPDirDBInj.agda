------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 26 — (B2, part 1) Π-INJECTIVITY of conversion
--                            (type-level confluence)
--
-- `NbEPDirDBSR` (dHoTT-24) scoped general subject reduction on exactly one
-- obstruction: inverting `⊢ lam t ∷ Π A B` through `⊢conv` needs Π-injectivity
-- of conversion, `Π A B ≅ᵀ Π A' B' → A ≅ᵀ A' × B ≅ᵀ B'`, which follows from
-- confluence. Confluence of terms is now proven (`NbEPDirDBConf`, dHoTT-25);
-- this module lifts it to TYPES and derives Π-injectivity — removing the
-- ceiling.
--
-- Type reduction has no top-level redex (β lives only at terms, reached via
-- `El`), so type confluence is the structural companion of term confluence:
-- parallel type reduction `_⟹ᵀ_` reuses the TERM triangle (`⟹-⁺`) at `El`
-- leaves. Then:
--   * `confluentᵀ` / `church-rosserᵀ` — confluence and joinability for types.
--   * `Π-reduct` — a reduct of `Π A B` is `Π A'' B''` with `A ⟶ᵀ* A''`,
--     `B ⟶ᵀ* B''` (Π-shape is preserved: only `ξ-Πˡ`/`ξ-Πʳ` apply).
--   * `Π-inj` — Π-INJECTIVITY OF CONVERSION. The dHoTT-24 ceiling, discharged.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBInj where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; base; Π; Σ'; El; RTm )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶ᵀ_; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; _⟶*_; done; step
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ )
open import poc.OCP0009.NbEPDirDBConf
  using ( _⟹_; _⁺; ⟹-refl; ⟹-⁺; ⟶→⟹; ⟹→⟶*; ⟶*-trans )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Type multi-step reduction and its congruences.
------------------------------------------------------------------------

infix 3 _⟶ᵀ*_
data _⟶ᵀ*_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  doneᵀ : {A : RTy Γ} → A ⟶ᵀ* A
  stepᵀ : {A B C : RTy Γ} → A ⟶ᵀ B → B ⟶ᵀ* C → A ⟶ᵀ* C

⟶ᵀ*-trans : {A B C : RTy Γ} → A ⟶ᵀ* B → B ⟶ᵀ* C → A ⟶ᵀ* C
⟶ᵀ*-trans doneᵀ       q = q
⟶ᵀ*-trans (stepᵀ r p) q = stepᵀ r (⟶ᵀ*-trans p q)

⟶ᵀ*-El : {t t' : RTm Γ} → t ⟶* t' → El t ⟶ᵀ* El t'
⟶ᵀ*-El done       = doneᵀ
⟶ᵀ*-El (step r p) = stepᵀ (ξ-El r) (⟶ᵀ*-El p)

⟶ᵀ*-Πˡ : {A A' : RTy Γ} {B : RTy (Γ ∙)} → A ⟶ᵀ* A' → Π A B ⟶ᵀ* Π A' B
⟶ᵀ*-Πˡ doneᵀ       = doneᵀ
⟶ᵀ*-Πˡ (stepᵀ r p) = stepᵀ (ξ-Πˡ r) (⟶ᵀ*-Πˡ p)

⟶ᵀ*-Πʳ : {A : RTy Γ} {B B' : RTy (Γ ∙)} → B ⟶ᵀ* B' → Π A B ⟶ᵀ* Π A B'
⟶ᵀ*-Πʳ doneᵀ       = doneᵀ
⟶ᵀ*-Πʳ (stepᵀ r p) = stepᵀ (ξ-Πʳ r) (⟶ᵀ*-Πʳ p)

⟶ᵀ*-Σˡ : {A A' : RTy Γ} {B : RTy (Γ ∙)} → A ⟶ᵀ* A' → Σ' A B ⟶ᵀ* Σ' A' B
⟶ᵀ*-Σˡ doneᵀ       = doneᵀ
⟶ᵀ*-Σˡ (stepᵀ r p) = stepᵀ (ξ-Σˡ r) (⟶ᵀ*-Σˡ p)

⟶ᵀ*-Σʳ : {A : RTy Γ} {B B' : RTy (Γ ∙)} → B ⟶ᵀ* B' → Σ' A B ⟶ᵀ* Σ' A B'
⟶ᵀ*-Σʳ doneᵀ       = doneᵀ
⟶ᵀ*-Σʳ (stepᵀ r p) = stepᵀ (ξ-Σʳ r) (⟶ᵀ*-Σʳ p)

------------------------------------------------------------------------
-- Parallel type reduction; reuses the TERM triangle at `El` leaves.
------------------------------------------------------------------------

infix 3 _⟹ᵀ_
data _⟹ᵀ_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  pbase : base {Γ} ⟹ᵀ base
  pEl   : {t t' : RTm Γ} → t ⟹ t' → El t ⟹ᵀ El t'
  pΠ    : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → A ⟹ᵀ A' → B ⟹ᵀ B' → Π A B ⟹ᵀ Π A' B'
  pΣ    : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → A ⟹ᵀ A' → B ⟹ᵀ B' → Σ' A B ⟹ᵀ Σ' A' B'

⟹ᵀ-refl : (A : RTy Γ) → A ⟹ᵀ A
⟹ᵀ-refl base     = pbase
⟹ᵀ-refl (El t)   = pEl (⟹-refl t)
⟹ᵀ-refl (Π A B)  = pΠ (⟹ᵀ-refl A) (⟹ᵀ-refl B)
⟹ᵀ-refl (Σ' A B) = pΣ (⟹ᵀ-refl A) (⟹ᵀ-refl B)

⟶ᵀ→⟹ᵀ : {A B : RTy Γ} → A ⟶ᵀ B → A ⟹ᵀ B
⟶ᵀ→⟹ᵀ (ξ-El r) = pEl (⟶→⟹ r)
⟶ᵀ→⟹ᵀ (ξ-Πˡ r) = pΠ (⟶ᵀ→⟹ᵀ r) (⟹ᵀ-refl _)
⟶ᵀ→⟹ᵀ (ξ-Πʳ r) = pΠ (⟹ᵀ-refl _) (⟶ᵀ→⟹ᵀ r)
⟶ᵀ→⟹ᵀ (ξ-Σˡ r) = pΣ (⟶ᵀ→⟹ᵀ r) (⟹ᵀ-refl _)
⟶ᵀ→⟹ᵀ (ξ-Σʳ r) = pΣ (⟹ᵀ-refl _) (⟶ᵀ→⟹ᵀ r)

⟹ᵀ→⟶ᵀ* : {A B : RTy Γ} → A ⟹ᵀ B → A ⟶ᵀ* B
⟹ᵀ→⟶ᵀ* pbase    = doneᵀ
⟹ᵀ→⟶ᵀ* (pEl p)  = ⟶ᵀ*-El (⟹→⟶* p)
⟹ᵀ→⟶ᵀ* (pΠ p q) = ⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟹ᵀ→⟶ᵀ* p)) (⟶ᵀ*-Πʳ (⟹ᵀ→⟶ᵀ* q))
⟹ᵀ→⟶ᵀ* (pΣ p q) = ⟶ᵀ*-trans (⟶ᵀ*-Σˡ (⟹ᵀ→⟶ᵀ* p)) (⟶ᵀ*-Σʳ (⟹ᵀ→⟶ᵀ* q))

------------------------------------------------------------------------
-- Complete development + triangle for types.
------------------------------------------------------------------------

_⁺ᵀ : RTy Γ → RTy Γ
base ⁺ᵀ   = base
El t ⁺ᵀ   = El (t ⁺)
Π A B ⁺ᵀ  = Π (A ⁺ᵀ) (B ⁺ᵀ)
Σ' A B ⁺ᵀ = Σ' (A ⁺ᵀ) (B ⁺ᵀ)

⟹ᵀ-⁺ : {A B : RTy Γ} → A ⟹ᵀ B → B ⟹ᵀ A ⁺ᵀ
⟹ᵀ-⁺ pbase    = pbase
⟹ᵀ-⁺ (pEl p)  = pEl (⟹-⁺ p)
⟹ᵀ-⁺ (pΠ p q) = pΠ (⟹ᵀ-⁺ p) (⟹ᵀ-⁺ q)
⟹ᵀ-⁺ (pΣ p q) = pΣ (⟹ᵀ-⁺ p) (⟹ᵀ-⁺ q)

------------------------------------------------------------------------
-- Diamond → confluence → Church–Rosser, for types.
------------------------------------------------------------------------

diamondᵀ : {A B C : RTy Γ} → A ⟹ᵀ B → A ⟹ᵀ C →
           Σ (RTy _) (λ D → (B ⟹ᵀ D) × (C ⟹ᵀ D))
diamondᵀ {A = A} pu pv = (A ⁺ᵀ) , (⟹ᵀ-⁺ pu , ⟹ᵀ-⁺ pv)

infix 3 _⟹ᵀ*_
data _⟹ᵀ*_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  pdoneᵀ : {A : RTy Γ} → A ⟹ᵀ* A
  pstepᵀ : {A B C : RTy Γ} → A ⟹ᵀ B → B ⟹ᵀ* C → A ⟹ᵀ* C

stripᵀ : {A B C : RTy Γ} → A ⟹ᵀ B → A ⟹ᵀ* C →
         Σ (RTy _) (λ D → (B ⟹ᵀ* D) × (C ⟹ᵀ D))
stripᵀ pu pdoneᵀ = _ , (pdoneᵀ , pu)
stripᵀ pu (pstepᵀ pv pv*) with diamondᵀ pu pv
... | w₁ , (u⟹w₁ , v₁⟹w₁) with stripᵀ v₁⟹w₁ pv*
...   | w , (w₁⟹*w , v⟹w) = w , (pstepᵀ u⟹w₁ w₁⟹*w , v⟹w)

confluent⟹ᵀ : {A B C : RTy Γ} → A ⟹ᵀ* B → A ⟹ᵀ* C →
              Σ (RTy _) (λ D → (B ⟹ᵀ* D) × (C ⟹ᵀ* D))
confluent⟹ᵀ pdoneᵀ pv = _ , (pv , pdoneᵀ)
confluent⟹ᵀ (pstepᵀ pu pu*) pv with stripᵀ pu pv
... | w₁ , (u₁⟹*w₁ , v⟹w₁) with confluent⟹ᵀ pu* u₁⟹*w₁
...   | w , (u⟹*w , w₁⟹*w) = w , (u⟹*w , pstepᵀ v⟹w₁ w₁⟹*w)

⟶ᵀ*→⟹ᵀ* : {A B : RTy Γ} → A ⟶ᵀ* B → A ⟹ᵀ* B
⟶ᵀ*→⟹ᵀ* doneᵀ       = pdoneᵀ
⟶ᵀ*→⟹ᵀ* (stepᵀ r p) = pstepᵀ (⟶ᵀ→⟹ᵀ r) (⟶ᵀ*→⟹ᵀ* p)

⟹ᵀ*→⟶ᵀ* : {A B : RTy Γ} → A ⟹ᵀ* B → A ⟶ᵀ* B
⟹ᵀ*→⟶ᵀ* pdoneᵀ        = doneᵀ
⟹ᵀ*→⟶ᵀ* (pstepᵀ p ps) = ⟶ᵀ*-trans (⟹ᵀ→⟶ᵀ* p) (⟹ᵀ*→⟶ᵀ* ps)

confluentᵀ : {A B C : RTy Γ} → A ⟶ᵀ* B → A ⟶ᵀ* C →
             Σ (RTy _) (λ D → (B ⟶ᵀ* D) × (C ⟶ᵀ* D))
confluentᵀ p q with confluent⟹ᵀ (⟶ᵀ*→⟹ᵀ* p) (⟶ᵀ*→⟹ᵀ* q)
... | w , (uw , vw) = w , (⟹ᵀ*→⟶ᵀ* uw , ⟹ᵀ*→⟶ᵀ* vw)

church-rosserᵀ : {A B : RTy Γ} → A ≅ᵀ B → Σ (RTy _) (λ C → (A ⟶ᵀ* C) × (B ⟶ᵀ* C))
church-rosserᵀ (credᵀ r)   = _ , (stepᵀ r doneᵀ , doneᵀ)
church-rosserᵀ crflᵀ       = _ , (doneᵀ , doneᵀ)
church-rosserᵀ (csymᵀ c) with church-rosserᵀ c
... | w , (aw , bw) = w , (bw , aw)
church-rosserᵀ (ctrnᵀ c d) with church-rosserᵀ c | church-rosserᵀ d
... | w₁ , (aw₁ , mw₁) | w₂ , (mw₂ , bw₂) with confluentᵀ mw₁ mw₂
...   | w , (w₁w , w₂w) = w , (⟶ᵀ*-trans aw₁ w₁w , ⟶ᵀ*-trans bw₂ w₂w)

------------------------------------------------------------------------
-- Π-shape is preserved by reduction, and Π-INJECTIVITY of conversion.
------------------------------------------------------------------------

record ΠRed {Γ} (A : RTy Γ) (B : RTy (Γ ∙)) (C : RTy Γ) : Set where
  constructor mkΠRed
  field
    A'' : RTy Γ
    B'' : RTy (Γ ∙)
    eqC : C ≡ Π A'' B''
    rA  : A ⟶ᵀ* A''
    rB  : B ⟶ᵀ* B''

Π-reduct : {A : RTy Γ} {B : RTy (Γ ∙)} {C : RTy Γ} → Π A B ⟶ᵀ* C → ΠRed A B C
Π-reduct {A = A} {B} doneᵀ = mkΠRed A B refl doneᵀ doneᵀ
Π-reduct (stepᵀ (ξ-Πˡ r) rest) with Π-reduct rest
... | mkΠRed A'' B'' eqC rA rB = mkΠRed A'' B'' eqC (stepᵀ r rA) rB
Π-reduct (stepᵀ (ξ-Πʳ r) rest) with Π-reduct rest
... | mkΠRed A'' B'' eqC rA rB = mkΠRed A'' B'' eqC rA (stepᵀ r rB)

-- reductions ⊆ conversion.
red→≅ᵀ : {A B : RTy Γ} → A ⟶ᵀ* B → A ≅ᵀ B
red→≅ᵀ doneᵀ       = crflᵀ
red→≅ᵀ (stepᵀ r p) = ctrnᵀ (credᵀ r) (red→≅ᵀ p)

-- Π constructor is injective for `≡`.
Πinj≡ : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → Π A B ≡ Π A' B' → (A ≡ A') × (B ≡ B')
Πinj≡ refl = refl , refl

-- ★ Π-INJECTIVITY OF CONVERSION — dHoTT-24's scoped ceiling, discharged.
Π-inj : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} →
        Π A B ≅ᵀ Π A' B' → (A ≅ᵀ A') × (B ≅ᵀ B')
Π-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) with Π-reduct r₁ | Π-reduct r₂
...   | mkΠRed A₁ B₁ eq₁ rA₁ rB₁ | mkΠRed A₂ B₂ eq₂ rA₂ rB₂
        with Πinj≡ (trans (sym eq₁) eq₂)
...       | (eqA , eqB) =
            ctrnᵀ (red→≅ᵀ rA₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqA) rA₂)))
          , ctrnᵀ (red→≅ᵀ rB₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqB) rB₂)))
