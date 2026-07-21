------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 41 (M1 raw route, milestone 2) — the TYPING RELATION
--   for the raw dependent calculus (with DEPENDENT universe codes).
--
-- Continues the raw-syntax faithful route (refinement #1, and #2 for free): the
-- IR/semantic-types trick cannot do dependent codes, but the raw route does —
-- here `⌜Π⌝ c d` is DEPENDENT (`d` a code in the context extended by `El c`), and
-- `app`'s result type uses the SYNTACTIC substitution `sub (single u) d` from
-- `NbEPDirDep`.  This module: raw types `RTy` (`U`/`El`), their renaming/
-- substitution, typed contexts, the typed-variable judgment, and the dependent
-- typing relation `Δ ⊢ t ∷ A`.  `--safe`, zero axioms.
--
-- Next (milestone 3): the set-model interpretation + the semantic substitution
-- lemma (stratified via codes-into-`Û`) → `Con(the raw dependent kernel)`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDepTy where

open import poc.OCP0009.NbEPDirDep
  using ( Cx; ε; _∙; Var; vz; vs; Tm; var; lam; app; ⌜⊥⌝; ⌜Π⌝
        ; Ren; ren; Sub; sub; single )

------------------------------------------------------------------------
-- Raw types, and their renaming / substitution.
------------------------------------------------------------------------

data RTy : Cx → Set where
  U  : ∀ {Γ} → RTy Γ
  El : ∀ {Γ} → Tm Γ → RTy Γ

renTy : ∀ {Γ Δ} → Ren Γ Δ → RTy Γ → RTy Δ
renTy ρ U      = U
renTy ρ (El t) = El (ren ρ t)

subTy : ∀ {Γ Δ} → Sub Γ Δ → RTy Γ → RTy Δ
subTy σ U      = U
subTy σ (El t) = El (sub σ t)

------------------------------------------------------------------------
-- Typed contexts (telescopes), and the typed-variable judgment.
------------------------------------------------------------------------

infixl 5 _▷_
data Con : Cx → Set where
  ε   : Con ε
  _▷_ : ∀ {Γ} → Con Γ → RTy Γ → Con (Γ ∙)

-- `Δ ∋ x ∷ A` — variable `x` has type `A` (weakened) in the typed context `Δ`.
data _∋_∷_ : ∀ {Γ} → Con Γ → Var Γ → RTy Γ → Set where
  vz : ∀ {Γ} {Δ : Con Γ} {A : RTy Γ} →
       (Δ ▷ A) ∋ vz ∷ renTy vs A
  vs : ∀ {Γ} {Δ : Con Γ} {A B : RTy Γ} {x : Var Γ} →
       Δ ∋ x ∷ A → (Δ ▷ B) ∋ vs x ∷ renTy vs A

------------------------------------------------------------------------
-- The dependent typing relation.  `⌜Π⌝` is genuinely DEPENDENT; `app` uses the
-- syntactic single substitution in its result type.
------------------------------------------------------------------------

infix 4 _⊢_∷_
data _⊢_∷_ : ∀ {Γ} → Con Γ → Tm Γ → RTy Γ → Set where
  ⊢var : ∀ {Γ} {Δ : Con Γ} {x A} →
         Δ ∋ x ∷ A → Δ ⊢ var x ∷ A
  ⊢lam : ∀ {Γ} {Δ : Con Γ} {c : Tm Γ} {d : Tm (Γ ∙)} {t : Tm (Γ ∙)} →
         (Δ ▷ El c) ⊢ t ∷ El d → Δ ⊢ lam t ∷ El (⌜Π⌝ c d)
  ⊢app : ∀ {Γ} {Δ : Con Γ} {c : Tm Γ} {d : Tm (Γ ∙)} {f u : Tm Γ} →
         Δ ⊢ f ∷ El (⌜Π⌝ c d) → Δ ⊢ u ∷ El c →
         Δ ⊢ app f u ∷ El (sub (single u) d)
  ⊢⌜⊥⌝ : ∀ {Γ} {Δ : Con Γ} → Δ ⊢ ⌜⊥⌝ ∷ U
  ⊢⌜Π⌝ : ∀ {Γ} {Δ : Con Γ} {c : Tm Γ} {d : Tm (Γ ∙)} →
         Δ ⊢ c ∷ U → (Δ ▷ El c) ⊢ d ∷ U → Δ ⊢ ⌜Π⌝ c d ∷ U
