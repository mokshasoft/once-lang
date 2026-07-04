-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Denotation.Meaning — the reference meaning as a DIRECT denotation of
-- typing DERIVATIONS (Plan 0.58 north star, OCP-0006).
--
-- This is the IR-FREE reference semantics: recursion on the typing derivation,
-- landing in the value domain `⟦_⟧ᴰ` / trace monad `T`. It replaces the current
-- `SD.⟦ realize _ ⟧ˢ` route, whose only IR contact is `Surface.Expr`'s
-- `lift-morphism`/`morph-app` leaves (a morphism represented AS `IR`). Denoting
-- the morphism realm `⊢ᵐ` directly to a function `⟦A⟧ᴰ → T⟦B⟧ᴰ = ⟦A ⇒ B⟧ᴰ`
-- removes IR entirely — note the imports below contain NO `Once.IR`, NO `evalᴰ`.
--
-- P1 (this file): the VALUE realm `⟦_⟧ᵍ` and the MORPHISM realm `⟦_⟧ᵐ` — exactly
-- the two realms that leak IR today. Self-contained (⊢ᵐ recurses only into ⊢ᵐ/⊢ᵍ).
-- The three genuinely-hard cases (`m-cata` fold, `m-named` def-environment, `g-In`
-- initial algebra) are P1 SCAFFOLDS, discharged in P2. The `⊢ᶜ`/`⊢ᵢ` realms (the
-- mechanical mirror of `SD`) are added next.
------------------------------------------------------------------------

module Once.Denotation.Meaning where

open import Data.Integer using (ℤ) renaming (∣_∣ to absℤ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)

open import Once.Type
  using (Type; Unit; Void; Int; _*_; _+_; _⇒[_]_; μ-type; Functor; ⟦_⟧T; Purity)
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
open import Once.TypeCheck.Judgment
  using (_⊢ᵍ_∶_; _⊢ᵐ_∶_⇨[_]_;
         g-int; g-terminal; g-pair; g-inl; g-inr; g-In;
         m-id; m-fst; m-snd; m-terminal; m-initial; m-inl; m-inr;
         m-compose; m-case; m-pair; m-curry; m-cata; m-const;
         m-named; m-named-resolved)

------------------------------------------------------------------------
-- P1 scaffolds (discharged in P2). NAMED and narrow — each is exactly one
-- rule's semantics that needs machinery this file does not yet set up.
------------------------------------------------------------------------

postulate
  -- g-In: the initial-algebra constructor `⟦F⟧T (μF) → μF` at the value level.
  in-value  : ∀ {F : Functor} → ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ → ⟦ μ-type F ⟧ᴰ
  -- m-cata: the structural fold of an algebra over `μF` (P2: reuse SD's cata-ev-algᴰ).
  cata-sem  : ∀ {F : Functor} {A : Type}
            → (⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ) → ⟦ μ-type F ⟧ᴰ → T ⟦ A ⟧ᴰ
  -- m-named / m-named-resolved: the named arrow's meaning (P2: the definition env).
  named-sem : ∀ {A B : Type} → String → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ

------------------------------------------------------------------------
-- The VALUE realm `⊢ᵍ` — a closed global element denotes a value `⟦A⟧ᴰ`.
------------------------------------------------------------------------

⟦_⟧ᵍ : ∀ {ctx e A} → ctx ⊢ᵍ e ∶ A → ⟦ A ⟧ᴰ
⟦ g-int n      ⟧ᵍ = absℤ n
⟦ g-terminal _ _ ⟧ᵍ = tt
⟦ g-pair ga gb ⟧ᵍ = ⟦ ga ⟧ᵍ , ⟦ gb ⟧ᵍ
⟦ g-inl ga     ⟧ᵍ = inj₁ ⟦ ga ⟧ᵍ
⟦ g-inr gb     ⟧ᵍ = inj₂ ⟦ gb ⟧ᵍ
⟦ g-In _ garg  ⟧ᵍ = in-value ⟦ garg ⟧ᵍ

------------------------------------------------------------------------
-- The MORPHISM realm `⊢ᵐ` — a categorical arrow denotes a Kleisli function
-- `⟦A⟧ᴰ → T⟦B⟧ᴰ = ⟦A ⇒ B⟧ᴰ`. Grade-erased (`π` ignored by the value domain).
------------------------------------------------------------------------

⟦_⟧ᵐ : ∀ {ctx e A π B} → ctx ⊢ᵐ e ∶ A ⇨[ π ] B → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
⟦ m-id _ _        ⟧ᵐ = λ a  → returnT a
⟦ m-fst _ _       ⟧ᵐ = λ ab → returnT (proj₁ ab)
⟦ m-snd _ _       ⟧ᵐ = λ ab → returnT (proj₂ ab)
⟦ m-terminal _ _  ⟧ᵐ = λ _  → returnT tt
⟦ m-initial _ _   ⟧ᵐ = λ v  → ⊥-elim v
⟦ m-inl _ _       ⟧ᵐ = λ a  → returnT (inj₁ a)
⟦ m-inr _ _       ⟧ᵐ = λ b  → returnT (inj₂ b)
⟦ m-compose _ f g ⟧ᵐ = λ a  → ⟦ g ⟧ᵐ a >>=T ⟦ f ⟧ᵐ
⟦ m-case f g      ⟧ᵐ = λ ab → [ ⟦ f ⟧ᵐ , ⟦ g ⟧ᵐ ]′ ab
⟦ m-pair f g      ⟧ᵐ = λ a  → ⟦ f ⟧ᵐ a >>=T λ b → ⟦ g ⟧ᵐ a >>=T λ c → returnT (b , c)
⟦ m-curry f       ⟧ᵐ = λ a  → returnT (λ b → ⟦ f ⟧ᵐ (a , b))
⟦ m-const gv      ⟧ᵐ = λ _  → returnT ⟦ gv ⟧ᵍ
⟦ m-cata _ alg    ⟧ᵐ = cata-sem ⟦ alg ⟧ᵐ
⟦_⟧ᵐ {A = A} {B = B} (m-named {x = x} _ _ _)        = named-sem {A} {B} x
⟦_⟧ᵐ {A = A} {B = B} (m-named-resolved {cn = cn} _) = named-sem {A} {B} (showCanonical cn)
