{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Canon — derivations of the combinators
-- (`Core.Derived`), built rule by rule. The closed ones mean their closures
-- definitionally; the ones with arms fix, by uniqueness of types, the type
-- any other derivation of the same term has.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Canon (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; Purity; pure; act; eff; _·p_; _⊑π_; ⊑-pure; ⊑-act; ⊑-eff; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; KCtx; Void; Unit; _*_; _+_; _⇒[_]_)
open import Once.Spec.Context using (Ctx; _▸_; Usage; zeroUsage)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.TermModel.Subst Σ S using (wk-⊢)
open import Once.Metatheory.Laws.Strengthen Σ S using (pure⊑)

-- A sequence of one grade is at that grade.
idem⊑ : ∀ π → (π ·p π) ⊑π π
idem⊑ pure = ⊑-pure
idem⊑ act  = ⊑-act
idem⊑ eff  = ⊑-eff

module _ {m : ℕ} {Δ : KCtx m} {n} {Γ : Ctx m n} where

  idD : (B : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] idᶜ B π ∷ B ⇒[ mk-kind Many π ] B ! pure
  idD B π = ⊢lam 1≤ω (⊢sub-eff (pure⊑ π) (⊢var zero))

  terminalD : (A : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] terminalᶜ A π ∷ A ⇒[ mk-kind Many π ] Unit ! pure
  terminalD A π = ⊢lam 0≤q (⊢sub-eff (pure⊑ π) ⊢unit)

  initialD : (A : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] initialᶜ A π ∷ Void ⇒[ mk-kind Many π ] A ! pure
  initialD A π = ⊢lam 1≤ω (⊢sub-eff (pure⊑ π) (⊢absurd (⊢var zero)))

  fstD sndD : (A B : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] _ ∷ _ ! pure
  fstD A B π = ⊢lam {A = A * B} {B = A} {t = fst v0} 1≤ω (⊢sub-eff (pure⊑ π) (⊢fst (⊢var zero)))
    where v0 = var zero
  sndD A B π = ⊢lam {A = A * B} {B = B} {t = snd v0} 1≤ω (⊢sub-eff (pure⊑ π) (⊢snd (⊢var zero)))
    where v0 = var zero

  fstD′ : (A B : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] fstᶜ A B π ∷ (A * B) ⇒[ mk-kind Many π ] A ! pure
  fstD′ A B π = fstD A B π
  sndD′ : (A B : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] sndᶜ A B π ∷ (A * B) ⇒[ mk-kind Many π ] B ! pure
  sndD′ A B π = sndD A B π

  inlD : (A B : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] inlᶜ A B π ∷ A ⇒[ mk-kind Many π ] (A + B) ! pure
  inlD A B π = ⊢lam 1≤ω (⊢sub-eff (pure⊑ π) (⊢inl (⊢var zero)))

  inrD : (A B : Ty m) (π : Purity) → Δ ⊩ Γ ⊢[ zeroUsage ] inrᶜ A B π ∷ B ⇒[ mk-kind Many π ] (A + B) ! pure
  inrD A B π = ⊢lam 1≤ω (⊢sub-eff (pure⊑ π) (⊢inr (⊢var zero)))

  applyD : (A B : Ty m) → Δ ⊩ Γ ⊢[ _ ] applyᶜ A B ∷ ((A ⇒[ mk-kind Many pure ] B) * A) ⇒[ mk-kind Many pure ] B ! pure
  applyD A B = ⊢lam ω≤ω (⊢app {q = Many} (⊢fst (⊢var zero)) (⊢snd (⊢var zero)))

  composeD : ∀ {Ψf Ψg πf πg A B C π f g}
           → Δ ⊩ Γ ⊢[ Ψf ] f ∷ B ⇒[ mk-kind Many π ] C ! πf → Δ ⊩ Γ ⊢[ Ψg ] g ∷ A ⇒[ mk-kind Many π ] B ! πg
           → Δ ⊩ Γ ⊢[ _ ] composeᶜ A π f g ∷ A ⇒[ mk-kind Many π ] C ! _
  composeD {π = π} df dg =
    ⊢let {q = One} df (⊢let {q = Many} (wk-⊢ dg)
      (⊢lam ω≤ω (⊢sub-eff (idem⊑ π) (⊢app {q = Many} (⊢var (suc (suc zero))) (⊢app {q = Many} (⊢var (suc zero)) (⊢var zero))))))

  pairD : ∀ {Ψf Ψg πf πg A B C π f g}
        → Δ ⊩ Γ ⊢[ Ψf ] f ∷ C ⇒[ mk-kind Many π ] A ! πf → Δ ⊩ Γ ⊢[ Ψg ] g ∷ C ⇒[ mk-kind Many π ] B ! πg
        → Δ ⊩ Γ ⊢[ _ ] pairᶜ C π f g ∷ C ⇒[ mk-kind Many π ] (A * B) ! _
  pairD {π = π} df dg =
    ⊢let {q = One} df (⊢let {q = One} (wk-⊢ dg)
      (⊢lam ω≤ω (⊢sub-eff (idem⊑ π) (⊢pair (⊢app {q = Many} (⊢var (suc (suc zero))) (⊢var zero))
                                            (⊢app {q = Many} (⊢var (suc zero)) (⊢var zero))))))

  curryD : ∀ {Ψf πf A B C f}
         → Δ ⊩ Γ ⊢[ Ψf ] f ∷ (A * B) ⇒[ mk-kind Many pure ] C ! πf
         → Δ ⊩ Γ ⊢[ _ ] curryᶜ A B pure pure f ∷ A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C) ! _
  curryD df =
    ⊢let {q = One} df (⊢lam ω≤ω (⊢lam ω≤ω (⊢app {q = Many} (⊢var (suc (suc zero))) (⊢pair (⊢var (suc zero)) (⊢var zero)))))
