-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Uniqueness — a core term, in its context,
-- determines its type (D310).
--
--     uniq : Γ ⊢[ Ψ ] t ∷ A ! π → Γ ⊢[ Ψ′ ] t ∷ A′ ! π′ → A ≡ A′
--
-- The non-syntax-directed rules change only the usage (`⊢sub-use`) and the
-- grade (`⊢sub-eff`); every other rule is fixed by the term's former, and its
-- type by its parts and its annotations. So two derivations of one judgment
-- type every subterm alike, which is what lets coherence compare them at ONE
-- type (`Fundamental`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Contract using (ISig)

module Once.Metatheory.Coherence.Uniqueness {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Spec.Type using (Type; _*_; _+_; _⇒[_]_; ν-type; ⟦_⟧T)
open import Once.Spec.Type.Grade using (mk-kind; Many)
open import Once.Spec.Context using (Ctx; _,_^_; _,_; Usage; _∷_)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S

uniq : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {t A A′ π π′}
     → Γ ⊢[ Ψ ] t ∷ A ! π → Γ ⊢[ Ψ′ ] t ∷ A′ ! π′ → A ≡ A′

private
  -- The premises' equations, matched at top level (no `with`).
  lam-u : ∀ {A B B′ q π} → B ≡ B′
        → (A ⇒[ mk-kind q π ] B) ≡ (A ⇒[ mk-kind q π ] B′)
  lam-u refl = refl

  app-u : ∀ {A A′ B B′ k k′} → (A ⇒[ k ] B) ≡ (A′ ⇒[ k′ ] B′) → B ≡ B′
  app-u refl = refl

  fst-u : ∀ {A A′ B B′} → (A * B) ≡ (A′ * B′) → A ≡ A′
  fst-u refl = refl

  snd-u : ∀ {A A′ B B′} → (A * B) ≡ (A′ * B′) → B ≡ B′
  snd-u refl = refl

  inl-u : ∀ {A A′ B} → A ≡ A′ → (A + B) ≡ (A′ + B)
  inl-u refl = refl

  inr-u : ∀ {A B B′} → B ≡ B′ → (A + B) ≡ (A + B′)
  inr-u refl = refl

  pair-u : ∀ {A A′ B B′} → A ≡ A′ → B ≡ B′ → (A * B) ≡ (A′ * B′)
  pair-u refl refl = refl

  unfold-u : ∀ {A A′ C C′ k k′ F π π′} → (A ⇒[ k ] C) ≡ (A′ ⇒[ k′ ] C′)
           → k ≡ mk-kind Many π
           → k′ ≡ mk-kind Many π′
           → ν-type F π ≡ ν-type F π′
  unfold-u refl refl refl = refl

  out-u : ∀ {F F′ π π′} → ν-type F π ≡ ν-type F′ π′ → ⟦ F ⟧T (ν-type F π) ≡ ⟦ F′ ⟧T (ν-type F′ π′)
  out-u refl = refl

  -- `let` and `case`: the bound variable's type is the premise's, so the body
  -- is compared in one context once the premises agree.
  let-u : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A A′ B B′ π π′ q q′ b}
        → A ≡ A′ → (Γ , A) ⊢[ q ∷ Ψ ] b ∷ B ! π → (Γ , A′) ⊢[ q′ ∷ Ψ′ ] b ∷ B′ ! π′ → B ≡ B′
  let-u refl db db′ = uniq db db′

  case-u : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A A′ B B′ C C′ π π′ q q′ l}
         → (A + B) ≡ (A′ + B′) → (Γ , A) ⊢[ q ∷ Ψ ] l ∷ C ! π → (Γ , A′) ⊢[ q′ ∷ Ψ′ ] l ∷ C′ ! π′ → C ≡ C′
  case-u refl dl dl′ = uniq dl dl′

uniq (⊢sub-use _ d) d′ = uniq d d′
uniq (⊢sub-eff _ d) d′ = uniq d d′
{-# CATCHALL #-}
uniq d (⊢sub-use _ d′) = uniq d d′
{-# CATCHALL #-}
uniq d (⊢sub-eff _ d′) = uniq d d′
uniq (⊢var i) (⊢var .i) = refl
uniq (⊢lam _ d) (⊢lam _ d′) = lam-u (uniq d d′)
uniq (⊢app df _) (⊢app df′ _) = app-u (uniq df df′)
uniq (⊢let de db) (⊢let de′ db′) = let-u (uniq de de′) db db′
uniq ⊢unit ⊢unit = refl
uniq (⊢pair da db) (⊢pair da′ db′) = pair-u (uniq da da′) (uniq db db′)
uniq (⊢fst d) (⊢fst d′) = fst-u (uniq d d′)
uniq (⊢snd d) (⊢snd d′) = snd-u (uniq d d′)
uniq (⊢inl d) (⊢inl d′) = inl-u (uniq d d′)
uniq (⊢inr d) (⊢inr d′) = inr-u (uniq d d′)
uniq (⊢case ds dl _) (⊢case ds′ dl′ _) = case-u (uniq ds ds′) dl dl′
uniq (⊢absurd _) (⊢absurd _) = refl
uniq (⊢roll _ _) (⊢roll _ _) = refl
uniq (⊢fold _ da _) (⊢fold _ da′ _) = app-u (uniq da da′)
uniq (⊢unfold _ dc _) (⊢unfold _ dc′ _) = unfold-u (uniq dc dc′) refl refl
uniq (⊢out _ d) (⊢out _ d′) = out-u (uniq d d′)
uniq (⊢coerce _ _) (⊢coerce _ _) = refl
uniq ⊢lit-int ⊢lit-int = refl
uniq ⊢lit-float ⊢lit-float = refl
uniq (⊢prim p _) (⊢prim .p _) = refl
uniq (⊢sigop _ _ _ _ _) (⊢sigop _ _ _ _ _) = refl
uniq (⊢ref _ _ _) (⊢ref _ _ _) = refl
