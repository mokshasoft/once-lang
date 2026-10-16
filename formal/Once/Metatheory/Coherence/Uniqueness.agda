{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Uniqueness — a core term in its context has one
-- type (Church style, `Spec.Core.Syntax`): two derivations of one term
-- conclude at one type, whatever usages and grades they carry.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Coherence.Uniqueness (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.Spec.Grade using (mk-kind)
open import Once.Spec.Type using (Ty; Fun; KCtx; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F)
open import Once.Spec.Context using (Ctx; _▸_; _∷_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S

private
  *-inj : ∀ {m} {A A′ B B′ : Ty m} → (A * B) ≡ (A′ * B′) → (A ≡ A′) × (B ≡ B′)
  *-inj refl = refl , refl
  +-inj : ∀ {m} {A A′ B B′ : Ty m} → (A + B) ≡ (A′ + B′) → (A ≡ A′) × (B ≡ B′)
  +-inj refl = refl , refl
  ν-inj : ∀ {m} {F F′ : Fun m} {π π′} → ν F π ≡ ν F′ π′ → (F ≡ F′) × (π ≡ π′)
  ν-inj refl = refl , refl

⇒-inj : ∀ {m} {A A′ B B′ : Ty m} {k k′} → (A ⇒[ k ] B) ≡ (A′ ⇒[ k′ ] B′) → (A ≡ A′) × (k ≡ k′) × (B ≡ B′)
⇒-inj refl = refl , refl , refl

kind-inj : ∀ {q q′ π π′} → mk-kind q π ≡ mk-kind q′ π′ → (q ≡ q′) × (π ≡ π′)
kind-inj refl = refl , refl

ty-unique : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ Ψ′ t A A′ π π′}
          → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ′ ] t ∷ A′ ! π′ → A ≡ A′

private
  under : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {A A′ Ψ Ψ′ t B B′ π π′ q q′} → A ≡ A′
        → Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ ] t ∷ B ! π → Δ ⊩ (Γ ▸ A′) ⊢[ q′ ∷ Ψ′ ] t ∷ B′ ! π′ → B ≡ B′
  under refl d d′ = ty-unique d d′

ty-unique (⊢sub-use _ d) d′ = ty-unique d d′
ty-unique (⊢sub-eff _ d) d′ = ty-unique d d′
{-# CATCHALL #-}
ty-unique d (⊢sub-use _ d′) = ty-unique d d′
{-# CATCHALL #-}
ty-unique d (⊢sub-eff _ d′) = ty-unique d d′
ty-unique (⊢var i)       (⊢var .i)        = refl
ty-unique (⊢lam _ d)     (⊢lam _ d′)      = cong (λ B → _ ⇒[ _ ] B) (ty-unique d d′)
ty-unique (⊢app df _)    (⊢app df′ _)     = proj₂ (proj₂ (⇒-inj (ty-unique df df′)))
ty-unique (⊢let d₁ d₂)   (⊢let d₁′ d₂′)   = under (ty-unique d₁ d₁′) d₂ d₂′
ty-unique ⊢unit          ⊢unit            = refl
ty-unique (⊢pair a b)    (⊢pair a′ b′)    = cong₂ _*_ (ty-unique a a′) (ty-unique b b′)
ty-unique (⊢fst d)       (⊢fst d′)        = proj₁ (*-inj (ty-unique d d′))
ty-unique (⊢snd d)       (⊢snd d′)        = proj₂ (*-inj (ty-unique d d′))
ty-unique (⊢inl d)       (⊢inl d′)        = cong (_+ _) (ty-unique d d′)
ty-unique (⊢inr d)       (⊢inr d′)        = cong (_ +_) (ty-unique d d′)
ty-unique (⊢case ds dl _) (⊢case ds′ dl′ _) = under (proj₁ (+-inj (ty-unique ds ds′))) dl dl′
ty-unique (⊢absurd _)    (⊢absurd _)      = refl
ty-unique (⊢roll _ _)    (⊢roll _ _)      = refl
ty-unique (⊢fold _ da _) (⊢fold _ da′ _) = proj₂ (proj₂ (⇒-inj (ty-unique da da′)))
ty-unique (⊢unfold _ _ dc _) (⊢unfold _ _ dc′ _) =
  cong (ν _) (proj₂ (kind-inj (proj₁ (proj₂ (⇒-inj (ty-unique dc dc′))))))
ty-unique (⊢out {F = F} _ d) (⊢out _ d′) =
  let e = ν-inj (ty-unique d d′) in cong₂ (λ F π → ⟦ F ⟧F (ν F π)) (proj₁ e) (proj₂ e)
ty-unique (⊢iter df _)   (⊢iter df′ _)    = proj₁ (+-inj (proj₂ (proj₂ (⇒-inj (ty-unique df df′)))))
ty-unique (⊢coerce _ _)  (⊢coerce _ _)    = refl
ty-unique ⊢lit-int       ⊢lit-int         = refl
ty-unique ⊢lit-float     ⊢lit-float       = refl
ty-unique (⊢prim p _)    (⊢prim .p _)     = refl
ty-unique (⊢sigop _)     (⊢sigop _)       = refl
ty-unique (⊢ref d τ _)   (⊢ref .d .τ _)   = refl
