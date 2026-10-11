-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.TermModel — plan 0.102 phase B (§4 B, §7; D276): THE TERM
-- MODEL IS A GRADED CATEGORY AND ⟦_⟧ IS A FUNCTOR OUT OF IT.
--
-- SPEC (a statement; the proof is `Once.Metatheory.TermModel`). Objects are
-- contexts, a morphism is a typed term, the identity is a variable and
-- COMPOSITION IS SUBSTITUTION. Three fields:
--
--   * `subst-⊢` — composition is DEFINED: substituting a pure term `u`
--     (a value, D250) for a variable used `q` times types at the grade the
--     model gives the composite, `Ψₜ +ᵘ q *ᵘ Ψᵤ`. This is the exact QTT
--     substitution lemma; it holds because grades are affine (D276).
--   * `let-β` — ⟦_⟧ PRESERVES composition: `t[u/x]` means what
--     `let x = u in t` means — the composite inside the language. For a pure
--     `u` this is REFERENTIAL TRANSPARENCY: a pure term may be replaced by
--     its definition and back, with no observable difference.
--
--   * `ty-subst-⊢` — the same for TYPE variables (D303): a typing over open
--     types survives every kind-respecting type substitution. It is what
--     makes "a polymorphic definition is typed once, its instances for free"
--     (D243) a theorem rather than an argument.
--
-- Deliberately not here (plan 0.102 §4 B): the rows of the equality judgment
-- (each joins with its first consumer), syntactic uniqueness for μ/ν, and
-- initiality — none has a consumer.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Contract using (ISig)

module Once.Spec.Core.TermModel {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Type.Grade using (Quantity; Purity; pure)
open import Once.Spec.Type using (Type)
open import Once.Spec.Type.Sub using (pure⊑)
open import Once.Target.Arch using (TargetNum)
open import Once.Spec.Context using (Ctx; _,_; Usage; _∷_; _+ᵘ_; _*ᵘ_)
open import Once.Spec.Core.Syntax S using (Tm; _[_])
open import Once.Spec.Core.Typing S using (_⊢[_]_∷_!_; ⊢let; ⊢sub-eff)
open import Once.Spec.Core.Meaning S using (⟦_⟧; DefSem; Env)
import Once.Spec.Core.PolyTy as PT
import Once.Spec.Core.PolyTyping S as PP
import Once.Spec.Core.TySubst S as TS

record TermModel : Set where
  field
    subst-⊢ : ∀ {n} {Γ : Ctx n} {Ψₜ Ψᵤ : Usage n} {q : Quantity} {π : Purity} {A B : Type}
                {t : Tm (ℕ.suc n)} {u : Tm n}
            → (Γ , A) ⊢[ q ∷ Ψₜ ] t ∷ B ! π
            → Γ ⊢[ Ψᵤ ] u ∷ A ! pure
            → Γ ⊢[ Ψₜ +ᵘ q *ᵘ Ψᵤ ] t [ u ] ∷ B ! π

    let-β : ∀ {n} {Γ : Ctx n} {Ψₜ Ψᵤ : Usage n} {q : Quantity} {π : Purity} {A B : Type}
              {t : Tm (ℕ.suc n)} {u : Tm n}
              (dt : (Γ , A) ⊢[ q ∷ Ψₜ ] t ∷ B ! π) (du : Γ ⊢[ Ψᵤ ] u ∷ A ! pure)
              (fmt : TargetNum) (δ : DefSem) (x : Env Γ (Ψₜ +ᵘ q *ᵘ Ψᵤ))
          → ⟦ subst-⊢ dt du ⟧ fmt δ x ≡ ⟦ ⊢let (⊢sub-eff (pure⊑ π) du) dt ⟧ fmt δ x

    -- Typing is stable under substitution of TYPES (D303): a derivation over
    -- open types `Ty m` at kinds `Δ` gives one at every kind-respecting
    -- instance `σ`, same usage, same purity.
    ty-subst-⊢ : ∀ {m k} {Δ : PT.KCtx m} {Δ′ : PT.KCtx k} {n} {Γ : PP.PCtx m n} {Ψ : Usage n}
                   {t : PP.PTm m n} {A : PT.Ty m} {π : Purity}
                 (σ : PT.Sub m k) → TS.KSub Δ Δ′ σ
               → Δ PP.⊩ Γ ⊢[ Ψ ] t ∷ A ! π
               → Δ′ PP.⊩ Γ TS.⟨ σ ⟩ᶜ ⊢[ Ψ ] t TS.⟨ σ ⟩ₜ ∷ A PT.⟨ σ ⟩ ! π
