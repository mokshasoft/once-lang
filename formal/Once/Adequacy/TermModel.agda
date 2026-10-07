-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TermModel — plan 0.102 phase B (D276): THE PROOF of
-- `Once.Spec.Core.TermModel`.
--
--   * `subst-⊢` is `Once.Spec.Core.Subst.subst-⊢` (composition is defined);
--   * `let-β`: `t[u/x]` means what `let x = u in t` means, for a pure `u` —
--     the semantic substitution lemma (`CoreSubstSem.sub-sem`) at the
--     substitution `single u`, whose induced environment is exactly the one
--     `let` binds (`single-env`, by environment extensionality), and the left
--     unit law of the grade's monad (a pure `u` is a value, D250).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Contract using (ISig)

module Once.Adequacy.TermModel {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (suc)
open import Data.Fin using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst; cong)
open import Once.Type using (Type; Quantity; Zero; One; Many; Purity; pure)
open import Once.Type.Sub using (pure⊑)
open import Once.Target.Arch using (TargetNum)
open import Once.Surface.Context
  using (Ctx; _,_; Usage; _∷_; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Denotation.GradedDomain using (bindM-idˡ)
open import Once.Denotation.PhaseV using (restrictᵛ; bindᵛ; bindᵛ0; lookupᵛUsed)
open import Once.Denotation.EnvAlgebraV using (Env; restrict-≡)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
open import Once.Spec.Core.Subst S using (SubTy; sub-⊢; single-ty; single-usage; subst-⊢)
import Once.Spec.Core.Meaning S as GM
open import Once.Spec.Core.TermModel S using (TermModel)
open import Once.Adequacy.CoreSubstSem S
  using (Live; l-one; l-many; l-suc; look; env-ext; look-bind; subst-restr; ⟦retype⟧; single-⊑; module Rows)

module _ (fmt : TargetNum) (δ : GM.DefSem) where
  open Rows fmt δ

  -- The environment `single u` induces is the one `let` binds.
  single-slot : ∀ {n} {Γ : Ctx n} {Ψₜ Ψᵤ : Usage n} {A u} (q : Quantity) (du : Γ ⊢[ Ψᵤ ] u ∷ A ! pure)
                  (x : Env Γ (Ψₜ +ᵘ q *ᵘ Ψᵤ)) (r : Ψᵤ ⊑ᵘ (Ψₜ +ᵘ q *ᵘ Ψᵤ)) {i} (l : Live (q ∷ Ψₜ) i)
              → look {Γ = Γ , A} l (rowsᴰ (single-ty du) (q ∷ Ψₜ) (subst (Env Γ) (sym (single-usage q Ψₜ Ψᵤ)) x))
                ≡ look {Γ = Γ , A} l (bindᵛ {Γ = Γ} {A = A} q (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψₜ (q *ᵘ Ψᵤ)) x) (GM.⟦ du ⟧ fmt δ (restrictᵛ {Γ = Γ} r x)))
  single-slot {Γ = Γ} {Ψₜ} {Ψᵤ} .One du x r l-one =
    trans (lookup-rowsᴰ (single-ty du) {Ψ = One ∷ Ψₜ} l-one _)
          (cong (GM.⟦ du ⟧ fmt δ)
                (trans (cong (restrictᵛ {Γ = Γ} _) (subst-restr {Δ = Γ} (sym (single-usage One Ψₜ Ψᵤ)) x))
                       (restrict-≡ {Γ = Γ} _ _ r x)))
  single-slot {Γ = Γ} {Ψₜ} {Ψᵤ} .Many du x r l-many =
    trans (lookup-rowsᴰ (single-ty du) {Ψ = Many ∷ Ψₜ} l-many _)
          (cong (GM.⟦ du ⟧ fmt δ)
                (trans (cong (restrictᵛ {Γ = Γ} _) (subst-restr {Δ = Γ} (sym (single-usage Many Ψₜ Ψᵤ)) x))
                       (restrict-≡ {Γ = Γ} _ _ r x)))
  single-slot {Γ = Γ} {Ψₜ} {Ψᵤ} {A} q du x r (l-suc {i = i} l) =
    trans (lookup-rowsᴰ (single-ty du) {Ψ = q ∷ Ψₜ} (l-suc l) _)
      (trans (cong (lookupᵛUsed Γ i)
                   (trans (cong (restrictᵛ {Γ = Γ} _) (subst-restr {Δ = Γ} (sym (single-usage q Ψₜ Ψᵤ)) x))
                          (trans (restrict-≡ {Γ = Γ} _ _ W x)
                                 (sym (restrict-≡ {Γ = Γ} (single-⊑ l) (⊑ᵘ-+ˡ Ψₜ (q *ᵘ Ψᵤ)) W x)))))
             (sym (look-bind {Γ = Γ} {A = A} q l (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψₜ (q *ᵘ Ψᵤ)) x) (GM.⟦ du ⟧ fmt δ (restrictᵛ {Γ = Γ} r x)))))
    where W = ⊑ᵘ-trans (single-⊑ l) (⊑ᵘ-+ˡ Ψₜ (q *ᵘ Ψᵤ))

  single-env : ∀ {n} {Γ : Ctx n} {Ψₜ Ψᵤ : Usage n} {A u} (q : Quantity) (du : Γ ⊢[ Ψᵤ ] u ∷ A ! pure)
                 (x : Env Γ (Ψₜ +ᵘ q *ᵘ Ψᵤ)) (r : Ψᵤ ⊑ᵘ (Ψₜ +ᵘ q *ᵘ Ψᵤ))
             → rowsᴰ (single-ty du) (q ∷ Ψₜ) (subst (Env Γ) (sym (single-usage q Ψₜ Ψᵤ)) x)
               ≡ bindᵛ {Γ = Γ} {A = A} q (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψₜ (q *ᵘ Ψᵤ)) x) (GM.⟦ du ⟧ fmt δ (restrictᵛ {Γ = Γ} r x))
  single-env {Γ = Γ} {Ψₜ} {Ψᵤ} {A} q du x r = env-ext {Γ = Γ , A} {Ψ = q ∷ Ψₜ} _ _ (single-slot {Γ = Γ} {Ψₜ} {Ψᵤ} {A} q du x r)

  -- …and at an erased binder, the one `let` binds without evaluating `u`.
  single-env0 : ∀ {n} {Γ : Ctx n} {Ψₜ Ψᵤ : Usage n} {A u} (du : Γ ⊢[ Ψᵤ ] u ∷ A ! pure) (x : Env Γ (Ψₜ +ᵘ Zero *ᵘ Ψᵤ))
              → rowsᴰ (single-ty du) (Zero ∷ Ψₜ) (subst (Env Γ) (sym (single-usage Zero Ψₜ Ψᵤ)) x)
                ≡ bindᵛ0 {Γ = Γ} {A = A} (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψₜ (Zero *ᵘ Ψᵤ)) x)
  single-env0 {Γ = Γ} {Ψₜ} {Ψᵤ} {A} du x =
    env-ext {Γ = Γ , A} {Ψ = Zero ∷ Ψₜ} _ _ slot
    where
      slot : ∀ {i} (l : Live (Zero ∷ Ψₜ) i) → _
      slot (l-suc {i = i} l) =
        trans (lookup-rowsᴰ (single-ty du) {Ψ = Zero ∷ Ψₜ} (l-suc l) _)
              (cong (lookupᵛUsed Γ i)
                    (trans (cong (restrictᵛ {Γ = Γ} _) (subst-restr {Δ = Γ} (sym (single-usage Zero Ψₜ Ψᵤ)) x))
                           (trans (restrict-≡ {Γ = Γ} _ _ W x)
                                  (sym (restrict-≡ {Γ = Γ} (single-⊑ l) (⊑ᵘ-+ˡ Ψₜ (Zero *ᵘ Ψᵤ)) W x)))))
        where W = ⊑ᵘ-trans (single-⊑ l) (⊑ᵘ-+ˡ Ψₜ (Zero *ᵘ Ψᵤ))

  -- THE β-LAW: substitution means `let`.
  let-β-sem : ∀ {n} {Γ : Ctx n} {Ψₜ Ψᵤ : Usage n} {q : Quantity} {π : Purity} {A B : Type}
                {t : Tm (suc n)} {u : Tm n}
                (dt : (Γ , A) ⊢[ q ∷ Ψₜ ] t ∷ B ! π) (du : Γ ⊢[ Ψᵤ ] u ∷ A ! pure)
                (x : Env Γ (Ψₜ +ᵘ q *ᵘ Ψᵤ))
            → GM.⟦ subst-⊢ dt du ⟧ fmt δ x ≡ GM.⟦ ⊢let (⊢sub-eff (pure⊑ π) du) dt ⟧ fmt δ x
  let-β-sem {Γ = Γ} {Ψₜ} {Ψᵤ} {Zero} dt du x =
    trans (⟦retype⟧ (single-usage Zero Ψₜ Ψᵤ) (sub-⊢ dt (single-ty du)) fmt δ x)
      (trans (sub-sem dt (single-ty du) _) (cong (GM.⟦ dt ⟧ fmt δ) (single-env0 du x)))
  let-β-sem {Γ = Γ} {Ψₜ} {Ψᵤ} {One} {π} dt du x =
    trans (⟦retype⟧ (single-usage One Ψₜ Ψᵤ) (sub-⊢ dt (single-ty du)) fmt δ x)
      (trans (sub-sem dt (single-ty du) _)
        (trans (cong (GM.⟦ dt ⟧ fmt δ) (single-env One du x (⊑ᵘ-trans (⊑ᵘ-*One Ψᵤ) (⊑ᵘ-+ʳ Ψₜ (One *ᵘ Ψᵤ)))))
               (sym (bindM-idˡ π _ _))))
  let-β-sem {Γ = Γ} {Ψₜ} {Ψᵤ} {Many} {π} dt du x =
    trans (⟦retype⟧ (single-usage Many Ψₜ Ψᵤ) (sub-⊢ dt (single-ty du)) fmt δ x)
      (trans (sub-sem dt (single-ty du) _)
        (trans (cong (GM.⟦ dt ⟧ fmt δ) (single-env Many du x (⊑ᵘ-trans (⊑ᵘ-*Many Ψᵤ) (⊑ᵘ-+ʳ Ψₜ (Many *ᵘ Ψᵤ)))))
               (sym (bindM-idˡ π _ _))))

termModel : TermModel
termModel = record
  { subst-⊢ = subst-⊢
  ; let-β   = λ dt du fmt δ x → let-β-sem fmt δ dt du x
  }
