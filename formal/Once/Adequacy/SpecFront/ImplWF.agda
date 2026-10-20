-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.ImplWF — the compiler's reading of a Spec
-- Interpretation does not depend on the well-formedness proof (plan 0.121
-- §3.6, F7).
--
-- `SpecInterp.toImpl` takes a proof that Σ is well-formed only to rule out
-- the branch where an answering operation's answer type is empty; the answer
-- itself is read at the inhabitant the DECISION gives (`answerAt-dec`). So
-- two proofs give the same implementation (`toImpl-wf`, by P1).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.ImplWF where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Postulates using (extensionality)
open import Once.Spec.Word using (Carrier)
import Once.Lang.Value Carrier Carrier as M
open import Once.Lang.Name using (showCanonical)
open import Once.Lang.Contract using (Impl; Key; kdom; kcod; answerKeys; answer-step)
open import Once.Lang.Event using (SigOpEvent; toEvent)
import Once.Spec.Signature as S
open S using (Signature; WellFormed; _∶_; operation; NotEmpty)
import Once.Spec.Observation as Obs
open import Once.Adequacy.SpecInterp
  using (toISig; toImpl; answerAt; answerStep; answerAt-dec; declContract; DeclContract; dc-const; dc-value; dc-op-answer; dc-op-effect; fromB; toB)

module _ (Σ : Signature) (J : Obs.Interp Σ) where

  private
    dec-eq : ∀ (o : S.Op Σ) h x (d : Dec (NotEmpty (S.Op.ans o))) ne₁ ne₂ → answerAt-dec Σ J o h x d ne₁ ≡ answerAt-dec Σ J o h x d ne₂
    dec-eq o h x (yes _) _ _ = refl
    dec-eq o h x (no ¬p) ne₁ _ = ⊥-elim (¬p ne₁)

  answer-eq : ∀ (Σ′ : Signature) (inj : ∀ {d} → d ∈ Σ′ → d ∈ Σ) (wf₁ wf₂ : WellFormed Σ′) h k p x
            → answerAt Σ J Σ′ inj wf₁ h k p x ≡ answerAt Σ J Σ′ inj wf₂ h k p x
  step-eq : ∀ {c t ct} (Σ′ : Signature) (inj : ∀ {d} → d ∈ ((c ∶ t) ∷ Σ′) → d ∈ Σ) w₁ w₂ (wf₁ wf₂ : WellFormed Σ′)
            (dc : DeclContract (showCanonical c) t ct) h k p x
          → answerStep Σ J Σ′ inj w₁ wf₁ dc h k p x ≡ answerStep Σ J Σ′ inj w₂ wf₂ dc h k p x

  answer-eq [] inj wf₁ wf₂ h k () x
  answer-eq ((c ∶ t) ∷ Σ′) inj (w₁ S.∷ wf₁) (w₂ S.∷ wf₂) h k p x = step-eq Σ′ inj w₁ w₂ wf₁ wf₂ (declContract (showCanonical c) t) h k p x

  step-eq {t = operation a q b} Σ′ inj w₁ w₂ wf₁ wf₂ (dc-op-answer ¬v ¬u) h k (here refl) x =
    cong (fromB b) (dec-eq (S.op (inj (here refl))) (map toEvent h) (toB (S.argAt q a) x) (S.notEmpty? b) _ _)
  step-eq Σ′ inj w₁ w₂ wf₁ wf₂ (dc-op-answer _ _) h k (there p) x = answer-eq Σ′ (λ m → inj (there m)) wf₁ wf₂ h k p x
  step-eq Σ′ inj w₁ w₂ wf₁ wf₂ dc-const h k p x = answer-eq Σ′ (λ m → inj (there m)) wf₁ wf₂ h k p x
  step-eq Σ′ inj w₁ w₂ wf₁ wf₂ dc-value h k p x = answer-eq Σ′ (λ m → inj (there m)) wf₁ wf₂ h k p x
  step-eq Σ′ inj w₁ w₂ wf₁ wf₂ dc-op-effect h k p x = answer-eq Σ′ (λ m → inj (there m)) wf₁ wf₂ h k p x

  toImpl-wf : ∀ (wf₁ wf₂ : WellFormed Σ) → toImpl Σ J wf₁ ≡ toImpl Σ J wf₂
  toImpl-wf wf₁ wf₂ =
    cong (λ f → record { answerI = f ; pureI = Impl.pureI (toImpl Σ J wf₁) })
         (extensionality λ h → extensionality λ k → extensionality λ p → extensionality λ x → answer-eq Σ (λ m → m) wf₁ wf₂ h k p x)
