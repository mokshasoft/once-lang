{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Observe — bisimilar computations have weakly bisimilar
-- traces (`trace-≈`), and a computation that returns at once is traced so
-- (`trace-return`).
--
-- By coinduction on the trace; within one visible step, by induction on how
-- it arrives (the silent steps at the blocks' ends).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call; Op; module Op; arg; NotEmpty; eventOf)

module Once.Metatheory.Observe (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.List using (_++_; [_])
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open Op using (ans)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ
open import Once.Spec.Delay using (Delay; module Delay; _⇓_; now⇓; later⇓; _≈⟨_⟩_)
open import Once.Metatheory.Bisim Σ using (_≈B_; return≈; next≈)
open import Once.Spec.Signature using (⟦_⟧ᵇ; Event)

open Delay using (step)
open Tr using (next)
open _≈ᵗ⟨_⟩_ using (same)
open _≈ν_ using (force≈)

module _ (w : World) {X : Set} where
  open World w using (answer)

  private
    S : Set
    S = End X ⊎ (Event × Tr X)

    clash : ∀ {A : Set} {a : A} {d : Delay A} {B : Set} → _≡_ {A = A ⊎ Delay A} (inj₁ a) (inj₂ d) → B
    clash ()

  -- Two visible steps of bisimilar blocks: equal ends, or the same call with
  -- bisimilar continuations (first-order evidence; the rests are related by
  -- corecursion below).
  data Step≈ : S → S → Set where
    end≈  : ∀ {e e′} → EndRel _≡_ e e′ → Step≈ (inj₁ e) (inj₁ e′)
    call≈ : ∀ {h o a k k′} (d : Dec (NotEmpty (ans o))) → (∀ b → k b ≈B k′ b)
          → Step≈ (inj₂ (eventOf o a , after w h o a k d)) (inj₂ (eventOf o a , after w h o a k′ d))

  -- Within one visible step: by induction on how it arrives.
  match  : ∀ (h : History) {t t′ : T (X ⊎ T∞ X)} → t ≈B t′ → ∀ o → blockD w h t ⇓ o
         → ∃[ o′ ] (blockD w h t′ ⇓ o′ × Step≈ o o′)
  match h {roll (done (inj₁ x))} {roll (done (inj₁ .x))} return≈ o (now⇓ refl) = _ , now⇓ refl , end≈ (returned≈ refl)
  match h {roll (done (inj₁ x))} {roll (done (inj₁ .x))} return≈ o (later⇓ e _) = clash e
  match h {roll (done (inj₁ x))} {roll (done (inj₂ _))} (done≈ ())
  match h {roll (done (inj₂ m))} {roll (done (inj₁ _))} (done≈ ())
  match h {roll (done (inj₂ m))} {roll (done (inj₂ m′))} (next≈ p) o (now⇓ ())
  match h {roll (done (inj₂ m))} {roll (done (inj₂ m′))} (next≈ p) o (later⇓ refl a) = more (match h (force≈ p) o a)
    where more : ∃[ o′ ] (blockD w h (force m′) ⇓ o′ × Step≈ o o′) → ∃[ o′ ] (blockD w h (roll (done (inj₂ m′))) ⇓ o′ × Step≈ o o′)
          more (o′ , a′ , r) = o′ , later⇓ refl a′ , r
  match h {roll (node (call op′ x k))} (node≈ e) o (now⇓ refl) = _ , now⇓ refl , call≈ (Once.Spec.Signature.notEmpty? (ans op′)) e
  match h {roll (node (call op′ x k))} (node≈ e) o (later⇓ () _)

  match′ : ∀ (h : History) {t t′ : T (X ⊎ T∞ X)} → t ≈B t′ → ∀ o′ → blockD w h t′ ⇓ o′
         → ∃[ o ] (blockD w h t ⇓ o × Step≈ o o′)
  match′ h {roll (done (inj₁ x))} {roll (done (inj₁ .x))} return≈ o′ (now⇓ refl) = _ , now⇓ refl , end≈ (returned≈ refl)
  match′ h {roll (done (inj₁ x))} {roll (done (inj₁ .x))} return≈ o′ (later⇓ e _) = clash e
  match′ h {roll (done (inj₁ x))} {roll (done (inj₂ _))} (done≈ ())
  match′ h {roll (done (inj₂ m))} {roll (done (inj₁ _))} (done≈ ())
  match′ h {roll (done (inj₂ m))} {roll (done (inj₂ m′))} (next≈ p) o′ (now⇓ ())
  match′ h {roll (done (inj₂ m))} {roll (done (inj₂ m′))} (next≈ p) o′ (later⇓ refl a) = more (match′ h (force≈ p) o′ a)
    where more : ∃[ o ] (blockD w h (force m) ⇓ o × Step≈ o o′) → ∃[ o ] (blockD w h (roll (done (inj₂ m))) ⇓ o × Step≈ o o′)
          more (o , a′ , r) = o , later⇓ refl a′ , r
  match′ h {roll (node (call op′ x k))} {roll (node (call .op′ .x k′))} (node≈ e) o′ (now⇓ refl) =
    _ , now⇓ refl , call≈ (Once.Spec.Signature.notEmpty? (ans op′)) e
  match′ h {roll (node (call op′ x k))} (node≈ e) o′ (later⇓ () _)

  -- Corecursively: the rests of matched steps are weakly bisimilar.
  trace-≈  : ∀ (h : History) {m m′ : T∞ X} → m ≈ m′ → trace w h m ≈ᵗ⟨ _≡_ ⟩ trace w h m′
  afterSim : ∀ (h : History) (o : Op Σ) (a : ⟦ arg o ⟧ᵇ) {k k′ : ⟦ ans o ⟧ᵇ → T (X ⊎ T∞ X)}
           → (∀ b → k b ≈B k′ b) → (d : Dec (NotEmpty (ans o))) → after w h o a k d ≈ᵗ⟨ _≡_ ⟩ after w h o a k′ d
  stepR    : ∀ {o o′} → Step≈ o o′ → StepRel _≡_ _≈ᵗ⟨ _≡_ ⟩_ o o′
  lift     : ∀ {d : Delay S} {o} → ∃[ o′ ] (d ⇓ o′ × Step≈ o o′) → ∃[ o′ ] (d ⇓ o′ × StepRel _≡_ _≈ᵗ⟨ _≡_ ⟩_ o o′)
  lift′    : ∀ {d : Delay S} {o′} → ∃[ o ] (d ⇓ o × Step≈ o o′) → ∃[ o ] (d ⇓ o × StepRel _≡_ _≈ᵗ⟨ _≡_ ⟩_ o o′)

  same (trace-≈ h p) = (λ o a → lift (match h (force≈ p) o a)) , (λ o′ a′ → lift′ (match′ h (force≈ p) o′ a′))
  same (afterSim h o a e (yes p)) =
      (λ o₁ a₁ → lift (match (h ++ [ eventOf o a ]) (e (answer o h a p)) o₁ a₁))
    , (λ o₁ a₁ → lift′ (match′ (h ++ [ eventOf o a ]) (e (answer o h a p)) o₁ a₁))
  same (afterSim h o a e (no _)) = (λ { _ (now⇓ refl) → _ , now⇓ refl , halted≈ ; _ (later⇓ () _) })
                                 , (λ { _ (now⇓ refl) → _ , now⇓ refl , halted≈ ; _ (later⇓ () _) })
  stepR (end≈ r) = r
  stepR (call≈ {h = h} {o} {a} d e) = refl , afterSim h o a e d
  lift (o′ , a′ , r) = o′ , a′ , stepR r
  lift′ (o , a , r) = o , a , stepR r

  trace-return : ∀ (h : History) (x : X) → next (trace w h (return∞ x)) ⇓ inj₁ (returned x)
  trace-return h x = now⇓ refl
