-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Freyd — effects form a Freyd category
-- (`Spec.Metatheory.Freyd`, plan 0.116 A2; over `T∞`, D312).
--
-- `T∞` is free over call and halt and has no silent node, so a computation
-- that is not a plain value is observably one: its root is a call or a halt.
-- Put before or after a computation whose root is a DIFFERENT event, it
-- changes the tree's root; dropped before `return∞ tt`, it changes it too. So
-- the central computations, and the discardable ones, are exactly the values
-- `return∞ y` — the image of J — up to bisimilarity.
------------------------------------------------------------------------

module Once.Metatheory.Freyd where

import Data.Unit
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Name using (gen)
open import Once.Lang.Type using (Unit)
open import Once.Lang.Type.WellFormed using (base-Unit)
open import Once.Spec.Metatheory using (Freyd; Central; _≈_)
open import Once.Lang.Trace using (callOp; unlinkedOp)
open import Once.Lang.Iterative
  using (T∞; T∞F; ret∞; call∞; halt∞; return∞; _>>=∞_; bind∞F; TreeEq∞; NodeEq; ret≈∞; module T∞)
open T∞ using (force)
open Once.Lang.Iterative.TreeEq∞ using (force≈)
open import Once.Denotation.TraceMonadInfLaws using (≈∞-refl; ≈∞-bind; ≈∞-rewrite; ≈∞-sym; ≈∞-idˡ; ≈∞-idʳ; ≈∞-assoc)

private
  ≈refl : ∀ {X} (m : T∞ X) → m ≈ m
  ≈refl = ≈∞-refl (λ _ → refl)

  ≈trans : ∀ {X} {a b c : T∞ X} → a ≈ b → b ≈ c → a ≈ c
  ≈trans {c = c} e₁ e₂ = ≈∞-rewrite e₁ (≈refl c) e₂

  -- Two trees whose roots differ in kind are not bisimilar.
  call≢halt : ∀ {X} {Q : T∞ X → T∞ X → Set} {l l′ : T∞F X (T∞ X)} {o a k o′ a′}
            → NodeEq _≡_ Q l l′ → l ≡ call∞ o a k → l′ ≡ halt∞ o′ a′ → ⊥
  call≢halt () refl refl
  halt≢call : ∀ {X} {Q : T∞ X → T∞ X → Set} {l l′ : T∞F X (T∞ X)} {o a o′ a′ k′}
            → NodeEq _≡_ Q l l′ → l ≡ halt∞ o a → l′ ≡ call∞ o′ a′ k′ → ⊥
  halt≢call () refl refl
  call≢ret : ∀ {X} {Q : T∞ X → T∞ X → Set} {l l′ : T∞F X (T∞ X)} {o a k x}
           → NodeEq _≡_ Q l l′ → l ≡ call∞ o a k → l′ ≡ ret∞ x → ⊥
  call≢ret () refl refl
  halt≢ret : ∀ {X} {Q : T∞ X → T∞ X → Set} {l l′ : T∞F X (T∞ X)} {o a x}
           → NodeEq _≡_ Q l l′ → l ≡ halt∞ o a → l′ ≡ ret∞ x → ⊥
  halt≢ret () refl refl

  -- A root that is a leaf makes the tree that leaf.
  ret-≈ : ∀ {Y} {m : T∞ Y} {y} → force m ≡ ret∞ y → m ≈ return∞ y
  force≈ (ret-≈ e) rewrite e = ret≈∞ refl

  -- A halt, and an answered call that then returns: events no value has.
  halt₀ : T∞ Data.Unit.⊤
  force halt₀ = halt∞ unlinkedOp tt

  probe : T∞ Data.Unit.⊤
  force probe = call∞ (callOp (gen "probe") Unit base-Unit Unit) tt (λ _ → return∞ tt)

central-pureF : ∀ {Y : Set} (m : T∞ Y) (l : T∞F Y (T∞ Y)) → force m ≡ l → Central m → Σ[ y ∈ Y ] m ≈ return∞ y
central-pureF m (ret∞ y)      e c = y , ret-≈ e
central-pureF m (call∞ o a k) e c with () ← call≢halt (force≈ (c halt₀)) (cong (λ z → bind∞F z _) e) refl
central-pureF m (halt∞ o a)   e c with () ← halt≢call (force≈ (c probe)) (cong (λ z → bind∞F z _) e) refl

central-pure : ∀ {Y : Set} (m : T∞ Y) → Central m → Σ[ y ∈ Y ] m ≈ return∞ y
central-pure m = central-pureF m (force m) refl

discard-pureF : ∀ {Y : Set} (m : T∞ Y) (l : T∞F Y (T∞ Y)) → force m ≡ l
              → (∀ {W : Set} (k : T∞ W) → (m >>=∞ λ _ → k) ≈ k) → Σ[ y ∈ Y ] m ≈ return∞ y
discard-pureF m (ret∞ y)      e h = y , ret-≈ e
discard-pureF m (call∞ o a k) e h with () ← call≢ret (force≈ (h (return∞ tt))) (cong (λ z → bind∞F z _) e) refl
discard-pureF m (halt∞ o a)   e h with () ← halt≢ret (force≈ (h (return∞ tt))) (cong (λ z → bind∞F z _) e) refl

discard-pure : ∀ {Y : Set} (m : T∞ Y) → (∀ {W : Set} (k : T∞ W) → (m >>=∞ λ _ → k) ≈ k)
             → Σ[ y ∈ Y ] m ≈ return∞ y
discard-pure m = discard-pureF m (force m) refl

pure-central : ∀ {Y : Set} (y : Y) → Central (return∞ y)
pure-central y n =
  ≈∞-rewrite (≈∞-idˡ y _) (≈∞-bind {R = _≡_} (≈refl n) (λ { {w} refl → ≈∞-idˡ y (λ y′ → return∞ (y′ , w)) }))
             (≈refl _)

-- G7: a central arm is a value, so projecting it away or pairing it twice
-- changes nothing; the rest is `T∞`'s monad laws.
β₁-at : ∀ {Y Z : Set} (m : T∞ Y) (n : T∞ Z) → Σ[ z ∈ Z ] n ≈ return∞ z
      → ((m >>=∞ λ y → n >>=∞ λ z → return∞ (y , z)) >>=∞ λ p → return∞ (proj₁ p)) ≈ m
β₁-at m n (z₀ , nz) =
  ≈trans (≈∞-assoc m _ _)
    (≈trans (≈∞-bind {R = _≡_} (≈refl m) (λ { {y} refl →
               ≈trans (≈∞-assoc n _ _)
                 (≈trans (≈∞-bind {R = _≡_} nz (λ { {z} refl → ≈∞-idˡ (y , z) _ }))
                         (≈∞-idˡ z₀ _)) }))
            (≈∞-idʳ m))

β₂-at : ∀ {Y Z : Set} (m : T∞ Y) (n : T∞ Z) → Σ[ y ∈ Y ] m ≈ return∞ y
      → ((m >>=∞ λ y → n >>=∞ λ z → return∞ (y , z)) >>=∞ λ p → return∞ (proj₂ p)) ≈ n
β₂-at m n (y₀ , my) =
  ≈trans (≈∞-assoc m _ _)
    (≈trans (≈∞-bind {R = _≡_} my (λ { refl → ≈refl _ }))
      (≈trans (≈∞-idˡ y₀ _)
        (≈trans (≈∞-assoc n _ _)
          (≈trans (≈∞-bind {R = _≡_} (≈refl n) (λ { {z} refl → ≈∞-idˡ (y₀ , z) _ }))
                  (≈∞-idʳ n)))))

η-at : ∀ {Y Z : Set} (m : T∞ (Y × Z)) → Σ[ p ∈ Y × Z ] m ≈ return∞ p
     → ((m >>=∞ λ p → return∞ (proj₁ p)) >>=∞ λ y → (m >>=∞ λ p → return∞ (proj₂ p)) >>=∞ λ z → return∞ (y , z)) ≈ m
η-at m (p₀ , mp) =
  ≈trans (≈∞-bind {R = _≡_} (proj-at proj₁) (λ { refl → ≈refl _ }))
    (≈trans (≈∞-idˡ (proj₁ p₀) _)
      (≈trans (≈∞-bind {R = _≡_} (proj-at proj₂) (λ { refl → ≈refl _ }))
        (≈trans (≈∞-idˡ (proj₂ p₀) _) (≈∞-sym mp))))
  where
    proj-at : ∀ {C : Set} (π : _ → C) → (m >>=∞ λ p → return∞ (π p)) ≈ return∞ (π p₀)
    proj-at π = ≈trans (≈∞-bind {R = _≡_} mp (λ { refl → ≈refl _ })) (≈∞-idˡ p₀ _)

freyd : Freyd
freyd = record
  { pure-central = pure-central
  ; central-pure = central-pure
  ; discard-pure = discard-pure
  ; pair-β₁ = λ f g c x → β₁-at (f x) (g x) (central-pure (g x) (c x))
  ; pair-β₂ = λ f g c x → β₂-at (f x) (g x) (central-pure (f x) (c x))
  ; pair-η  = λ h c x → η-at (h x) (central-pure (h x) (c x))
  }
