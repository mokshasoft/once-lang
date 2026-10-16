-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Effects — each grade's monad is a monad, and the
-- morphisms along the order and into `T∞` are monad morphisms
-- (`Spec.Metatheory.Effects`).
--
-- Not `--safe`: equality at `act` is `≡` on finite trees, whose nodes hold
-- continuations, so the laws at `act` use function extensionality
-- (`Once.Postulates`), as HEAD's proof did.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Effects (Σ : Signature) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Postulates using (extensionality)
open import Once.Spec.Grade using (Purity; pure; act; eff; _·p_; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-eff)
open import Once.Spec.Effect Σ
open import Once.Spec.Metatheory using (Effects)
open import Once.Metatheory.Bisim Σ
open import Once.Metatheory.Erase Σ
open import Once.Metatheory.Observe Σ using (obs-≈; obs-return)

open T∞ using (force)
open _≈_ using (force≈)

T-idʳ : ∀ {X} (m : T X) → (m >>=T returnT) ≡ m
T-idʳ (roll (done x))            = refl
T-idʳ (roll (node (call o a k))) = cong (λ k → roll (node (call o a k))) (extensionality λ b → T-idʳ (k b))

T-assoc : ∀ {X Y Z} (m : T X) (f : X → T Y) (g : Y → T Z) → ((m >>=T f) >>=T g) ≡ (m >>=T λ x → f x >>=T g)
T-assoc (roll (done x))            f g = refl
T-assoc (roll (node (call o a k))) f g = cong (λ k → roll (node (call o a k))) (extensionality λ b → T-assoc (k b) f g)

M-identityˡ : ∀ π {X Y : Set} (x : X) (k : X → M π Y) → EqM π (bind π (return π x) k) (k x)
M-identityˡ pure x k = refl
M-identityˡ act  x k = refl
M-identityˡ eff  x k = idˡ x k

M-identityʳ : ∀ π {X : Set} (m : M π X) → EqM π (bind π m (return π)) m
M-identityʳ pure m = refl
M-identityʳ act  m = T-idʳ m
M-identityʳ eff  m = idʳ m

M-assoc : ∀ π {X Y Z : Set} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
        → EqM π (bind π (bind π m f) g) (bind π m (λ x → bind π (f x) g))
M-assoc pure m f g = refl
M-assoc act  m f g = T-assoc m f g
M-assoc eff  m f g = assoc m f g

sub-return : ∀ {π π′} (g : π ⊑π π′) {X : Set} (x : X) → EqM π′ (sub g (return π x)) (return π′ x)
sub-return ⊑-pure x = refl
sub-return ⊑-pa   x = refl
sub-return ⊑-pe   x = ≈-refl (return∞ x)
sub-return ⊑-act  x = refl
sub-return ⊑-ae   x = embed-return x
sub-return ⊑-eff  x = ≈-refl (return∞ x)

sub-bind : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (m : M π X) (k : X → M π Y)
         → EqM π′ (sub g (bind π m k)) (bind π′ (sub g m) (λ x → sub g (k x)))
sub-bind ⊑-pure m k = refl
sub-bind ⊑-pa   m k = refl
sub-bind ⊑-pe   m k = ≈-sym (idˡ m (λ x → return∞ (k x)))
sub-bind ⊑-act  m k = refl
sub-bind ⊑-ae   m k = embed-bind m k
sub-bind ⊑-eff  m k = ≈-refl (m >>=∞ k)

-- One lift from each grade to each larger one.
sub-∘ : ∀ {π₁ π₂ π₃} (g : π₁ ⊑π π₂) (h : π₂ ⊑π π₃) (k : π₁ ⊑π π₃) {X : Set} (m : M π₁ X)
      → EqM π₃ (sub h (sub g m)) (sub k m)
sub-∘ ⊑-pure ⊑-pure ⊑-pure m = refl
sub-∘ ⊑-pure ⊑-pa   ⊑-pa   m = refl
sub-∘ ⊑-pure ⊑-pe   ⊑-pe   m = ≈-refl (return∞ m)
sub-∘ ⊑-pa   ⊑-act  ⊑-pa   m = refl
sub-∘ ⊑-pa   ⊑-ae   ⊑-pe   m = embed-return m
sub-∘ ⊑-pe   ⊑-eff  ⊑-pe   m = ≈-refl (return∞ m)
sub-∘ ⊑-act  ⊑-act  ⊑-act  m = refl
sub-∘ ⊑-act  ⊑-ae   ⊑-ae   m = ≈-refl (embed m)
sub-∘ ⊑-ae   ⊑-eff  ⊑-ae   m = ≈-refl (embed m)
sub-∘ ⊑-eff  ⊑-eff  ⊑-eff  m = ≈-refl m

effects : Effects Σ
effects = record
  { M-identityˡ = M-identityˡ
  ; M-identityʳ = M-identityʳ
  ; M-assoc     = M-assoc
  ; sub-return  = sub-return
  ; sub-bind    = sub-bind
  ; sub-∘       = sub-∘
  ; toT∞-sub    = toT∞-sub
  ; toT∞-return = toT∞-return
  ; toT∞-bind   = toT∞-bind
  ; toT∞-bindᵍ  = toT∞-bindᵍ
  ; obs-≈       = obs-≈
  ; obs-return  = obs-return
  }
