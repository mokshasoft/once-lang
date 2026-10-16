-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Lawful — each grade with a unit (`pure ⊑π π`) is a
-- lawful monad up to its equality `EqM π`, packaged once so that the
-- recursion laws are proved once for all of them.
--
-- Not `--safe`: at `act` the equality is `≡` on finite trees, so binding
-- equal continuations is function extensionality (`Once.Postulates`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Lawful (Σ : Signature) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Postulates using (extensionality)
open import Once.Spec.Grade using (Purity; pure; act; eff)
open import Once.Spec.Effect Σ
open import Once.Metatheory.Bisim Σ
open import Once.Metatheory.Effects Σ using (T-idʳ; T-assoc)

record Lawful (π : Purity) : Set₁ where
  field
    eq-refl   : ∀ {X} (m : M π X) → EqM π m m
    eq-sym    : ∀ {X} {m m′ : M π X} → EqM π m m′ → EqM π m′ m
    eq-trans  : ∀ {X} {m₁ m₂ m₃ : M π X} → EqM π m₁ m₂ → EqM π m₂ m₃ → EqM π m₁ m₃
    bind-cong : ∀ {X Y} {m m′ : M π X} {f g : X → M π Y} → EqM π m m′ → (∀ x → EqM π (f x) (g x))
              → EqM π (bind π m f) (bind π m′ g)
    bind-idˡ  : ∀ {X Y} (x : X) (f : X → M π Y) → EqM π (bind π (return π x) f) (f x)
    bind-idʳ  : ∀ {X} (m : M π X) → EqM π (bind π m (return π)) m
    bind-assoc : ∀ {X Y Z} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
               → EqM π (bind π (bind π m f) g) (bind π m (λ x → bind π (f x) g))
    fmap-bind : ∀ {X Y} (f : X → Y) (m : M π X) → EqM π (fmap π f m) (bind π m (λ x → return π (f x)))

private
  T-cong : ∀ {X Y} (m : T X) {f g : X → T Y} → (∀ x → f x ≡ g x) → (m >>=T f) ≡ (m >>=T g)
  T-cong m h = cong (m >>=T_) (extensionality h)

lawful : ∀ π → Lawful π
lawful pure = record
  { eq-refl = λ m → refl ; eq-sym = sym ; eq-trans = trans
  ; bind-cong = λ { refl h → h _ }
  ; bind-idˡ = λ x f → refl ; bind-idʳ = λ m → refl ; bind-assoc = λ m f g → refl
  ; fmap-bind = λ f m → refl }
lawful act = record
  { eq-refl = λ m → refl ; eq-sym = sym ; eq-trans = trans
  ; bind-cong = λ { {m = m} refl h → T-cong m h }
  ; bind-idˡ = λ x f → refl ; bind-idʳ = T-idʳ ; bind-assoc = T-assoc
  ; fmap-bind = λ f m → refl }
lawful eff = record
  { eq-refl = ≈-refl ; eq-sym = ≈-sym ; eq-trans = ≈-trans
  ; bind-cong = ≈-bind
  ; bind-idˡ = idˡ ; bind-idʳ = idʳ ; bind-assoc = assoc
  ; fmap-bind = λ f m → ≈-refl _ }
