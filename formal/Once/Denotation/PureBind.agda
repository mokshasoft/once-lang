-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.PureBind — the identity monad's bind: application.
--
-- It is OPAQUE so that a pure meaning keeps the shape of its evaluation order
-- (`m >>=ᵖ k`, not the reduct `k m`): the meaning-preservation proofs relate
-- two meanings bind by bind, exactly as they do at `T∞`. The value is what
-- `>>=ᵖ-β` says it is.
------------------------------------------------------------------------

module Once.Denotation.PureBind where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infixl 1 _>>=ᵖ_
opaque
  _>>=ᵖ_ : ∀ {X Y : Set} → X → (X → Y) → Y
  m >>=ᵖ k = k m

opaque
  unfolding _>>=ᵖ_
  >>=ᵖ-β : ∀ {X Y : Set} (m : X) (k : X → Y) → (m >>=ᵖ k) ≡ k m
  >>=ᵖ-β m k = refl

opaque
  unfolding _>>=ᵖ_
  >>=ᵖ-assoc : ∀ {X Y Z : Set} (m : X) (f : X → Y) (g : Y → Z)
             → ((m >>=ᵖ f) >>=ᵖ g) ≡ (m >>=ᵖ λ x → f x >>=ᵖ g)
  >>=ᵖ-assoc m f g = refl

  >>=ᵖ-idʳ : ∀ {X : Set} (m : X) → (m >>=ᵖ λ x → x) ≡ m
  >>=ᵖ-idʳ m = refl
