{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Type.Grade — what the compiler computes with the Spec's grades
-- (`Once.Spec.Grade`; plan 0.121 §5, layer 1).
--
-- The Spec states the grades and their order as relations; the checker
-- decides them: the usage order as a Boolean (`_≤qᵇ_`), the join of two usages
-- (`_⊔q_`, where two arms meet) and of two grades (`_⊔p_`, on the chain the
-- product), and the two arrow kinds it names.
------------------------------------------------------------------------

module Once.Type.Grade where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; act; eff; ArrowKind; mk-kind)

-- The usage order, decided.
_≤qᵇ_ : Quantity → Quantity → Bool
Zero ≤qᵇ _    = true
One  ≤qᵇ Zero = false
One  ≤qᵇ One  = true
One  ≤qᵇ Many = true
Many ≤qᵇ Zero = false
Many ≤qᵇ One  = false
Many ≤qᵇ Many = true


-- Every usage is below `Many`.
≤q-Many : ∀ q → (q ≤qᵇ Many) ≡ true
≤q-Many Zero = refl
≤q-Many One  = refl
≤q-Many Many = refl

-- The least usage above both.
_⊔q_ : Quantity → Quantity → Quantity
Zero ⊔q q    = q
One  ⊔q Zero = One
One  ⊔q One  = One
One  ⊔q Many = Many
Many ⊔q _    = Many

infixl 55 _⊔q_

-- The least grade above both: where two arms meet, of which one runs.
_⊔p_ : Purity → Purity → Purity
pure ⊔p p    = p
act  ⊔p pure = act
act  ⊔p act  = act
act  ⊔p eff  = eff
eff  ⊔p _    = eff

infixr 5 _⊔p_

-- A pure arrow used `q` times; an effectful one.
pureK : Quantity → ArrowKind
pureK q = mk-kind q pure

effK : ArrowKind
effK = mk-kind Many eff
