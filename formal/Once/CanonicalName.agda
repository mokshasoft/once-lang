-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CanonicalName — deciding and comparing canonical names.
--
-- The names are the Spec's (`Once.Spec.Name`). This module holds what the
-- implementation needs beyond them: decidable equality. (A generator is not a
-- name: `Once.Generators` decides the table.)
------------------------------------------------------------------------

module Once.CanonicalName where

open import Once.Spec.Name using (CanonicalName; canonical)

open import Data.List.Properties using (≡-dec)
import Data.String as Str
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl; cong)
open import Relation.Nullary using (yes; no)

-- Decidable equality — the trace's `ev-name` comparison needs it.
_≟ᶜ_ : DecidableEquality CanonicalName
canonical ps ≟ᶜ canonical qs with ≡-dec Str._≟_ ps qs
... | yes p = yes (cong canonical p)
... | no ¬p = no λ where refl → ¬p refl
