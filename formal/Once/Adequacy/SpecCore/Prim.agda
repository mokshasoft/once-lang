-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Prim — the compiler's literals and primitive
-- operations as the Spec's (plan 0.121, the core bridge). Plan 0.122: they
-- ARE the Spec's; the readings are identities, kept for the front-end bridge.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Adequacy.SpecCore.Prim {s : ℕ} (S : Defs s) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Once.Spec.Core.Syntax as SC
open import Once.Adequacy.SpecCore.Schema using (ptyS)

litS : SC.Lit → SC.Lit
litS l = l

primS : SC.Prim → SC.Prim
primS p = p

module _ {m : ℕ} where

  primDom-S : ∀ p → ptyS (SC.primDom {m} p) ≡ SC.primDom (primS p)
  primDom-S p = refl

  primCod-S : ∀ p → ptyS (SC.primCod {m} p) ≡ SC.primCod (primS p)
  primCod-S p = refl
