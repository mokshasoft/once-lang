-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.DeclType — a declaration's type, read as the
-- compiler's (`declTy`) and back (`declS`): the identity (plan 0.121 §3.5).
------------------------------------------------------------------------

module Once.Adequacy.SpecCore.DeclType where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

import Once.Spec.Grade as SG
import Once.Spec.Signature as S
open S using (constant; value; operation)
open import Once.Core.Decl using (declS; toB)
open import Once.Adequacy.SpecInterp using (declTy; ⌞_⌟)

-- Reading a declaration's type as the compiler's, and back, is the identity.
toB-⌞⌟ : ∀ b → toB ⌞ b ⌟ ≡ b
toB-⌞⌟ S.unit    = refl
toB-⌞⌟ S.void    = refl
toB-⌞⌟ S.int     = refl
toB-⌞⌟ S.float   = refl
toB-⌞⌟ (a S.* b) = cong₂ S._*_ (toB-⌞⌟ a) (toB-⌞⌟ b)
toB-⌞⌟ (a S.+ b) = cong₂ S._+_ (toB-⌞⌟ a) (toB-⌞⌟ b)

declS-declTy : ∀ t → declS (declTy t) ≡ t
declS-declTy (constant S.unit)      = refl
declS-declTy (constant S.void)      = refl
declS-declTy (constant S.int)       = refl
declS-declTy (constant S.float)     = refl
declS-declTy (constant (a S.* b))   = cong constant (toB-⌞⌟ (a S.* b))
declS-declTy (constant (a S.+ b))   = cong constant (toB-⌞⌟ (a S.+ b))
declS-declTy (value a SG.Zero b)     = cong₂ (λ x y → value x SG.Zero y) (toB-⌞⌟ a) (toB-⌞⌟ b)
declS-declTy (value a SG.One b)      = cong₂ (λ x y → value x SG.One y) (toB-⌞⌟ a) (toB-⌞⌟ b)
declS-declTy (value a SG.Many b)     = cong₂ (λ x y → value x SG.Many y) (toB-⌞⌟ a) (toB-⌞⌟ b)
declS-declTy (operation a SG.Zero b) = cong₂ (λ x y → operation x SG.Zero y) (toB-⌞⌟ a) (toB-⌞⌟ b)
declS-declTy (operation a SG.One b)  = cong₂ (λ x y → operation x SG.One y) (toB-⌞⌟ a) (toB-⌞⌟ b)
declS-declTy (operation a SG.Many b) = cong₂ (λ x y → operation x SG.Many y) (toB-⌞⌟ a) (toB-⌞⌟ b)
