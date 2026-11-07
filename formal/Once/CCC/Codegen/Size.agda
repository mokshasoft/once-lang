-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.Size — every value's STATIC size in words (plan 0.123 B.4,
-- D381, D384).
--
-- A base value is its `Spec.ABI` words; a μ or ν node, or a closure, is one
-- pointer word to its cell-heap block (D384: nodes are flat, sized per type,
-- with each recursive position a pointer). So every type has a size fixed by
-- the type alone, and the emitter's one rule follows: size 0 is nowhere, size
-- 1 is its word in a register, size ≥ 2 is its words at an address.
--
-- `size-words`: on a base type it IS `Spec.ABI.words`, so the internal layout
-- of a base value is the boundary's (D383: `correct` observes it there).
------------------------------------------------------------------------

module Once.CCC.Codegen.Size where

open import Data.Nat using (ℕ; suc; _⊔_) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.IRTy using (IRTy; Unit; Void; _*_; _+_; _⇛_; μ-type; ν-type; Int; Float; ⌈_⌉)
open import Once.Spec.Type using (Base; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; ∅ₖ)
open import Once.Spec.Signature using (Signature)
import Once.Spec.ABI

size : IRTy → ℕ
size Unit       = 0
size Void       = 0
size (A * B)    = size A +ℕ size B
size (A + B)    = suc (size A ⊔ size B)
size (A ⇛ B)    = 1
size (μ-type F) = 1
size (ν-type F) = 1
size Int        = 1
size Float      = 1

-- On a base type, the size is the boundary layout's (`Spec.ABI.words` does not
-- read the signature it is stated at).
size-words : ∀ (Σ : Signature) (A : IRTy) (b : Base ∅ₖ ⌈ A ⌉)
           → size A ≡ Once.Spec.ABI.words Σ b
size-words Σ Unit    b-Unit    = refl
size-words Σ Void    b-Void    = refl
size-words Σ Int     b-Int     = refl
size-words Σ Float   b-Float   = refl
size-words Σ (A * B) (b-* a b) = cong₂ _+ℕ_ (size-words Σ A a) (size-words Σ B b)
size-words Σ (A + B) (b-+ a b) = cong suc (cong₂ _⊔_ (size-words Σ A a) (size-words Σ B b))
