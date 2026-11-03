{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.ABI — THE LAYOUT OF A BASE VALUE AT THE BOUNDARY (plan 0.138 S1).
--
-- SPEC. What crosses a boundary — an Interpretation's operation called by Once
-- (FFI out), a library's export called by a client (FFI in) — is a value of a
-- BASE type, and this is the memory it occupies there: the layout of the C type
-- that represents it, under the target's standard procedure-call standard.
-- An Interpretation's author and a library's client rely on it, and it is all
-- they need to know of Once's values.
--
-- In WORDS of the target (`Spec.Numerics.int-bits`; 8 bytes on x86-64 and
-- riscv64, 4 on x86-32), in order of increasing address:
--
--   Int, Float   one word: the value (`Spec.Domain`: both denote a word, the
--                Float one its encoding in the target's format, D113);
--   Unit         no words (a C struct omits it; an argument of type Unit is
--                not passed);
--   A * B        A's words, then B's (a flat C struct);
--   A + B        a tag word (0 for `inl`, 1 for `inr`), then the payload,
--                padded to the larger alternative (a tagged union); so
--                `Bool = Unit + Unit` is one word;
--   Void         no value exists.
--
-- Every scalar is one word on every target Once has, so a layout is a sequence
-- of words with no alignment gaps. The padding of a sum's shorter alternative
-- is UNSPECIFIED: any words; a reader must not look at it.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

-- At a signature only because the value domain is stated at one; a base
-- value's words do not depend on it.
module Once.Spec.ABI (Σ : Signature) where

open import Data.Nat using (ℕ; suc; _+_; _⊔_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Type
  using (Type; Base; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; ∅ₖ)
open import Once.Spec.Word using (Carrier)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)

-- THE SIZE, in words: a base type's size is static.
words : ∀ {A : Type} → Base ∅ₖ A → ℕ
words (b-var {()} _)
words b-Unit    = 0
words b-Void    = 0
words b-Int     = 1
words b-Float   = 1
words (b-* a b) = words a + words b
words (b-+ a b) = suc (words a ⊔ words b)

-- THE LAYOUT: `Layout b v ws` — the value `v` of the base type `b` occupies the
-- words `ws`, from its address up.
data Layout : ∀ {A : Type} (b : Base ∅ₖ A) → ⟦ A ⟧ᵛ → List Carrier → Set where
  l-unit  : Layout b-Unit tt []
  l-int   : ∀ {v} → Layout b-Int v (v ∷ [])
  l-float : ∀ {v} → Layout b-Float v (v ∷ [])
  l-pair  : ∀ {A B} {a : Base ∅ₖ A} {b : Base ∅ₖ B} {x y ws vs}
          → Layout a x ws → Layout b y vs → Layout (b-* a b) (x , y) (ws ++ vs)
  -- a sum: the tag, the payload, then padding (any words) to the larger side
  l-inl   : ∀ {A B} {a : Base ∅ₖ A} {b : Base ∅ₖ B} {x ws pad}
          → Layout a x ws → length (ws ++ pad) ≡ words a ⊔ words b
          → Layout (b-+ a b) (inj₁ x) (0 ∷ ws ++ pad)
  l-inr   : ∀ {A B} {a : Base ∅ₖ A} {b : Base ∅ₖ B} {y vs pad}
          → Layout b y vs → length (vs ++ pad) ≡ words a ⊔ words b
          → Layout (b-+ a b) (inj₂ y) (1 ∷ vs ++ pad)
