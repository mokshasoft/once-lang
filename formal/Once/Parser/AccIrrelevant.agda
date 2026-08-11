-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.AccIrrelevant
--
-- Proof-of-concept: any two `Acc _<_ n` proofs for the same index
-- are propositionally equal. Required for the plan 0.3 task #40
-- refactor — when the parser's public signature carries `Acc _<_
-- (length toks)` and downstream rewrites reference
-- `parseType … (<-wellFounded …)`, distinct `Acc` derivations at
-- rewrite sites need to unify. This lemma handles the mismatch via
-- `rewrite Acc-irrelevant`.
--
-- Proof uses function extensionality (from `Once.Postulates`) —
-- standard since `Acc` constructors wrap a function
-- `(y : A) → y < x → Acc R y`.
------------------------------------------------------------------------

module Once.Parser.AccIrrelevant where

open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Postulates using (extensionality)

-- | Propositional irrelevance for `Acc R x` at Set-level.
-- Specialised to Set-level since `Once.Postulates.extensionality` is
-- Set-level. For the parser use case (Acc of `_<_` on ℕ), this is
-- exactly the needed instantiation.
--
-- Proof by structural induction on the first Acc argument, with
-- funext applied twice (once per argument of Acc's wrapped function).
-- The inner function of `acc` has `{y : A}` implicit. Extensionality
-- via explicit arguments requires going through an explicit-argument
-- form. We build the equation pointwise on the explicit `y<x` arg;
-- the implicit `y` follows by unification at rewrite sites.
Acc-irrelevant :
  ∀ {A : Set} {R : A → A → Set} {x : A}
  → (p q : Acc R x) → p ≡ q
Acc-irrelevant (acc rp) (acc rq) =
  cong acc (implicit-ext λ y →
    extensionality λ y<x → Acc-irrelevant (rp y<x) (rq y<x))
  where
    -- Extensionality at implicit-function level, packaged from the
    -- explicit-function form via λ {y} → _. (Postulated shape matches
    -- Once.Postulates.extensionality but for implicit domain.)
    implicit-ext :
      ∀ {A : Set} {B : A → Set} {f g : ∀ {x : A} → B x}
      → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
    implicit-ext eq = cong (λ h → λ {x} → h x)
                           (extensionality eq)
