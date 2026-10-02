-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE GLOBAL SIGNATURE of closed definitions.
--                      (PLAN-BIDI §2-bis, S5 — design (ii), route B)
--
-- ★ WHAT IT IS.  Entries `0 … size-1`, each a closed annotated body of a
--   declared closed type.  An annotated term names entry `d` by `ref d`.
--   The theory this extends is the kernel's own: extension BY DEFINITIONS.
--
--     type d  — the DECLARED type; `ref d` is typed by it alone, so a
--               body is checked once, never at its use sites.
--     body d  — the body, ERASED.  Erasure unfolds `ref d` to it (δ), so
--               conversion in `⊢ᴬ`, which is on erasures, sees through
--               every definition — transparent definitions.
--
--   The annotated bodies themselves, and the proof that each is typed in
--   its PREFIX (acyclic, hence δ terminates), are well-formedness data —
--   `Metatheory/Signature`'s `WfSig` — not part of what a use site needs.
--
-- ★ `SigOK`: what the bridge to the kernel needs — every erased body has
--   its erased declared type, in the empty context.  `WfSig` proves it.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Signature where
open import normalizer.Syntax.Types using ( ¬_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing using ( ◇; _⊢_∷_ )
open import DirectedHoTT.Spec.Annotated

record Sig : Set where
  field
    size : ℕ
    type : ℕ → ATy ε
    body : ℕ → RTm ε

-- the signature's first `d` entries
prefix : Sig → ℕ → Sig
prefix S d = record S { size = d }

-- `d` names an entry of a signature with `n` entries
infix 4 _<ˢ_
data _<ˢ_ : ℕ → ℕ → Set where
  <-here  : ∀ {n} → n <ˢ suc n
  <-there : ∀ {d n} → d <ˢ n → d <ˢ suc n

<ˢ-zero : ∀ {d} → ¬ (d <ˢ zero)
<ˢ-zero ()

-- ★ the bridge's hypothesis: every entry, erased, is a closed kernel term
--   of its erased declared type
SigOK : Sig → Set
SigOK S = ∀ {d} → d <ˢ Sig.size S → ◇ ⊢ Sig.body S d ∷ Era.⌈_⌉ᵀ (Sig.body S) (Sig.type S d)
