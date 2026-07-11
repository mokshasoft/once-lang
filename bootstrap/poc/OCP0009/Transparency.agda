------------------------------------------------------------------------
-- OCP-0009 · POC-0 — The two adequacy obligations (the named holes)
--
-- `conv` (Conv.agda) is postulate-free and RUNS. What is *not* yet proven
-- is that it decides the intended DEFINITIONAL EQUALITY. That is the
-- "transparency / NbE-adequacy" obligation OCP-0009 flags (Motivation →
-- "The property, stated at the right altitude"; §6 → "The load-bearing
-- POC") and that `normalizer-vs-compiler-path.md` names as the honest next
-- step of the evaluator route. It splits into the two directions of the
-- sound+complete scorecard:
--
--   completeness — reduction-equal terms are identified by `conv`
--   soundness    — terms `conv` identifies are reduction-equal
--
-- This module STATES them as postulates so the holes are explicit and
-- name-checked; it is deliberately NOT `--safe`. Discharging them (via a
-- logical-relation / NbE-adequacy argument for `eval`) is the content of
-- POC-0's proof half — see README "Next".
--
-- `_≈_` below is the definitional equality of the IR: the reflexive-
-- symmetric-transitive closure of the one-step reduction `_⟶_` (CCC.agda).
-- Note `_⟶_` already includes congruence, so `_≈_` is a congruence too.
------------------------------------------------------------------------

module poc.OCP0009.Transparency where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Conv

------------------------------------------------------------------------
-- Definitional equality: RST-closure of ⟶.
------------------------------------------------------------------------

data _≈_ {A B : Ty} : Term A B → Term A B → Set where
  ≈-refl : ∀ {t}     → t ≈ t
  ≈-step : ∀ {t u v} → t ⟶ u → u ≈ v → t ≈ v
  ≈-back : ∀ {t u v} → u ⟶ t → u ≈ v → t ≈ v

------------------------------------------------------------------------
-- The two obligations.
--
-- Discharging BOTH is exactly "conv is a sound + complete + terminating
-- decision procedure for the chosen congruence" (OCP-0009 scorecard).
-- Termination is already free: `conv` is a total Agda function (it is
-- `--safe` in Conv.agda). Soundness + completeness are what remains.
------------------------------------------------------------------------

postulate
  -- COMPLETENESS — the evaluator does not over-distinguish: definitionally
  -- equal closed morphisms evaluate to the same canonical value. This is
  -- the more tractable half (`eval` respects each reduction rule; prove by
  -- induction on `_≈_`, one lemma per rule of `_⟶_`).
  conv-complete : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
                → t ≈ u → conv fo t u ≡ true

  -- SOUNDNESS / TRANSPARENCY — the genuine NbE-adequacy content: if the
  -- evaluator cannot tell two closed morphisms apart, they are definitionally
  -- equal. Requires a logical relation between syntax and the value domain
  -- (`eval a ≡ eval b → a ≈ b` on first-order codomains).
  conv-sound    : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
                → conv fo t u ≡ true → t ≈ u

------------------------------------------------------------------------
-- Corollary once both holes are filled: `conv` is a decision procedure for
-- `_≈_` on first-order closed morphisms — i.e. decidable conversion for the
-- fragment, obtained WITHOUT confluence. (Stated here as the target shape;
-- provable the moment the two postulates become lemmas.)
------------------------------------------------------------------------
