------------------------------------------------------------------------
-- OCP-0009 · POC-0 — Adequacy of `conv` (status board)
--
-- `conv` (Conv.agda) must be a SOUND + COMPLETE + TERMINATING decision
-- procedure for the definitional equality `_≈_` (OCP-0009 scorecard).
--
--   · terminating — FREE: `conv` is a total Agda function (Conv.agda is --safe).
--   · complete    — DISCHARGED: `conv-complete` (poc.OCP0009.Complete),
--                   proven from `eval-sound` (eval respects every ⟶ rule).
--                   One standard axiom (funext), used only under `curry`.
--   · sound       — REMAINING HOLE: `conv-sound`. This is the genuine
--                   NbE-adequacy / transparency content OCP-0009 flags as the
--                   open frontier of the evaluator route (Motivation; §6;
--                   normalizer-vs-compiler-path.md → `EvalFullCorrectness`).
--
-- `_≈_` and `conv-complete` are imported from `Complete`; only `conv-sound`
-- is postulated here. See `Sound.agda` for the in-progress logical-relation
-- attempt that aims to replace this postulate.
------------------------------------------------------------------------

module poc.OCP0009.Transparency where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Conv
open import poc.OCP0009.Complete public using (_≈_; ≈-refl; ≈-step; ≈-back; conv-complete)

------------------------------------------------------------------------
-- The remaining obligation: soundness / transparency.
--
-- If the evaluator cannot tell two closed first-order morphisms apart, they
-- are definitionally equal. Requires reflecting model equality back into
-- syntax — a normalization / logical-relation argument (see Sound.agda).
------------------------------------------------------------------------

postulate
  conv-sound : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
             → conv fo t u ≡ true → t ≈ u

------------------------------------------------------------------------
-- Target corollary (holds once `conv-sound` is discharged): `conv` decides
-- `_≈_` on first-order closed morphisms — decidable conversion for the
-- fragment, obtained WITHOUT confluence.
------------------------------------------------------------------------
