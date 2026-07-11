------------------------------------------------------------------------
-- OCP-0009 · POC-0 — Adequacy of `conv` (status board)
--
-- `conv` (Conv.agda) must be a SOUND + COMPLETE + TERMINATING decision
-- procedure for the definitional equality `_≈_` (OCP-0009 scorecard). This
-- module re-exports the results and records exactly what is proven.
--
--   · terminating — FREE: `conv` is a total Agda function (Conv.agda, --safe).
--   · complete    — DISCHARGED: `conv-complete` (Complete.agda), from
--                   `eval-sound` (eval respects every ⟶ rule).
--   · sound       — REDUCED: `conv-sound` (Sound.agda) is DERIVED from a
--                   single canonicity lemma `reify-eval` (t ≈ ↑ (eval t tt)).
--                   Everything else around it — `eq-val-sound`, reify `↑`,
--                   its section `eval-reify`, `_≈_` as an equivalence — is
--                   proven.
--
-- Remaining postulates in the whole POC (both named, standard, minimal):
--   · funext      (Complete.agda) — congruence under `curry`.
--   · reify-eval  (Sound.agda)    — canonicity; the genuine NbE-adequacy /
--                 transparency content of the evaluator route, matching the
--                 repo's open `EvalFullCorrectness`. Proof = a Tait-style
--                 logical relation over all types (POC-0b).
------------------------------------------------------------------------

module poc.OCP0009.Transparency where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)

open import poc.OCP0009.Conv public
open import poc.OCP0009.Complete public using (_≈_; ≈-refl; ≈-step; ≈-back; conv-complete)
open import poc.OCP0009.Sound public using (≈-trans; ≈-sym; conv-sound; eval-reflect)

------------------------------------------------------------------------
-- The decision procedure for `_≈_` on first-order closed morphisms:
-- decidable conversion for the fragment, obtained WITHOUT confluence.
-- (`conv-complete` + `conv-sound` together; the latter modulo `reify-eval`.)
------------------------------------------------------------------------

decides-≈ : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
          → (t ≈ u → conv fo t u ≡ true)
          × (conv fo t u ≡ true → t ≈ u)
decides-≈ fo t u = conv-complete fo t u , conv-sound fo t u
