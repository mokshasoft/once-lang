------------------------------------------------------------------------
-- OCP-0009 · POC-0 — Adequacy of `conv` (status board, FINALIZED)
--
-- `conv` decides CONVERSION for the closed first-order fragment of the IR,
-- where conversion is observational (model) equality `_≋_` — the correct,
-- fully-extensional definitional equality (Sound.agda). This is the
-- evaluator route of OCP-0009 fully realized for the fragment: determinism
-- of `eval` replaces confluence; no rewriting/SN/confluence is used.
--
--   · terminating — `conv` is a total Agda function (Conv.agda, --safe).      ✓
--   · sound       — conv-sound : conv fo t u ≡ true → t ≋ u   (Sound.agda).   ✓
--   · complete    — conv-complete : t ≋ u → conv fo t u ≡ true (Sound.agda).  ✓
--   ⇒ conv-decides : conv is a decision procedure for `_≋_`.                  ✓
--
-- Both directions are PROVEN with ZERO postulates. The reduction theory is
-- related by `≈⊆≋` (eval-soundness): `conv` also accepts everything `_⟶_`
-- equates (≈→conv), so it respects the reduction rules too.
--
-- Whole-POC axiom inventory: exactly ONE — `funext` (Complete.agda), used
-- only for congruence under `curry` in eval-soundness (the `≈⊆≋` bridge).
-- The core decision result `conv-decides` is funext-free.
--
-- Scope: closed morphisms `Term Unit C`, first-order `C`. Lifting to open
-- terms / higher-order codomains (where `_≋_`'s `∀ x` no longer collapses to
-- a single point) is POC-0b — residualizing NbE.
------------------------------------------------------------------------

module poc.OCP0009.Transparency where

open import poc.OCP0009.Conv public
open import poc.OCP0009.Complete public
  using (_≈_; ≈-refl; ≈-step; ≈-back; eval-sound; eval-≈; ≈→conv)
open import poc.OCP0009.Sound public
  using (_≋_; ≋-refl; ≋-sym; ≋-trans; ≋-∘; ≋-⟨,⟩; ⟶⊆≋; ≈⊆≋;
         eq-val-sound; conv-sound; conv-complete; conv-decides)
-- POC-0b(i): conversion on any FINITE first-order domain (not just `Unit`),
-- by enumeration. Fully proven, zero postulates. Maps the boundary: `μ`/`⇒`
-- domains are exactly what enumeration cannot reach — the NbE frontier.
open import poc.OCP0009.Finite public
  using (FiniteFO; conv-fin; conv-fin-sound; conv-fin-complete; conv-fin-decides)
