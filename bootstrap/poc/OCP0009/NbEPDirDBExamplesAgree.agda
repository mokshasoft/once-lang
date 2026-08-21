-- OCP-0009 · EXAMPLES — DOES THE `-ren` FAMILY ACTUALLY APPLY TO
--                        `AmTΠ`'s OWN DEFINITIONS?
--
-- ⚠ PROMOTED FROM A SPIKE 2026-08-21.  Standing rule: finished library AND
--   finished EXAMPLES material does not live in a `Spike*` module.
--
-- ⚠⚠ AND IT WAS NOT MERELY MISNAMED — IT WAS UNGUARDED.  `sweep.sh` gathers
--   `Spike*` as PROBES and, at target `all` (kernel + libs + examples),
--   does not build them at all.  This file was green when moved, but
--   nothing had been checking that.  ⇒ a result kept in a Spike is a result
--   nobody is watching.
--
-- ★ A ONE-QUESTION CHECK, and `…LibAmrecRen`'s header DEPENDS ON ITS
--   ANSWER — it states the renaming laws on the parameterised forms and
--   asserts they agree definitionally with the module's own.  If a `refl`
--   below ever breaks, route (b) is unsound and the laws apply to a
--   parallel pair rather than to `AmTΠ`.
--
-- ⚠ THE CLAIM UNDER TEST.  `…LibAmrec` states its renaming laws on the
--   PARAMETERISED forms (`amrecTm'`, `auxIH'`, `ihS-atP'`) while `AmTΠ`
--   keeps its own bodies — because REPOINTING them made
--   `…ExamplesGcdLeMid` OOM (measured: exit 143 at 1m2s vs 8.4s).
--
--   That only works if the two agree DEFINITIONALLY.  I asserted that;
--   this module checks it.  If each `refl` below typechecks, the laws
--   apply to the module's own constructions and route (b) stands.  If not,
--   step 6 is being built on sand.
--
-- ⭐ WHY A SEPARATE MODULE.  Five attempts to add these three lines inside
--   `…LibAmrec` failed on PLACEMENT — it is ~3800 lines and every
--   programmatic insertion landed in the wrong scope.  The conceptual
--   question is three lines; isolating it removes the only thing that was
--   actually going wrong.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesAgree where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import poc.OCP0009.NbEPDirDBPi using ( Cx; _∙; RTy; RTm; U; Nat )
open import poc.OCP0009.NbEPDirDBType using ( Ctx; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_ )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( aStepT; module AmTΠ )
-- ⚠ the primed forms moved to `…LibAmrecRen` (2026-08-21) — keeping them in
--   `…LibAmrec` made the combined Gcd build OOM.
open import poc.OCP0009.NbEPDirDBLibAmrecRen
  using ( amrecTm'; auxIH'; ihS-atP' )

module Agree (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
             (dA   : Δ ⊢ty A)
             (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
             (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
             (dstp : Δ ⊢ stp ∷ aStepT A cM m)
             where

  open AmTΠ Δ A cM m stp dA dcM dm dstp using ( amrecTm; auxIH; ihS-atP )

  -- ★ the three that matter for step 6
  amrecTm-agrees : amrecTm ≡ amrecTm' stp cM m
  amrecTm-agrees = refl

  auxIH-agrees : (x k : RTm ⌊ Δ ⌋) → auxIH x k ≡ auxIH' stp cM m x k
  auxIH-agrees x k = refl

  ihS-atP-agrees : (x a k p : RTm ⌊ Δ ⌋) →
                   ihS-atP x a k p ≡ ihS-atP' stp cM m x a k p
  ihS-atP-agrees x a k p = refl
