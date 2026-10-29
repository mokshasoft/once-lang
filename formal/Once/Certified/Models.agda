-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Certified.Models — the apex is NOT VACUOUS: a model of every
-- assumption whose type is not obviously inhabited (D302).
--
-- A false OBLIGATION shows up as a proof that will not go through. A false
-- ASSUMPTION does not: a postulate of an empty type is a postulate of `⊥`, and
-- a quantifier or hypothesis over an empty type makes the theorem true of
-- nothing — and either makes the proofs that use it EASIER, not harder. Both
-- have happened here:
--
--   * `RuntimeContract` placed the stack and the code both at address 0 while
--     requiring them disjoint, so it was empty and each per-arch
--     `<arch>-runtime : RuntimeContract` was a postulate of `⊥` (plan 0.100 P0).
--   * `Interp` had to answer EVERY conceivable SigOp, some codomains are empty,
--     so it was empty and the apex's `∀ ι` was over nothing (plan 0.105, D257:
--     `interp-empty ι = answer ι [] (callOp (bare "x") Unit base-Unit Void) tt`).
--
-- Each was found by a probe and fixed; the probes that showed the fixed types
-- inhabited lived as islands and were nearly deleted as dead code. Here they
-- are a field of `CertifiedBuild`, so a change that empties one of these types
-- again turns `once-certified` red.
--
-- A model shows a type is INHABITED, not that the postulate at it is TRUE.
-- Not yet covered (plan 0.11) (the block-table hypotheses are gone, plan 0.125 S5):
-- the 22 resource-bound parameters of `Once.Certified`, the propositional CPU
-- postulates (`as-faithful-*`, …), and — the real
-- target — ONE concrete program for which every hypothesis holds together.
------------------------------------------------------------------------

module Once.Certified.Models where

open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl; m≤m+n)
open import Once.Internal.Trace using (Interp; interp)
open import Once.Memory.RuntimeContract using (RuntimeContract)

record NonVacuous : Set where
  field
    -- the apex's `∀ ι` is not over an empty type (plan 0.105)
    an-interp     : Interp
    -- the per-arch `<arch>-runtime : RuntimeContract` postulates are not of
    -- `⊥` (plan 0.100 P0); one type for all three arches, so one model
    runtime-model : RuntimeContract

-- The interpretation that declares nothing.
no-world : Interp
no-world = interp [] (record { answerI = λ _ _ () ; pureI = λ _ () })

-- stack [0,9], heap [10,19], code [20,29]
an-instance : RuntimeContract
an-instance = record
  { stack-upper = 9 ; heap-lower = 10 ; heap-upper = 19 ; code-lower = 20 ; code-upper = 29
  ; stack<heap = ≤-refl ; heap-valid = m≤m+n 10 9
  ; heap<code = ≤-refl ; code-valid = m≤m+n 20 9 }

models : NonVacuous
models = record { an-interp = no-world ; runtime-model = an-instance }
