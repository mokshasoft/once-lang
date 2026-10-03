-- PROBE (plan 0.105, D257 amendment). It used to prove `Interp → ⊥`:
--
--     interp-empty ι = answer ι [] (callOp (bare "x") Unit base-Unit Void) tt
--
-- — one interpretation had to answer EVERY conceivable SigOp, some codomains
-- are empty, so none existed and the apex's `∀ ι` was vacuous. An
-- interpretation is now its DECLARED signatures with an implementation of
-- them (D061's three times, D257 amendment 2); the witness is the one that
-- declares nothing.
module Once.Probe.InterpEmpty where

open import Once.Denotation.TraceMonad using (Interp; no-world)

interp-inhabited : Interp
interp-inhabited = no-world
