-- PROBE (plan 0.105, D257 amendment). It used to prove `Interp → ⊥`:
--
--     interp-empty ι = answer ι [] (callOp (bare "x") Unit base-Unit Void) tt
--
-- — a world had to answer EVERY conceivable contract, some codomains are
-- empty, so no world existed and the apex's `∀ ι` was vacuous. A world now
-- PROVIDES contracts and answers only those (D257 (A)), so worlds exist; the
-- witness is the world that provides nothing.
module Once.Probe.InterpEmpty where

open import Once.Denotation.TraceMonad using (Interp; no-world)

interp-inhabited : Interp
interp-inhabited = no-world
