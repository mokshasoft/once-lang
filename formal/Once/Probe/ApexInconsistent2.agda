-- PROBE (untracked). Is the ⊥ of EvalGoodInconsistent reachable from the APEX?
-- Not "does DenotPrefix derive ⊥" (it does) but: does `Once.Certified`'s own
-- import cone carry it? Import the apex and the postulate together — if this
-- module typechecks, the apex is in the same consistent-or-not fate.
module Once.Probe.ApexInconsistent2 where

open import Data.Empty using (⊥)
open import Once.Certified using (once-certified)
open import Once.Denotation.DenotPrefix using (evalᴰ-good-schemes)

apex-is-bottom : ⊥
apex-is-bottom = evalᴰ-good-schemes
