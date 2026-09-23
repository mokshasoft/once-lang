-- PROBE (deliberately untracked — see formal/Once/Probe/, which is not in git
-- because a file deriving ⊥ must not sit in the tree as if it were a result).
--
-- Question: is `evalᴰ-good-schemes` (DenotPrefix.agda:151) an inconsistency, and
-- is it REACHABLE from the apex?
--
--     postulate
--       evalᴰ-good-schemes : ∀ {X : Set} → X
--
-- A postulate inhabiting EVERY type is not a scaffold; it is ⊥ with a different
-- name. If this typechecks, every proof under `Once.Certified` is vacuous.
module Once.Probe.EvalGoodInconsistent where

open import Data.Empty using (⊥)
open import Once.Denotation.DenotPrefix using (evalᴰ-good)

-- `evalᴰ-good` falls through to the universal postulate at DenotPrefix.agda:199
-- for every recursion scheme, so ⊥ is derivable from the postulate directly.
open import Once.Denotation.DenotPrefix

boom : ⊥
boom = evalᴰ-good-schemes
