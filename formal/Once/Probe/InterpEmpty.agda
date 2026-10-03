-- PROBE (plan 0.105): is `Interp` inhabited? `answer` must answer every
-- `CallOp`, including one whose codomain is `Void`.
module Once.Probe.InterpEmpty where

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Unit using (tt)
open import Once.Type using (Unit; Void)
open import Once.Functor.Translate using (base-Unit)
open import Once.CanonicalName using (bare)
open import Once.Denotation.TraceMonad using (Interp; callOp; answer)

interp-empty : Interp → ⊥
interp-empty ι = answer ι [] (callOp (bare "x") Unit base-Unit Void) tt
