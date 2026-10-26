-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IR.Semantics.Out — what a fuelled run shows (D320, plan 0.119 §7 D4b).
--
-- The calls it made, and how it ended: `just e` when the run reached its end
-- `e` within the fuel (`returned` at the Host's `leave`; `halted` at a call
-- with no answer, a fault, or a pc off the code), `nothing` when the fuel ran
-- out first. A run that has not ended says nothing about how it will.
------------------------------------------------------------------------

module Once.IR.Semantics.Out where

open import Data.List using (List; []; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.IR.Semantics.Event using (SigOpEvent)
open import Once.Spec.Trace using (End)
import Once.Spec.Trace

Out : Set
Out = List SigOpEvent × Maybe (End ⊤)

-- The fuel ran out before anything more was seen.
cut : Out
cut = [] , nothing

-- The run ended, after no further call.
ended : End ⊤ → Out
ended e = [] , just e

-- These calls first, then what the rest of the run shows.
infixr 5 _▹_
_▹_ : List SigOpEvent → Out → Out
vs ▹ o = vs ++ proj₁ o , proj₂ o

▹-assoc : ∀ (a b : List SigOpEvent) (o : Out) → (a ++ b) ▹ o ≡ a ▹ (b ▹ o)
▹-assoc a b o = cong (_, proj₂ o) (++-assoc a b (proj₁ o))

-- The run ended with no answer to give back: halted.
stop : Out
stop = ended Once.Spec.Trace.halted

-- A halted machine's end, by whether it LEFT (D320: the Host's `leave` ended
-- the run, which is `returned`) or stopped at a call with no answer or a fault.
end-of-left : Bool → End ⊤
end-of-left true  = Once.Spec.Trace.returned tt
end-of-left false = Once.Spec.Trace.halted
