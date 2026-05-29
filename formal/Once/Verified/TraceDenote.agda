-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.TraceDenote — the step/fuel-indexed trace denotation
-- of the CCC IR (Plan 0.24, Phase B).
--
-- `obs fuel ir x` runs `ir` on input `x`, returning the SigOp events it
-- emits (the observable trace prefix) and its output value (`just v`
-- when the run completes within `fuel`, `nothing` when it runs out —
-- which can only happen inside a productive coinductive unfold).
--
-- The effect structure lives in exactly four constructors:
--   SigOp     — emit an event
--   _∘_       — run f, then g on f's result (sequencing)
--   ⟨_,_⟩     — run f, then g, on the same input (pairing)
--   case      — dispatch on the sum value
-- Every other constructor is value-pure (no SigOp of its own) and is
-- delegated to the value evaluator `eval` with an empty event list.
--
-- NOTE (Plan 0.24 Phase B, remaining): the recursion-scheme
-- constructors (Cata/Para/Ana/Hylo/Fuse/In/out-μ/Out/in-ν) are
-- currently in the value-pure catch-all. That is faithful for folds
-- and unfolds whose algebra/coalgebra performs no SigOp (all current
-- programs). An *effectful* fold emits finitely many events; an
-- *effectful* `Ana` is the productive/reactive case and is where the
-- `fuel` parameter becomes load-bearing (recurse through the unfold,
-- decrementing fuel). Those event-collecting versions are the next
-- sub-step; the `fuel` index is already threaded so they slot in
-- without changing the interface.
------------------------------------------------------------------------

module Once.Verified.TraceDenote where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)

open import Once.CCC.IR
open import Once.CCC.Eval using (eval; ⟦_⟧)
open import Once.CCC.SigOp.Info using (semM)
open import Once.Semantics.Machine using (sem-pair)
open import Once.Verified.Trace using (SigOpEvent; mkEvent)

------------------------------------------------------------------------
-- The step-indexed denotation.
--
-- Result: (events emitted , output value | `nothing` if out of fuel).
-- Structural recursion on the IR (the `fuel` index is threaded
-- unchanged through the effect-structural constructors; it is consumed
-- only by the — not-yet-written — recursion-scheme cases).
------------------------------------------------------------------------

obs : ∀ {A B} → ℕ → IR A B → ⟦ A ⟧ → List SigOpEvent × Maybe ⟦ B ⟧
obs n (SigOp si) x = (mkEvent si x ∷ [] , just (semM si x))
obs n (g ∘ f) x with obs n f x
... | ev₁ , just y  with obs n g y
...   | ev₂ , r = (ev₁ ++ ev₂ , r)
obs n (g ∘ f) x | ev₁ , nothing = (ev₁ , nothing)
obs n (⟨ f , g ⟩ _) x with obs n f x
... | ev₁ , just b  with obs n g x
...   | ev₂ , just c  = (ev₁ ++ ev₂ , just (sem-pair b c))
...   | ev₂ , nothing = (ev₁ ++ ev₂ , nothing)
obs n (⟨ f , g ⟩ _) x | ev₁ , nothing = (ev₁ , nothing)
obs n (case f g) (inj₁ a) = obs n f a
obs n (case f g) (inj₂ b) = obs n g b
-- value-pure constructors (no SigOp of their own): no events.
obs n c x = ([] , just (eval c x))
