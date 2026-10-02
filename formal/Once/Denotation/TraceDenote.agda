-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.TraceDenote — shared trace helpers for the SigOp-event
-- observable (Plan 0.24, Phase B).
--
-- D060/Plan 0.46 (2026-06-18): the operational `obs` trace reader is
-- RETIRED. It was an alternate, parallel-`eval`-valued observable of the
-- IR; the single denotational meaning is now `DenotTrace.evalᴰ`, and the
-- machine refines THAT (`IRObsCorrectFlat.MachineRefinesObsF.traces-agree`
-- ≡ `projTrace (evalᴰ …)`). What remains here are the small, value-model-
-- free helper the live layers share:
--   * `events-F`  — foldMap one functor layer's children into an event
--                   list (used by `evalᴰ`/`⟦_⟧ˢ`/`FaithfulLemmas`).
-- (Plan 0.105 deleted `sig1`/`emit-eff`, the budgeted emission rule: under the
-- interaction tree an event is a node, and the budget is a `take` of a run.)
------------------------------------------------------------------------

module Once.Denotation.TraceDenote where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.Semantics.Machine using (⟦_⟧F)
open import Once.Denotation.Trace using (SigOpEvent)

-- `events-F F p fc` foldMaps the children of one functor layer into a
-- single event list, left-to-right (functor order = fold order). For
-- the Writer carrier the projection `p` reads each child's accumulated
-- events. Recurses structurally on the polynomial functor code.
events-F : ∀ F {X} → (X → List SigOpEvent) → ⟦ F ⟧F X → List SigOpEvent
events-F (K _)   p x        = []
events-F Id      p x        = p x
events-F (F ⊕ G) p (inj₁ x) = events-F F p x
events-F (F ⊕ G) p (inj₂ y) = events-F G p y
events-F (F ⊗ G) p (x , y)  = events-F F p x ++ events-F G p y
