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
-- free helpers the live meaning + machine layers share:
--   * `events-F`  — foldMap one functor layer's children into an event
--                   list (used by `evalᴰ`/`⟦_⟧ˢ`/`FaithfulLemmas`).
--   * `sig1`/`emit-eff` — the effect-aware emission rule ("only `Emits`/
--                   `Halts` SigOps are observable; one event costs one
--                   budget unit"), shared with the flat machine's
--                   `FlatEvents`.
------------------------------------------------------------------------

module Once.Denotation.TraceDenote where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.CCC.Eval using (⟦_⟧)
open import Once.SigOp.Info using (SigOpInfo; effect; Pure; Emits; Halts)
open import Once.Semantics.Machine using (⟦_⟧F)
open import Once.Denotation.Trace using (SigOpEvent; mkEvent)

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

-- EVENT-INDEXED to match the top-level observable: `Behavior n` is "the first
-- `n` SigOp events" (Once.Denotation.Behavior). A `SigOp` is the ONLY IR that
-- produces something observable; it spends one budget unit, emitted iff the
-- budget `n ≥ 1`. Kept as a helper so callers split on the IR first.
sig1 : ℕ → SigOpEvent → List SigOpEvent
sig1 zero    _ = []
sig1 (suc _) e = e ∷ []

-- ONLY effectful SigOps are observable (`main : Eff Unit Unit` produces nothing
-- but effects, and effects come only from effectful SigOps). A `Pure` SigOp
-- (arith, literals — the arith.block lowering is an optimization, not an
-- observable) emits NOTHING; `Emits`/`Halts` (e.g. the exit syscall) emit the event.
-- The machine `flat-events` is made effect-aware in lockstep with this rule.
emit-eff : ∀ {A B} → SigOpInfo A B → ℕ → ⟦ A ⟧ → List SigOpEvent
emit-eff si n x with effect si
... | Pure    = []
... | Emits _ = sig1 n (mkEvent si x)
... | Halts _ = sig1 n (mkEvent si x)
