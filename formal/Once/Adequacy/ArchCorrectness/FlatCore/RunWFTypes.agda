-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWFTypes
--
-- THE THREE OBLIGATIONS `FlatCore.RunWF` CONSUMES, as named types
-- (Plan 0.65 G1d, 2026-08-12).
--
-- `RunWF` takes them as PARAMETERS rather than declaring them, so the
-- residuals keep living where the ledger already records them
-- (`ConcFlatSim`) while the 1,076 lines that USE them become arch-generic.
-- Moving the residuals themselves into the core is a separate, ledger-visible
-- step — worth doing (a residual in the core is discharged once for all three
-- arches instead of once per arch), but not worth entangling with a move.
--
-- Why a companion module: a module parameter's type cannot mention that
-- module's own body, and all three of these are stated in terms of `RunAt`,
-- the shape table and the emitter. Same reason `X86-64.ResourceBounds` exists.
--
-- None of the three mentions a machine state — the postulate block in
-- `ConcFlatSim` says so itself ("No `X.State` in the type: this is a fact
-- about the ABSTRACT machine"), which is exactly why they can cross into the
-- core unchanged.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.CanonicalName using (CanonicalName)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.FlatCore.RunWFTypes
  (o : CanonicalName)
  (FS : FrameSemantics)
  (slot-size : ℕ)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Product using (Σ; _×_; _,_)
open import Data.Maybe using (just)
open import Data.Bool using (true)
open import Once.IR using (IR; Unit)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-thunk; c-jmp; AbstractTrace)
open import Once.CCC.Machine.Flat
open FlatMachine {FS} using (FlatState; fpc; fetch)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq
  using (RunAt)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace)
open import Once.CCC.Codegen.ShapeTable
  using (LabelEnv; entry-expect; check-shapes; state-at; HeapModed)
import Once.CCC.Codegen.ShapeTable as ST
open ST.Sem FS using (Meets)

-- M3 — RUN CONSISTENCY: a reachable state of a CHECKED program meets the
-- scanned expectation at its pc.
RunMeets : Set
RunMeets = ∀ prog (fs : FlatState) → RunAt prog fs → (env : LabelEnv)
         → check-shapes env (entry-expect Unit) prog ≡ true
         → Meets (state-at env (entry-expect Unit) prog (fpc fs)) fs

-- the emitted program passes the shape scan under SOME label environment
EmittedShapeCheck : Set
EmittedShapeCheck = ∀ (ir : IR Unit Unit) → HeapModed ir
                  → Σ LabelEnv (λ env →
                      check-shapes env (entry-expect Unit) (ir-to-trace ir) ≡ true)

-- in an emitted trace a `c-thunk` sits at `suc q` with a `c-jmp` at `q` — the
-- guard `ir-to-trace'` emits to stop the parent falling into the body
EmittedThunkGuarded : Set
EmittedThunkGuarded = ∀ (ir : IR Unit Unit) (p : ℕ) (ℓ : LabelId) (bb : ℕ)
                    → fetch (ir-to-trace ir) p ≡ just (instr-ctrl (c-thunk ℓ bb))
                    → Σ ℕ (λ q → (p ≡ suc q)
                          × Σ LabelId (λ m → fetch (ir-to-trace ir) q
                                               ≡ just (instr-ctrl (c-jmp m))))
