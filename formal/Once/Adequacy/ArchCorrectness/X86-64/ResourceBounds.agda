-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds
--
-- The x86-64 RESOURCE BOUNDS, given names so they can be threaded as
-- PARAMETERS instead of postulated (D087: resource bounds are parameters,
-- not postulates — and `--safe` rejects every postulate outright).
--
-- WHY A NAME AND NOT AN INLINE TELESCOPE: the bound has to be written in
-- TWO telescopes — `…ArchCorrectness.X86-64`'s, which consumes it, and
-- every module above that threads it (`ArchCorrectness`, `Compiler`,
-- `Certified`). A module parameter's type cannot mention that module's own
-- body, so the statement needs a home outside both. Naming it here also
-- means the bound is stated ONCE; the thread above is `HeapRoom o` at every
-- level and cannot drift.
--
-- WHAT THIS IS NOT: a place for stubs. `conc-fuel` does NOT belong here —
-- it asserts the adequacy of `step-budget-x86-64`, which is an UNDEFINED
-- postulated `ℕ → ℕ` in `Once.Adequacy.CPU.X86-64`. That is a hole in the
-- implementation, not a fact about the world, and dressing it as a resource
-- parameter would freeze it as one. It becomes provable when `step-budget`
-- is pinned to a definition.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds (o : CanonicalName) where

open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence as FCx
import Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation as FSimx
import Once.Adequacy.ArchCorrectness.X86-64.RunContext as RCx
import Once.CCC.Target.X86-64.Semantics as X
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; instr-alloc-heap; instr-ctrl; c-thunk)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Target.X86-64.Syntax using (slots; reg; rsp)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Target.X86-64.FrameInstantiation using (x86-64-frame-semantics)

------------------------------------------------------------------------
-- HEAP EXHAUSTION: at an emitted `instr-alloc-heap n` the bump does not run
-- the heap frontier up into the stack's high-water mark.
--
-- CONDITIONED on the run context (`RunAt`) and the correspondence
-- (`CompiledCorr`) — unconditioned it is REFUTABLE (a view with
-- `lo ≡ hfront` kills it), which is the 2026-07-30 vacuity lesson, and why
-- `RunAt` had to move to `RunContext` in the first place.
--
-- This is the honest kind of assumption: a property of the running program
-- that a linker could one day discharge by sizing the heap and stack for the
-- compiled program. A PARAMETER is exactly the shape such a proof slots
-- into — a postulate could only be deleted and re-plumbed.
------------------------------------------------------------------------
HeapRoom : Set₁
HeapRoom =
  ∀ {hv : FCx.HeapView x86-64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {x86-64-frame-semantics})
    (s : X.State) (n : ℕ)
  → RCx.RunAt o x86-64-frame-semantics refl prog fs
  → FSimx.CompiledCorr x86-64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {x86-64-frame-semantics} prog
      (FlatMachine.fpc {x86-64-frame-semantics} fs) ≡ just (instr-alloc-heap n)
  → FCx.hfront hv + slots n ≤ FCx.lo hv

------------------------------------------------------------------------
-- STACK EXHAUSTION: at an emitted `c-thunk m b` the body's reservation does
-- not run `%rsp` down into the heap's allocation frontier.
--
-- THE EXACT MIRROR OF `HeapRoom`, and deliberately so — the two bounds say
-- the same thing about the two ends of the same virgin region `[hfront, lo)`:
-- an allocation must not consume it from below, a frame reservation must not
-- consume it from above. Same conditioning (`RunAt` + `CompiledCorr` + the
-- site), same class, same reason it is a PARAMETER and not a postulate
-- (D087): a linker sizing pass discharges it, and a parameter is the hole
-- that proof slots into.
--
-- WHY `hfront + slots b ≤ %rsp` AND NOT THE TWO CONSEQUENCES SEPARATELY. The
-- `c-thunk` block-step needs `slots b ≤ %rsp` (the `sub` does not underflow)
-- and `hfront ≤ %rsp ∸ slots b` (the reserved frame stays above the heap).
-- Truncated subtraction makes the second NOT imply the first, so stating them
-- apart would be two parameters where the additive form is one — and the
-- additive form is also the one a sizing pass would actually establish.
------------------------------------------------------------------------
StackRoom : Set₁
StackRoom =
  ∀ {hv : FCx.HeapView x86-64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {x86-64-frame-semantics})
    (s : X.State) (m : LabelId) (b : ℕ)
  → RCx.RunAt o x86-64-frame-semantics refl prog fs
  → FSimx.CompiledCorr x86-64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {x86-64-frame-semantics} prog
      (FlatMachine.fpc {x86-64-frame-semantics} fs) ≡ just (instr-ctrl (c-thunk m b))
  → FCx.hfront hv + slots b ≤ X.readReg (X.State.regs s) rsp
