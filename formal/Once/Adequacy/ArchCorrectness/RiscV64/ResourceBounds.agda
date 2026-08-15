-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds
--
-- riscv64's three RESOURCE BOUNDS, as the types the apex threads (D087, and
-- plan 0.65's corrected ordering).
--
-- WHY THIS MODULE EXISTS AT ALL, and why it could not before today: all three
-- are CONDITIONED on `CompiledCorr` and `RunAt`. Unconditioned they are
-- REFUTABLE — a view with `lo ≡ hfront` kills `HeapRoom` — which is the
-- 2026-07-30 vacuity lesson and the reason `RunAt` moved to `RunContext`. So
-- riscv64 had no way to STATE its bounds until it had a correspondence, and
-- therefore no way to thread them from `Certified` down.
--
-- That ordering matters more than it looks. The plan originally built G2's
-- block-steps first and threaded the bounds afterwards (G3) — which means each
-- block-step invents the shape of its own resource premise and the thread then
-- has to match shapes already chosen. With the bounds threaded FIRST, the apex
-- constrains them and the block-steps receive their premises instead.
--
-- Same three, same shapes, same reasons as x86-64's — including the ADDITIVE
-- form of `StackRoom`/`CallRoom`, which is not stylistic: the block-step needs
-- both `slots b ≤ sp` (the reservation does not underflow) and
-- `hfront ≤ sp ∸ slots b` (it stays above the heap), and truncated subtraction
-- makes the second not imply the first.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds (o : CanonicalName) where

open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence as FCr
import Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation as FSimr
import Once.Adequacy.ArchCorrectness.FlatCore.RunContext as RCr
import Once.CCC.Target.RiscV64.Semantics as R
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; instr-alloc-heap; instr-ctrl; c-thunk; instr-call-closure; lea-slot)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Target.RiscV64.Syntax using (slots; slot-size; sp)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (slot-to-disp)
open import Data.Nat using (_<_)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Target.RiscV64.FrameInstantiation using (rv64-frame-semantics)
-- …and riscv64's ENGINE INTERFACES (plan 0.65 G2). Imported here for the same
-- reason this module's own siblings are: nothing else reaches them, and an
-- unimported module is invisible to the four clusters. The instantiation pins
-- the frame semantics exactly as the bounds above do.
-- (imported, not applied: the import alone is what makes it typechecked, and
-- it now takes a resource parameter the apex will thread — `SlotAddrNoWrap`
-- below.)
import Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim as CFSr

------------------------------------------------------------------------
-- HEAP EXHAUSTION: at an emitted `instr-alloc-heap n` the bump does not run
-- the heap frontier up into the stack's high-water mark.
------------------------------------------------------------------------
HeapRoom : Set₁
HeapRoom =
  ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
    (s : R.State) (n : ℕ)
  → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
  → FSimr.CompiledCorr rv64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {rv64-frame-semantics} prog
      (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (instr-alloc-heap n)
  → FCr.hfront hv + slots n ≤ FCr.lo hv

------------------------------------------------------------------------
-- STACK EXHAUSTION: at an emitted `c-thunk m b` the body's reservation does
-- not run `sp` down into the heap's allocation frontier.
------------------------------------------------------------------------
StackRoom : Set₁
StackRoom =
  ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
    (s : R.State) (m : LabelId) (b : ℕ)
  → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
  → FSimr.CompiledCorr rv64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {rv64-frame-semantics} prog
      (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (instr-ctrl (c-thunk m b))
  → FCr.hfront hv + slots b ≤ R.readReg (R.State.regs s) sp

------------------------------------------------------------------------
-- CALL DEPTH: at an emitted `instr-call-closure` there is room for the ONE
-- slot the call spends on the return address.
------------------------------------------------------------------------
CallRoom : Set₁
CallRoom =
  ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
    (s : R.State)
  → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
  → FSimr.CompiledCorr rv64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {rv64-frame-semantics} prog
      (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just instr-call-closure
  → FCr.hfront hv + slot-size ≤ R.readReg (R.State.regs s) sp

------------------------------------------------------------------------
-- THE SLOT ADDRESS DOES NOT WRAP (plan 0.65 G2, D087 class).
--
-- riscv64's fourth bound, and the one x86-64 has no counterpart for: it has no
-- `lea`, so a slot address is computed with `addi`, a real add, and `add`
-- computes `W.⊕` unconditionally (D054 — wraparound is DEFINED semantics, so
-- no no-overflow precondition may sit on the instruction). The range
-- obligation lands here instead.
--
-- NOT conditioned on `RunAt`, unlike its three siblings above, and that is
-- forced rather than chosen: the engine's `bs-lea-slot` field hands an arch
-- only the correspondence, the non-halt and the fetch. So this is STRICTLY
-- STRONGER than the family it belongs to. Check it against the 2026-07-30
-- refutability probe before trusting it; if it does not survive, the fix is to
-- give the engine's field a `RunAt` premise rather than to weaken this.
------------------------------------------------------------------------
SlotAddrNoWrap : Set₁
SlotAddrNoWrap =
  ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
    (s : R.State) (slot : ℕ)
  → FSimr.CompiledCorr rv64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {rv64-frame-semantics} prog
      (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (lea-slot slot)
  → R.readReg (R.State.regs s) sp + slot-to-disp slot < R.W.modulus
