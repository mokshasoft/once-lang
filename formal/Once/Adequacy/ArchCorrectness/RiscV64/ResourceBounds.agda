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

open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence as FCr
import Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation as FSimr
import Once.Adequacy.ArchCorrectness.FlatCore.RunContext as RCr
import Once.CCC.Target.RiscV64.Semantics as R
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; instr-alloc-heap; instr-ctrl; c-thunk; c-ret; instr-call-closure
        ; lea-slot; instr-reg-op; scratch-dec; count-inc; instr-load-tag-lit
        ; instr-load-const)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Target.RiscV64.Syntax using (slots; slot-size; sp; s3; s4; Reg)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (slot-to-disp)
open import Data.Nat using (_<_)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Target.RiscV64.FrameInstantiation using (rv64-frame-semantics)
open import Once.Word using (Carrier)
open import Once.Type using (fits-int; fits-float)
open import Once.Float.Dyadic using (Dyadic; encode; binary32; binary64)
open import Data.Float using () renaming (Float to AgdaFloat)
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
  → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
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
  → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
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
  → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
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
-- CONDITIONED ON `RunAt`, like its three siblings — and it took a REFUTATION
-- to get there (2026-08-16). Written first without the run context, because
-- the engine's `bs-lea-slot` field handed an arch only the correspondence, the
-- non-halt and the fetch, the 2026-07-30 probe killed it outright:
--
--     the empty view (`HDom ≡ ⊥`, `hfront ≡ lo ≡ 0`), a current frame based at
--     address 0, every register zero, and `prog ≡ lea-slot modulus ∷ []`
--     satisfies `CompiledCorr` and the fetch — while the conclusion reads
--     `modulus * 8 < modulus`.
--
-- NOTHING IN A CORRESPONDENCE BOUNDS A SLOT INDEX. Bounding it is `RunAt`'s
-- job (`Emitted` ⇒ the shape check ⇒ `slot < frame-slots ≤ ir-stack-budget`),
-- which is precisely why the other three carry it. So the engine's field now
-- hands the `RunAt` down, and this bound has the family's shape.
------------------------------------------------------------------------
SlotAddrNoWrap : Set₁
SlotAddrNoWrap =
  ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
    (s : R.State) (slot : ℕ)
  → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
  → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {rv64-frame-semantics} prog
      (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (lea-slot slot)
  → R.readReg (R.State.regs s) sp + slot-to-disp slot < R.W.modulus

------------------------------------------------------------------------
-- THE REST OF THE FAMILY (plan 0.65 G2), stated exactly the way
-- `X86-64/ResourceBounds.agda` states them. Every one is a fact about the
-- COMPILED PROGRAM'S LAYOUT or about the frontend's literal range — never a
-- claim about user arithmetic, which goes through the Arith backend over
-- `Once.Word` and wraps there by design (D054).
------------------------------------------------------------------------

-- (1) EVERY REGISTER HOLDS A MACHINE WORD. The machine is finite; this says so.
RegRange : Set₁
RegRange =
  ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
    (s : R.State) (r : Reg)
  → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
  → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
  → R.readReg (R.State.regs s) r < R.W.modulus

-- (2) A REACHABLE `scratch-dec` FINDS A NON-ZERO SCRATCH — the no-borrow
-- condition, and NOT a new assumption: the emitter reaches the decrement only
-- through a branch that was not taken. Same class and route as
-- `emitted-thunk-guarded`.
ScratchDecGuarded : Set₁
ScratchDecGuarded =
  ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
    (s : R.State)
  → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
  → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {rv64-frame-semantics} prog
      (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (instr-reg-op scratch-dec)
  → 1 ≤ R.readReg (R.State.regs s) s3

------------------------------------------------------------------------
-- (3) THE ADDRESS SPACE DOES NOT WRAP at the emitted `addi` sites.
--
-- SITE-CONDITIONED, and that is forced: quantified over an arbitrary addend
-- this family is REFUTABLE (take the addend `≡ modulus`).
--
-- `ret-no-wrap` says `suc b`, NOT `b` (2026-08-16). The representable quantity
-- is THE CALLER'S FRAME BASE — the frame AND the slot the call spent. x86-64
-- reaches it in two instructions and needed a bound only on the first; riscv64
-- does both in one `addi`, which is what exposed the field as short by a slot.
------------------------------------------------------------------------
record AddrNoWrap : Set₁ where
  field
    ret-no-wrap :
      ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
        (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
        (s : R.State) (b : ℕ)
      → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
      → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
      → FlatMachine.fetch {rv64-frame-semantics} prog
          (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (instr-ctrl (c-ret b))
      → R.readReg (R.State.regs s) sp + slots (suc b) < R.W.modulus

    -- `count-inc` → `addi s4, s4, 1`: THE ONE NON-ADDRESS SITE. `s4` is the
    -- observable counter, so this says the run does not emit 2⁶⁴ observations.
    count-no-wrap :
      ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
        (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
        (s : R.State)
      → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
      → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
      → FlatMachine.fetch {rv64-frame-semantics} prog
          (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (instr-reg-op count-inc)
      → R.readReg (R.State.regs s) s4 + 1 < R.W.modulus

    -- THE STACK'S HIGH-WATER MARK IS REPRESENTABLE. Not site-conditioned — it
    -- mentions no addend — and it is what discharges the heap bump's no-wrap
    -- outright, since `HeapRoom` already bounds the bumped frontier by `lo`.
    lo-fits :
      ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
        (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
        (s : R.State)
      → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
      → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
      → FCr.lo hv < R.W.modulus
open AddrNoWrap public

------------------------------------------------------------------------
-- (4) THE EMITTED LITERALS FIT IN A MACHINE WORD (plan 0.70 phase D).
--
-- NOT the same class as the rooms: D054 makes an ELABORATED literal in range BY
-- CONSTRUCTION, so this is a fact about the frontend that is simply not
-- threaded here yet — which is exactly what a parameter, and not a postulate,
-- leaves room for (D087).
------------------------------------------------------------------------
record LitFits : Set₁ where
  field
    tag-fits :
      ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
        (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
        (s : R.State) (n : ℕ)
      → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
      → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
      → FlatMachine.fetch {rv64-frame-semantics} prog
          (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (instr-load-tag-lit n)
      → n < R.W.modulus

    lit-fits :
      ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
        (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
        (s : R.State) (v : Carrier)
      → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
      → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
      → FlatMachine.fetch {rv64-frame-semantics} prog
          (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (instr-load-const fits-int v)
      → v < R.W.modulus

    float-fits :
      ∀ {hv : FCr.HeapView rv64-frame-semantics refl}
        (prog : AbstractTrace) (fs : FlatMachine.FlatState {rv64-frame-semantics})
        (s : R.State) (v : Dyadic)
      → RCr.RunAt o rv64-frame-semantics slot-size refl prog fs
      → FSimr.CompiledCorr o rv64-frame-semantics refl hv prog fs s
      → FlatMachine.fetch {rv64-frame-semantics} prog
          (FlatMachine.fpc {rv64-frame-semantics} fs) ≡ just (instr-load-const fits-float v)
      → (encode binary64) v < R.W.modulus
open LitFits public
