-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Data.Nat using (ℕ; _+_; _≤_; _<_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence as FCx
import Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation as FSimx
import Once.Adequacy.ArchCorrectness.X86-64.RunContext as RCx
import Once.CCC.Target.X86-64.Semantics as X
import Once.Word as W64
module W = W64.Width 64
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; instr-alloc-heap; instr-ctrl; c-thunk; c-ret; instr-call-closure
        ; instr-reg-op; scratch-dec; count-inc)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Target.X86-64.Syntax using (slots; slot-size; reg; rsp; rbx; r14; Reg)
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
-- site), same class, same reason it is a PARAMETER (D087): a linker sizing
-- pass discharges it, and a parameter is the hole that proof slots into.
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

------------------------------------------------------------------------
-- CALL DEPTH: at an emitted `instr-call-closure` there is room for the ONE
-- slot the call spends on the return address.
--
-- The third of the same family, and the smallest: ONE slot, the one a call
-- spends on the return address (D086 — the body's `c-thunk` reserves the
-- rest). So this is stack exhaustion measured per CALL rather than per frame.
-- Same conditioning, same class, same reason it is a parameter (D087).
--
-- ADDITIVE, for `StackRoom`'s reason: the block-step needs both `slot-size ≤
-- %rsp` (the push does not underflow) and `hfront ≤ %rsp ∸ slot-size` (the
-- pushed cell stays above the heap), and truncated subtraction makes the
-- second not imply the first.
------------------------------------------------------------------------
CallRoom : Set₁
CallRoom =
  ∀ {hv : FCx.HeapView x86-64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {x86-64-frame-semantics})
    (s : X.State)
  → RCx.RunAt o x86-64-frame-semantics refl prog fs
  → FSimx.CompiledCorr x86-64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {x86-64-frame-semantics} prog
      (FlatMachine.fpc {x86-64-frame-semantics} fs) ≡ just instr-call-closure
  → FCx.hfront hv + slot-size ≤ X.readReg (X.State.regs s) rsp

------------------------------------------------------------------------
-- THE MACHINE IS FINITE (plan 0.70 phase C).
--
-- Once the model's arithmetic is MODULAR, two facts the ℕ model gave for free
-- have to be said. Both are D087-class — properties of a running program that
-- a loader or the emitter establishes — so both are PARAMETERS, which is the
-- hole a future proof slots into.
--
-- (1) REGISTERS HOLD MACHINE WORDS. Trivially true of any real state, and not
-- derivable here: `⊕`/`⊖` produce normed results, but `mov reg, imm n` and
-- `lea` write values this model does not bound. It becomes a THEOREM the day
-- the register file carries its range, and this parameter is where that proof
-- will land.
RegRange : Set₁
RegRange =
  ∀ {hv : FCx.HeapView x86-64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {x86-64-frame-semantics})
    (s : X.State) (r : Reg)
  → RCx.RunAt o x86-64-frame-semantics refl prog fs
  → FSimx.CompiledCorr x86-64-frame-semantics refl hv prog fs s
  → X.readReg (X.State.regs s) r < W.modulus

-- (2) A REACHABLE `scratch-dec` FINDS A NON-ZERO SCRATCH — the no-borrow
-- condition for the one subtraction that never had one. NOT a new assumption
-- about the world: the emitter already guarantees it, since `cata-nat-I₂`/`I₃`
-- emit `L4: branch-if-scratch-zero → L5 ; body ; scratch-dec ; jmp L4 ; L5:`
-- and the decrement is reached only when the branch was not taken. Same class
-- and same route as `emitted-thunk-guarded`: a fact about `ir-to-trace`'s
-- output, discharged by the structural induction over it.
ScratchDecGuarded : Set₁
ScratchDecGuarded =
  ∀ {hv : FCx.HeapView x86-64-frame-semantics refl}
    (prog : AbstractTrace) (fs : FlatMachine.FlatState {x86-64-frame-semantics})
    (s : X.State)
  → RCx.RunAt o x86-64-frame-semantics refl prog fs
  → FSimx.CompiledCorr x86-64-frame-semantics refl hv prog fs s
  → FlatMachine.fetch {x86-64-frame-semantics} prog
      (FlatMachine.fpc {x86-64-frame-semantics} fs) ≡ just (instr-reg-op scratch-dec)
  → 1 ≤ X.readReg (X.State.regs s) rbx

------------------------------------------------------------------------
-- (3) THE ADDRESS SPACE DOES NOT WRAP at the emitted `add` sites.
--
-- Plan 0.70 phase C. `execInstr`'s `add` computes `W.⊕` — modular, always,
-- with NO no-overflow premise, because D054 makes wraparound *correct,
-- defined* Once semantics, "not something the programmer or the compiler
-- must prove absent". A precondition there would be exactly "the narrow
-- regime where the impossible accidentally holds", which D054 rejects.
--
-- So the obligation moves to the CONSUMER, and this is it. It is NOT a claim
-- about user arithmetic: every `add` the compiler emits computes an ADDRESS
-- (`rsp` frame release, `r15` heap bump, the `rcx`/`rdi` index scaling) or
-- the observable COUNTER (`r14`). A user `Int` addition never reaches this
-- instruction — it goes through the Arith backend over `Once.Word` and wraps
-- there by design, which is why a program whose `Int` arithmetic overflows is
-- still fully covered by the correctness theorem.
--
-- What this says is therefore the same KIND of thing as `HeapRoom` /
-- `StackRoom` / `CallRoom`: the compiled program's layout fits in the machine's
-- address space. Same discharge route too — a linker that sizes the image.
--
-- SITE-CONDITIONED, and that is forced: quantified over an arbitrary addend
-- `n` this family is REFUTABLE (take `n ≡ modulus`), the residual-inconsistency
-- trap. Every field therefore pins its addend to the fetched instruction.
--
-- A RECORD rather than loose definitions so the thread above
-- (`ArchCorrectness.X86-64` → `ArchCorrectness` → `Compiler` → `Certified`)
-- is written once and does not change as fields are added.
record AddrNoWrap : Set₁ where
  field
    -- `c-ret b` → `add rsp, slots b`: releasing the frame stays in range.
    -- (The released address is the caller's frame base less one slot — see
    -- `block-step-c-ret`'s `addr-eq`/`gap` — so this is a layout fact.)
    ret-no-wrap :
      ∀ {hv : FCx.HeapView x86-64-frame-semantics refl}
        (prog : AbstractTrace) (fs : FlatMachine.FlatState {x86-64-frame-semantics})
        (s : X.State) (b : ℕ)
      → RCx.RunAt o x86-64-frame-semantics refl prog fs
      → FSimx.CompiledCorr x86-64-frame-semantics refl hv prog fs s
      → FlatMachine.fetch {x86-64-frame-semantics} prog
          (FlatMachine.fpc {x86-64-frame-semantics} fs) ≡ just (instr-ctrl (c-ret b))
      → X.readReg (X.State.regs s) rsp + slots b < W.modulus

    -- `count-inc` → `add r14, 1`: THE ONE NON-ADDRESS SITE. `%r14` is the
    -- observable counter, so this says the run does not emit 2⁶⁴ observations.
    count-no-wrap :
      ∀ {hv : FCx.HeapView x86-64-frame-semantics refl}
        (prog : AbstractTrace) (fs : FlatMachine.FlatState {x86-64-frame-semantics})
        (s : X.State)
      → RCx.RunAt o x86-64-frame-semantics refl prog fs
      → FSimx.CompiledCorr x86-64-frame-semantics refl hv prog fs s
      → FlatMachine.fetch {x86-64-frame-semantics} prog
          (FlatMachine.fpc {x86-64-frame-semantics} fs) ≡ just (instr-reg-op count-inc)
      → X.readReg (X.State.regs s) r14 + 1 < W.modulus

    -- THE STACK'S HIGH-WATER MARK IS REPRESENTABLE. Not site-conditioned,
    -- because it need not be: it mentions no addend. This is the layout bound
    -- in its most basic form — and it is what discharges the heap bump's
    -- no-wrap outright, since `HeapRoom` already bounds the bumped frontier
    -- by `lo`. The other three fields are the sites where no such bound was
    -- already in hand.
    lo-fits :
      ∀ {hv : FCx.HeapView x86-64-frame-semantics refl}
        (prog : AbstractTrace) (fs : FlatMachine.FlatState {x86-64-frame-semantics})
        (s : X.State)
      → RCx.RunAt o x86-64-frame-semantics refl prog fs
      → FSimx.CompiledCorr x86-64-frame-semantics refl hv prog fs s
      → FCx.lo hv < W.modulus
open AddrNoWrap public
