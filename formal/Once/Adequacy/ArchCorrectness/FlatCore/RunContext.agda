-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.RunContext
--
-- THE RUN CONTEXT, extracted from `ConcFlatSim` (Plan 0.63, 2026-08-05) and
-- generalised off x86-64 (Plan 0.65 G1, 2026-08-11).
--
-- ARCH-GENERIC. Nothing here mentions a machine: `EntryLike`, `Reachable`,
-- `Emitted` and `RunAt` are statements about the FLAT machine and the emitted
-- trace. The only thing x86-64 was supplying is the NUMBER `slot-size`, for
-- `word-eq`. That is a parameter now, so the three arches share one definition
-- instead of three copies that have to be kept in step.
--
-- Why it is its own module: the correspondence's honest RESOURCE bounds
-- (heap room, stack room) must become PARAMETERS of `ConcFlatSim` rather than
-- postulates inside it — `agda --safe` rejects every postulate outright, so
-- the endgame is a cone with none, and each remaining assumption visible in
-- the apex theorem's TYPE. A module parameter's type has to be expressible
-- BEFORE the module body, and those bounds are conditioned on `RunAt`
-- (without that conditioning they are refutable — the 2026-07-30 vacuity
-- lesson). So `RunAt` has to live one layer down. That is all this module is.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatCore.RunContext (o : CanonicalName)
  (FS : FrameSemantics)
  -- the arch's slot width (8 on x86-64 and riscv64, 4 on x86-32) — the one
  -- thing this module used to import from a target
  (slot-size : ℕ)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Nat using (zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open import Once.IR using (IR; Unit)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-stack-budget)
open import Once.CCC.Codegen.ShapeTable using (HeapModed)

-- A state a program can START in: at the first instruction, running, with nothing
-- allocated on either side. (The apex's entry state is one — see `entry-run`.)
-- NB: NOT `frame-slots ≡ 0`. The loader hands `main` a frame the per-arch prologue
-- has already reserved (`subq $budget*8, %rsp`), and `ir-to-trace` emits no frame
-- op that could reserve one later — so a start state whose `frame-slots` is 0 would
-- make the live stack window empty FOR THE WHOLE RUN, and every "the slot this
-- instruction reads is in frame" residual false. `FlatFromObs.entry-s` therefore
-- starts at `ir-stack-budget`, and this predicate leaves `frame-slots` free.
EntryLike : FlatState → Set
EntryLike fs = (fpc fs ≡ 0)
             × (halted (floc fs) ≡ false)
             × (next-slot (falloc fs) ≡ 0)
             × (saved-frames (falloc fs) ≡ [])
             -- …and the GHOST RETURN STACK is empty too (Plan 0.63). Without
             -- this a "start" state could arrive already owing a return, and
             -- the frame stack and the return stack — which `c-thunk`/`c-ret`
             -- push and pop TOGETHER — would not be relatable. True of the
             -- apex's entry state by construction (`mkFlat` defaults it).
             × (fret fs ≡ [])
             × (∀ hl → heapMem (floc fs) hl ≡ nothing)
             × (∀ f k → stackMem (floc fs) f k ≡ nothing)
             × (∀ r → block-size (falloc fs) r ≡ 0)
             -- …and NO REGISTER holds a pointer AT ALL. Every entry register
             -- is the tag filler `SV-Tag 0` (D074), so this is true of the
             -- entry state by construction. STRENGTHENED 2026-08-01 from "no
             -- stack pointer": with the block sizes all 0, a dynamic filler
             -- pointer would refute the pointer-bounds invariant at entry the
             -- same way a stack filler would refute the stack-pointer one —
             -- this component starts BOTH invariants (and the store-WF one)
             -- off (`entry-stack-ptr` / `entry-ptr-bounds` / `entry-flat-wf`).
             × (∀ (r : AbstractReg) (loc : ValueLocation FS)
                → readReg (regs (floc fs)) r ≡ SV-Ptr loc → ⊥)

-- …indexed by the STATIC SLOT BUDGET `B` the prologue reserved. The entry state
-- pins `frame-slots` to it (`reach-start`), and no reachable step can move it —
-- `ir-to-trace` emits no frame op, and the frame ops are the only writers of
-- `frame-slots`. That is what turns "the slot this instruction addresses is in
-- frame" from an assumption about arbitrary states into arithmetic about the
-- emitter's own frontier (`run-stack-slot` + `emitted-slot-below-budget` below).
data Reachable (prog : AbstractTrace) (B : ℕ) : FlatState → Set where
  reach-start : ∀ (fs : FlatState) → EntryLike fs
              → frame-slots (falloc fs) ≡ B
              → Reachable prog B fs
  reach-step  : ∀ (i : AbstractInstr) (fs : FlatState)
              → Reachable prog B fs
              → fetch prog (fpc fs) ≡ just i
              → halted (floc fs) ≡ false
              → Reachable prog B (flat-exec-instr i prog fs)

-- …and the program is one the compiler EMITTED. Without this, a hand-picked
-- `prog` refutes the program-shape residuals AT THE ENTRY STATE (e.g.
-- `load-from-slot 5 ∷ []` reads a slot the entry frame does not have).
Emitted : AbstractTrace → Set
Emitted prog = Σ (IR Unit Unit) (λ ir → prog ≡ ir-to-trace ir)

-- THE RUN CONTEXT every state/program fact below needs, as ONE record: the
-- program is `ir`'s emitted trace, and the state is reachable in a run that
-- started in `ir`'s reserved frame. The budget is tied to the SAME `ir` as the
-- program — bundling is what makes that possible (two separate hypotheses would
-- quantify over unrelated IRs, and "same trace ⇒ same budget" is not available).
record RunAt (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkRunAt
  field
    run-ir    : IR Unit Unit
    run-emit  : prog ≡ ir-to-trace run-ir
    -- Plan 0.62 wiring: the run's IR is HEAP-MODED (the pipeline compiles
    -- with `C.Heap`; supplied at the apex via `moduleToIR-heap`). The shape
    -- checker's claims are heap-shaped, so its emitter fact needs this.
    run-heap  : HeapModed run-ir
    run-reach : Reachable prog (ir-stack-budget run-ir) fs
open RunAt public

run-emitted : ∀ {prog fs} → RunAt prog fs → Emitted prog
run-emitted r = run-ir r , run-emit r
