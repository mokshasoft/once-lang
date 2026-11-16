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

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word; fs-interp)
open import Once.IR.Semantics.Trace using (module Interp)
open Interp using (sig)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.Spec.Name using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatCore.RunContext (o : CanonicalName)
  (FS : FrameSemantics)
  -- the arch's slot width (8 on x86-64 and riscv64, 4 on x86-32) — the one
  -- thing this module used to import from a target
  (slot-size : ℕ)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Bool using (false)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Sum using (_⊎_)
open import Data.Nat using (suc; _<_)
open import Once.CCC.Machine.FrameFree using (ImageI)
open import Once.CCC.Codegen.AllocMin o using (AllocMinI)
open import Once.CCC.Codegen.SlotSeg using (seg-at; mkSeg; SegState; module SegState)
open import Once.CCC.Codegen.LabelSeg using (mention-at)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.CCC.Machine.Locations using (Slot; AtDynamic)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.CCC.Label using (LabelId; EntryId)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.CCC.Machine.SMCore
open AllocState using (next-slot; saved-frames; block-size; frame-slots)
open LocState using (halted; heapMem; stackMem; regs)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.Type using (FitsInReg)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.Machine.Flat
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (Sound; sound-step)
open FlatMachine {FS}
open import Once.IR using (IR)
open import Once.IRTy using (Unit)
open import Once.CCC.Codegen.ProgramImage using (program-image)
open import Once.Denotation.Program using (IRFun; irProgram; LinkedProgram)
open import Data.List using (List)

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
             -- …and NO UNSPILLED RETURN (plan 0.65 G2, 2026-08-16). `flink`
             -- marks the one-step call window, and a start state is not in
             -- one — it has not been called from anywhere. True of the apex's
             -- entry state by construction (`mkFlat` defaults it), and it is
             -- the base case of `run-link-at-thunk`: without it a "start"
             -- state could claim a pending return that no call ever made.
             × (flink fs ≡ nothing)
             -- …and NO REGISTER holds a literal (D397): the entry registers are
             -- the tag filler, so the store-WF invariant's word range (every
             -- stored `Int` below the modulus) starts off too (`entry-flat-wf`).
             × (∀ (r : AbstractReg) {A} (p : FitsInReg A) (v : ⟦ A ⟧)
                → readReg (regs (floc fs)) r ≡ SV-Lit p v → ⊥)

-- …indexed by the STATIC SLOT BUDGET `B` the prologue reserved. The entry state
-- pins `frame-slots` to it (`reach-start`), and no reachable step can move it —
-- `ir-to-trace` emits no frame op, and the frame ops are the only writers of
-- `frame-slots`. That is what turns "the slot this instruction addresses is in
-- frame" from an assumption about arbitrary states into arithmetic about the
-- emitter's own frontier (`run-stack-slot` + `emitted-slot-below-budget` below).
data Reachable (prog : AbstractTrace) (B : ℕ) : FlatState → Set where
  reach-start : ∀ (fs : FlatState) → EntryLike fs
              → frame-slots (falloc fs) ≡ B
              -- D367: …and the run from the start NEVER FAULTS. Not a property
              -- of the code alone (a hand-built state can hold a non-pointer
              -- anywhere) but of the program's own run, which `ir-obs-correct`
              -- describes: the apex supplies it (`FlatFromObs.start-sound`),
              -- and every reached state inherits it (`reach-sound`).
              → Sound prog fs
              → Reachable prog B fs
  reach-step  : ∀ (i : AbstractInstr) (fs : FlatState)
              → Reachable prog B fs
              → fetch prog (fpc fs) ≡ just i
              → halted (floc fs) ≡ false
              → Reachable prog B (flat-exec-instr i prog fs)

-- …and the program is one the compiler EMITTED. Without this, a hand-picked
-- `prog` refutes the program-shape residuals AT THE ENTRY STATE (e.g.
-- `load-from-slot 5 ∷ []` reads a slot the entry frame does not have).
-- D244/D245: the program is a PROGRAM IMAGE — `main`'s unit, then every entry
-- of its function table (`ProgramImage`). A program whose table is empty is
-- `main`'s unit alone, the shape this module assumed before.
-- plan 0.146 B1.6: the program's facts the arch layer reads, as ONE bundle, in
-- place of "it is the old lowering's image" (`prog ≡ program-image …`), so that
-- any image meeting them — the old one (`RunWF.old-emitted`), the new core's —
-- runs on the arch layer. Each field is what a site lemma of `RunWF` read off
-- the old image; the last three are about the program's RUN (reachable states).
record Emitted (prog : AbstractTrace) : Set where
  field
    -- the start: pc 0 and nowhere else, at the program's stack budget
    em-budget : ℕ
    em-zero   : fetch prog 0 ≡ just (instr-ctrl (c-start em-budget))
    em-start  : ∀ k b → fetch prog k ≡ just (instr-ctrl (c-start b)) → k ≡ 0
    -- every instruction the arch layer covers, a heap block of two words at least
    em-image  : All ImageI prog
    em-alloc  : All AllocMinI prog
    -- a slot an instruction addresses is below the segment in force
    em-slots  : ∀ k (i : AbstractInstr) (slot : Slot) → fetch prog k ≡ just i → slot-of i ≡ just slot
              → slot < SegState.cur (seg-at prog k (mkSeg 0 []))
    -- a call names an entry; a code address names a body; an entry is guarded:
    -- what precedes it does not fall through (a jump, a return, or the
    -- program's leave, which halts where it stands: D437)
    em-calls  : ∀ k f → fetch prog k ≡ just (instr-ctrl (c-call-fn f)) → Σ ℕ (λ j → find-fn prog f ≡ just j)
    em-code   : ∀ p (ℓ : LabelId) → fetch prog p ≡ just (instr-load-code-addr ℓ) → Σ ℕ (λ j → find-thunk prog ℓ ≡ just j)
    em-guard  : ∀ p (ℓ : EntryId) (bb : ℕ) → fetch prog p ≡ just (instr-ctrl (c-entry ℓ bb))
              → Σ ℕ (λ q → (p ≡ suc q)
                    × ((Σ LabelId (λ m → fetch prog q ≡ just (instr-ctrl (c-jmp m))))
                       ⊎ (Σ ℕ (λ b → fetch prog q ≡ just (instr-ctrl (c-ret b))))
                       ⊎ (fetch prog q ≡ just (instr-ctrl c-leave))))
    -- a jump stays in its segment
    em-jump   : ∀ p q (m : LabelId) (st : SegState) → mention-at prog p ≡ just m → find-label prog m ≡ just q
              → seg-at prog q st ≡ seg-at prog p st
    -- the run: a closure call's register, a return owed, its budget the reservation in force
    em-call-site : ∀ fs → Reachable prog 0 fs → fetch prog (fpc fs) ≡ just instr-call-closure
                 → Σ HeapLocation (λ hl → Σ LabelId (λ ℓ → Σ ℕ (λ j →
                     (fclosure fs ≡ SV-Ptr (AtDynamic hl))
                     × (heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ))
                     × (find-thunk prog ℓ ≡ just j))))
    em-ret-owes  : ∀ fs (b : ℕ) → Reachable prog 0 fs → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
                 → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest))
    em-ret-budget : ∀ fs (b : ℕ) → Reachable prog 0 fs → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
                  → b ≡ frame-slots (falloc fs)
open Emitted public

-- (`CallI`, the two calls, lives beside the instruction set: `SMCore`.)

-- A call neither jumps nor returns.
call-not-jmp : ∀ (c : AbstractInstr) → CallI c → ∀ m → c ≡ instr-ctrl (c-jmp m) → ⊥
call-not-jmp c ci m refl = ci

call-not-ret : ∀ (c : AbstractInstr) → CallI c → ∀ b → c ≡ instr-ctrl (c-ret b) → ⊥
call-not-ret c ci b refl = ci

-- Every call in the image is linked (`Once.Denotation.Program.Linked`) — and
-- (plan 0.105) every FFI SigOp it calls is declared by the interpretation the
-- machine runs against.
LinkedImage : List IRFun → IR Unit Unit → Set
LinkedImage tbl ir = LinkedProgram (sig (fs-interp FS)) (irProgram tbl ir)

-- THE RUN CONTEXT every state/program fact below needs, as ONE record: the
-- program is `ir`'s emitted trace, and the state is reachable in a run that
-- started in `ir`'s reserved frame. The budget is tied to the SAME `ir` as the
-- program — bundling is what makes that possible (two separate hypotheses would
-- quantify over unrelated IRs, and "same trace ⇒ same budget" is not available).
record RunAt (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkRunAt
  field
    -- the program's facts (plan 0.146 B1.6: a bundle, in place of the old image's equation)
    run-em    : Emitted prog
    -- plan 0.107: the run starts OUTSIDE every frame — `c-start` (pc 0) reserves
    -- the outermost one as an ordinary, proved step.
    run-reach : Reachable prog 0 fs
open RunAt public

-- D367: a reached state's run never faults — the start's does, and a step
-- keeps it. What the site facts in `RunWF` are read off.
reach-sound : ∀ {prog B fs} → Reachable prog B fs → Sound prog fs
reach-sound (reach-start _ _ _ snd)    = snd
reach-sound (reach-step i fs r ftq h) = sound-step (reach-sound r) h ftq

run-sound : ∀ {prog fs} → RunAt prog fs → Sound prog fs
run-sound r = reach-sound (run-reach r)

run-emitted : ∀ {prog fs} → RunAt prog fs → Emitted prog
run-emitted r = run-em r
