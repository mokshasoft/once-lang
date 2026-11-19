-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.Entry (plan 0.146 step 4, D465: the entry facts of master's
-- apex, which went with master's lowering; nothing here names an image) — was: — riscv64's backend-correctness
-- witness, routed THROUGH the generic per-IR observable theorem.
--
-- Mirror of `Once.Adequacy.ArchCorrectness.X86-64` (Plan 0.53 Phase 3):
-- `riscv64-correct` is discharged through `ir-obs-correct` — the total
-- IR-observable dispatch (`Once.CCC.Codegen.IRObsCorrectFlat`, GENERIC in
-- `FrameSemantics`), instantiated at riscv64's `FrameSemantics`. Since
-- `ir-obs-correct` routes `Cata → cata-correct`, `cata-correct` is
-- LOAD-BEARING for the apex `correct` on this target too.
--
-- riscv64-correct is now CONSTRUCTED via the shared `FlatFromObs` module
-- (Phase B L1): `asm-sem`/`flat-trace` DEFINED, `assemble-correct` = `refl`,
-- with named postulates `asm-trace-correct`/`ir-flat-correct` + the loader
-- `entry-s`/`entry-alloc`. The old monolithic `riscv64-flat-from-obs`
-- postulate is retired.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.Spec.Name using (CanonicalName)


import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBr
import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence as FCr

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun)
open import Once.IR.Semantics.Trace using (Interp; module Interp)
open Interp using (sig)
module Once.Adequacy.ArchCorrectness.RiscV64.Entry (o : CanonicalName)
  -- Plan 0.105: the interpretation the program runs against.
  (ι : Interp)
  -- Plan 0.65: the resource bounds, as PARAMETERS threaded from the apex (D087),
  -- symmetric with x86-64. G3 (2026-08-17) is where they finally get CONSUMED:
  -- until the simulation was whole-cloth nothing below had asked for them, and
  -- three of the twelve were all that had been written down. (The three room
  -- bounds left with plan 0.123 A.4 step 5: the checks and their budget.)
  (riscv64-reg-range : RBr.RegRange o ι)
  (riscv64-slot-addr-no-wrap : RBr.SlotAddrNoWrap o ι)
  (riscv64-addr-no-wrap : RBr.AddrNoWrap o ι)
  (riscv64-lit-fits : RBr.LitFits o ι) where

import Once.CCC.Machine.SMCore
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([])
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.Adequacy.MachineTrace using (module Machine)
import Once.Target.Arch
open import Once.Adequacy.BudgetApex (Once.Target.Arch.arch-numerics Once.Target.Arch.riscv64) using (budget-apex-⊑; BudgetFact⊑; budget-fact-of)
open import Once.Denotation.Program using (runIR)
open import Once.IR.Semantics.Trace using (pureHalf)
open import Data.Bool using (Bool)
open import Data.Product using (proj₁; proj₂; _,_)
open import Once.Adequacy.CPU.RiscV64 using (call-at-riscv64; ev-riscv64; block-env; run-trace-riscv64)
import Once.CCC.Target.RiscV64.File as RF
import Data.Maybe
open import Data.Sum using (inj₁; inj₂)
open import Once.IR.Semantics.Event using (SigOpEvent)
open import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 using (val-riscv64)
import Once.Arith.Backend.RiscV64.RunTrace as RTr
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Once.IR using (IR)
open import Once.IRTy using (Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Adequacy.CPU using (arch-semantics)
open import Once.Target.Arch using (riscv64)
open import Once.Arith.Backend.CallAnswer using (answer-at)
open import Once.Adequacy.SourceTrace using (⟦_⟧IRᵗ)
import Once.IR as IR
open import Once.Denotation.Program using (irProgram; LinkedProgram; IRProgram)
open Once.Denotation.Program.IRProgram using (main; table)
open import Once.Target.Arch using (arch-numerics)
open import Once.CCC.Target.RiscV64.FrameInstantiation using () renaming (rv64-frame-semantics to rv64-frame-semantics-at)
open import Once.CCC.FrameSemantics using (FrameSemantics)

rv64-frame-semantics : FrameSemantics
rv64-frame-semantics = rv64-frame-semantics-at ι
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace-cnt; compile-trace-cnt-agrees; compile-trace; slot-to-disp)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size) renaming (Program to RVProgram)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; sucHL; module HeapLocation)
open HeapLocation using (heap-offset)
open import Once.CCC.Label using (LabelId; thunk)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore using (module AllocState)
open AllocState using (current-frame)
open FrameSemantics using (frame-base)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Nat using (_+_; _*_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; ≤-refl; ≤-reflexive; m≤m+n)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D100: the assembler's precondition (distinct emitted local labels), threaded
-- into this arch's `loader-faithful` axiom.
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.Adequacy.RoomChecksEvents using (module RoomEvents)
import Once.CCC.Target.RiscV64.Semantics as RS
open import Once.CCC.Target.RiscV64.Layout using (module Regions)
open Regions using (InStack)
open import Once.Memory.StackSlots using (stack-addr)

-- Plan 0.91 S1 (D213): `program-bound` is GONE. It was introduced by Plan 0.54
-- rung D / D087 as a per-arch RESOURCE BOUND, threaded from the apex so the
-- top-level statement said "for any program bound" — but `ir-obs-correct`
-- recurses STRUCTURALLY on the IR and never read the bound as a fact, and the
-- apex could not discharge `ir-size ir < program-bound` for an `ir` that does
-- not exist yet (that was the false `entry-size`). The premise and the whole
-- telescope are deleted.

------------------------------------------------------------------------
-- THE ENTRY FRAME — CONSTRUCTED (plan 0.65 G3, 2026-08-17).
--
-- It used to be an opaque postulate, with the comment "riscv64 has no
-- correspondence yet, so nothing constrains this frame". That reason is gone,
-- and so is the postulate: a riscv64 `Frame` is a `StackPointer` (an address
-- plus a proof it lies in the stack region) tagged with its depth, with
-- `frame-base = addr` (plan 0.134), so the frame can simply BE the loader's
-- `sp` at depth zero — exactly as on x86-64, and
-- `entry-frame-base` collapses to `refl`.
--
-- OPAQUE means nothing about it is provable, which is why the x86-64 version of
-- this needed a SECOND postulate just to say its base is the loader's `%rsp` —
-- and that second one was unprovable BY CONSTRUCTION. What survives here is the
-- one irreducible loader fact: the `sp` we are handed lies in the stack region.
------------------------------------------------------------------------
postulate
  stack-top-in-stack : InStack RS.stack-top

entry-frame-riscv64 : FrameSemantics.Frame rv64-frame-semantics
entry-frame-riscv64 = stack-addr RS.stack-top stack-top-in-stack , 0

-- the entry state (`FlatFromObs`'s, `Interface.start-at`): outside every frame, nothing in its
-- heap or log, every register the tag filler (D074)
entry-regs : Once.CCC.Machine.SMCore.Registers rv64-frame-semantics
entry-regs = Once.CCC.Machine.SMCore.mkRegs (Once.CCC.Machine.SMCore.SV-Tag 0) (Once.CCC.Machine.SMCore.SV-Tag 0)

entry-alloc : ℕ → Once.CCC.Machine.SMCore.AllocState {rv64-frame-semantics}
entry-alloc slots = Once.CCC.Machine.SMCore.mkAllocState entry-frame-riscv64 [] slots 0 1 (λ _ → 0)

entry-s : Once.CCC.Machine.SMCore.LocState rv64-frame-semantics
entry-s = Once.CCC.Machine.SMCore.mkLocState entry-regs (λ _ _ → nothing) (λ _ → nothing) false [] false false

start-flat : FlatMachine.FlatState {rv64-frame-semantics}
start-flat = FlatMachine.mkFlat {rv64-frame-semantics} entry-s (entry-alloc 0) 0

asR = arch-semantics riscv64

------------------------------------------------------------------------
-- Plan 0.107: THE LOADER AXIOM IS GONE. `riscv64-loader-faithful` stood here,
-- quantified over the TEXT the compiler emitted — the trust point D261's
-- segfaulting prologue hid behind. What replaces it is a THEOREM over the FILE
-- (`file-flat-riscv64` below). The only trust left is `as-faithful`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- THE ENGINE, APPLIED. riscv64's `ConcFlatSim` takes the ten resource bounds
-- as parameters (D087); this is where the apex's own hand them down. Symmetric
-- with x86-64's application, field for field.
------------------------------------------------------------------------
open import Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim o
  rv64-frame-semantics refl refl riscv64-slot-addr-no-wrap
  riscv64-reg-range
  (RBr.AddrNoWrap.ret-no-wrap riscv64-addr-no-wrap)
  (RBr.LitFits.tag-fits riscv64-lit-fits) (RBr.LitFits.lit-fits riscv64-lit-fits)
  (RBr.float-fits o ι) (RBr.LitFits.room-fits riscv64-lit-fits)
  using (module EE; module FlatSimulation)
open EE.RunContext′ using (EntryLike)
open FlatSimulation using ()
open FlatSimulation.CompiledCorrespondence using (CompiledCorr)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o rv64-frame-semantics slot-size refl using (mkRunAt)

open FlatMachine {rv64-frame-semantics} using (mkFlat)
open import Once.CCC.Machine.FlatStoreWF rv64-frame-semantics using (FlatWF; sv-below)
open import Once.CCC.Machine.SMCore using
  (AbstractReg; AbstractTrace; Input1; Output; readReg; SV-Ptr; SV-Lit; module LocState)
open LocState using (regs)

------------------------------------------------------------------------
-- THE ENTRY HEAP VIEW. Nothing is allocated yet: the domain is EMPTY, the
-- frontier is 0 (= the concrete `s2` of `emptyRegFile`), and the address map
-- only has to be slot-linear. The code map IS the compiled program's own scan,
-- which is what makes `entry-corr`'s `code-eq` `refl` on the found case.
------------------------------------------------------------------------
code-map : RVProgram → LabelId → ℕ
code-map prog ℓ = pick (RS.find-label prog (thunk ℓ))
  where pick : Maybe ℕ → ℕ
        pick (just j) = j
        pick nothing  = 0

entry-view : RVProgram → FCr.FlatCorrespondence.HeapView rv64-frame-semantics refl
entry-view cprog = record
  { haddr     = λ hl → slot-to-disp (heap-offset hl)
  ; caddr     = code-map cprog
  ; HDom      = λ _ → ⊥
  ; hfront    = RS.heap-base
  ; haddr-suc = suc-law
  ; haddr-inj = λ ()
  ; dom-below = λ ()
  -- nothing has run, so the lowest `sp` ever reached IS the loader's
  -- `stack-top`, and `[0, stack-top)` is virgin — which `entry-corr.untouched`
  -- discharges from `emptyMemory`. `front-lo`: the stack top is above the heap base (D367).
  ; lo        = RS.stack-top
  ; front-lo  = m≤m+n RS.heap-base RS.stack-span
  -- D367: the heap starts one word up, so no mapped address is 0
  ; front-pos = s≤s z≤n
  ; dom-pos   = λ ()
  }
  where
    suc-law : ∀ (hl : HeapLocation) → slot-to-disp (heap-offset (sucHL hl))
                                    ≡ slot-to-disp (heap-offset hl) + slot-size
    suc-law (heap-loc r o) = +-comm slot-size (o * slot-size)

-- (`main-heap-moded` WAS A POSTULATE here: every IR is heap-moded now,
-- `ShapeTable.heap-moded`, and the run context no longer carries it.)

-- A THEOREM here, where x86-64 needed a postulate before its frame was
-- constructed: the entry frame IS the loader's `sp`, and `frame-base` on
-- riscv64 is the `addr` projection.
entry-frame-base : frame-base rv64-frame-semantics
                     (current-frame (entry-alloc 0)) ≡ RS.stack-top
entry-frame-base = refl

------------------------------------------------------------------------
-- THE ENTRY CORRESPONDENCE, PROVEN. The concrete `initState` (every register 0
-- except `sp`, which the loader set; empty memory; pc 0; running) relates to the
-- flat entry state. Every register equality reduces to `enc-hl (entry heap-loc)
-- ≡ 0`; halt/pc are `refl`; `heap-eq` is vacuous (the entry heap is empty).
------------------------------------------------------------------------
entry-corr : ∀ (prog : AbstractTrace)
           → CompiledCorr (entry-view (compile-trace prog)) prog
                          start-flat RS.initState
entry-corr prog = record
  { dataCorr = record
      { in1-eq = refl ; out-eq = refl
      ; clos-eq = refl
      ; halt-eq = refl
      -- initState's `sp` IS the entry frame's base — TRUE only since the model
      -- fix (plan 0.65 G3): it used to be 0, and no frame is based at 0.
      ; sp-eq = sym entry-frame-base
      ; frontier-eq = refl          -- initState's `s2` IS the heap base, the entry frontier (D367)
      ; dom-fresh = λ ()            -- nothing is mapped yet
      ; dom-written = λ _ ()        -- …and the entry heap is empty
      ; dom-sized = λ _ ()          -- …and no block has a size
      ; heap-eq = λ _ ()
      ; lo-le = ≤-refl              -- initState's `sp` IS `stack-top` (the entry mark)
      ; stack-eq = ≤-reflexive (sym entry-frame-base) , (λ _ _ _ ()) , tt
      }
  ; pc-off = refl
  -- NOTHING IS OWED AT ENTRY (D093): the ghost return stack starts empty.
  ; ret-eq = tt
  ; code-eq = λ ℓ j fl → cong-pick fl
  }
  where cong-pick : ∀ {ℓ j} → RS.find-label (compile-trace prog) (thunk ℓ) ≡ just j
                  → code-map (compile-trace prog) ℓ ≡ j
        cong-pick e rewrite e = refl

-- The ENTRY store-WF: the heap and stack are empty and every
-- register holds the tag filler `SV-Tag 0` (D074).
entry-wf : ∀ (B : ℕ) → FlatWF (mkFlat entry-s (entry-alloc B) 0)
entry-wf B = record
  { wf-regs = reg-below ; wf-heap = λ _ → tt ; wf-stack = λ _ _ → tt ; wf-fresh = λ _ _ → refl }
  where
    reg-below : ∀ (r : AbstractReg) → sv-below 1 (readReg (regs entry-s) r)
    reg-below Input1  = tt
    reg-below Output  = tt


-- the loader's state is a legitimate starting state: first instruction, running,
-- nothing allocated, no block sized, no register holding a pointer, and — plan
-- 0.65 G2 — no unspilled return, since the entry state is not in a call window.
open import Once.Type using (FitsInReg)
entry-like : ∀ (B : ℕ) → EntryLike (mkFlat entry-s (entry-alloc B) 0)
entry-like B = refl , refl , refl , refl , refl
             , (λ _ → refl) , (λ _ _ → refl) , (λ _ → refl)
             , no-ptr
             , refl
             , no-lit
  where
    no-ptr : ∀ (r : AbstractReg) (loc : _) → readReg (regs entry-s) r ≡ SV-Ptr loc → _
    no-ptr Input1  loc ()
    no-ptr Output  loc ()
    -- no register holds a literal either (D397's word range starts)
    no-lit : ∀ (r : AbstractReg) {A} (p : FitsInReg A) v → readReg (regs entry-s) r ≡ SV-Lit p v → _
    no-lit Input1  p v ()
    no-lit Output  p v ()
