-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64 — riscv64's backend-correctness
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
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CanonicalName using (CanonicalName)

open import Data.Nat using (ℕ)

import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBr
import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence as FCr

module Once.Adequacy.ArchCorrectness.RiscV64 (o : CanonicalName) (program-bound : ℕ)
  -- Plan 0.65: the resource bounds, as PARAMETERS threaded from the apex (D087),
  -- symmetric with x86-64. G3 (2026-08-17) is where they finally get CONSUMED:
  -- until the simulation was whole-cloth nothing below had asked for them, and
  -- three of the twelve were all that had been written down.
  (riscv64-heap-room : RBr.HeapRoom o) (riscv64-stack-room : RBr.StackRoom o)
  (riscv64-call-room : RBr.CallRoom o)
  (riscv64-reg-range : RBr.RegRange o)
  (riscv64-scratch-dec-guarded : RBr.ScratchDecGuarded o)
  (riscv64-slot-addr-no-wrap : RBr.SlotAddrNoWrap o)
  (riscv64-addr-no-wrap : RBr.AddrNoWrap o)
  (riscv64-lit-fits : RBr.LitFits o) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([])
open import Data.Bool using (false)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.List using (take)
open import Once.Adequacy.CPU.RiscV64 using (ev-riscv64; arith-env-riscv64; step-budget-riscv64)
open import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 using (val-riscv64)
import Once.Arith.Backend.RiscV64.RunTrace as RTr
open import Once.CCC.Codegen.IRToTrace o using (ir-stack-budget)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (riscv64; arch-semantics)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR)
open import Once.CCC.Target.RiscV64.FrameInstantiation using (rv64-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace-cnt; compile-trace-cnt-agrees; compile-trace; slot-to-disp)
open import Once.CCC.Machine.NoNested using (no-nested-of-all)
open import Once.CCC.Codegen.FrameFreeTrace o using (ir-to-trace-frame-free)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size) renaming (Program to RVProgram)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; heap-offset; sucHL)
open import Once.CCC.Label using (LabelId; thunk)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore using (current-frame)
open import Once.CCC.Codegen.ShapeTable using (HeapModed)
open import Once.CCC.FrameSemantics using (frame-base)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Nat using (zero; suc; _+_; _*_; _≤_; z≤n)
open import Data.Nat.Properties using (+-comm; ≤-refl; ≤-reflexive)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D100: the assembler's precondition (distinct emitted local labels), threaded
-- into this arch's `loader-faithful` axiom.
open import Once.Adequacy.LabelClash using (DistinctLabels)
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO
import Once.CCC.Target.RiscV64.Semantics as RS
open import Once.CCC.Target.RiscV64.Layout using (InStack)
open import Once.Memory.StackSlots using (stack-addr)

-- Plan 0.54 rung D / D087: `program-bound` is a RESOURCE BOUND and so is now a
-- module PARAMETER threaded from the apex.
open IRObsCorrectFlatness {rv64-frame-semantics} program-bound
  using (ir-obs-correct; module MachineRefinesObsF)

------------------------------------------------------------------------
-- THE ENTRY FRAME — CONSTRUCTED (plan 0.65 G3, 2026-08-17).
--
-- It used to be an opaque postulate, with the comment "riscv64 has no
-- correspondence yet, so nothing constrains this frame". That reason is gone,
-- and so is the postulate: a riscv64 `Frame` IS a `StackPointer` (an address
-- plus a proof it lies in the stack region, with `frame-base = addr`), so the
-- frame can simply BE the loader's `sp` — exactly as on x86-64, and
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
entry-frame-riscv64 = stack-addr RS.stack-top stack-top-in-stack

module FFOr = FFO o riscv64 rv64-frame-semantics entry-frame-riscv64 (arch-semantics riscv64) program-bound
asR = arch-semantics riscv64

-- The concrete machine's SigOp trace of a compiled IR (see X86-64 for the full
-- rationale): lower the IR to a concrete riscv64 `Program` (the compiler's real
-- path `compile-trace-cnt ∘ ir-to-trace`) and run the concrete machine on it.
conc-trace : Maybe (IR Unit Unit) → Behavior
conc-trace nothing   _ = []
conc-trace (just ir) =
  ArchSemantics.run-trace asR (proj₂ (compile-trace-cnt o 0 (ir-to-trace ir)))
                          (ArchSemantics.initialState asR)

postulate
  -- (A) TOOLCHAIN TRUST — assembler + loader + printer + decoder round-trip
  -- (GNU `as` class); NOT the CPU, NOT the arith logic.
  -- D100: preconditioned on distinct emitted local labels — see the x86-64
  -- instance for why the unconditioned form was FALSE rather than trusted.
  riscv64-loader-faithful :
    ∀ (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false riscv64 m ≡ C.Built asm →
    DistinctLabels riscv64 m →
    ∀ (n : ℕ) → FFOr.asm-sem asm n ≡ conc-trace (moduleToIR m) n

------------------------------------------------------------------------
-- THE ENGINE, APPLIED. riscv64's `ConcFlatSim` takes the twelve resource bounds
-- as parameters (D087); this is where the apex's own hand them down. Symmetric
-- with x86-64's application, field for field.
------------------------------------------------------------------------
open import Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim o
  rv64-frame-semantics refl riscv64-slot-addr-no-wrap
  riscv64-heap-room riscv64-stack-room riscv64-call-room
  riscv64-reg-range riscv64-scratch-dec-guarded
  (RBr.ret-no-wrap riscv64-addr-no-wrap) (RBr.count-no-wrap riscv64-addr-no-wrap)
  (RBr.lo-fits riscv64-addr-no-wrap)
  (RBr.tag-fits riscv64-lit-fits) (RBr.lit-fits riscv64-lit-fits)
  (RBr.float-fits riscv64-lit-fits)
  using (events-agree; CompiledCorr
        ; FlatInv; EntryLike; Reachable; reach-start
        ; inv-wf; inv-regtag; inv-ev; inv-env; inv-run; mkRunAt)

open FlatMachine {rv64-frame-semantics} using (mkFlat)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {rv64-frame-semantics} using (flat-events)
open import Once.CCC.Machine.FlatStoreWF rv64-frame-semantics using (FlatWF; sv-below)
open import Once.CCC.Machine.FlatRegTagWF rv64-frame-semantics using (FlatRegTag)
open import Once.CCC.Machine.SMCore using
  (AbstractReg; Input1; Input2; Output; Scratch; Count; readReg; regs; SV-Ptr; AtStack)

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

entry-view : RVProgram → FCr.HeapView rv64-frame-semantics refl
entry-view cprog = record
  { haddr     = λ hl → slot-to-disp (heap-offset hl)
  ; caddr     = code-map cprog
  ; HDom      = λ _ → ⊥
  ; hfront    = 0
  ; haddr-suc = suc-law
  ; haddr-inj = λ ()
  ; dom-below = λ ()
  -- nothing has run, so the lowest `sp` ever reached IS the loader's
  -- `stack-top`, and `[0, stack-top)` is virgin — which `entry-corr.untouched`
  -- discharges from `emptyMemory`. `front-lo` is `z≤n`: heap base 0 WLOG.
  ; lo        = RS.stack-top
  ; front-lo  = z≤n
  }
  where
    suc-law : ∀ (hl : HeapLocation) → slot-to-disp (heap-offset (sucHL hl))
                                    ≡ slot-to-disp (heap-offset hl) + slot-size
    suc-law (heap-loc r o) = +-comm slot-size (o * slot-size)

postulate
  -- THE PIPELINE'S ALLOCATION MODE, as at x86-64: the compiler builds with
  -- `C.Heap`, so every `AllocMode` in the IR it produces is `Heap`.
  main-heap-moded : ∀ (ir : IR Unit Unit) → HeapModed ir

-- A THEOREM here, where x86-64 needed a postulate before its frame was
-- constructed: the entry frame IS the loader's `sp`, and `frame-base` on
-- riscv64 is the `addr` projection.
entry-frame-base : frame-base rv64-frame-semantics
                     (current-frame (FFOr.entry-alloc 0)) ≡ RS.stack-top
entry-frame-base = refl

------------------------------------------------------------------------
-- THE ENTRY CORRESPONDENCE, PROVEN. The concrete `initState` (every register 0
-- except `sp`, which the loader set; empty memory; pc 0; running) relates to the
-- flat entry state. Every register equality reduces to `enc-hl (entry heap-loc)
-- ≡ 0`; halt/pc are `refl`; `heap-eq` is vacuous (the entry heap is empty).
------------------------------------------------------------------------
entry-corr : ∀ (ir : IR Unit Unit)
           → CompiledCorr (entry-view (compile-trace (ir-to-trace ir))) (ir-to-trace ir)
                          (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0)
                          (ArchSemantics.initialState asR)
entry-corr ir = record
  { dataCorr = record
      { in1-eq = refl ; in2-eq = refl ; out-eq = refl
      ; scratch-eq = refl ; count-eq = refl ; clos-eq = refl
      ; halt-eq = refl
      -- initState's `sp` IS the entry frame's base — TRUE only since the model
      -- fix (plan 0.65 G3): it used to be 0, and no frame is based at 0.
      ; sp-eq = sym entry-frame-base
      ; frontier-eq = refl          -- emptyRegFile's `s2` ≡ 0 ≡ the entry frontier
      ; dom-fresh = λ ()            -- nothing is mapped yet
      ; dom-written = λ _ ()        -- …and the entry heap is empty
      ; dom-sized = λ _ ()          -- …and no block has a size
      ; heap-eq = λ _ ()
      ; lo-le = ≤-refl              -- initState's `sp` IS `stack-top` (the entry mark)
      ; untouched = λ _ _ _ → refl  -- `emptyMemory`: every address reads `nothing`
      ; stack-eq = ≤-reflexive (sym entry-frame-base) , (λ _ _ _ ()) , tt
      }
  ; pc-off = refl
  -- NOTHING IS OWED AT ENTRY (D093): the ghost return stack starts empty.
  ; ret-eq = tt
  ; code-eq = λ ℓ j fl → cong-pick fl
  }
  where cong-pick : ∀ {ℓ j} → RS.find-label (compile-trace (ir-to-trace ir)) (thunk ℓ) ≡ just j
                  → code-map (compile-trace (ir-to-trace ir)) ℓ ≡ j
        cong-pick e rewrite e = refl

-- The ENTRY store-WF and register-tag WF: the heap and stack are empty and every
-- register holds the tag filler `SV-Tag 0` (D074).
entry-wf : ∀ (B : ℕ) → FlatWF (mkFlat FFOr.entry-s (FFOr.entry-alloc B) 0)
entry-wf B = record
  { wf-regs = reg-below ; wf-heap = λ _ → tt ; wf-stack = λ _ _ → tt ; wf-fresh = λ _ _ → refl }
  where
    reg-below : ∀ (r : AbstractReg) → sv-below 1 (readReg (regs FFOr.entry-s) r)
    reg-below Input1  = tt
    reg-below Input2  = tt
    reg-below Output  = tt
    reg-below Scratch = tt
    reg-below Count   = tt

entry-regtag : ∀ (B : ℕ) → FlatRegTag (mkFlat FFOr.entry-s (FFOr.entry-alloc B) 0)
entry-regtag B = record { scratch-tag = 0 , refl ; count-tag = 0 , refl }

-- the loader's state is a legitimate starting state: first instruction, running,
-- nothing allocated, no block sized, no register holding a pointer, and — plan
-- 0.65 G2 — no unspilled return, since the entry state is not in a call window.
entry-like : ∀ (B : ℕ) → EntryLike (mkFlat FFOr.entry-s (FFOr.entry-alloc B) 0)
entry-like B = refl , refl , refl , refl , refl
             , (λ _ → refl) , (λ _ _ → refl) , (λ _ → refl)
             , no-ptr
             , refl
  where
    no-ptr : ∀ (r : AbstractReg) (loc : _) → readReg (regs FFOr.entry-s) r ≡ SV-Ptr loc → _
    no-ptr Input1  loc ()
    no-ptr Input2  loc ()
    no-ptr Output  loc ()
    no-ptr Scratch loc ()
    no-ptr Count   loc ()

entry-inv : ∀ (ir : IR Unit Unit)
          → FlatInv ev-riscv64 (arith-env-riscv64 (compile-trace (ir-to-trace ir)))
                    (ir-to-trace ir) (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0)
entry-inv ir = record
  { inv-wf      = entry-wf (ir-stack-budget ir)
  ; inv-closure = tt          -- D097: the entry closure register is a TAG filler
  ; inv-regtag  = entry-regtag (ir-stack-budget ir)
  ; inv-ev      = refl        -- the apex runs the REAL extractor
  ; inv-env     = refl        -- …and the REAL arith env
  ; inv-run     = mkRunAt ir refl (main-heap-moded ir)
                    (reach-start (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0)
                                 (entry-like (ir-stack-budget ir)) refl)
  }

-- the flat step-fuel that `traces-agree` guarantees emits the first `n` events
Nof : IR Unit Unit → ℕ → ℕ
Nof ir n = proj₁ (MachineRefinesObsF.traces-agree (FFOr.entry-witness ir (ir-obs-correct ir)) n)

postulate
  -- STEP-BUDGET ADEQUACY / fuel coherence — the honest abstract adequate-fuel
  -- seam (D5), the same one x86-64 carries and the same one `FlatFromObs`
  -- carries on the flat side. `events-agree` supplies an existential concrete
  -- fuel `M` that reproduces the adequate flat prefix (that is the `hyp`
  -- argument); `conc-trace` runs at the DESIGNED budget. Because `M` already
  -- reproduces the first-`n`-event prefix, the only remaining content is that
  -- `step-budget-riscv64 n` itself reaches ≥ n events.
  conc-fuel : ∀ (ir : IR Unit Unit) (n M : ℕ) →
      RTr.run-events val-riscv64 ev-riscv64
        (arith-env-riscv64 (compile-trace (ir-to-trace ir)))
        M (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState asR)
      ≡ flat-events (Nof ir n) (ir-to-trace ir)
          (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0) →
      take n (RTr.run-events val-riscv64 ev-riscv64
                (arith-env-riscv64 (compile-trace (ir-to-trace ir)))
                (step-budget-riscv64 n) (compile-trace (ir-to-trace ir))
                (ArchSemantics.initialState asR))
    ≡ take n (RTr.run-events val-riscv64 ev-riscv64
                (arith-env-riscv64 (compile-trace (ir-to-trace ir)))
                M (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState asR))

conc-flat-sim-just :
  ∀ (ir : IR Unit Unit) (n : ℕ) →
  conc-trace (just ir) n ≡ FFOr.flat-trace-of ir-obs-correct (just ir) n
conc-flat-sim-just ir n
  rewrite compile-trace-cnt-agrees o 0 (ir-to-trace ir)
            (no-nested-of-all (ir-to-trace ir)
              (ir-to-trace-frame-free ir (main-heap-moded ir))) =
  trans (conc-fuel ir n (proj₁ agree) (proj₂ agree)) (cong (take n) (proj₂ agree))
  where
    agree = events-agree (Nof ir n)
              ev-riscv64 (arith-env-riscv64 (compile-trace (ir-to-trace ir)))
              (ir-to-trace ir) (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0)
              (ArchSemantics.initialState asR) (entry-corr ir) (entry-inv ir)

------------------------------------------------------------------------
-- (B) THE SIMULATION — NO LONGER A POSTULATE (plan 0.65 G3).
--
-- WHY THIS IS BEING WRITTEN TOP-DOWN, and why it should have been from the
-- start: G1/G2 were an EXTRACTION, so nothing above the island was ever red and
-- it grew to completion without the apex once asking for it. That is precisely
-- what a whole-cloth postulate here buys, and precisely what it costs — the
-- FIRST thing this deletion turned red was `initState`, which handed `main` a
-- stack pointer of ZERO. A wrong model, invisible for as long as the top did
-- not ask.
------------------------------------------------------------------------
riscv64-conc-flat-sim :
  ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) →
  conc-trace mir n ≡ FFOr.flat-trace-of ir-obs-correct mir n
riscv64-conc-flat-sim nothing   n = refl
riscv64-conc-flat-sim (just ir) n = conc-flat-sim-just ir n

asm-trace-correct-riscv64 : FFOr.AsmTraceCorrect (FFOr.flat-trace-of ir-obs-correct)
asm-trace-correct-riscv64 m asm eq dl n =
  trans (riscv64-loader-faithful m asm eq dl n)
        (riscv64-conc-flat-sim (moduleToIR m) n)

riscv64-correct : ArchCorrect riscv64 (arch-semantics riscv64)
riscv64-correct =
  FFO.flat-from-obs o riscv64 rv64-frame-semantics entry-frame-riscv64 (arch-semantics riscv64)
    program-bound ir-obs-correct asm-trace-correct-riscv64
