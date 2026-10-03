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

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun; tableEnv)
open import Once.Denotation.TraceMonad using (Interp)
module Once.Adequacy.ArchCorrectness.RiscV64 (o : CanonicalName) (tbl : List IRFun)
  -- Plan 0.105: the interpretation the program runs against.
  (ι : Interp)
  -- Plan 0.65: the resource bounds, as PARAMETERS threaded from the apex (D087),
  -- symmetric with x86-64. G3 (2026-08-17) is where they finally get CONSUMED:
  -- until the simulation was whole-cloth nothing below had asked for them, and
  -- three of the twelve were all that had been written down.
  (riscv64-heap-room : RBr.HeapRoom o ι) (riscv64-stack-room : RBr.StackRoom o ι)
  (riscv64-call-room : RBr.CallRoom o ι)
  (riscv64-reg-range : RBr.RegRange o ι)
  (riscv64-scratch-dec-guarded : RBr.ScratchDecGuarded o ι)
  (riscv64-slot-addr-no-wrap : RBr.SlotAddrNoWrap o ι)
  (riscv64-addr-no-wrap : RBr.AddrNoWrap o ι)
  (riscv64-lit-fits : RBr.LitFits o ι) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([])
open import Data.Bool using (false)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.List using (take)
open import Once.Adequacy.CPU.RiscV64 using (call-at-riscv64; ev-riscv64; arith-env-riscv64; step-budget-riscv64)
open import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 using (val-riscv64)
import Once.Arith.Backend.RiscV64.RunTrace as RTr
open import Once.CCC.Codegen.IRToTrace o using (ir-stack-budget)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior; at; silent)
open import Once.Adequacy.CPU using (riscv64; arch-semantics)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Arith.Backend.CallAnswer using (answer-at)
open import Once.Adequacy.SourceTrace using (moduleToIR; moduleTable; rewrite-program; ⟦_⟧IR)
open import Once.Denotation.Program using (irProgram; table; main; LinkedProgram)
open import Once.CCC.Codegen.ProgramImageFacts o using (image-frame-free)
open import Once.Target.Arch using (arch-numerics)
open import Once.CCC.Target.RiscV64.FrameInstantiation using () renaming (rv64-frame-semantics to rv64-frame-semantics-at)
open import Once.CCC.FrameSemantics using (FrameSemantics)

rv64-frame-semantics : FrameSemantics
rv64-frame-semantics = rv64-frame-semantics-at ι
open import Once.CCC.Codegen.IRObsCorrectFlat o tbl using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace)
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-trace-cnt; compile-trace-cnt-agrees; compile-trace; slot-to-disp)
open import Once.CCC.Machine.NoNested using (no-nested-of-all)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size) renaming (Program to RVProgram)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; heap-offset; sucHL)
open import Once.CCC.Label using (LabelId; thunk)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore using (current-frame)
open import Once.CCC.FrameSemantics using (frame-base)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Nat using (zero; suc; _+_; _*_; _≤_; z≤n)
open import Data.Nat.Properties using (+-comm; ≤-refl; ≤-reflexive)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D100: the assembler's precondition (distinct emitted local labels), threaded
-- into this arch's `loader-faithful` axiom.
open import Once.Adequacy.LabelClash using (DistinctLabels; LabelsResolvable)
open import Once.Adequacy.SymbolClash using (SymbolsResolvable)
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO
import Once.CCC.Target.RiscV64.Semantics as RS
open import Once.CCC.Target.RiscV64.Layout using (InStack)
open import Once.Memory.StackSlots using (stack-addr)

-- Plan 0.91 S1 (D213): `program-bound` is GONE. It was introduced by Plan 0.54
-- rung D / D087 as a per-arch RESOURCE BOUND, threaded from the apex so the
-- top-level statement said "for any program bound" — but `ir-obs-correct`
-- recurses STRUCTURALLY on the IR and never read the bound as a fact, and the
-- apex could not discharge `ir-size ir < program-bound` for an `ir` that does
-- not exist yet (that was the false `entry-size`). The premise and the whole
-- telescope are deleted; this `open` takes no bound.
open IRObsCorrectFlatness {rv64-frame-semantics}
  using (ir-obs-correct; module MachineRefinesObsF; module ValueRealized; BlockRuns)

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

module FFOr = FFO o tbl riscv64 rv64-frame-semantics refl entry-frame-riscv64 (arch-semantics riscv64)
asR = arch-semantics riscv64

-- The concrete machine's SigOp trace of a compiled IR (see X86-64 for the full
-- rationale): lower the IR to a concrete riscv64 `Program` (the compiler's real
-- path `compile-trace-cnt ∘ ir-to-trace`) and run the concrete machine on it.
-- D244/D245: the concrete machine runs the PROGRAM IMAGE — `main` and every
-- table entry, as the emitted file contains them.
conc-trace : IR Unit Unit → Behavior
conc-trace ir =
  ArchSemantics.run-trace asR ι (proj₂ (compile-trace-cnt o 0 (FFOr.image ir)))
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
    -- D167: …and it links — every compiler-minted SigOp the text calls has
    -- its arith block emitted. `ld`'s rejection; nothing stated it before.
    LabelsResolvable riscv64 m →
    SymbolsResolvable riscv64 m →
    -- D244: the emitted PROGRAM, at this instance's table.
    ∀ (ir : IR Unit Unit) → moduleToIR m ≡ just ir
    → tbl ≡ table (rewrite-program (irProgram (moduleTable m) ir)) →
    ∀ (n : ℕ) → at (FFOr.asm-sem asm) n
              ≡ at (conc-trace (main (rewrite-program (irProgram (moduleTable m) ir)))) n

------------------------------------------------------------------------
-- THE ENGINE, APPLIED. riscv64's `ConcFlatSim` takes the twelve resource bounds
-- as parameters (D087); this is where the apex's own hand them down. Symmetric
-- with x86-64's application, field for field.
------------------------------------------------------------------------
open import Once.Adequacy.ArchCorrectness.RiscV64.ConcFlatSim o
  rv64-frame-semantics refl refl riscv64-slot-addr-no-wrap
  riscv64-heap-room riscv64-stack-room riscv64-call-room
  riscv64-reg-range riscv64-scratch-dec-guarded
  (RBr.ret-no-wrap riscv64-addr-no-wrap) (RBr.count-no-wrap riscv64-addr-no-wrap)
  (RBr.lo-fits riscv64-addr-no-wrap)
  (RBr.tag-fits riscv64-lit-fits) (RBr.lit-fits riscv64-lit-fits)
  (RBr.float-fits o ι)
  using (events-agree; CompiledCorr
        ; FlatInv; EntryLike; Reachable; reach-start
        ; inv-wf; inv-regtag; inv-ev; inv-env; inv-run; mkRunAt)

open FlatMachine {rv64-frame-semantics} using (mkFlat)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {rv64-frame-semantics} using (flat-events)
open import Once.CCC.Machine.FlatStoreWF rv64-frame-semantics using (FlatWF; sv-below)
open import Once.CCC.Machine.FlatRegTagWF rv64-frame-semantics using (FlatRegTag)
open import Once.CCC.Machine.SMCore using
  (AbstractReg; Input1; Output; Scratch; Count; readReg; regs; SV-Ptr; AtStack)

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

-- (`main-heap-moded` WAS A POSTULATE here: every IR is heap-moded now,
-- `ShapeTable.heap-moded`, and the run context no longer carries it.)

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
           → CompiledCorr (entry-view (compile-trace (FFOr.image ir))) (FFOr.image ir)
                          (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0)
                          (ArchSemantics.initialState asR)
entry-corr ir = record
  { dataCorr = record
      { in1-eq = refl ; out-eq = refl
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
  where cong-pick : ∀ {ℓ j} → RS.find-label (compile-trace (FFOr.image ir)) (thunk ℓ) ≡ just j
                  → code-map (compile-trace (FFOr.image ir)) ℓ ≡ j
        cong-pick e rewrite e = refl

-- The ENTRY store-WF and register-tag WF: the heap and stack are empty and every
-- register holds the tag filler `SV-Tag 0` (D074).
entry-wf : ∀ (B : ℕ) → FlatWF (mkFlat FFOr.entry-s (FFOr.entry-alloc B) 0)
entry-wf B = record
  { wf-regs = reg-below ; wf-heap = λ _ → tt ; wf-stack = λ _ _ → tt ; wf-fresh = λ _ _ → refl }
  where
    reg-below : ∀ (r : AbstractReg) → sv-below 1 (readReg (regs FFOr.entry-s) r)
    reg-below Input1  = tt
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
    no-ptr Output  loc ()
    no-ptr Scratch loc ()
    no-ptr Count   loc ()

entry-inv : ∀ (ir : IR Unit Unit) → LinkedProgram (irProgram tbl ir)
          → FlatInv ev-riscv64 (arith-env-riscv64 (compile-trace (FFOr.image ir)))
                    (FFOr.image ir) (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0)
entry-inv ir lk = record
  { inv-wf      = entry-wf (ir-stack-budget ir)
  ; inv-closure = tt          -- D097: the entry closure register is a TAG filler
  ; inv-regtag  = entry-regtag (ir-stack-budget ir)
  ; inv-ev      = refl        -- the apex runs the REAL extractor
  ; inv-env     = refl        -- …and the REAL arith env
  ; inv-run     = mkRunAt tbl ir refl lk
                    (reach-start (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0)
                                 (entry-like (ir-stack-budget ir)) refl)
  }

-- the flat step-fuel that `traces-agree` guarantees emits the first `n` events
-- D159/D160: `traces-agree` is CHAIN-BOUNDED now — one fuel that emits the
-- whole chain, with `take k` agreeing for every `k` — so there is no
-- per-`n` existential left to project. The fuel is the witness's own
-- `steps`, which is exactly what `flat-trace-of` runs at, so the two sides
-- match definitionally instead of through a chosen `N`.
Nof : FFOr.BlockRunsT → (ir : IR Unit Unit) → LinkedProgram (irProgram tbl ir) → ℕ → ℕ
Nof brs ir lk n =
  ValueRealized.steps
    (MachineRefinesObsF.value-realized (FFOr.entry-witness ir (ir-obs-correct ir (proj₁ lk)) brs n)) + 0

postulate
  -- STEP-BUDGET ADEQUACY / fuel coherence — the honest abstract adequate-fuel
  -- seam (D5), the same one x86-64 carries and the same one `FlatFromObs`
  -- carries on the flat side. `events-agree` supplies an existential concrete
  -- fuel `M` that reproduces the adequate flat prefix (that is the `hyp`
  -- argument); `conc-trace` runs at the DESIGNED budget. Because `M` already
  -- reproduces the first-`n`-event prefix, the only remaining content is that
  -- `step-budget-riscv64 n` itself reaches ≥ n events.
  conc-fuel : ∀ (brs : FFOr.BlockRunsT) (ir : IR Unit Unit) (lk : LinkedProgram (irProgram tbl ir)) (n M : ℕ) →
      RTr.run-events val-riscv64 (answer-at ι call-at-riscv64) ev-riscv64
        (arith-env-riscv64 (compile-trace (FFOr.image ir)))
        [] M (compile-trace (FFOr.image ir)) (ArchSemantics.initialState asR)
      ≡ flat-events (Nof brs ir lk n) (FFOr.image ir)
          (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0) →
      take n (RTr.run-events val-riscv64 (answer-at ι call-at-riscv64) ev-riscv64
                (arith-env-riscv64 (compile-trace (FFOr.image ir)))
                [] (step-budget-riscv64 n) (compile-trace (FFOr.image ir))
                (ArchSemantics.initialState asR))
    ≡ take n (RTr.run-events val-riscv64 (answer-at ι call-at-riscv64) ev-riscv64
                (arith-env-riscv64 (compile-trace (FFOr.image ir)))
                [] M (compile-trace (FFOr.image ir)) (ArchSemantics.initialState asR))

conc-flat-sim-just :
  ∀ (brs : FFOr.BlockRunsT) (ir : IR Unit Unit) (lk : LinkedProgram (irProgram tbl ir)) (n : ℕ) →
  at (conc-trace ir) n ≡ at (FFOr.flat-main ir-obs-correct brs ir lk) n
conc-flat-sim-just brs ir lk n
  rewrite compile-trace-cnt-agrees o 0 (FFOr.image ir)
            (no-nested-of-all (FFOr.image ir)
              (image-frame-free tbl ir)) =
  trans (conc-fuel brs ir lk n (proj₁ agree) (proj₂ agree)) (cong (take n) (proj₂ agree))
  where
    agree = events-agree (Nof brs ir lk n)
              ev-riscv64 (arith-env-riscv64 (compile-trace (FFOr.image ir)))
              (FFOr.image ir) (mkFlat FFOr.entry-s (FFOr.entry-alloc (ir-stack-budget ir)) 0)
              (ArchSemantics.initialState asR) (entry-corr ir) (entry-inv ir lk)

------------------------------------------------------------------------
-- THIS INSTANCE'S THREE FACTS, at its table. `ArchCorrectness` assembles them
-- into the per-program `ArchCorrect` (each program brings its own table).
-- plan 0.91 parallel track: the block-table coherence HYPOTHESIS, named so it
-- can be threaded to `Once.Certified` (each target has its own
-- `FrameSemantics`, so `BlockRuns` differs per arch and one hypothesis cannot
-- serve all three). D244: over the PROGRAM IMAGE.
BlockRunsHyp-riscv64 : Set
BlockRunsHyp-riscv64 = FFOr.BlockRunsT

flat-riscv64 : BlockRunsHyp-riscv64 → (ir : IR Unit Unit) → LinkedProgram (irProgram tbl ir) → Behavior
flat-riscv64 brs = FFOr.flat-main ir-obs-correct brs

ir-flat-correct-riscv64 : ∀ (brs : BlockRunsHyp-riscv64) (ir : IR Unit Unit) (lk : LinkedProgram (irProgram tbl ir)) (n : ℕ)
                     → at (flat-riscv64 brs ir lk) n ≡ at (⟦ just (irProgram tbl ir) ⟧IR (arch-numerics riscv64) ι) n
ir-flat-correct-riscv64 brs = FFOr.ir-flat-correct-main ir-obs-correct brs

asm-sem-riscv64 : String → Behavior
asm-sem-riscv64 = FFOr.asm-sem

-- The seam, ASSEMBLED from (A) ∘ (B): the toolchain axiom, then the simulation.
asm-flat-riscv64 : ∀ (brs : BlockRunsHyp-riscv64) (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false riscv64 m ≡ C.Built asm →
    DistinctLabels riscv64 m → LabelsResolvable riscv64 m → SymbolsResolvable riscv64 m →
    ∀ (ir : IR Unit Unit) (mi : moduleToIR m ≡ just ir)
    → (teq : tbl ≡ table (rewrite-program (irProgram (moduleTable m) ir)))
    → (lk : LinkedProgram (irProgram tbl (main (rewrite-program (irProgram (moduleTable m) ir))))) →
    ∀ (n : ℕ) → at (FFOr.asm-sem asm) n
              ≡ at (flat-riscv64 brs (main (rewrite-program (irProgram (moduleTable m) ir))) lk) n
asm-flat-riscv64 brs m asm eq dl lr sr ir mi teq lk n =
  trans (riscv64-loader-faithful m asm eq dl lr sr ir mi teq n)
        (conc-flat-sim-just brs (main (rewrite-program (irProgram (moduleTable m) ir))) lk n)
