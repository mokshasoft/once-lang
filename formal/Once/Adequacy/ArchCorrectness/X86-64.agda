-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64
--
-- x86-64 backend correctness, CONSTRUCTED via the shared `FlatFromObs`.
-- Explicit trust surface: `asm-sem` DEFINED, `assemble-correct` = `refl`,
-- `flat-trace` DEFINED, `ir-flat-correct` PROVED. The one remaining seam
-- `asm-trace-correct` is DECOMPOSED here (Plan 0.54 rung B step 2) into an
-- honest external axiom + a provable simulation — see below.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

open import Data.Nat using (ℕ)

import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun; tableEnv)
open import Once.Denotation.TraceMonad using (Interp; sig)
module Once.Adequacy.ArchCorrectness.X86-64
  (o : CanonicalName) (tbl : List IRFun)
  -- Plan 0.105: the interpretation the program runs against.
  (ι : Interp)
  (x86-64-heap-room : RB.HeapRoom o ι) (x86-64-stack-room : RB.StackRoom o ι)
  (x86-64-call-room : RB.CallRoom o ι)
  -- PLAN 0.70 PHASE C: the machine is finite. Same class and same threading as
  -- the three rooms (D087) — a fact about the running program that a loader or
  -- the emitter establishes, and a parameter is the hole its proof slots into.
  (x86-64-reg-range : RB.RegRange o ι)
  (x86-64-scratch-dec-guarded : RB.ScratchDecGuarded o ι)
  -- …and the four `add` sites' range obligations, bundled: `add` computes
  -- `W.⊕` unconditionally (D054 — wraparound is correct, defined semantics, so
  -- no no-overflow precondition may sit on the instruction), which moves the
  -- range obligation to the consumer. All four are LAYOUT/counter facts, never
  -- claims about user arithmetic.
  (x86-64-addr-no-wrap : RB.AddrNoWrap o ι)
  -- …and the LITERAL seam (phase D): an emitted immediate fits in a machine
  -- word. Not a linker fact like the rooms — D054 makes an elaborated literal
  -- in range BY CONSTRUCTION; this is the frontend's range, not yet threaded.
  (x86-64-lit-fits : RB.LitFits o ι) where

open import Data.Nat using (ℕ; _+_; s≤s; z≤n; suc)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.List using ([]; take)
open import Data.Bool using (false)
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-loc; mkHeapRef; heap-offset)
open import Once.CCC.Machine.SMCore using (AllocState; current-frame)
open import Once.CCC.FrameSemantics using (frame-base)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Once.CCC.Target.X86-64.AbstractToX86 using (slot-to-disp)
open import Data.Empty using (⊥)
open import Data.Nat using (_*_)
open import Data.Nat.Properties using (+-comm; ≤-refl; ≤-reflexive)
open import Once.Adequacy.CPU.X86-64 using (call-at-x86-64; ev-x86-64; block-env; run-trace-x86-64; step-budget-x86-64; val-x86-64)
import Once.CCC.Target.X86-64.File as RF
import Data.Maybe
open import Data.Sum using (inj₂)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Adequacy.EmitFile using (file-is-emit)
open import Once.CCC.Machine.NoNested using (NoNested; no-nested-of-all)
open import Once.CCC.Codegen.ProgramImage using (program-image)
import Once.Arith.Backend.X86-64.RunTrace as RTx
import Once.CCC.Target.X86-64.Semantics as X
import Once.CCC.Target.X86-64.Syntax as XS
open import Once.CCC.Label using (LabelId; thunk)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior; at; silent)
open import Once.Adequacy.CPU using (arch-semantics)
open import Once.Target.Arch using (x86-64)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Arith.Backend.CallAnswer using (answer-at)
open import Once.Adequacy.SourceTrace using (⟦_⟧IR)
open import Once.Compile using (moduleToIR; moduleTable; rewrite-program)
open import Once.Denotation.Program using (irProgram; table; main; LinkedProgram; IRProgram)
open import Once.CCC.Codegen.ProgramImageFacts o using (image-frame-free)
open import Once.Target.Arch using (arch-numerics)
open import Once.CCC.Target.X86-64.Layout using (InStack; stack-addr)
open import Once.CCC.Target.X86-64.FrameInstantiation using (X86Frame)
open import Once.CCC.Target.X86-64.FrameInstantiation using () renaming (x86-64-frame-semantics to x86-64-frame-semantics-at)
open import Once.CCC.FrameSemantics using (FrameSemantics)

x86-64-frame-semantics : FrameSemantics
x86-64-frame-semantics = x86-64-frame-semantics-at ι
open import Once.CCC.Codegen.IRObsCorrectFlat o tbl using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-stack-budget)
open import Once.CCC.Target.X86-64.AbstractToX86
  using (compile-trace; compile-trace-cnt; compile-trace-cnt-agrees)
open import Data.Empty using (⊥)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D100: the assembler's precondition (distinct emitted local labels), threaded
-- into this arch's `loader-faithful` axiom.
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

-- Plan 0.91 S1 (D213): `program-bound` is GONE. It was introduced by Plan 0.54
-- rung D / D087 as a per-arch RESOURCE BOUND, threaded from the apex so the
-- top-level statement said "for any program bound" — but `ir-obs-correct`
-- recurses STRUCTURALLY on the IR and never read the bound as a fact, and the
-- apex could not discharge `ir-size ir < program-bound` for an `ir` that does
-- not exist yet (that was the false `entry-size`). The premise and the whole
-- telescope are deleted; this `open` takes no bound.
open IRObsCorrectFlatness {x86-64-frame-semantics} using (ir-obs-correct; MachineRefinesObsF; ValueRealized; BlockRuns)

-- The FlatFromObs bundle at the x86-64 params (concrete machine now VISIBLE).
------------------------------------------------------------------------
-- THE ENTRY FRAME, CONSTRUCTED (Plan 0.54 rung D).
--
-- `FlatFromObs` used to postulate this as an opaque `Frame FS`. Opaque means
-- nothing about it is provable — which is why the apex needed a SECOND
-- postulate, `entry-frame-base`, just to say that its base is the `%rsp` the
-- loader hands `main`. Two postulates to express one fact, and the second one
-- unprovable BY CONSTRUCTION.
--
-- An x86-64 `Frame` is a `StackAddr`: an address plus a proof it lies in the
-- stack region, with `frame-base = addr`. So the frame can simply BE the
-- loader's `%rsp`, and `entry-frame-base` collapses to `refl` (see
-- `entry-frame-base` below — a theorem now).
--
-- What survives is the one irreducible loader fact: that the `%rsp` we are
-- handed is inside the stack region. `stack-top` itself is already postulated
-- next door in `…X86-64.Semantics` as "the %rsp the loader hands main"; this
-- says where it lives. It is the honest residue of the two it replaces.
------------------------------------------------------------------------
postulate
  stack-top-in-stack : InStack X.stack-top

entry-frame-x86-64 : X86Frame
entry-frame-x86-64 = stack-addr X.stack-top stack-top-in-stack

module FFOx = FFO o tbl x86-64 x86-64-frame-semantics refl entry-frame-x86-64 (arch-semantics x86-64)

-- A THEOREM: the entry frame IS the loader's `%rsp`
-- (`entry-frame-x86-64 = stack-addr stack-top _`) and `frame-base` on x86-64 is
-- the `addr` projection, so this holds DEFINITIONALLY. Both `entry-corr`'s
-- `sp-eq` and the `stack-eq` floor bound consume it.
entry-frame-base : frame-base x86-64-frame-semantics
                     (current-frame (FFOx.entry-alloc 0)) ≡ X.stack-top
entry-frame-base = refl
as64 = arch-semantics x86-64

------------------------------------------------------------------------
-- Plan 0.107: THE LOADER AXIOM IS GONE. `x86-64-loader-faithful` stood here,
-- quantified over the TEXT the compiler emitted — so it trusted every piece of
-- code that built the text (D261's riscv64 prologue hid behind its sibling).
-- What replaces it is a THEOREM over the FILE (`file-flat-x86-64` below): the
-- file is `emit` of the program, its code is the lowering of the image the
-- proofs reason about, and its run is the flat run. The only trust left is
-- `as-faithful` (`Once.Adequacy.CPU.X86-64`).
------------------------------------------------------------------------

-- ── (B) THE SIMULATION, WIRED to the ConcFlatSim assembly.
-- The apex node `conc-flat-sim-just` is DEFINED via `events-agree`; every gap it
-- rests on is a NAMED obligation on THIS path (deleting it fails the typecheck).
open FlatMachine {x86-64-frame-semantics} using (mkFlat)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {x86-64-frame-semantics} using (flat-events)

-- THE MEMORY BOUND, now supplied HERE rather than postulated inside the
-- correspondence (2026-08-05). It is the same class as `conc-fuel` below — a
-- statement that a finite resource does not run out — so it belongs with it,
-- and moving it means the correspondence carries NO resource postulate at all.
-- The unapplied imports let the statement be written before `ConcFlatSim` is
-- instantiated (it is one of its arguments).
import Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence as FCx
import Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation as FSimx
import Once.Adequacy.ArchCorrectness.X86-64.RunContext as RCx
open import Once.CCC.Machine.SMCore using (AbstractTrace; instr-alloc-heap)
open import Once.CCC.Target.X86-64.Syntax using (slots)
open import Data.Nat using (_≤_)

-- (`x86-64-heap-room` is now a module PARAMETER — see
-- `…X86-64.ResourceBounds.HeapRoom`, D087: resource bounds are parameters.)

open import Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim o
  x86-64-frame-semantics refl refl x86-64-heap-room x86-64-stack-room x86-64-call-room
  x86-64-reg-range x86-64-scratch-dec-guarded
  (RB.ret-no-wrap x86-64-addr-no-wrap) (RB.count-no-wrap x86-64-addr-no-wrap)
  (RB.tag-fits x86-64-lit-fits) (RB.lit-fits x86-64-lit-fits) (RB.float-fits o ι)
  (RB.lo-fits x86-64-addr-no-wrap)
  using (events-agree; events-agree-start; CompiledCorr; HeapView
        ; FlatInv; EntryLike; Reachable; reach-start; RunAt
        ; inv-wf; inv-regtag; inv-ev; inv-env; inv-run; mkRunAt)
open import Once.CCC.Machine.FlatStoreWF x86-64-frame-semantics using (FlatWF; sv-below)
open import Once.CCC.Machine.FlatRegTagWF x86-64-frame-semantics using (FlatRegTag)
open import Once.CCC.Machine.SMCore using (AbstractReg; Input1; Output; Scratch; Count; readReg; regs; SV-Ptr; AtStack)

-- The heap address map is CARRIED by the correspondence and EXTENDED at each
-- `instr-alloc-heap` (the fresh block lands at the concrete `%r15` frontier), so
-- the apex no longer postulates a global `enc-hl` / `LiveIn` / injectivity /
-- successor law / entry-address — it EXHIBITS the entry view and the extension
-- proves the rest. At entry nothing is allocated yet: the domain is EMPTY, the
-- frontier is 0 (= the concrete `%r15` of `emptyRegFile`), and the placeholder
-- address map only has to be slot-linear (`haddr-suc`) and put the erased Unit
-- filler cell at 0 — which the x86 entry registers (all 0) match exactly.
-- D096: THE CODE MAP. A code address is the label's index in the compiled
-- program, so the entry view is now indexed by the program — and the map is
-- literally the scan the concrete `lea`/`call` perform, which is what makes
-- `entry-corr`'s `code-eq` `refl` on the found case. `0` for an unresolvable
-- label is a filler that no emitted program reaches (`emitted-code-addr-has-body`).
code-map : XS.Program → LabelId → ℕ
code-map prog ℓ = pick (X.find-label prog (thunk ℓ))
  where pick : Maybe ℕ → ℕ
        pick (just j) = j
        pick nothing  = 0

entry-view : XS.Program → HeapView
entry-view cprog = record
  { haddr     = λ hl → slot-to-disp (heap-offset hl)
  ; caddr     = code-map cprog
  ; HDom      = λ _ → ⊥
  ; hfront    = 0
  ; haddr-suc = suc-law
  ; haddr-inj = λ ()
  ; dom-below = λ ()
  -- THE ENTRY HIGH-WATER MARK (plan 0.54 rung D step 3): nothing has run yet, so
  -- the lowest %rsp ever reached IS the loader's `stack-top`, and the whole gap
  -- `[0, stack-top)` is virgin — which `entry-corr.untouched` discharges from
  -- `emptyMemory`. `front-lo` is `z≤n`: the heap base is 0 WLOG.
  ; lo        = X.stack-top
  ; front-lo  = z≤n
  }
  where
    suc-law : ∀ (hl : HeapLocation) → slot-to-disp (heap-offset (sucHL hl))
                                    ≡ slot-to-disp (heap-offset hl) + slot-size
    suc-law (heap-loc r o) = +-comm slot-size (o * slot-size)

-- (`main-heap-moded` WAS A POSTULATE here: every IR is heap-moded now,
-- `ShapeTable.heap-moded`, and the run context no longer carries it.)

-- Initial-state correspondence, PROVEN: the concrete `initState` (all registers 0,
-- empty memory, pc 0, running) relates to the flat entry state `mkFlat entry-s
-- entry-alloc 0`. The four register equalities all reduce to `enc-hl (entry heap-
-- loc) ≡ 0` (the `enc-hl-entry` leaf); halt/pc are refl; heap-eq is vacuous
-- (`nothing ≡ nothing`, the entry heap is empty). No longer a postulate.
entry-corr : ∀ (ir : IR Unit Unit)
           → CompiledCorr (entry-view (compile-trace (FFOx.image ir))) (FFOx.image ir)
                          FFOx.start-flat X.initState
entry-corr ir = record
  { dataCorr = record
      { in1-eq  = refl
      -- D097: the entry `%r12` is 0 and the entry `fclosure` is the D074 tag
      -- filler, which encodes to 0 — the same match the other registers make.
      ; clos-eq  = refl
      ; out-eq  = refl
      ; scratch-eq  = refl
      -- emptyRegFile's %r14 ≡ 0 ≡ enc-sv (SV-Tag 0), the entry `Count` filler
      ; count-eq  = refl
      ; halt-eq = refl
      ; sp-eq  = sym entry-frame-base   -- initState's %rsp IS the entry frame's base
      ; frontier-eq  = refl          -- emptyRegFile's %r15 ≡ 0 ≡ the entry frontier
      ; dom-fresh = λ ()        -- nothing is mapped yet
      -- …and nothing needs to be: the entry heap is empty (`dom-written`'s
      -- hypothesis is `nothing ≡ just w`) and no block has a size yet
      -- (`dom-sized`'s is `offset < 0`). Both absurd, both `λ _ ()`.
      ; dom-written = λ _ ()
      ; dom-sized = λ _ ()
      ; heap-eq = λ _ ()
      -- LAYOUT SEPARATION at entry: the heap frontier is 0 and both the mark and
      -- %rsp are the loader's `stack-top`, so the heap is (vacuously) below the
      -- stack. This is the base case of the invariant that replaced the
      -- disjointness postulates (`front-lo` = `z≤n` in `entry-view`).
      ; lo-le = ≤-refl          -- initState's %rsp IS `stack-top` (the entry mark)
      -- THE VIRGIN REGION at entry: `initState`'s memory is `emptyMemory`, so
      -- every address reads `nothing` — no address arithmetic needed.
      ; untouched = λ _ _ _ → refl
      -- THE RESERVED FRAME AGREES — VACUOUSLY, now that `C.Window` is
      -- one-directional (Plan 0.54 rung D): the entry frame is unwritten
      -- abstractly (`λ _ _ → nothing`), and nothing is claimed about cells the
      -- abstract side has not written. The old bidirectional statement ALSO had
      -- to say the concrete cells were unmapped; that happened to be true here
      -- (`emptyMemory`) but was false at every later frame entry, which is why
      -- it had to go.
      -- Plan 0.63 (D085): the frame LIST at entry is one frame long
      -- (`entry-alloc`'s `saved-frames` is `[]`), so the tail is `tt` and the
      -- floor bound is `entry-frame-base` — the loader's `%rsp` IS the entry
      -- frame's base, so the mark sits exactly at it.
      ; stack-eq = ≤-reflexive (sym entry-frame-base) , (λ _ _ _ ()) , tt
      }
  ; pc-off = refl
  -- NOTHING IS OWED AT ENTRY (D093): `mkFlat` starts the ghost return stack
  -- empty, so the pending-return component is trivially `tt`. Written out
  -- rather than left to eta — a field Agda solves silently is a field nobody
  -- notices going stale.
  ; ret-eq = tt
  -- …and the code map IS the program's own scan, by construction
  ; code-eq = λ ℓ j fl → cong-pick fl
  }
  where cong-pick : ∀ {ℓ j} → X.find-label (compile-trace (FFOx.image ir)) (thunk ℓ) ≡ just j
                  → code-map (compile-trace (FFOx.image ir)) ℓ ≡ j
        cong-pick e rewrite e = refl

-- The ENTRY store-WF: at the entry state the heap and stack are empty and every
-- register holds the tag filler `SV-Tag 0` (D074) — `sv-below` puts no
-- constraint on a non-pointer, so every case is `tt`. Everything downstream is
-- the flat-machine theorem (`FlatStoreWF.flat-wf-step`), applied once per step
-- inside `ccc-step-bs` — no per-instruction obligation here.
entry-wf : ∀ (B : ℕ) → FlatWF (mkFlat FFOx.entry-s (FFOx.entry-alloc B) 0)
entry-wf B = record
  { wf-regs = reg-below ; wf-heap = λ _ → tt ; wf-stack = λ _ _ → tt ; wf-fresh = λ _ _ → refl }
  where
    reg-below : ∀ (r : AbstractReg) → sv-below 1 (readReg (regs FFOx.entry-s) r)
    reg-below Input1  = tt
    reg-below Output  = tt
    reg-below Scratch = tt
    reg-below Count   = tt

-- The ENTRY register-tag WF: `entry-regs` starts both counters at `SV-Tag 0`
-- (`FlatFromObs.entry-regs`), so the invariant that makes the counter
-- instructions correspond to their x86 lowerings holds at entry by
-- construction. Downstream it is the flat-machine theorem
-- (`FlatRegTagWF.flat-regtag-step`), applied once per step inside
-- `ccc-step-bs` alongside the store-WF one.
entry-regtag : ∀ (B : ℕ) → FlatRegTag (mkFlat FFOx.entry-s (FFOx.entry-alloc B) 0)
entry-regtag B = record { scratch-tag = 0 , refl ; count-tag = 0 , refl }

------------------------------------------------------------------------
-- THE RUN CONTEXT AT ENTRY (2026-07-30, the vacuity fix).
--
-- Every state/program residual in ConcFlatSim is now conditioned on "this program
-- is compiler output and this state is one it can reach" — without that they were
-- FALSE (⊥ was derivable from six of them by hand-building a violating state). The
-- apex is where the hypothesis is EXHIBITED, and it costs nothing real: the
-- program IS `ir-to-trace ir`, and the entry state IS a start state.
------------------------------------------------------------------------

-- the loader's state is a legitimate starting state: first instruction, running,
-- nothing allocated on stack or heap, no block sized yet
-- NB `frame-slots ≡ 0` is GONE from `EntryLike`: the loader hands `main` a frame the
-- prologue already reserved (`ir-stack-budget`), which is exactly what makes the
-- slot residuals dischargeable instead of false. See the note in `FlatFromObs`.
entry-like : ∀ (B : ℕ) → EntryLike (mkFlat FFOx.entry-s (FFOx.entry-alloc B) 0)
entry-like B = refl , refl , refl , refl , refl
             , (λ _ → refl) , (λ _ _ → refl) , (λ _ → refl)
             -- no register holds ANY pointer: every entry register is the
             -- tag filler `SV-Tag 0` (D074)
             , no-ptr
             -- the entry state is not inside a call window (plan 0.65 G2)
             , refl
  where no-ptr : ∀ (r : AbstractReg) loc
               → readReg (regs FFOx.entry-s) r ≡ SV-Ptr loc → ⊥
        no-ptr Input1  loc ()
        no-ptr Output  loc ()
        no-ptr Scratch loc ()
        no-ptr Count   loc ()

-- Plan 0.107: THE RUN, FROM THE ENVIRONMENT'S STATE. The program's start (pc 0)
-- is crossed by `events-agree-start` — its block is `block-step-c-start`, so the
-- prologue the old loader axiom absorbed is now a proved step — and the rest is
-- `events-agree`. The flat side is `FlatFromObs`'s run from `start-flat`.
Nof : FFOx.BlockRunsT → (ir : IR Unit Unit) → LinkedProgram (sig ι) (irProgram tbl ir) → ℕ → ℕ
Nof brs ir lk n =
  ValueRealized.steps
    (MachineRefinesObsF.value-realized (FFOx.entry-witness ir (ir-obs-correct ir (proj₁ lk)) brs n)) + 0

-- the concrete run of the program image under a block table, from the
-- environment's state
conc-run : List (String × RF.Payload) → IR Unit Unit → ℕ → List SigOpEvent
conc-run bs ir M =
  RTx.run-events val-x86-64 (answer-at ι call-at-x86-64) ev-x86-64 (block-env bs)
    [] M (compile-trace (FFOx.image ir)) X.initState

-- …and the fuel that run is observed at (D268: the budget reads the run)
conc-budget : List (String × RF.Payload) → IR Unit Unit → ℕ → ℕ
conc-budget bs ir = step-budget-x86-64 bs (compile-trace (FFOx.image ir)) X.initState

postulate
  -- STEP-BUDGET ADEQUACY / fuel coherence — the honest abstract adequate-fuel seam
  -- (D5), the SAME gap `FlatFromObs.flat-trace` / `traces-agree` carry on the
  -- flat side: a fuel `M` that reproduces the adequate flat prefix agrees, on
  -- its first `n` events, with the DESIGNED budget `step-budget-x86-64 n`.
  -- Plan 0.107: over the FILE'S block table (`C.blocks-x86-64 p`), and from
  -- the environment's state with the start ahead of it.
  conc-fuel : ∀ (brs : FFOx.BlockRunsT) (p : IRProgram) (ir : IR Unit Unit)
                (lk : LinkedProgram (sig ι) (irProgram tbl ir)) (n M : ℕ) →
      conc-run (C.blocks-x86-64 p) ir M
      ≡ flat-events (suc (Nof brs ir lk n)) (FFOx.image ir) FFOx.start-flat →
      take n (conc-run (C.blocks-x86-64 p) ir (conc-budget (C.blocks-x86-64 p) ir n))
    ≡ take n (conc-run (C.blocks-x86-64 p) ir M)

-- THE SIMULATION from the environment's state: the concrete run of the image
-- (under the file's block table) is the flat run of the program.
conc-flat-sim :
  ∀ (brs : FFOx.BlockRunsT) (p : IRProgram) (ir : IR Unit Unit)
    (lk : LinkedProgram (sig ι) (irProgram tbl ir))
  → FFOx.image ir ≡ C.image-of p
  → ∀ (n : ℕ) → take n (conc-run (C.blocks-x86-64 p) ir (conc-budget (C.blocks-x86-64 p) ir n))
              ≡ at (FFOx.flat-main ir-obs-correct brs ir lk) n
conc-flat-sim brs p ir lk img n =
  trans (conc-fuel brs p ir lk n (proj₁ agree) (proj₂ agree)) (cong (take n) (proj₂ agree))
  where
    run₀ : RunAt (FFOx.image ir) FFOx.start-flat
    run₀ = mkRunAt tbl ir refl lk (reach-start FFOx.start-flat (entry-like 0) refl)
    agree = events-agree-start (Nof brs ir lk n)
              ev-x86-64 (block-env (C.blocks-x86-64 p))
              (FFOx.image ir) FFOx.start-flat X.initState (ir-stack-budget ir) (entry-corr ir)
              (entry-wf 0) tt (entry-regtag 0) refl (p , img , refl) run₀
              refl refl refl refl

-- THIS INSTANCE'S FACTS, at its table. `ArchCorrectness` assembles them into
-- the per-program `ArchCorrect` (each program brings its own table).
-- plan 0.91 parallel track: the block-table coherence HYPOTHESIS, named so it
-- can be threaded to `Once.Certified` (each target has its own
-- `FrameSemantics`, so `BlockRuns` differs per arch and one hypothesis cannot
-- serve all three). D244: over the PROGRAM IMAGE.
BlockRunsHyp-x86-64 : Set
BlockRunsHyp-x86-64 = FFOx.BlockRunsT

flat-x86-64 : BlockRunsHyp-x86-64 → (ir : IR Unit Unit) → LinkedProgram (sig ι) (irProgram tbl ir) → Behavior
flat-x86-64 brs = FFOx.flat-main ir-obs-correct brs

ir-flat-correct-x86-64 : ∀ (brs : BlockRunsHyp-x86-64) (ir : IR Unit Unit) (lk : LinkedProgram (sig ι) (irProgram tbl ir)) (n : ℕ)
                     → at (flat-x86-64 brs ir lk) n ≡ at (⟦ just (irProgram tbl ir) ⟧IR (arch-numerics x86-64) ι) n
ir-flat-correct-x86-64 brs = FFOx.ir-flat-correct-main ir-obs-correct brs

-- Plan 0.107: RUNNING THE FILE IS THE FLAT RUN OF THE PROGRAM IT WAS EMITTED
-- FROM — a theorem, over the file. The file is `emit` of the module's program
-- (`file-is-emit`); its code is the lowering of the image (one walk, and the
-- counter-threaded lowering agrees with the plain one on a nested-free image);
-- its block table is the one `ArithTable` names; and the run starts at its
-- entry, pc 0, which is the start.
file-flat-x86-64 :
  ∀ (brs : BlockRunsHyp-x86-64) (m : P.Module) (F : RF.Image)
  → C.compileFileFromModule C.Heap false x86-64 m ≡ inj₂ F
  → ∀ (ir : IR Unit Unit) (mi : moduleToIR m ≡ just ir)
  → (oq : o ≡ C.entry-owner)
  → (teq : tbl ≡ table (rewrite-program (irProgram (moduleTable m) ir)))
  → (lk : LinkedProgram (sig ι) (irProgram tbl (main (rewrite-program (irProgram (moduleTable m) ir)))))
  → ∀ (n : ℕ) → at (run-trace-x86-64 ι F (X.initStateAt (Data.Maybe.fromMaybe 0 (RF.entry F)))) n
              ≡ at (flat-x86-64 brs (main (rewrite-program (irProgram (moduleTable m) ir))) lk) n
file-flat-x86-64 brs m F eq ir mi oq teq lk n =
  subst (λ G → at (run-trace-x86-64 ι G (X.initStateAt (Data.Maybe.fromMaybe 0 (RF.entry G)))) n
               ≡ at (flat-x86-64 brs ir′ lk) n)
        (sym (file-is-emit x86-64 m F ir eq mi))
        (trans (cong (λ cd → take n (RTx.run-events val-x86-64 (answer-at ι call-at-x86-64) ev-x86-64
                                       (block-env (C.blocks-x86-64 p)) [] (step-budget-x86-64 (C.blocks-x86-64 p) cd X.initState n) cd X.initState))
                     code-eq)
               (conc-flat-sim brs p ir′ lk img n))
  where
    p   = irProgram (moduleTable m) ir
    ir′ = main (rewrite-program p)
    img : FFOx.image ir′ ≡ C.image-of p
    img = img-at o oq tbl teq
      where img-at : ∀ o′ → o′ ≡ C.entry-owner → ∀ t → t ≡ table (rewrite-program p)
                   → program-image o′ (irProgram t ir′) ≡ C.image-of p
            img-at .C.entry-owner refl .(table (rewrite-program p)) refl = refl
    code-eq : proj₂ (compile-trace-cnt C.entry-owner 0 (C.image-of p)) ≡ compile-trace (FFOx.image ir′)
    code-eq = trans (cong proj₂ (compile-trace-cnt-agrees C.entry-owner 0 (C.image-of p)
                       (subst (λ t → NoNested t) img (no-nested-of-all (FFOx.image ir′) (image-frame-free tbl ir′)))))
                    (cong compile-trace (sym img))
