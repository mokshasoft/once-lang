-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32
--
-- x86-32 backend correctness, CONSTRUCTED via the shared `FlatFromObs`.
--
-- PLAN 0.66 X2/X3: `x86-32-conc-flat-sim` — the whole-cloth postulate that used
-- to assume the entire simulation here — is DELETED, and the apex now proves it
-- from the ConcFlatSim assembly, exactly as x86-64 and riscv64 do. Deleting it
-- is what made this arch's model answerable at all: it is what turned `esp ≡ 0`
-- and the `ud2` float lowering into type errors (D107's lesson, D109's find).
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

import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB

module Once.Adequacy.ArchCorrectness.X86-32
  (o : CanonicalName) (program-bound : ℕ)
  (x86-32-heap-room : RB.HeapRoom o) (x86-32-stack-room : RB.StackRoom o)
  (x86-32-call-room : RB.CallRoom o)
  -- PLAN 0.70 PHASE C: the machine is finite. Same class and same threading as
  -- the three rooms (D087) — a fact about the running program that a loader or
  -- the emitter establishes, and a parameter is the hole its proof slots into.
  (x86-32-reg-range : RB.RegRange o)
  (x86-32-scratch-dec-guarded : RB.ScratchDecGuarded o)
  -- …and the four `add` sites' range obligations, bundled: `add` computes
  -- `W.⊕` unconditionally (D054 — wraparound is correct, defined semantics, so
  -- no no-overflow precondition may sit on the instruction), which moves the
  -- range obligation to the consumer. All four are LAYOUT/counter facts, never
  -- claims about user arithmetic.
  (x86-32-addr-no-wrap : RB.AddrNoWrap o)
  -- …and the LITERAL seam (phase D): an emitted immediate fits in a machine
  -- word. Not a linker fact like the rooms — D054 makes an elaborated literal
  -- in range BY CONSTRUCTION; this is the frontend's range, not yet threaded.
  (x86-32-lit-fits : RB.LitFits o) where

open import Data.Nat using (ℕ; _+_; s≤s; z≤n)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.List using ([]; take)
open import Data.Bool using (false)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-loc; mkHeapRef; heap-offset)
open import Once.CCC.Machine.SMCore using (AllocState; current-frame)
open import Once.CCC.FrameSemantics using (frame-base)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Target.X86-32.Syntax using (slot-size)
open import Once.CCC.Target.X86-32.AbstractToX86-32 using (slot-to-disp)
open import Data.Empty using (⊥)
open import Data.Nat using (_*_)
open import Data.Nat.Properties using (+-comm; ≤-refl; ≤-reflexive)
open import Once.Adequacy.CPU.X86-32 using (ev-x86-32; arith-env-x86-32; step-budget-x86-32)
-- `val-x86-32` lives with the arith simulation on this arch (x86-64 re-exports
-- its own from `Adequacy.CPU`).
open import Once.Adequacy.ArchCorrectness.ArithSimX86-32 using (val-x86-32)
import Once.Arith.Backend.X86-32.RunTrace as RTx
import Once.CCC.Target.X86-32.Semantics as X
import Once.CCC.Target.X86-32.Syntax as XS
open import Once.CCC.Label using (LabelId; thunk)
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (x86-32; arch-semantics)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR)
open import Once.CCC.Target.X86-32.Layout using (InStack; stack-addr)
open import Once.CCC.Target.X86-32.FrameInstantiation using (X86-32Frame)
open import Once.CCC.Target.X86-32.FrameInstantiation using (x86-32-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-stack-budget)
open import Once.CCC.Codegen.ShapeTable using (HeapModed)
open import Once.CCC.Target.X86-32.AbstractToX86-32
  using (compile-trace; compile-trace-cnt; compile-trace-cnt-agrees; no-nested-of-all)
open import Once.CCC.Codegen.FrameFreeTrace o using (ir-to-trace-frame-free)
open import Data.Empty using (⊥)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D100: the assembler's precondition (distinct emitted local labels), threaded
-- into this arch's `loader-faithful` axiom.
open import Once.Adequacy.LabelClash using (DistinctLabels)
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

-- Plan 0.54 rung D / D087: `program-bound` is a RESOURCE BOUND, so it is a
-- PARAMETER. It used to be postulated once per arch (three copies);
-- threading it from the top means the top-level statement says
-- "for any program bound" explicitly instead of assuming one into existence.
-- (`--safe` rejects every postulate, so this is on the critical path too.)
open IRObsCorrectFlatness {x86-32-frame-semantics} program-bound using (ir-obs-correct; MachineRefinesObsF)

-- The FlatFromObs bundle at the x86-32 params (concrete machine now VISIBLE).
------------------------------------------------------------------------
-- THE ENTRY FRAME, CONSTRUCTED (Plan 0.54 rung D).
--
-- `FlatFromObs` used to postulate this as an opaque `Frame FS`. Opaque means
-- nothing about it is provable — which is why the apex needed a SECOND
-- postulate, `entry-frame-base`, just to say that its base is the `%esp` the
-- loader hands `main`. Two postulates to express one fact, and the second one
-- unprovable BY CONSTRUCTION.
--
-- An x86-32 `Frame` is a `StackAddr`: an address plus a proof it lies in the
-- stack region, with `frame-base = addr`. So the frame can simply BE the
-- loader's `%esp`, and `entry-frame-base` collapses to `refl` (see
-- `entry-frame-base` below — a theorem now).
--
-- What survives is the one irreducible loader fact: that the `%esp` we are
-- handed is inside the stack region. `stack-top` itself is already postulated
-- next door in `…X86-32.Semantics` as "the %esp the loader hands main"; this
-- says where it lives. It is the honest residue of the two it replaces.
------------------------------------------------------------------------
postulate
  stack-top-in-stack : InStack X.stack-top

entry-frame-x86-32 : X86-32Frame
entry-frame-x86-32 = stack-addr X.stack-top stack-top-in-stack

module FFOx = FFO o x86-32 x86-32-frame-semantics entry-frame-x86-32 (arch-semantics x86-32) program-bound

-- A THEOREM: the entry frame IS the loader's `%esp`
-- (`entry-frame-x86-32 = stack-addr stack-top _`) and `frame-base` on x86-32 is
-- the `addr` projection, so this holds DEFINITIONALLY. Both `entry-corr`'s
-- `sp-eq` and the `stack-eq` floor bound consume it.
entry-frame-base : frame-base x86-32-frame-semantics
                     (current-frame (FFOx.entry-alloc 0)) ≡ X.stack-top
entry-frame-base = refl
as32 = arch-semantics x86-32

------------------------------------------------------------------------
-- The seam `asm-trace-correct`, DECOMPOSED (Plan 0.54 rung B step 2).
--
-- The middle term `conc-trace` is the CONCRETE machine's SigOp trace of a
-- compiled IR: lower the IR to a concrete x86-32 `Program` (the compiler's real
-- IR→instruction path `compile-trace ∘ ir-to-trace`) and run the concrete
-- `run-events` machine on it. DEFINED — so the split below is genuine (relates
-- real machines), not two postulates bridged by a third.
------------------------------------------------------------------------

conc-trace : Maybe (IR Unit Unit) → Behavior
conc-trace nothing   _ = []
conc-trace (just ir) =
  -- THE REAL EMITTER: `Once.Target.X86-32` lowers via `compile-trace-cnt`
  -- (which threads the label counter through case/loop), not the plain fold.
  ArchSemantics.run-trace as32 (proj₂ (compile-trace-cnt o 0 (ir-to-trace ir)))
                          (ArchSemantics.initialState as32)

postulate
  -- (A) TOOLCHAIN TRUST — the honest external boundary (GNU `as` class): the
  -- emitted text, assembled+decoded+loaded, traces as the concrete machine
  -- traces the compiled IR's `Program` directly. This is the assembler + loader
  -- + printer + decoder round-trip. It is NOT the CPU semantics and NOT the
  -- arith logic; it is exactly the toolchain boundary every verified compiler
  -- keeps (cf. CompCert's assembler/loader).
  -- D100: PRECONDITIONED on the emitted local labels being distinct. Without
  -- it this axiom is FALSE, not merely trusted: `as` refuses a file that
  -- defines `.L…` twice, so its LHS is the trace of a program that was never
  -- produced. Externally false, and no `⊥`-probe could have found it —
  -- `assemble : String → List Byte` is uninterpreted with no failure mode.
  x86-32-loader-faithful :
    ∀ (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false x86-32 m ≡ C.Built asm →
    DistinctLabels x86-32 m →
    ∀ (n : ℕ) → FFOx.asm-sem asm n ≡ conc-trace (moduleToIR m) n

-- ── (B) THE SIMULATION, WIRED to the ConcFlatSim assembly.
-- The apex node `conc-flat-sim-just` is DEFINED via `events-agree`; every gap it
-- rests on is a NAMED obligation on THIS path (deleting it fails the typecheck).
open FlatMachine {x86-32-frame-semantics} using (mkFlat)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {x86-32-frame-semantics} using (flat-events)

-- THE MEMORY BOUND, now supplied HERE rather than postulated inside the
-- correspondence (2026-08-05). It is the same class as `conc-fuel` below — a
-- statement that a finite resource does not run out — so it belongs with it,
-- and moving it means the correspondence carries NO resource postulate at all.
-- The unapplied imports let the statement be written before `ConcFlatSim` is
-- instantiated (it is one of its arguments).
import Once.Adequacy.ArchCorrectness.X86-32.FlatCorrespondence as FCx
import Once.Adequacy.ArchCorrectness.X86-32.FlatSimulation as FSimx
import Once.Adequacy.ArchCorrectness.X86-32.RunContext as RCx
open import Once.CCC.Machine.SMCore using (AbstractTrace; instr-alloc-heap)
open import Once.CCC.Target.X86-32.Syntax using (slots)
open import Data.Nat using (_≤_)

-- (`x86-32-heap-room` is now a module PARAMETER — see
-- `…X86-32.ResourceBounds.HeapRoom`, D087: resource bounds are parameters.)

open import Once.Adequacy.ArchCorrectness.X86-32.ConcFlatSim o
  x86-32-frame-semantics refl x86-32-heap-room x86-32-stack-room x86-32-call-room
  x86-32-reg-range x86-32-scratch-dec-guarded
  (RB.ret-no-wrap x86-32-addr-no-wrap) (RB.count-no-wrap x86-32-addr-no-wrap)
  (RB.tag-fits x86-32-lit-fits) (RB.lit-fits x86-32-lit-fits) (RB.float-fits o)
  (RB.lo-fits x86-32-addr-no-wrap)
  using (events-agree; CompiledCorr; HeapView
        ; FlatInv; EntryLike; Reachable; reach-start
        ; inv-wf; inv-regtag; inv-ev; inv-env; inv-run; mkRunAt)
open import Once.CCC.Machine.FlatStoreWF x86-32-frame-semantics using (FlatWF; sv-below)
open import Once.CCC.Machine.FlatRegTagWF x86-32-frame-semantics using (FlatRegTag)
open import Once.CCC.Machine.SMCore using (AbstractReg; Input1; Output; Scratch; Count; readReg; regs; SV-Ptr; AtStack)

-- The heap address map is CARRIED by the correspondence and EXTENDED at each
-- `instr-alloc-heap` (the fresh block lands at the concrete `%esi` frontier), so
-- the apex no longer postulates a global `enc-hl` / `LiveIn` / injectivity /
-- successor law / entry-address — it EXHIBITS the entry view and the extension
-- proves the rest. At entry nothing is allocated yet: the domain is EMPTY, the
-- frontier is 0 (= the concrete `%esi` of `emptyRegFile`), and the placeholder
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
  -- the lowest %esp ever reached IS the loader's `stack-top`, and the whole gap
  -- `[0, stack-top)` is virgin — which `entry-corr.untouched` discharges from
  -- `emptyMemory`. `front-lo` is `z≤n`: the heap base is 0 WLOG.
  ; lo        = X.stack-top
  ; front-lo  = z≤n
  }
  where
    suc-law : ∀ (hl : HeapLocation) → slot-to-disp (heap-offset (sucHL hl))
                                    ≡ slot-to-disp (heap-offset hl) + slot-size
    suc-law (heap-loc r o) = +-comm slot-size (o * slot-size)

postulate
  -- THE PIPELINE'S ALLOCATION MODE (Plan 0.62 wiring, 2026-08-02): the
  -- compiler builds with `C.Heap` (`compileFromModule C.Heap C.Build …` —
  -- the apex's own `AsmTraceCorrect` statement fixes it), so every
  -- `AllocMode` argument of the IR it produces is `Heap`. A FRONTEND-CLASS
  -- fact about `moduleToIR`, named here rather than left implicit; the
  -- shape checker needs it because a stack-mode representation lives in
  -- slots that `store-at-slot` overwrites.
  main-heap-moded : ∀ (ir : IR Unit Unit) → HeapModed ir

  -- The entry frame's base IS the %esp the loader hands `main` (`X64.stack-top`,
  -- the one opaque entry-layout constant). A property of the (abstract) entry
  -- frame `FlatFromObs` postulates, tying it to the concrete entry state.
  -- Plan 0.54 rung D: this used to say `≡ 0`, which together with the entry
  -- heap base (also 0) made stack slot `k` and heap cell `(block 0, offset k)`
  -- the SAME address — the layout was degenerate, so every heap/stack
  -- disjointness assumption below it was false.


-- Initial-state correspondence, PROVEN: the concrete `initState` (all registers 0,
-- empty memory, pc 0, running) relates to the flat entry state `mkFlat entry-s
-- entry-alloc 0`. The four register equalities all reduce to `enc-hl (entry heap-
-- loc) ≡ 0` (the `enc-hl-entry` leaf); halt/pc are refl; heap-eq is vacuous
-- (`nothing ≡ nothing`, the entry heap is empty). No longer a postulate.
entry-corr : ∀ (ir : IR Unit Unit)
           → CompiledCorr (entry-view (compile-trace (ir-to-trace ir))) (ir-to-trace ir)
                          (mkFlat FFOx.entry-s (FFOx.entry-alloc (ir-stack-budget ir)) 0)
                          (ArchSemantics.initialState as32)
entry-corr ir = record
  { dataCorr = record
      { in1-eq  = refl
      -- D097: the entry `%ebx` is 0 and the entry `fclosure` is the D074 tag
      -- filler, which encodes to 0 — the same match the other registers make.
      ; clos-eq  = refl
      ; out-eq  = refl
      ; scratch-eq  = refl
      -- emptyRegFile's %edi ≡ 0 ≡ enc-sv (SV-Tag 0), the entry `Count` filler
      ; count-eq  = refl
      ; halt-eq = refl
      ; sp-eq  = sym entry-frame-base   -- initState's %esp IS the entry frame's base
      ; frontier-eq  = refl          -- emptyRegFile's %esi ≡ 0 ≡ the entry frontier
      ; dom-fresh = λ ()        -- nothing is mapped yet
      -- …and nothing needs to be: the entry heap is empty (`dom-written`'s
      -- hypothesis is `nothing ≡ just w`) and no block has a size yet
      -- (`dom-sized`'s is `offset < 0`). Both absurd, both `λ _ ()`.
      ; dom-written = λ _ ()
      ; dom-sized = λ _ ()
      ; heap-eq = λ _ ()
      -- LAYOUT SEPARATION at entry: the heap frontier is 0 and both the mark and
      -- %esp are the loader's `stack-top`, so the heap is (vacuously) below the
      -- stack. This is the base case of the invariant that replaced the
      -- disjointness postulates (`front-lo` = `z≤n` in `entry-view`).
      ; lo-le = ≤-refl          -- initState's %esp IS `stack-top` (the entry mark)
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
      -- floor bound is `entry-frame-base` — the loader's `%esp` IS the entry
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
  where cong-pick : ∀ {ℓ j} → X.find-label (compile-trace (ir-to-trace ir)) (thunk ℓ) ≡ just j
                  → code-map (compile-trace (ir-to-trace ir)) ℓ ≡ j
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

entry-inv : ∀ (ir : IR Unit Unit)
          → FlatInv ev-x86-32 (arith-env-x86-32 (compile-trace (ir-to-trace ir)))
                    (ir-to-trace ir) (mkFlat FFOx.entry-s (FFOx.entry-alloc (ir-stack-budget ir)) 0)
entry-inv ir = record
  { inv-wf      = entry-wf (ir-stack-budget ir)
  -- D097: `mkFlat`'s closure register is the D074 tag filler, and a tag
  -- references no block at all — so the bound is `tt`.
  ; inv-closure = tt
  ; inv-regtag  = entry-regtag (ir-stack-budget ir)
  ; inv-ev      = refl        -- the apex runs the REAL extractor
  ; inv-env     = refl        -- …and the REAL arith env
  -- the program is this IR's emitted trace, and the loader's state starts the run
  -- INSIDE the frame the prologue reserved: `frame-slots ≡ ir-stack-budget ir`,
  -- which is what makes the slot cluster a theorem rather than an assumption.
  ; inv-run     = mkRunAt ir refl (main-heap-moded ir)
                    (reach-start (mkFlat FFOx.entry-s (FFOx.entry-alloc (ir-stack-budget ir)) 0)
                                 (entry-like (ir-stack-budget ir)) refl)
  }

-- The flat adequacy witness for `ir` at event-count `n`: the flat step-fuel that
-- `traces-agree` guarantees emits the first `n` events. `flat-trace-of` and
-- `events-agree` both index the flat trace by exactly this `N`.
Nof : IR Unit Unit → ℕ → ℕ
Nof ir n = proj₁ (MachineRefinesObsF.traces-agree (FFOx.entry-witness ir (ir-obs-correct ir)) n)

postulate
  -- STEP-BUDGET ADEQUACY / fuel coherence — the honest abstract adequate-fuel seam (D5),
  -- the SAME gap `FlatFromObs.flat-trace` / `traces-agree` carry on the flat side.
  --
  -- `events-agree` supplies an existential concrete fuel `M` that REPRODUCES the adequate
  -- flat prefix `flat-events (Nof ir n)` — the flat trace at the adequacy witness for `n`
  -- events (that is the `hyp` argument). `conc-trace` runs at the DESIGNED budget
  -- `step-budget-x86-32 n`. Because `M` already reproduces the first-`n`-event prefix and
  -- `step-budget-x86-32 n` is adequate, their `take n` prefixes agree.
  --
  -- This is TRUE, unlike the earlier `∀ M` form (which was false — at `M ≡ 0`,
  -- `run-events 0 ≡ []`, so it claimed `take n adequate-run ≡ []`). The `hyp` argument
  -- ties `M` to the adequate flat trace, so the only remaining content is that
  -- `step-budget-x86-32 n` itself reaches ≥ n events — the abstract adequacy of the
  -- postulated `ℕ→ℕ` fuel map. Provable core: `run-events` fuel-prefix monotonicity;
  -- residual leaf: `step-budget-x86-32` adequacy (needs `step-budget` pinned, D5).
  conc-fuel : ∀ (ir : IR Unit Unit) (n M : ℕ) →
      RTx.run-events val-x86-32 ev-x86-32 (arith-env-x86-32 (compile-trace (ir-to-trace ir)))
        M (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState as32)
      ≡ flat-events (Nof ir n) (ir-to-trace ir) (mkFlat FFOx.entry-s (FFOx.entry-alloc (ir-stack-budget ir)) 0) →
      take n (RTx.run-events val-x86-32 ev-x86-32 (arith-env-x86-32 (compile-trace (ir-to-trace ir)))
                (step-budget-x86-32 n) (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState as32))
    ≡ take n (RTx.run-events val-x86-32 ev-x86-32 (arith-env-x86-32 (compile-trace (ir-to-trace ir)))
                M (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState as32))

-- `conc-flat-sim-nested` RETIRED (Plan 0.54 item 6, 2026-08-01): with `case`
-- compiled to flat control, EVERY emitted trace is nested-free
-- (`no-nested-of-all` on the frame-free walk), so the two lowerings coincide
-- unconditionally (`compile-trace-cnt-agrees`) and the apex needs no split.
conc-flat-sim-just :
  ∀ (ir : IR Unit Unit) (n : ℕ) →
  conc-trace (just ir) n ≡ FFOx.flat-trace-of ir-obs-correct (just ir) n
conc-flat-sim-just ir n
  rewrite compile-trace-cnt-agrees o 0 (ir-to-trace ir)
            (no-nested-of-all (ir-to-trace ir) (ir-to-trace-frame-free ir (main-heap-moded ir))) =
  trans (conc-fuel ir n (proj₁ agree) (proj₂ agree)) (cong (take n) (proj₂ agree))
  where
    agree = events-agree (Nof ir n)
              ev-x86-32 (arith-env-x86-32 (compile-trace (ir-to-trace ir)))
              (ir-to-trace ir) (mkFlat FFOx.entry-s (FFOx.entry-alloc (ir-stack-budget ir)) 0)
              (ArchSemantics.initialState as32) (entry-corr ir) (entry-inv ir)

-- conc-flat-sim, top-down: `nothing` proven (both traces `[]`); `just` delegates
-- to `conc-flat-sim-just` — the single refinement obligation the recovered cluster
-- fills. Everything hangs off this apex node (no proof islands).
x86-32-conc-flat-sim :
  ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) →
  conc-trace mir n ≡ FFOx.flat-trace-of ir-obs-correct mir n
x86-32-conc-flat-sim nothing   n = refl
x86-32-conc-flat-sim (just ir) n = conc-flat-sim-just ir n

-- The seam, ASSEMBLED from (A) ∘ (B). No longer one opaque postulate: the
-- provable half is named and separated from the honest toolchain axiom.
asm-trace-correct-x86-32 : FFOx.AsmTraceCorrect (FFOx.flat-trace-of ir-obs-correct)
asm-trace-correct-x86-32 m asm eq dl n =
  trans (x86-32-loader-faithful m asm eq dl n)
        (x86-32-conc-flat-sim (moduleToIR m) n)

x86-32-correct : ArchCorrect x86-32 (arch-semantics x86-32)
x86-32-correct =
  FFO.flat-from-obs o x86-32 x86-32-frame-semantics entry-frame-x86-32 (arch-semantics x86-32)
    program-bound ir-obs-correct asm-trace-correct-x86-32
