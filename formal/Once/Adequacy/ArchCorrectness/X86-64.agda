-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64
--
-- x86-64 backend correctness, CONSTRUCTED via the shared `FlatFromObs`.
-- Explicit trust surface: `asm-sem` DEFINED, `assemble-correct` = `refl`,
-- `flat-trace` DEFINED, `ir-flat-correct` PROVED. The one remaining seam
-- `asm-trace-correct` is DECOMPOSED here (Plan 0.54 rung B step 2) into an
-- honest external axiom + a provable simulation — see below.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.X86-64 where

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
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Once.CCC.Target.X86-64.AbstractToX86 using (slot-to-disp)
open import Data.Empty using (⊥)
open import Data.Nat using (_*_)
open import Data.Nat.Properties using (+-comm; ≤-refl)
open import Once.Adequacy.CPU.X86-64 using (ev-x86-64; arith-env-x86-64; step-budget-x86-64; val-x86-64)
import Once.Arith.Backend.X86-64.RunTrace as RTx
import Once.CCC.Target.X86-64.Semantics as X
open import Once.IR using (IR; Unit)  -- Plan 0.52 M2: IRTy Unit
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.CPU using (x86-64; arch-semantics)
open import Once.Adequacy.CPU.Interface using (ArchSemantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Once.Adequacy.SourceTrace using (moduleToIR)
open import Once.CCC.Target.X86-64.FrameInstantiation using (x86-64-frame-semantics)
open import Once.CCC.Codegen.IRObsCorrectFlat using (module IRObsCorrectFlatness)
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace; ir-stack-budget)
open import Once.CCC.Target.X86-64.AbstractToX86
  using (compile-trace; compile-trace-cnt; compile-trace-cnt-agrees; NoNested; NoNested?)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty using (⊥)
import Once.Compile as C
import Once.Parser.Module.Core as P
import Once.Adequacy.ArchCorrectness.FlatFromObs as FFO

postulate
  program-bound : ℕ

open IRObsCorrectFlatness {x86-64-frame-semantics} program-bound using (ir-obs-correct; MachineRefinesObsF)

-- The FlatFromObs bundle at the x86-64 params (concrete machine now VISIBLE).
module FFOx = FFO x86-64 x86-64-frame-semantics (arch-semantics x86-64) program-bound
as64 = arch-semantics x86-64

------------------------------------------------------------------------
-- The seam `asm-trace-correct`, DECOMPOSED (Plan 0.54 rung B step 2).
--
-- The middle term `conc-trace` is the CONCRETE machine's SigOp trace of a
-- compiled IR: lower the IR to a concrete x86-64 `Program` (the compiler's real
-- IR→instruction path `compile-trace ∘ ir-to-trace`) and run the concrete
-- `run-events` machine on it. DEFINED — so the split below is genuine (relates
-- real machines), not two postulates bridged by a third.
------------------------------------------------------------------------

conc-trace : Maybe (IR Unit Unit) → Behavior
conc-trace nothing   _ = []
conc-trace (just ir) =
  -- THE REAL EMITTER: `Once.Target.X86-64` lowers via `compile-trace-cnt`
  -- (which threads the label counter through case/loop), not the plain fold.
  ArchSemantics.run-trace as64 (proj₂ (compile-trace-cnt 0 (ir-to-trace ir)))
                          (ArchSemantics.initialState as64)

postulate
  -- (A) TOOLCHAIN TRUST — the honest external boundary (GNU `as` class): the
  -- emitted text, assembled+decoded+loaded, traces as the concrete machine
  -- traces the compiled IR's `Program` directly. This is the assembler + loader
  -- + printer + decoder round-trip. It is NOT the CPU semantics and NOT the
  -- arith logic; it is exactly the toolchain boundary every verified compiler
  -- keeps (cf. CompCert's assembler/loader).
  x86-64-loader-faithful :
    ∀ (m : P.Module) (asm : String) →
    C.compileFromModule C.Heap C.Build false x86-64 m ≡ C.Built asm →
    ∀ (n : ℕ) → FFOx.asm-sem asm n ≡ conc-trace (moduleToIR m) n

-- ── (B) THE SIMULATION, now WIRED to the ConcFlatSim assembly (not a postulate).
-- The apex node `conc-flat-sim-just` is DEFINED via `events-agree`; every gap it
-- rests on is a NAMED obligation on THIS path (deleting it fails the typecheck).
open FlatMachine {x86-64-frame-semantics} using (mkFlat)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {x86-64-frame-semantics} using (flat-events)

open import Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim
  x86-64-frame-semantics refl
  using (events-agree; CompiledCorr; HeapView
        ; FlatInv; EntryLike; Reachable; reach-start
        ; inv-wf; inv-regtag; inv-ev; inv-env; inv-run; mkRunAt)
open import Once.CCC.Machine.FlatStoreWF x86-64-frame-semantics using (FlatWF; sv-below)
open import Once.CCC.Machine.FlatRegTagWF x86-64-frame-semantics using (FlatRegTag)
open import Once.CCC.Machine.SMCore using (AbstractReg; Input1; Input2; Output; Scratch; Count; readReg; regs; SV-Ptr; AtStack)

-- The heap address map is CARRIED by the correspondence and EXTENDED at each
-- `instr-alloc-heap` (the fresh block lands at the concrete `%r15` frontier), so
-- the apex no longer postulates a global `enc-hl` / `LiveIn` / injectivity /
-- successor law / entry-address — it EXHIBITS the entry view and the extension
-- proves the rest. At entry nothing is allocated yet: the domain is EMPTY, the
-- frontier is 0 (= the concrete `%r15` of `emptyRegFile`), and the placeholder
-- address map only has to be slot-linear (`haddr-suc`) and put the erased Unit
-- filler cell at 0 — which the x86 entry registers (all 0) match exactly.
entry-view : HeapView
entry-view = record
  { haddr     = λ hl → slot-to-disp (heap-offset hl)
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

postulate
  -- The entry frame's base IS the %rsp the loader hands `main` (`X64.stack-top`,
  -- the one opaque entry-layout constant). A property of the (abstract) entry
  -- frame `FlatFromObs` postulates, tying it to the concrete entry state.
  -- Plan 0.54 rung D: this used to say `≡ 0`, which together with the entry
  -- heap base (also 0) made stack slot `k` and heap cell `(block 0, offset k)`
  -- the SAME address — the layout was degenerate, so every heap/stack
  -- disjointness assumption below it was false.
  entry-frame-base : frame-base x86-64-frame-semantics
                       (current-frame FFOx.entry-alloc) ≡ X.stack-top

-- Initial-state correspondence, PROVEN: the concrete `initState` (all registers 0,
-- empty memory, pc 0, running) relates to the flat entry state `mkFlat entry-s
-- entry-alloc 0`. The four register equalities all reduce to `enc-hl (entry heap-
-- loc) ≡ 0` (the `enc-hl-entry` leaf); halt/pc are refl; heap-eq is vacuous
-- (`nothing ≡ nothing`, the entry heap is empty). No longer a postulate.
entry-corr : ∀ (ir : IR Unit Unit)
           → CompiledCorr entry-view (ir-to-trace ir) (mkFlat (FFOx.entry-s (ir-stack-budget ir)) FFOx.entry-alloc 0)
                          (ArchSemantics.initialState as64)
entry-corr ir = record
  { dataCorr = record
      { rdi-eq  = refl
      ; rsi-eq  = refl
      ; rax-eq  = refl
      ; rbx-eq  = refl
      -- emptyRegFile's %r14 ≡ 0 ≡ enc-sv (SV-Tag 0), the entry `Count` filler
      ; r14-eq  = refl
      ; halt-eq = refl
      ; rsp-eq  = sym entry-frame-base   -- initState's %rsp IS the entry frame's base
      ; r15-eq  = refl          -- emptyRegFile's %r15 ≡ 0 ≡ the entry frontier
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
      -- THE RESERVED FRAME AGREES, and this is now real content rather than a
      -- vacuous bound: the prologue's `slots` cells are UNWRITTEN on both sides —
      -- `emptyMemory` concretely, `λ _ _ → nothing` abstractly.
      ; stack-eq = λ _ _ → refl
      }
  ; pc-off = refl
  }

-- The ENTRY store-WF: at the entry state the heap and stack are empty and every
-- register holds the tag filler `SV-Tag 0` (D074) — `sv-below` puts no
-- constraint on a non-pointer, so every case is `tt`. Everything downstream is
-- the flat-machine theorem (`FlatStoreWF.flat-wf-step`), applied once per step
-- inside `ccc-step-bs` — no per-instruction obligation here.
entry-wf : ∀ (B : ℕ) → FlatWF (mkFlat (FFOx.entry-s B) FFOx.entry-alloc 0)
entry-wf B = record
  { wf-regs = reg-below ; wf-heap = λ _ → tt ; wf-stack = λ _ _ → tt ; wf-fresh = λ _ _ → refl }
  where
    reg-below : ∀ (r : AbstractReg) → sv-below 1 (readReg (regs (FFOx.entry-s B)) r)
    reg-below Input1  = tt
    reg-below Input2  = tt
    reg-below Output  = tt
    reg-below Scratch = tt
    reg-below Count   = tt

-- The ENTRY register-tag WF: `entry-regs` starts both counters at `SV-Tag 0`
-- (`FlatFromObs.entry-regs`), so the invariant that makes the counter
-- instructions correspond to their x86 lowerings holds at entry by
-- construction. Downstream it is the flat-machine theorem
-- (`FlatRegTagWF.flat-regtag-step`), applied once per step inside
-- `ccc-step-bs` alongside the store-WF one.
entry-regtag : ∀ (B : ℕ) → FlatRegTag (mkFlat (FFOx.entry-s B) FFOx.entry-alloc 0)
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
-- NB `stackSlot ≡ 0` is GONE from `EntryLike`: the loader hands `main` a frame the
-- prologue already reserved (`ir-stack-budget`), which is exactly what makes the
-- slot residuals dischargeable instead of false. See the note in `FlatFromObs`.
entry-like : ∀ (B : ℕ) → EntryLike (mkFlat (FFOx.entry-s B) FFOx.entry-alloc 0)
entry-like B = refl , refl , refl , refl
             , (λ _ → refl) , (λ _ _ → refl) , (λ _ → refl)
             -- no register holds ANY pointer: every entry register is the
             -- tag filler `SV-Tag 0` (D074)
             , no-ptr
  where no-ptr : ∀ (r : AbstractReg) loc
               → readReg (regs (FFOx.entry-s B)) r ≡ SV-Ptr loc → ⊥
        no-ptr Input1  loc ()
        no-ptr Input2  loc ()
        no-ptr Output  loc ()
        no-ptr Scratch loc ()
        no-ptr Count   loc ()

entry-inv : ∀ (ir : IR Unit Unit)
          → FlatInv ev-x86-64 (arith-env-x86-64 (compile-trace (ir-to-trace ir)))
                    (ir-to-trace ir) (mkFlat (FFOx.entry-s (ir-stack-budget ir)) FFOx.entry-alloc 0)
entry-inv ir = record
  { inv-wf      = entry-wf (ir-stack-budget ir)
  ; inv-regtag  = entry-regtag (ir-stack-budget ir)
  ; inv-ev      = refl        -- the apex runs the REAL extractor
  ; inv-env     = refl        -- …and the REAL arith env
  -- the program is this IR's emitted trace, and the loader's state starts the run
  -- INSIDE the frame the prologue reserved: `stackSlot ≡ ir-stack-budget ir`,
  -- which is what makes the slot cluster a theorem rather than an assumption.
  ; inv-run     = mkRunAt ir refl
                    (reach-start (mkFlat (FFOx.entry-s (ir-stack-budget ir)) FFOx.entry-alloc 0)
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
  -- `step-budget-x86-64 n`. Because `M` already reproduces the first-`n`-event prefix and
  -- `step-budget-x86-64 n` is adequate, their `take n` prefixes agree.
  --
  -- This is TRUE, unlike the earlier `∀ M` form (which was false — at `M ≡ 0`,
  -- `run-events 0 ≡ []`, so it claimed `take n adequate-run ≡ []`). The `hyp` argument
  -- ties `M` to the adequate flat trace, so the only remaining content is that
  -- `step-budget-x86-64 n` itself reaches ≥ n events — the abstract adequacy of the
  -- postulated `ℕ→ℕ` fuel map. Provable core: `run-events` fuel-prefix monotonicity;
  -- residual leaf: `step-budget-x86-64` adequacy (needs `step-budget` pinned, D5).
  conc-fuel : ∀ (ir : IR Unit Unit) (n M : ℕ) →
      RTx.run-events val-x86-64 ev-x86-64 (arith-env-x86-64 (compile-trace (ir-to-trace ir)))
        M (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState as64)
      ≡ flat-events (Nof ir n) (ir-to-trace ir) (mkFlat (FFOx.entry-s (ir-stack-budget ir)) FFOx.entry-alloc 0) →
      take n (RTx.run-events val-x86-64 ev-x86-64 (arith-env-x86-64 (compile-trace (ir-to-trace ir)))
                (step-budget-x86-64 n) (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState as64))
    ≡ take n (RTx.run-events val-x86-64 ev-x86-64 (arith-env-x86-64 (compile-trace (ir-to-trace ir)))
                M (compile-trace (ir-to-trace ir)) (ArchSemantics.initialState as64))

postulate
  -- THE NESTED FRAGMENT. `compile-trace-cnt` (what the compiler emits) and the
  -- plain `compile-trace` (what the cluster's fetch/offset layer is stated over)
  -- differ on EXACTLY `instr-case-on-tag` and `instr-loop`, where the fold emits
  -- the `ud2` sentinel and the threaded version emits the real label/branch
  -- lowering. For traces containing them the correspondence is unproven ANYWAY
  -- (they are the two constructors still in `events-running-fetch-rest`), so this
  -- names that one gap instead of leaving the emitter mismatch silent.
  conc-flat-sim-nested :
    ∀ (ir : IR Unit Unit) (n : ℕ) → (NoNested (ir-to-trace ir) → ⊥) →
    conc-trace (just ir) n ≡ FFOx.flat-trace-of ir-obs-correct (just ir) n

conc-flat-sim-just :
  ∀ (ir : IR Unit Unit) (n : ℕ) →
  conc-trace (just ir) n ≡ FFOx.flat-trace-of ir-obs-correct (just ir) n
conc-flat-sim-just ir n = go (NoNested? (ir-to-trace ir))
  where
    agree = events-agree (Nof ir n)
              ev-x86-64 (arith-env-x86-64 (compile-trace (ir-to-trace ir)))
              (ir-to-trace ir) (mkFlat (FFOx.entry-s (ir-stack-budget ir)) FFOx.entry-alloc 0)
              (ArchSemantics.initialState as64) (entry-corr ir) (entry-inv ir)
    -- on the case/loop-FREE fragment the two lowerings coincide, so the
    -- correspondence proved over `compile-trace` IS about the emitted program.
    go : Dec (NoNested (ir-to-trace ir))
       → conc-trace (just ir) n ≡ FFOx.flat-trace-of ir-obs-correct (just ir) n
    go (yes nn) rewrite compile-trace-cnt-agrees 0 (ir-to-trace ir) nn =
      trans (conc-fuel ir n (proj₁ agree) (proj₂ agree)) (cong (take n) (proj₂ agree))
    go (no ¬nn) = conc-flat-sim-nested ir n ¬nn

-- conc-flat-sim, top-down: `nothing` proven (both traces `[]`); `just` delegates
-- to `conc-flat-sim-just` — the single refinement obligation the recovered cluster
-- fills. Everything hangs off this apex node (no proof islands).
x86-64-conc-flat-sim :
  ∀ (mir : Maybe (IR Unit Unit)) (n : ℕ) →
  conc-trace mir n ≡ FFOx.flat-trace-of ir-obs-correct mir n
x86-64-conc-flat-sim nothing   n = refl
x86-64-conc-flat-sim (just ir) n = conc-flat-sim-just ir n

-- The seam, ASSEMBLED from (A) ∘ (B). No longer one opaque postulate: the
-- provable half is named and separated from the honest toolchain axiom.
asm-trace-correct-x86-64 : FFOx.AsmTraceCorrect (FFOx.flat-trace-of ir-obs-correct)
asm-trace-correct-x86-64 m asm eq n =
  trans (x86-64-loader-faithful m asm eq n)
        (x86-64-conc-flat-sim (moduleToIR m) n)

x86-64-correct : ArchCorrect x86-64 (arch-semantics x86-64)
x86-64-correct =
  FFO.flat-from-obs x86-64 x86-64-frame-semantics (arch-semantics x86-64)
    program-bound ir-obs-correct asm-trace-correct-x86-64
