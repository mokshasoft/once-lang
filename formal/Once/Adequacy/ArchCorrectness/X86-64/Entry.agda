-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.Entry — plan 0.146 step 4 (D462): WHERE
-- AN x86-64 RUN STARTS, for any image.
--
-- The flat machine at the interpretation (`x86-64-frame-semantics`), the
-- entry frame (the loader's `%rsp`), the entry state (`start-flat`, the
-- state `Interface.start-at` is), and its correspondence with the CPU's
-- initial state (`entry-corr`, `entry-wf`, `entry-like`), for any program.
-- Moved here from master's apex (`ArchCorrectness.X86-64`), which went with
-- master's lowering; nothing here names an image.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Name using (CanonicalName)
import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB
open import Once.IR.Semantics.Trace using (Interp)

module Once.Adequacy.ArchCorrectness.X86-64.Entry
  (o : CanonicalName) (ι : Interp)
  (x86-64-reg-range : RB.RegRange o ι)
  (x86-64-addr-no-wrap : RB.AddrNoWrap o ι)
  (x86-64-lit-fits : RB.LitFits o ι) where

open import Data.Nat using (ℕ; _+_; z≤n; s≤s; suc; _*_)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([])
open import Data.Bool using (Bool; false)
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Data.Empty using (⊥)
open import Data.Nat.Properties using (+-comm; ≤-refl; ≤-reflexive; ≤-trans; m≤m+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-loc; module HeapLocation)
open HeapLocation using (heap-offset)
open import Once.CCC.Machine.SMCore using (module AllocState; AllocState; LocState; Registers; mkRegs; mkAllocState; mkLocState; SV-Tag)
open AllocState using (current-frame)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-base)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Once.CCC.Target.X86-64.AbstractToX86 using (slot-to-disp; compile-trace)
import Once.CCC.Target.X86-64.Semantics as X
import Once.CCC.Target.X86-64.Syntax as XS
open import Once.CCC.Label using (LabelId; thunk)
open import Once.CCC.Target.X86-64.Layout using (InStack; stack-addr)
open import Once.CCC.Target.X86-64.FrameInstantiation using (X86Frame)
import Once.CCC.Target.X86-64.FrameInstantiation

x86-64-frame-semantics : FrameSemantics
x86-64-frame-semantics = Once.CCC.Target.X86-64.FrameInstantiation.x86-64-frame-semantics ι

postulate
  stack-top-in-stack : InStack X.stack-top

entry-frame-x86-64 : X86Frame
entry-frame-x86-64 = stack-addr X.stack-top stack-top-in-stack , 0

-- the entry state (`FlatFromObs`'s, `Interface.start-at`): outside every frame, nothing in its
-- heap or log, every register the tag filler (D074)
entry-regs : Registers x86-64-frame-semantics
entry-regs = mkRegs (SV-Tag 0) (SV-Tag 0)

entry-alloc : ℕ → AllocState {x86-64-frame-semantics}
entry-alloc slots = mkAllocState entry-frame-x86-64 [] slots 0 1 (λ _ → 0)

entry-s : LocState x86-64-frame-semantics
entry-s = mkLocState entry-regs (λ _ _ → nothing) (λ _ → nothing) false [] false false

start-flat : FlatMachine.FlatState {x86-64-frame-semantics}
start-flat = FlatMachine.mkFlat {x86-64-frame-semantics} entry-s (entry-alloc 0) 0

entry-frame-base : frame-base x86-64-frame-semantics
                     (current-frame (entry-alloc 0)) ≡ X.stack-top
entry-frame-base = refl
open FlatMachine {x86-64-frame-semantics} using (mkFlat)

-- THE MEMORY BOUND, now supplied HERE rather than postulated inside the
-- correspondence (2026-08-05): a statement that a finite resource does not
-- run out belongs at the apex,
-- and moving it means the correspondence carries NO resource postulate at all.
-- The unapplied imports let the statement be written before `ConcFlatSim` is
-- instantiated (it is one of its arguments).
import Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence as FCx
import Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation as FSimx
import Once.Adequacy.ArchCorrectness.X86-64.RunContext as RCx

open import Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim o
  x86-64-frame-semantics refl refl
  x86-64-reg-range
  (RB.AddrNoWrap.ret-no-wrap x86-64-addr-no-wrap)
  (RB.LitFits.tag-fits x86-64-lit-fits) (RB.LitFits.lit-fits x86-64-lit-fits) (RB.float-fits o ι)
  using (CompiledCorr; HeapView; EntryLike)
open import Once.CCC.Machine.FlatStoreWF x86-64-frame-semantics using (FlatWF; sv-below)
open import Once.CCC.Machine.SMCore using (AbstractReg; AbstractTrace; Input1; Output; readReg; SV-Ptr; SV-Lit; module LocState)
open LocState using (regs)

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
  ; hfront    = X.heap-base
  ; haddr-suc = suc-law
  ; haddr-inj = λ ()
  ; dom-below = λ ()
  -- THE ENTRY HIGH-WATER MARK (plan 0.54 rung D step 3): nothing has run yet, so
  -- the lowest %rsp ever reached IS the loader's `stack-top`, and the whole gap
  -- `[0, stack-top)` is virgin — which `entry-corr.untouched` discharges from
  -- `emptyMemory`. `front-lo`: the stack top is above the heap base (D367).
  ; lo        = X.stack-top
  ; front-lo  = m≤m+n X.heap-base X.stack-span
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

-- Initial-state correspondence, PROVEN: the concrete `initState` (all registers 0,
-- empty memory, pc 0, running) relates to the flat entry state `mkFlat entry-s
-- entry-alloc 0`. The four register equalities all reduce to `enc-hl (entry heap-
-- loc) ≡ 0` (the `enc-hl-entry` leaf); halt/pc are refl; heap-eq is vacuous
-- (`nothing ≡ nothing`, the entry heap is empty). No longer a postulate.
entry-corr : ∀ (prog : AbstractTrace)
           → CompiledCorr (entry-view (compile-trace prog)) prog
                          start-flat X.initState
entry-corr prog = record
  { dataCorr = record
      { in1-eq  = refl
      -- D097: the entry `%r12` is 0 and the entry `fclosure` is the D074 tag
      -- filler, which encodes to 0 — the same match the other registers make.
      ; clos-eq  = refl
      ; out-eq  = refl
      ; halt-eq = refl
      ; sp-eq  = sym entry-frame-base   -- initState's %rsp IS the entry frame's base
      ; frontier-eq  = refl          -- initState's %r15 IS the heap base, the entry frontier (D367)
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
      -- disjointness postulates (`front-lo` in `entry-view`).
      ; lo-le = ≤-refl          -- initState's %rsp IS `stack-top` (the entry mark)
      -- THE VIRGIN REGION at entry: `initState`'s memory is `emptyMemory`, so
      -- every address reads `nothing` — no address arithmetic needed.
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
  where cong-pick : ∀ {ℓ j} → X.find-label (compile-trace prog) (thunk ℓ) ≡ just j
                  → code-map (compile-trace prog) ℓ ≡ j
        cong-pick e rewrite e = refl

-- The ENTRY store-WF: at the entry state the heap and stack are empty and every
-- register holds the tag filler `SV-Tag 0` (D074) — `sv-below` puts no
-- constraint on a non-pointer, so every case is `tt`. Everything downstream is
-- the flat-machine theorem (`FlatStoreWF.flat-wf-step`), applied once per step
-- inside `ccc-step-bs` — no per-instruction obligation here.
entry-wf : ∀ (B : ℕ) → FlatWF (mkFlat entry-s (entry-alloc B) 0)
entry-wf B = record
  { wf-regs = reg-below ; wf-heap = λ _ → tt ; wf-stack = λ _ _ → tt ; wf-fresh = λ _ _ → refl }
  where
    reg-below : ∀ (r : AbstractReg) → sv-below 1 (readReg (regs entry-s) r)
    reg-below Input1  = tt
    reg-below Output  = tt


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
open import Once.Type using (FitsInReg)
entry-like : ∀ (B : ℕ) → EntryLike (mkFlat entry-s (entry-alloc B) 0)
entry-like B = refl , refl , refl , refl , refl
             , (λ _ → refl) , (λ _ _ → refl) , (λ _ → refl)
             -- no register holds ANY pointer: every entry register is the
             -- tag filler `SV-Tag 0` (D074)
             , no-ptr
             -- the entry state is not inside a call window (plan 0.65 G2)
             , refl
             -- no register holds a literal either (D397's word range starts)
             , no-lit
  where no-ptr : ∀ (r : AbstractReg) loc
               → readReg (regs entry-s) r ≡ SV-Ptr loc → ⊥
        no-ptr Input1  loc ()
        no-ptr Output  loc ()
        no-lit : ∀ (r : AbstractReg) {A} (p : FitsInReg A) v
               → readReg (regs entry-s) r ≡ SV-Lit p v → ⊥
        no-lit Input1  p v ()
        no-lit Output  p v ()
