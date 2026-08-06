-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim  (Plan 0.54 rung D / D4.3)
--
-- Wiring the recovered flat↔x86-64 refinement cluster (FlatSimulation +
-- FlatCorrespondence + FlatComposition + StepLemmas) toward the apex
-- `x86-64-conc-flat-sim`. This module is the ASSEMBLY layer:
--
--   * `ccc-step-bs` — the CCC engine: given a `BlockStep` (one flat step ↔
--     `X.exec` of its compiled x86 block, preserving `CompiledCorr`), mirror it
--     into run-events (block-run-exec) and recurse (events-agree). Each fetched
--     AbstractInstr feeds its PROVEN `block-step-*` lemma directly (moves/reg-ops/
--     label straight through; c-jmp/scratch-dec/load-store-indirect case their
--     witness then feed the proven lemma, WF/liveness bad-cases as named residuals).
--     No `block-step-any` dispatcher / `block-step-rest` catch-all — deleted.
--
-- Parameterised exactly like FlatSimulation (FS + the heap-address encoding),
-- so the concrete instantiation (x86-64-frame-semantics + the heap layout) is
-- supplied once, at the point this feeds `conc-flat-sim`.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; shift-frame; frame-word; frame-base; slot-addr; slot-addr-linear)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-offset; heap-ref; ref-id)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Once.CCC.Label using (once; LabelId)
open import Once.CCC.Target.X86-64.Syntax using
  ( slot-size; slots; Program; Instr; Reg; Operand; reg; imm; mem; base; base+disp; rsp; rbp; rax; rdi; rbx
  ; mov; lea; add; sub; cmp; test; jmp; je; jne; call; call-sym
  ; ret; push; pop; nop; ud2; syscall; label )
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; _∸_; _≡ᵇ_; _⊓_)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; <-transˡ; <-irrefl; m≤m+n; m≤n+m; m∸n≤m
                                      ; ⊓-glb; m⊓n≤m; m⊓n≤n; m+n≤o⇒m≤o∸n; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_)
-- …and the pieces the RESOURCE parameter's type needs. Imported UNAPPLIED, so
-- the module's own `FS`/`word-eq` can be threaded into them by Agda's
-- telescoping (`RC.RunAt o FS word-eq …`) — a parameter's type is elaborated
-- before the body, where the applied `open import … FS word-eq` has not run.
open import Data.Maybe using (just)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; instr-alloc-heap; instr-ctrl; c-thunk)
open import Once.CCC.Machine.Flat using (module FlatMachine)
import Once.CCC.Target.X86-64.Semantics as X
import Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence as FC
import Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation as FSim
import Once.Adequacy.ArchCorrectness.X86-64.RunContext as RC

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim (o : CanonicalName)
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  -- MEMORY EXHAUSTION, as a PARAMETER rather than a postulate (2026-08-05).
  -- The honest runtime bound: at an emitted `instr-alloc-heap n` the bump does
  -- not run the heap up into the stack's high-water mark. Same class as the
  -- apex's `conc-fuel`, and now stated in the same place — which is what lets
  -- the correspondence carry NO resource postulate at all, and what `--safe`
  -- requires (it rejects every postulate outright).
  --
  -- Conditioned on `RunAt` and `CompiledCorr`: without them it is REFUTABLE
  -- (a view with `lo ≡ hfront` kills it), which is the 2026-07-30 vacuity
  -- lesson. That conditioning is why `RunAt` had to move to `RunContext`.
  (heap-room : ∀ {hv : FC.HeapView FS word-eq}
                 (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
                 (s : X.State) (n : ℕ)
             → RC.RunAt o FS word-eq prog fs
             → FSim.CompiledCorr FS word-eq hv prog fs s
             → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
               ≡ just (instr-alloc-heap n)
             -- (record projections INFER the module params from the record's own
             -- type, so these take `hv` directly — unlike `RunAt`/`CompiledCorr`,
             -- which telescope them explicitly)
             → FC.hfront hv + slots n ≤ FC.lo hv)
  -- STACK EXHAUSTION, the exact mirror (2026-08-06). At an emitted `c-thunk`
  -- the body's reservation does not run `%rsp` down into the heap frontier.
  -- Same class, same conditioning, same reason it is a parameter — see
  -- `…X86-64.ResourceBounds.StackRoom`, which is where the statement lives.
  (stack-room : ∀ {hv : FC.HeapView FS word-eq}
                  (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
                  (s : X.State) (m : LabelId) (b : ℕ)
              → RC.RunAt o FS word-eq prog fs
              → FSim.CompiledCorr FS word-eq hv prog fs s
              → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
                ≡ just (instr-ctrl (c-thunk m b))
              → FC.hfront hv + slots b ≤ X.readReg (X.State.regs s) rsp)
  where

open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst; subst₂)

open import Once.CCC.Machine.SMCore
open MemOps {FS} using (writeLoc; writeLocToHeap; writeLoc-halted; readLoc)
open FrameSemantics FS using (Frame)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X

open import Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation FS word-eq public
open import Once.CCC.Machine.FlatStoreWF FS using
  (FlatWF; flat-wf-step; wf-regs; wf-heap; wf-stack; wf-fresh; sv-below; svm-below)
open import Once.CCC.Machine.FlatRegTagWF FS using
  (FlatRegTag; flat-regtag-step; flat-scratch-is-tag; flat-count-is-tag; scratch-tag)
open C using (HeapView; haddr; HDom; hfront; lo) public
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Once.Adequacy.ArchCorrectness.X86-64.FlatComposition FS
  using (x86-len; x86-off; drop-compile; fetch-drop; drop-[]; fetch-block-head
        ; find-label-none-corr; fetch-block-2nd)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace; compile-abstract; slot-to-disp)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-stack-budget)
open import Once.CCC.Machine.FrameFree using (FrameFreeI; FrameFreeT; EmittableI; frame-free-emittable)
open import Data.List.Relation.Unary.All using () renaming (All to AllL; [] to allL-[]; _∷_ to _allL∷_)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.CCC.Machine.FlatStackSlot FS using (flat-same-frames; sf-slots; sf-saved; sf-ret)
open import Once.CCC.Machine.FlatStackPtr FS using
  (StackPtrWF; StackPtrOK; StackPtrOK?; stack-ptr-frame; stack-ptr-live; stack-ptr-suc-live
  ; flat-stack-ptr)
open import Once.CCC.Machine.FlatPtrBounds FS using
  (PtrBoundsWF; PtrB; PtrB?; ptr-bounds-cell; ptr-bounds-suc; flat-ptr-bounds
  ; mkPtrBounds; pb-regs; pb-heap; pb-stack)
open import Once.CCC.Codegen.FrameFreeTrace o using (fetch-frame-free; ir-to-trace-frame-free)
open import Once.CCC.Codegen.AllocMin o using (AllocMinI; fetch-alloc-min)
open import Once.CCC.Codegen.ShapeTable as ST using
  (LabelEnv; Expect; entry-expect; check-shapes; state-at; check-at; at-pc;
   HeapModed; e-in1)
open ST.Sem FS using (Meets; site-load-ptr; site-branch-tag; site-store-ptr; fetch-at-pc; site-slot-written)
open import Once.CCC.Codegen.LabelScope o using (emitted-jump-in-segment; mention-at; mention-of; once-label-of)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.CCC.Codegen.SlotBudget o using
  (emitted-slot-seg; below; pair-below; trace-lookup; seg-at; SegState; mkSeg; cur
  ; seg-action; is-id?; seg-idle?; idle-step; idle-head; idle-tail; seg-at-suc
  ; seg-step; saved)
open import Once.IR using (IR; Unit)
open import Once.CCC.Target.X86-64.Syntax using (slots; r15)

------------------------------------------------------------------------
-- Imports for the run-events event-trace correspondence (block-run-exec + the
-- events-agree induction below).
open import Once.Adequacy.CPU.X86-64 using (val-x86-64; ev-x86-64; arith-env-x86-64)
import Once.Arith.Backend.X86-64.RunTrace as RTx
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Once.SigOp.Info using (SigOpInfo; effect; EffectShape; Pure; Emits; Halts)
open import Once.Type using (fits-int; fits-float)
open import Once.Word using (Carrier)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Arith.Backend.X86-64.Dispatch using (dispatch-arith)
open import Data.Product using (uncurry)

-- NON-HALTING ⇒ NON-CALL: `call-sym` is the ONLY instruction `matchCall` accepts,
-- and `execInstr (call-sym _)` always sets `halted := true`. So any step that
-- leaves the machine running (`halted s₁ ≡ false`) cannot have been a `call-sym`,
-- i.e. `matchCall j ≡ nothing`. (The one absurd case is `call-sym`, ruled out by
-- the halt clash; every other instruction is `matchCall … = nothing` definitionally.)
nonhalt-noncall : ∀ prog s j {s₁} → X.execInstr prog s j ≡ just s₁
                → X.State.halted s₁ ≡ false → RTx.matchCall j ≡ nothing
nonhalt-noncall prog s (call-sym lbl) eq hnh
  with trans (cong X.State.halted (just-injective eq)) hnh
... | ()
nonhalt-noncall prog s (mov _ _)  eq hnh = refl
nonhalt-noncall prog s (lea _ _)  eq hnh = refl
nonhalt-noncall prog s (add _ _)  eq hnh = refl
nonhalt-noncall prog s (sub _ _)  eq hnh = refl
nonhalt-noncall prog s (cmp _ _)  eq hnh = refl
nonhalt-noncall prog s (test _ _) eq hnh = refl
nonhalt-noncall prog s (jmp _)    eq hnh = refl
nonhalt-noncall prog s (je _)     eq hnh = refl
nonhalt-noncall prog s (jne _)    eq hnh = refl
nonhalt-noncall prog s (call _)   eq hnh = refl
nonhalt-noncall prog s ret        eq hnh = refl
nonhalt-noncall prog s (push _)   eq hnh = refl
nonhalt-noncall prog s (pop _)    eq hnh = refl
nonhalt-noncall prog s nop        eq hnh = refl
nonhalt-noncall prog s ud2        eq hnh = refl
nonhalt-noncall prog s syscall    eq hnh = refl
nonhalt-noncall prog s (label _)  eq hnh = refl

private
  t≢f : true ≡ false → ⊥
  t≢f ()
  n≢j : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
  n≢j ()

------------------------------------------------------------------------
-- THE FLAT-MACHINE INVARIANT carried through the event-trace induction.
--
-- Two arch-neutral state invariants of the abstract machine, bundled so the
-- ~19 mutually recursive members below carry ONE hypothesis rather than two:
--
--   * `FlatWF`     — no forward pointers (`Once.CCC.Machine.FlatStoreWF`);
--   * `FlatRegTag` — the counter registers hold tags
--                    (`Once.CCC.Machine.FlatRegTagWF`).
--
-- Both are re-established ONCE per step, inside `ccc-step-bs`, by their own
-- flat-machine theorem — no per-block-step obligation. The apex exhibits the
-- entry witness of each.
------------------------------------------------------------------------
open import Data.List using ([])   -- for `EntryLike`'s empty frame stack

------------------------------------------------------------------------
-- THE RUN CONTEXT (2026-07-30, the vacuity fix).
--
-- Every residual below is a fact about a state the machine can REACH while
-- running a program the COMPILER emitted, with the REAL extractor and arith env.
-- Stated without those hypotheses they are not weak assumptions, they are FALSE:
-- `⊥` was derivable from six of them by hand-building a state that violates them
-- (probe, 2026-07-30). Site-conditioning (`fetch prog (fpc fs) ≡ just i`, the
-- 2026-07-28 pass) pins the INSTRUCTION and leaves the STATE arbitrary, so it did
-- not close the hole.
--
-- `Reachable` is DATA, not a postulated predicate: a postulated one could be
-- uninhabited, which trades inconsistency for conditional vacuity. `reach-start`
-- admits any state a loader could hand `main`; `reach-step` is one flat step.
------------------------------------------------------------------------

-- (The run context — `EntryLike`, `Reachable`, `Emitted`, `RunAt` — now
-- lives in `…X86-64.RunContext`, one layer down, so that the resource bounds
-- can be MODULE PARAMETERS here rather than postulates. See that module.)
open import Once.Adequacy.ArchCorrectness.X86-64.RunContext o FS word-eq public


-- The bundle threaded through `events-agree`: the two proved state invariants
-- PLUS the hypotheses that make the residuals true. `ev`/`env` are pinned because
-- the SigOp contracts speak about them: quantified over an arbitrary `env`,
-- `arith-sigop-contract` asserts `env sym ≡ just pl`, which `env := λ _ → nothing`
-- refutes.
record FlatInv (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
               (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkFlatInv
  field
    inv-wf      : FlatWF fs
    inv-regtag  : FlatRegTag fs
    inv-ev      : ev ≡ ev-x86-64
    inv-env     : env ≡ arith-env-x86-64 (compile-trace prog)
    inv-run     : RunAt prog fs
open FlatInv public

-- THE FRAME OPS HAVE NO PRODUCER (plan 0.54 rung D, item 2). The four abstract
-- frame instructions are not a fragment the correspondence has yet to cover —
-- an EMITTED program cannot contain them at all: the per-arch backend brackets
-- each trace with `subq $budget*8, %rsp` / `addq` itself (`ir-stack-budget`), so
-- `ir-to-trace` never emits `instr-alloc-stack` / `instr-dealloc-stack` /
-- `instr-push-frame` / `instr-pop-frame`; they survive only in the legacy IR-WF
-- layer, which is not on this path.
--
-- Consequently the four dispatch clauses below are UNREACHABLE (`⊥-elim`), and
-- with them go ELEVEN residuals that used to condition them — `alloc-stack-entry`,
-- `alloc-stack-fresh-{abs,x86}`, `stack-room`, `dealloc-stack-{full,restores}`,
-- `frame-room`, `pop-frame-{empty,saved,restores}`, `pop-room`. That is the point
-- of stating it this way rather than proving each: they were facts about matched
-- prologue/epilogue pairs the emitter never produces.
--
-- `FrameFreeI` (`Once.CCC.Machine.FrameFree`) and its emitter induction live
-- below this layer
-- (`Once.CCC.Codegen.FrameFreeTrace`) — this is a fact about `ir-to-trace`, not
-- about the machine. Here it is only APPLIED, at the `Emitted` witness the run
-- context already carries.
-- Plan 0.63 step 2b: also needs HEAP MODE, because `lea-slot` joined the ⊥
-- set — it is emitted, but only by the four Stack-mode clauses. `RunAt`
-- carries `run-heap`, so every call site already has the evidence.
-- Plan 0.63 (the flip): this now yields the EMITTER FENCE (`EmittableI`), not
-- semantic frame-freeness — an emitted trace really does contain the two
-- closure markers, and they really do move the frame. The fossils are
-- unchanged, so every ⊥-route below still closes; what changed is that the
-- markers now need REAL clauses instead of `⊥-elim`.
frame-op-absurd : ∀ prog (fs : FlatState) (i : AbstractInstr) (em : Emitted prog)
                → HeapModed (proj₁ em)
                → fetch prog (fpc fs) ≡ just i → EmittableI i
frame-op-absurd .(ir-to-trace ir) fs i (ir , refl) hm ftq = fetch-frame-free {FS} ir hm ftq

flat-inv-step : ∀ {ev env} (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
              → fetch prog (fpc fs) ≡ just i → halted (floc fs) ≡ false
              → FlatInv ev env prog fs → FlatInv ev env prog (flat-exec-instr i prog fs)
flat-inv-step i prog fs ftq h inv = record
  { inv-wf      = flat-wf-step i prog fs (inv-wf inv)
  ; inv-regtag  = flat-regtag-step i prog fs (inv-regtag inv)
  ; inv-ev      = inv-ev inv
  ; inv-env     = inv-env inv
  ; inv-run     = mkRunAt (run-ir (inv-run inv)) (run-emit (inv-run inv))
                          (run-heap (inv-run inv))
                          (reach-step i fs (run-reach (inv-run inv)) ftq h)
  }

-- THE SLOT AN INSTRUCTION ADDRESSES, if any. Enumerated (no catch-all, so it
-- reduces at the use sites). This is what ties a slot-liveness assumption to
-- the instruction actually fetched: a residual stated for an *arbitrary* slot
-- at a site is not a weaker assumption, it is an inconsistent one.
------------------------------------------------------------------------
-- HEAP/STACK DISJOINTNESS, DERIVED (plan 0.54 rung D).
--
-- The two regions grow towards each other, and `FlatCorr.sep` carries the one
-- fact that says so: the heap frontier is at or below `%rsp`. A LIVE heap cell
-- is strictly below the frontier (`HeapView.dom-below`), hence below any address
-- at or above `%rsp` — which is every stack slot the emitted code touches. So
-- the four disjointness residuals are now THEOREMS; what is assumed instead is
-- only that the allocating instructions have room (the `*-room` block below),
-- i.e. that the program does not exhaust memory.
------------------------------------------------------------------------
above-frontier-disj : ∀ {hv : HeapView} (a : ℕ) → hfront hv ≤ a
                    → ∀ hl → HDom hv hl → a ≡ haddr hv hl → ⊥
above-frontier-disj {hv} a le hl live eq = <-irrefl (sym eq) (<-transˡ (C.dom-below hv live) le)

-- a current-frame slot address is at or above %rsp, hence above every live cell
slot-heap-disj : ∀ {hv : HeapView} (fs : FlatState) (s : X.State) → C.FlatCorr hv fs s
               → (k : Slot) → ∀ hl → HDom hv hl
               → (X.readReg (X.State.regs s) rsp + slot-to-disp k ≡ haddr hv hl) → ⊥
slot-heap-disj {hv} fs s corr k =
  above-frontier-disj {hv} (X.readReg (X.State.regs s) rsp + slot-to-disp k)
    (≤-trans (C.sep corr) (m≤m+n (X.readReg (X.State.regs s) rsp) (slot-to-disp k)))

-- (`ptr-heap-disj` — the same fact with the heap stores' argument order —
-- DELETED with Plan 0.63's D085: a heap store no longer takes stack
-- disjointness as a premise, it derives it for EVERY live frame from the frame
-- list's floor (`C.windows-heap-store`).)


-- WITNESS-FREE block chaining: if `X.exec L` reaches a NON-halted `s'`, then every
-- one of the L steps was non-halting (else exec would have stopped at a halted
-- state ≠ s'), hence non-call — so run-events mirrors it, emitting [] and landing
-- on s'. The concrete-side backbone of the per-instruction dispatch, derived purely
-- from `X.exec L ≡ just s'` + `halted s' ≡ false` (no separate call-free witness).
--
-- Key mechanism: in each branch the `with … in` abstraction has ALREADY reduced
-- `X.exec (suc L)` inside `eq`'s type (through `halted s` / fetch / execInstr /
-- `halted s₁`), so `eq` speaks directly about the peeled result — we USE that rather
-- than fight it by re-introducing `X.exec` via lemmas. Every early-stop leaves
-- `eq : just <a halted state> ≡ just s'`, whose `halted = true` clashes with `hs'`
-- (`maybe′ halted`-cong avoids `just-injective`'s eta-expansion of `s'`); the one
-- running step is non-call (nonhalt-noncall) so run-events-noncall advances, then recurse.
block-run-exec : ∀ (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                   L rest cprog s {s'} → X.exec L cprog s ≡ just s' → X.State.halted s' ≡ false
               → RTx.run-events val-x86-64 ev env (L + rest) cprog s
                   ≡ RTx.run-events val-x86-64 ev env rest cprog s'
block-run-exec ev env zero rest cprog s eq hs' =
  cong (λ z → RTx.run-events val-x86-64 ev env rest cprog z) (just-injective eq)
block-run-exec ev env (suc L) rest cprog s {s'} eq hs' with X.State.halted s in hs
... | true  = ⊥-elim (t≢f (trans (sym hs) (trans (cong (maybe′ X.State.halted true) eq) hs')))
... | false with X.fetch cprog (X.State.pc s) in ft
...   | nothing = ⊥-elim (t≢f (trans (cong (maybe′ X.State.halted true) eq) hs'))
...   | just j with X.execInstr cprog s j in exq
...     | nothing = ⊥-elim (n≢j eq)
...     | just s₁ with X.State.halted s₁ in hs1
...       | true  = ⊥-elim (t≢f (trans (sym hs1) (trans (cong (maybe′ X.State.halted true) eq) hs')))
...       | false rewrite nonhalt-noncall cprog s j exq hs1 | exq =
              block-run-exec ev env L rest cprog s₁ eq hs'

------------------------------------------------------------------------
-- (3) events-agree: the fuel induction relating the concrete run-events event
-- trace to the abstract flat-events, threading CompiledCorr. Base + halted are
-- proven here; the running case dispatches each fetched abstract instruction to
-- its brick (block-run-1 / run-events-arith / run-events-external), accumulating
-- events on both sides (events-running, the per-instruction step).
------------------------------------------------------------------------
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {FS} using (flat-events; flat-events-step; flat-events-fetch; event-of; flat-events-halted)
open import Data.List using (List; []; _∷_; _++_; drop)
open import Once.Denotation.Trace using (SigOpEvent)

-- fetch prog k ≡ nothing (k past the trace) ⇒ dropping k blocks leaves []. The
-- abstract-side ingredient for the program-end boundary.
fetch-nothing-drop : ∀ (prog : AbstractTrace) (k : ℕ) → fetch prog k ≡ nothing → drop k prog ≡ []
fetch-nothing-drop []       k       eq = drop-[] k
fetch-nothing-drop (i ∷ is) zero    ()
fetch-nothing-drop (i ∷ is) (suc k) eq = fetch-nothing-drop is k eq

-- fetch prog k ≡ just i ⇒ dropping k blocks exposes i at the head. The abstract-
-- side ingredient for the per-instruction pc-alignment (concrete fetch = the
-- compiled head of the fetched abstract instruction).
fetch-just-drop : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
                → fetch prog k ≡ just i → drop k prog ≡ i ∷ drop (suc k) prog
fetch-just-drop []       k       i ()
fetch-just-drop (x ∷ xs) zero    i eq = cong (_∷ xs) (just-injective eq)
fetch-just-drop (x ∷ xs) (suc k) i eq = fetch-just-drop xs k i eq

-- pc-alignment at a SigOp: the concrete pc = x86-off prog (fpc fs) (pc-off) fetches
-- the compiled head of `instr-sigop si`, which is exactly its one `call-sym`
-- (compile-sigOp = call-sym (once-symbol-path (name si)) ∷ []). Chain: pc-off ▸
-- fetch-drop ▸ drop-compile ▸ fetch-just-drop ▸ (compile-trace cons reduces the head).
sigop-concrete-fetch : ∀ {hv : HeapView} prog fs s {A B} (si : SigOpInfo A B)
                     → CompiledCorr hv prog fs s → fetch prog (fpc fs) ≡ just (instr-sigop si)
                     → X.fetch (compile-trace prog) (X.State.pc s)
                         ≡ just (call-sym (once-symbol-path (SigOpInfo.name si)))
sigop-concrete-fetch prog fs s si cc ftq =
  trans (cong (X.fetch (compile-trace prog)) (pc-off cc))
  (trans (fetch-drop (compile-trace prog) (x86-off prog (fpc fs)))
  (trans (cong (λ z → X.fetch z 0) (drop-compile prog (fpc fs)))
         (cong (λ z → X.fetch (compile-trace z) 0) (fetch-just-drop prog (fpc fs) (instr-sigop si) ftq))))

-- The run-events REDUCTION at an ARITH (Pure) SigOp, PROVEN given the arith-env
-- contract (env maps the symbol to the block pl): the compiled `call-sym` is fetched
-- (sigop-concrete-fetch), matched (matchCall refl), dispatched to the arith block with
-- NO event (run-events-arith). halted s is false via halt-eq. Leaves the concrete
-- state at `dispatch-arith`'s post-state — the value-carrying step, mirroring
-- flat-events' [] for a Pure SigOp.
sigop-run-arith : ∀ {hv : HeapView} ev env n prog fs s {A B} (si : SigOpInfo A B) (pl : List XInstr × ℕ)
                → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
                → fetch prog (fpc fs) ≡ just (instr-sigop si)
                → env (once-symbol-path (SigOpInfo.name si)) ≡ just pl
                → RTx.run-events val-x86-64 ev env (suc n) (compile-trace prog) s
                    ≡ RTx.run-events val-x86-64 ev env n (compile-trace prog)
                        (uncurry (dispatch-arith val-x86-64) pl s)
sigop-run-arith ev env n prog fs s si pl cc h ftq env-eq =
  RTx.run-events-arith val-x86-64 ev env n (compile-trace prog) s
    (call-sym (once-symbol-path (SigOpInfo.name si))) (once-symbol-path (SigOpInfo.name si)) pl
    (trans (C.halt-eq (dataCorr cc)) h)
    (sigop-concrete-fetch prog fs s si cc ftq)
    refl
    env-eq

-- `execInstr` at a memory-compare with a known read (aux helper — a
-- `rewrite` inside the deep tag-branch where-block does not abstract).
execInstr-cmp-mi : ∀ prog (s : X.State) a v
  → X.readMem (X.State.memory s) (X.effectiveAddr s a) ≡ just v
  → X.execInstr prog s (cmp (mem a) (imm 0))
    ≡ just (record s { flags = X.mkflags (v ≡ᵇ 0) (v X.<ᵇ 0) false
                     ; pc = X.State.pc s + 1 })
execInstr-cmp-mi prog s a v rd rewrite rd = refl

-- A Pure SigOp emits no event (ev-of-loc's Pure branch is []).
event-of-pure : ∀ {A B} (si : SigOpInfo A B) fs → effect si ≡ Pure → event-of (instr-sigop si) fs ≡ []
event-of-pure si fs eqe rewrite eqe = refl

-- STORE-GUARD, PROVEN UNCONDITIONALLY (2026-07-31): `writeLoc (AtDynamic hl) v ≡
-- writeLocToHeap hl v` for every StoredValue shape, the stack pointer included.
--
-- It used to hold for four shapes out of five, because `writeLoc` DROPPED a stack
-- pointer written into a heap cell (a silent no-op on lifetime grounds), and the
-- fifth route was ruled out by two residuals — `store-{,suc-}output-not-stackref`,
-- "the emitted code never has a stack pointer in Output at a store site". That was
-- a dataflow claim about codegen, unproved and not even expressible as a property
-- of the trace; and it was needed only to paper over a MODEL DEFECT, since the
-- hardware's `mov [rdi],rax` stores the address and continues. `writeLoc` now
-- writes (SMCore), so both residuals are DELETED rather than discharged.
store-guard : ∀ fs (hl : HeapLocation)
            → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
              ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
store-guard fs hl = go (readReg (regs (floc fs)) Output) refl
  where go : ∀ (v : StoredValue FS) → readReg (regs (floc fs)) Output ≡ v
           → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
             ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
        go (SV-Tag t)             o-eq rewrite o-eq = refl
        go (SV-Lit p v)           o-eq rewrite o-eq = refl
        go (SV-Code c)            o-eq rewrite o-eq = refl
        go (SV-Ptr (AtDynamic w)) o-eq rewrite o-eq = refl
        go (SV-Ptr (AtStack f k)) o-eq rewrite o-eq = refl

-- `slot-empty-stop` DELETED (Plan 0.54 rung D). It read "the abstract slot is
-- empty ⇒ the concrete cell is unmapped ⇒ both machines stop", and that middle
-- step was exactly the direction of `C.Window` that had to go: on frame
-- re-entry the concrete cell holds the previous incarnation's data, so the two
-- machines would NOT stop together — a real divergence the old bidirectional
-- statement concealed.
--
-- The three routes that used it (load-from-slot, restore-input, worklist-pop)
-- are now UNREACHABLE instead: `site-ok` requires a non-`e-any` claim at every
-- slot read, and `MeetsSlot` sends such a claim at `nothing` to `⊥`. See
-- `slot-read-written` below.
-- The run-events REDUCTION at an EXTERNAL (Emits/Halts) SigOp, PROVEN given the
-- external-env contract (env maps the symbol to `nothing`): the compiled `call-sym`
-- is fetched + matched, and run-events-external EMITS `ev lbl s` then continues past
-- the call (ret-past). This is the value-carrying observable emission; the `ev`
-- extractor's value is pinned to `machine-event` by the honest per-target contract.
sigop-run-external : ∀ {hv : HeapView} ev env n prog fs s {A B} (si : SigOpInfo A B)
                   → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (instr-sigop si)
                   → env (once-symbol-path (SigOpInfo.name si)) ≡ nothing
                   → RTx.run-events val-x86-64 ev env (suc n) (compile-trace prog) s
                       ≡ ev (once-symbol-path (SigOpInfo.name si)) s
                         ++ RTx.run-events val-x86-64 ev env n (compile-trace prog) (RTx.ret-past s)
sigop-run-external ev env n prog fs s si cc h ftq env-eq =
  RTx.run-events-external val-x86-64 ev env n (compile-trace prog) s
    (call-sym (once-symbol-path (SigOpInfo.name si))) (once-symbol-path (SigOpInfo.name si))
    (trans (C.halt-eq (dataCorr cc)) h)
    (sigop-concrete-fetch prog fs s si cc ftq)
    refl
    env-eq

-- PROGRAM END (wp-end), PROVEN: the abstract fetch runs out (`fpc` past the trace),
-- so the concrete pc = `x86-off prog (fpc fs)` (pc-off) sits past `compile-trace prog`
-- — fetch there is `nothing`, hence run-events emits []. Chain: pc-off ▸ fetch-drop ▸
-- drop-compile ▸ fetch-nothing-drop (drop past ⇒ [] ⇒ compile-trace [] ⇒ fetch [] = nothing).
events-running-end : ∀ {hv : HeapView} (n : ℕ) (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                       prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ nothing
                   → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s ≡ [])
events-running-end {hv} n ev env prog fs s cc wf h ftq =
  1 , RTx.run-events-fetch-none val-x86-64 ev env 0 (compile-trace prog) s cfetch-nothing
  where cfetch-nothing : X.fetch (compile-trace prog) (X.State.pc s) ≡ nothing
        cfetch-nothing =
          trans (cong (X.fetch (compile-trace prog)) (pc-off cc))
          (trans (fetch-drop (compile-trace prog) (x86-off prog (fpc fs)))
          (trans (cong (λ z → X.fetch z 0) (drop-compile prog (fpc fs)))
                 (cong (λ z → X.fetch (compile-trace z) 0) (fetch-nothing-drop prog (fpc fs) ftq))))

postulate
  -- PER-INSTRUCTION DISPATCH residual for the cases not yet routed to `ccc-step`
  -- (instr-sigop arith/external, control jmp/branch, memory/frame/slot). Shrinks as
  -- each is wired (arith→run-events-arith, external→run-events-external+contract, …).
  -- `events-running-case` RETIRED (Plan 0.54 item 6, 2026-08-01): `case`
  -- compiles to FLAT control, `instr-case-on-tag` has no producer, and the
  -- nested-trace correspondence it demanded is not needed at all — the
  -- dispatch clause is `⊥`-elim like the frame ops.
  -- THE CLOSURE CALL — a MODEL gap: `exec-abstract instr-call-closure = s , alloc`
  -- (identity) while the concrete `call *0x8(%r12)` transfers control to the
  -- closure body. No proof can bridge that; the abstract machine has to model
  -- the call (or codegen has to inline it) first.
  events-running-call : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                          prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                      → fetch prog (fpc fs) ≡ just instr-call-closure
                      → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                            ≡ event-of instr-call-closure fs
                              ++ flat-events n prog (flat-exec-instr instr-call-closure prog fs))

  -- (`events-running-thunk` LIVED HERE. It is now a THEOREM — `thunk-step`
  -- below.)
  --
  -- …and `events-running-ret` is GONE TOO (2026-08-06), but for a different
  -- reason: it is not provable BEFORE the call is modelled, and it is not the
  -- right thing to assume either. What replaces it is this ONE invariant of the
  -- ABSTRACT machine — note the type mentions no `X.State` at all, so by the
  -- ledger's own test it is no longer a correspondence gap:
  --
  --   A REACHABLE RETURN OWES A RETURN. Landing on a `c-ret` means a call put
  --   you inside a closure body, and a call pushes the return pc (D086: the
  --   CALL owns the return-address slot). So `fret` is a cons there.
  --
  -- Composed with the THEOREM `run-no-ret` ("nothing ever owes a return",
  -- because `instr-call-closure`'s abstract semantics is the identity) this
  -- gives `⊥` — which is exactly right, and is the whole content of the model
  -- gap: in today's machine a body is entered by NO ONE, so its return runs in
  -- no reachable state. `ret-step` below is that composition, and it is a
  -- theorem. See D091.
  --
  -- WHY NOT THE `FlatCorr` COMPONENT the old handoff designed (a field relating
  -- the ghost `fret` to the cell at the frame's window end): that field is not
  -- PRESERVED by `c-thunk` in today's machine. `grow-frame` keeps `frame-base +
  -- slots frame-slots` fixed only when the pre-state reservation is 0 — true of
  -- a frame a CALL just entered, false of the caller's frame the marker
  -- currently deepens. Its cell is then the caller's slot 0, which the emitter
  -- writes (`store-at-slot closure-slot`). So the field would have been assumed
  -- false, in the `fresh-x86` mould.
  --
  -- DISCHARGE: model the call (`events-running-call`). Then `instr-call-closure`
  -- pushes `fret`/`saved-frames`, `run-no-ret` STOPS being true (as it must),
  -- and this invariant becomes the honest call/return discipline — provable from
  -- the same push, and the return correspondence becomes provable with it.
  ret-site-owes : ∀ prog (fs : FlatState) (b : ℕ) → RunAt prog fs
                → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
                → Σ ℕ (λ pc' → Σ (List ℕ) (λ rest → fret fs ≡ pc' ∷ rest))

  -- THE BRANCH SCRUTINEE DISCIPLINE (D073, replaces `branch-tag-badptr` +
  -- `branch-tag-bad`): at an emitted `c-branch-tag-zero` site the scrutinee
  -- register holds a live heap pointer to a WRITTEN TAG cell — codegen only
  -- emits the tag branch right after loading a constructed node's pointer.
  -- The old pair asserted a RUN-EVENTS equation for the divergent routes,
  -- which is closable by NO layout choice (D054 literals are arbitrary words,
  -- so a non-pointer's encoding can always collide with a mapped address);
  -- this is the honest dataflow fact instead, in the
  -- `store-indirect-inbounds` mold. Discharge trajectory: a per-site
  -- register-shape invariant (static expectation at each emitted site +
  -- preservation, the FlatStackPtr pattern).
  -- PLAN 0.62's TWO OBLIGATIONS (the dataflow disciplines' discharge now
  -- routes through the typed shape checker; these are the remaining named
  -- milestones — their TYPES are the M2b/M3 specs):
  --
  -- M2b — THE EMITTER SHAPE CHECK: for a heap-moded IR, the typed
  -- expectation checker accepts the emitted trace (some label environment —
  -- the cata/case loop invariants — makes every site and control transfer
  -- check). Discharge: the FrameFreeTrace/SlotBudget-mold walk over
  -- `ir-to-trace'`, `check-++` at every splice, the G2 invariants as the
  -- LabelEnv values.
  emitted-shape-check : ∀ (ir : IR Unit Unit) → HeapModed ir
                      → Σ LabelEnv (λ env →
                          check-shapes env (entry-expect Unit) (ir-to-trace ir) ≡ true)
  -- M3 — RUN CONSISTENCY: a reachable state of a CHECKED program meets the
  -- scanned expectation at its pc. Discharge: induction on `Reachable`
  -- (entry: the D074 all-tag state meets `entry-expect Unit` via `rs-unit`;
  -- step: per-instruction transfer soundness — the `shape-uw`/
  -- `meets-cell-uw` store bricks, `sub-expect-sound` at control).
  run-meets : ∀ prog (fs : FlatState) → RunAt prog fs → (env : LabelEnv)
            → check-shapes env (entry-expect Unit) prog ≡ true
            → Meets (state-at env (entry-expect Unit) prog (fpc fs)) fs
  -- `branch-tag-label-miss` RETIRED 2026-08-01 — a theorem now (`go-miss` in
  -- `tag-branch-step`): not-taken rides the label-free
  -- `block-step-c-branch-tag-nz`, taken-plus-missing is the je-halt template
  -- on `find-label-none-corr`, and the bad-read routes fold into
  -- `branch-tag-bad` (they never depended on the label).


  -- `stack-ptr-case` / `ptr-bounds-case` RETIRED with item 6: the case steps
  -- of both invariants are absurd on `FrameFreeI` now.

  -- The load/branch DISCIPLINE residuals are GONE (Plan 0.62 wiring,
  -- 2026-08-02): `load-indirect{,-suc}-target-ptr` and
  -- `branch-tag-scrutinee-wf` are now THEOREMS below, derived from
  -- `emitted-shape-check` + `run-meets` + the checker's site extraction.
  -- `store-indirect{,-suc}-bad` RETIRED 2026-08-03: the divergent route (a
  -- store through a NON-pointer) is unreachable in emitted code — the
  -- shape checker's store-site discipline (`is-fresh`) makes it absurd.
  -- See `store-indirect{,-suc}-target-ptr` below.

  -- A slot the emitted code READS is frame-live (`slot < frame-slots`): reads stay
  -- inside the frame the prologue reserved. Conditioned on the SITE (a property of
  -- emitted programs, not of arbitrary states) and covering the empty case too —
  -- which used to be what let the empty-slot reads be proved via
  -- `slot-empty-stop`. That lemma is GONE (Plan 0.54 rung D): the empty case is
  -- now UNREACHABLE instead, because `site-ok` requires a claim at every slot
  -- read and `MeetsSlot` refutes a claim at an unwritten slot. The slot MUST be the fetched instruction's own
  -- (`slot-of i ≡ just slot`): quantified over an unrelated `slot` this claims
  -- `slot < frame-slots` for every slot, which is inconsistent (take `slot ≡
  -- frame-slots`) — it would prove the whole correspondence vacuously.
  -- MEMORY EXHAUSTION (plan 0.54 rung D) — the price of "the two regions grow
  -- towards each other", and the ONLY thing the layout separation assumes. The
  -- ONE allocating instruction the emitter produces has room between the heap
  -- frontier and the stack's high-water mark; the
  -- disjointness facts that used to be postulated are derived from the carried
  -- `sep` these keep true. A real runtime failure mode (OOM / stack overflow),
  -- not a claim about addresses — the same class as the `conc-fuel` step budget.
  -- Plan 0.54 rung D step 3: the heap's room is measured against the stack's
  -- HIGH-WATER MARK, not the current `%rsp` — a region the stack has already
  -- visited keeps its (dead) contents, so only the VIRGIN part of the gap is
  -- available. That is also what discharges the fresh block's freshness on the
  -- concrete side, which is why `alloc-heap-fresh-x86` is gone.
  -- (`heap-room` is a MODULE PARAMETER now — see the header. It was the one
  -- resource bound stated inside the correspondence rather than at the apex
  -- beside `conc-fuel`.)
  -- RETIRED 2026-07-31 (plan 0.54 rung D, item 2): `stack-room` / `frame-room` /
  -- `pop-room`, and the alloc-stack FRESH-FRAME pair `alloc-stack-fresh-{abs,x86}`
  -- together with `alloc-stack-entry`, all conditioned a frame-op site — and an
  -- EMITTED program has none (`FrameFree` / `frame-op-absurd`). The fresh-frame
  -- pair was the one place where the correspondence assumed something FALSE of a
  -- re-entered frame (both halves false, agreeing); it is gone with its site.
  -- RETIRED 2026-07-30 (plan 0.54 rung D step 3): "the fresh block is UNWRITTEN on
  -- the concrete side" was `alloc-heap-fresh-x86`, and stated over the region at or
  -- above `%r15` it was FALSE — a deep call that returns leaves written cells below
  -- the current `%rsp`, and the heap can bump into them. It is now a THEOREM about
  -- the region the stack has never reached: `FlatCorr.untouched` on
  -- `[hfront, lo)`, which `heap-room` puts the fresh cells inside.
  -- (Its abstract counterpart — nothing references or has written the not-yet-
  -- allocated block — was already PROVEN, `FlatStoreWF`.)
  -- `lea-indexed-wf` RETIRED 2026-08-01: `lea-indexed` has NO PRODUCER — the
  -- cata codegen walks heap-LINKED stacks (`push2`/`pop2`; IRToTrace says
  -- "NOT lea-indexed") — so it joined `FrameFreeI`'s ⊥ set and its dispatch
  -- route is `⊥`-elim. The cursor-discipline residual died with its site.

  -- RETIRED 2026-07-31 (plan 0.54 rung D, item 2): the MATCHED PROLOGUE/EPILOGUE
  -- family — `dealloc-stack-restores`, `pop-frame-restores`, `dealloc-stack-full`,
  -- `pop-frame-empty`, `pop-frame-saved`. Each was a pairing property of emitted
  -- code at a frame-op site, and emitted code contains no frame op.
  -- `load-const-float` RETIRED 2026-08-03 (D079): a float CONSTANT is a
  -- 64-bit pattern, so codegen emits it as an ordinary immediate instead of
  -- `ud2` — both machines now load the same word and continue. (Float
  -- ARITHMETIC remains unsupported; that is a separate, unemitted path.)

  -- ARITH SIGOP interpretation contract (D061): the internal-producer obligation,
  -- discharged OFFLINE from the arith proofs (dispatch-arith-preserves + arith-block-
  -- correct). For a Pure SigOp, the arith-env maps its symbol to the block `pl`, and
  -- dispatching `pl` yields the CompiledCorr of the flat post-state. `sigop-step` proves
  -- the run-events mechanics AROUND this (pc-alignment + run-events-arith), so this
  -- states exactly the residual arith obligation — nothing about the machine loop.
  arith-sigop-contract : ∀ {hv : HeapView} (env : RTx.ArithEnv val-x86-64) prog fs s {A B} (si : SigOpInfo A B)
                       → RunAt prog fs
                       -- THE REAL ENV (2026-07-30): over an arbitrary `env` the
                       -- conclusion `env sym ≡ just pl` is refuted by `λ _ → nothing`.
                       → env ≡ arith-env-x86-64 (compile-trace prog)
                       → effect si ≡ Pure → CompiledCorr hv prog fs s → fetch prog (fpc fs) ≡ just (instr-sigop si)
                       → Σ (List XInstr × ℕ) (λ pl → env (once-symbol-path (SigOpInfo.name si)) ≡ just pl
                           × CompiledCorr hv prog (flat-exec-instr (instr-sigop si) prog fs)
                               (uncurry (dispatch-arith val-x86-64) pl s))

  -- EXTERNAL SIGOP (Emits/Halts) interpretation contract — the value-carrying observable,
  -- the honest per-(SigOp×target) TrustedBase (D061). Bundles: env maps the symbol to
  -- `nothing` (external, not an arith block); the `ev` extractor emits EXACTLY the
  -- abstract `event-of` (`ev ≡ machine-event` — matching the observable value); and the
  -- concrete post-call state (ret-past) is the CompiledCorr of the flat post-state.
  -- `sigop-external` proves the run-events emission mechanics AROUND this.
  external-sigop-contract : ∀ {hv : HeapView} (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                              prog fs s {A B} (si : SigOpInfo A B)
                          → RunAt prog fs
                          -- THE REAL EXTRACTOR AND ENV (2026-07-30): over arbitrary
                          -- `ev`/`env` the emission claim is refuted by `λ _ _ → []`.
                          → ev ≡ ev-x86-64 → env ≡ arith-env-x86-64 (compile-trace prog)
                          → CompiledCorr hv prog fs s
                          → fetch prog (fpc fs) ≡ just (instr-sigop si)
                          → (env (once-symbol-path (SigOpInfo.name si)) ≡ nothing)
                            × (ev (once-symbol-path (SigOpInfo.name si)) s ≡ event-of (instr-sigop si) fs)
                            × CompiledCorr hv prog (flat-exec-instr (instr-sigop si) prog fs) (RTx.ret-past s)

------------------------------------------------------------------------
-- SLOT LIVENESS IS NOW A THEOREM (plan 0.54 rung D, item 2).
--
-- `slot-read-in-frame` used to be the residual that carried the whole slot
-- cluster (`load-from-slot`, `store-at-slot`, `restore-input`, `worklist-*`,
-- `lea-indexed`). It splits cleanly into a MACHINE fact and an EMITTER fact:
-- the live window never moves during a run, and it started out big enough.
------------------------------------------------------------------------

-- THE EMITTER HALF: every slot an emitted instruction addresses is below the
-- reservation IN FORCE AT ITS POSITION (`ir-to-trace'` threads the frontier and
-- hands it back as `ir-stack-budget`; a `c-thunk` inside the trace switches to
-- the body's). Proved in the codegen layer — see `SlotBudget.SegOK`.
--
-- Plan 0.63 (2b): the bound is POSITIONAL now, because with closure bodies
-- inlined a single budget per trace is false. `fetch` is the frame-semantics-
-- parameterised copy of the codegen layer's `trace-lookup`, so they bridge by
-- an induction on the trace.
fetch≡lookup : ∀ (t : AbstractTrace) (k : ℕ) → fetch t k ≡ trace-lookup t k
fetch≡lookup []       _       = refl
fetch≡lookup (i ∷ is) zero    = refl
fetch≡lookup (i ∷ is) (suc k) = fetch≡lookup is k

emitted-slot-below-budget : ∀ (ir : IR Unit Unit) (k : ℕ) (i : AbstractInstr) (slot : Slot)
                          → fetch (ir-to-trace ir) k ≡ just i → slot-of i ≡ just slot
                          → slot < cur (seg-at (ir-to-trace ir) k (mkSeg (ir-stack-budget ir) []))
emitted-slot-below-budget ir k i slot ftq soq =
  emitted-slot-seg ir k i slot (trans (sym (fetch≡lookup (ir-to-trace ir) k)) ftq) soq

-- THE SEGMENTATION IS STILL CONSTANT — for exactly as long as no emitted trace
-- contains a marker. `FrameFreeI` puts `c-thunk`/`c-ret` in its ⊥ set (they
-- MOVE THE FRAME), and `ir-to-trace-frame-free` says a heap-moded emitted trace
-- has none, so `seg-at` is the identity and the positional bound collapses to
-- the flat one. THIS IS THE BRIDGE THE FLIP REPLACES: once bodies are inlined
-- the fold genuinely varies, and what takes its place is the per-pc invariant
-- plus label scoping (a jump inside a body lands inside that body's segment).
-- ENUMERATED, like `stack-ptr-step`: a catchall would leave `seg-action i`
-- stuck on the variable, and neither classifier can be read off the other
-- without the split.
ff→seg-id : ∀ (i : AbstractInstr) → FrameFreeI i → is-id? (seg-action i) ≡ true
ff→seg-id (instr-ctrl (c-thunk _ _))          ()
ff→seg-id (instr-ctrl (c-ret _))              ()
ff→seg-id (instr-ctrl (c-label _))            _ = refl
ff→seg-id (instr-ctrl (c-jmp _))              _ = refl
ff→seg-id (instr-ctrl (c-branch-scratch-zero _)) _ = refl
ff→seg-id (instr-ctrl (c-branch-tag-zero _))  _ = refl
ff→seg-id mov-to-output                       _ = refl
ff→seg-id mov-to-input                        _ = refl
ff→seg-id mov-output-to-input2                _ = refl
ff→seg-id mov-input2-to-output                _ = refl
ff→seg-id load-indirect                       _ = refl
ff→seg-id load-indirect-suc                   _ = refl
ff→seg-id (load-from-slot _)                  _ = refl
ff→seg-id (store-at-slot _)                   _ = refl
ff→seg-id store-indirect                      _ = refl
ff→seg-id store-indirect-suc                  _ = refl
ff→seg-id (lea-slot _)                        _ = refl
ff→seg-id (lea-indexed _)                     _ = refl
ff→seg-id (restore-input _)                   _ = refl
ff→seg-id (instr-alloc-stack _)               _ = refl
ff→seg-id (instr-dealloc-stack _)             _ = refl
ff→seg-id (instr-reclaim-to _)                _ = refl
ff→seg-id (instr-push-frame _)                _ = refl
ff→seg-id instr-pop-frame                     _ = refl
ff→seg-id instr-call-closure                  _ = refl
ff→seg-id (worklist-init _)                   _ = refl
ff→seg-id (worklist-push _)                   _ = refl
ff→seg-id (worklist-pop _)                    _ = refl
ff→seg-id (worklist-check _)                  _ = refl
ff→seg-id (instr-sigop _)                     _ = refl
ff→seg-id (instr-load-const _ _)              _ = refl
ff→seg-id (instr-load-code-addr _)            _ = refl
ff→seg-id instr-save-closure-reg              _ = refl
ff→seg-id (instr-load-tag-lit _)              _ = refl
ff→seg-id (instr-case-on-tag _ _)             _ = refl
ff→seg-id (instr-alloc-heap _)                _ = refl
ff→seg-id (instr-loop _)                      _ = refl
ff→seg-id (instr-reg-op _)                    _ = refl

-- (`ff→idle` / `idle-seg-at` / `emitted-seg-const` are GONE with the flip.
-- They said "an emitted trace never moves the segment", which is exactly what
-- stopped being true: closure bodies are inline, so an emitted trace contains
-- the two markers and the segmentation genuinely varies along it. Everything
-- that leant on them is now proved per-instruction below — the last of them,
-- the JUMP case, is the label-scoping obligation.)

-- (An `emitted-jump-in-segment` POSTULATE stood here while the flip was being
-- measured. It is now the PROVED `LabelScope.emitted-jump-in-segment`, wired
-- into the jump clause below — so the scaffolding is deleted rather than left
-- beside its theorem.)

------------------------------------------------------------------------
-- THE FRAME STACK AND THE RETURN STACK ARE ONE STACK (Plan 0.63).
--
-- `c-thunk` pushes the caller's frame while `instr-call-closure` pushes the
-- return pc; `c-ret` pops both. So they have the same length, and — the part
-- that makes the SEGMENTED budget survive a return — each saved frame's
-- reservation is the segment in force at the pc it will return to. Without
-- that second half, `c-ret` restores a slot count from `saved-frames` and
-- lands the pc at a return address with NOTHING relating the two, and
-- `run-stack-slot` below cannot be re-established.
--
-- A DATATYPE (not a `with`-free function on two lists) so the cons/nil cases
-- compose at the pushes and pops the markers produce.
------------------------------------------------------------------------
data RetMatch (prog : AbstractTrace) (B : ℕ) : List (Frame × ℕ) → List ℕ → Set where
  rm-[]  : RetMatch prog B [] []
  rm-∷   : ∀ {f b rpc frs rs}
         → b ≡ cur (seg-at prog rpc (mkSeg B []))
         → RetMatch prog B frs rs
         → RetMatch prog B ((f , b) ∷ frs) (rpc ∷ rs)

-- THE RUN INVARIANT, per frame. `seg-cur` is what `slot-read-in-frame`
-- consumes; `seg-stack` is what a return will consume. One induction.
record SegWF (prog : AbstractTrace) (B : ℕ) (fs : FlatState) : Set where
  constructor mkSegWF
  field
    seg-cur   : frame-slots (falloc fs) ≡ cur (seg-at prog (fpc fs) (mkSeg B []))
    seg-stack : RetMatch prog B (saved-frames (falloc fs)) (fret fs)
open SegWF public

------------------------------------------------------------------------
-- HOW THE PC MOVES, per instruction. Everything a frame-free step can be
-- either FALLS THROUGH (`flat-step-straight`, and `c-label`) or is one of the
-- three JUMPS. That split is what confines the label-scoping obligation:
-- a fall-through's segment fact is the fold's own recursion (`seg-at-suc`),
-- with nothing assumed about emitted code.
------------------------------------------------------------------------
-- where a jump can land: fall through, halt with the pc unmoved (the label
-- was not found), or at the label's resolved index. The last is the only case
-- that needs LABEL SCOPING, and carrying the target `m` here is what lets it
-- consume `emitted-jump-in-segment`.
-- the three post-pc shapes, read off `do-jump` / `do-branch`
dj-aux : ∀ (mj : Maybe ℕ) (fs : FlatState)
       → (fpc (do-jump mj fs) ≡ fpc fs)
         ⊎ (Σ ℕ (λ q → (mj ≡ just q) × (fpc (do-jump mj fs) ≡ q)))
dj-aux (just q) fs = inj₂ (q , refl , refl)
dj-aux nothing  fs = inj₁ refl

-- …and the branch, over a VARIABLE condition. Taking `b` as an argument is
-- what makes `do-branch b` reduce on the split — abstracting the scrutinee at
-- the use site does not work, because its normal form is spelled differently
-- from the source term (`readReg … Scratch` vs the field accessor).
db-aux : ∀ (b : Bool) (m : LabelId) (prog : AbstractTrace) (fs : FlatState)
       → (fpc (do-branch b m prog fs) ≡ suc (fpc fs))
         ⊎ ((fpc (do-branch b m prog fs) ≡ fpc fs)
            ⊎ (Σ ℕ (λ q → (find-label prog m ≡ just q)
                        × (fpc (do-branch b m prog fs) ≡ q))))
db-aux false m prog fs = inj₁ refl
db-aux true  m prog fs = inj₂ (dj-aux (find-label prog m) fs)

data JumpPost (i : AbstractInstr) (m : LabelId) (prog : AbstractTrace) (fs : FlatState) : Set where
  jp-suc  : fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs) → JumpPost i m prog fs
  jp-halt : fpc (flat-exec-instr i prog fs) ≡ fpc fs → JumpPost i m prog fs
  jp-to   : ∀ (q : ℕ) → find-label prog m ≡ just q
          → fpc (flat-exec-instr i prog fs) ≡ q → JumpPost i m prog fs

-- Plan 0.63 (post-flip): an EMITTED instruction is one of four kinds, and the
-- markers are now among them. `pv-suc`/`pv-jump` are the frame-free ones (they
-- carry `FrameFreeI`, which is what `flat-same-frames` and the invariant
-- inductions consume); `pv-thunk`/`pv-ret` are the two that MOVE THE FRAME and
-- carry their reservation instead.
data PcView (i : AbstractInstr) : Set where
  pv-suc   : FrameFreeI i
           → (∀ prog fs → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)) → PcView i
  pv-jump  : FrameFreeI i → ∀ (m : LabelId) → once-label-of i ≡ just m
           → (∀ prog fs → JumpPost i m prog fs) → PcView i
  pv-thunk : ∀ (ℓ : LabelId) (bb : ℕ) → i ≡ instr-ctrl (c-thunk ℓ bb) → PcView i
  pv-ret   : ∀ (bb : ℕ) → i ≡ instr-ctrl (c-ret bb) → PcView i

pcView : ∀ (i : AbstractInstr) → EmittableI i → PcView i
pcView (instr-ctrl (c-label _))               _ = pv-suc tt (λ _ _ → refl)
pcView (instr-ctrl (c-jmp m))                 _ = pv-jump tt m refl go
  where go : ∀ prog fs → JumpPost (instr-ctrl (c-jmp m)) m prog fs
        go prog fs = mk (dj-aux (find-label prog m) fs)
          where mk : (fpc (do-jump (find-label prog m) fs) ≡ fpc fs)
                     ⊎ (Σ ℕ (λ q → (find-label prog m ≡ just q)
                                 × (fpc (do-jump (find-label prog m) fs) ≡ q)))
                   → JumpPost (instr-ctrl (c-jmp m)) m prog fs
                mk (inj₁ e)            = jp-halt e
                mk (inj₂ (q , fq , e)) = jp-to q fq e
-- the branches abstract their scrutinee WITH an equation (J-style), so the
-- goal's `do-branch <cond>` reduces on the taken/not-taken split
pcView (instr-ctrl (c-branch-scratch-zero m))     _ = pv-jump tt m refl go
  where
    go : ∀ prog fs → JumpPost (instr-ctrl (c-branch-scratch-zero m)) m prog fs
    go prog fs = mk (db-aux (sv-is-zero (readReg (regs (floc fs)) Scratch)) m prog fs)
      where mk : _ → JumpPost (instr-ctrl (c-branch-scratch-zero m)) m prog fs
            mk (inj₁ e)                     = jp-suc e
            mk (inj₂ (inj₁ e))              = jp-halt e
            mk (inj₂ (inj₂ (q , fq , e)))   = jp-to q fq e
pcView (instr-ctrl (c-branch-tag-zero m))     _ = pv-jump tt m refl go
  where
    go : ∀ prog fs → JumpPost (instr-ctrl (c-branch-tag-zero m)) m prog fs
    go prog fs = mk (db-aux (tag-zf (flat-read-tag (floc fs))) m prog fs)
      where mk : _ → JumpPost (instr-ctrl (c-branch-tag-zero m)) m prog fs
            mk (inj₁ e)                     = jp-suc e
            mk (inj₂ (inj₁ e))              = jp-halt e
            mk (inj₂ (inj₂ (q , fq , e)))   = jp-to q fq e
pcView (instr-ctrl (c-thunk ℓ bb))            _ = pv-thunk ℓ bb refl
pcView (instr-ctrl (c-ret bb))                _ = pv-ret bb refl
pcView (instr-alloc-stack _)                  ()
pcView (instr-dealloc-stack _)                ()
pcView (instr-push-frame _)                   ()
pcView instr-pop-frame                        ()
pcView (instr-case-on-tag _ _)                ()
pcView (instr-loop _)                         ()
pcView (lea-slot _)                           ()
pcView (lea-indexed _)                        ()
pcView mov-to-output                          _ = pv-suc tt (λ _ _ → refl)
pcView mov-to-input                           _ = pv-suc tt (λ _ _ → refl)
pcView mov-output-to-input2                   _ = pv-suc tt (λ _ _ → refl)
pcView mov-input2-to-output                   _ = pv-suc tt (λ _ _ → refl)
pcView load-indirect                          _ = pv-suc tt (λ _ _ → refl)
pcView load-indirect-suc                      _ = pv-suc tt (λ _ _ → refl)
pcView (load-from-slot _)                     _ = pv-suc tt (λ _ _ → refl)
pcView (store-at-slot _)                      _ = pv-suc tt (λ _ _ → refl)
pcView store-indirect                         _ = pv-suc tt (λ _ _ → refl)
pcView store-indirect-suc                     _ = pv-suc tt (λ _ _ → refl)
pcView (restore-input _)                      _ = pv-suc tt (λ _ _ → refl)
pcView (instr-reclaim-to _)                   _ = pv-suc tt (λ _ _ → refl)
pcView instr-call-closure                     _ = pv-suc tt (λ _ _ → refl)
pcView (worklist-init _)                      _ = pv-suc tt (λ _ _ → refl)
pcView (worklist-push _)                      _ = pv-suc tt (λ _ _ → refl)
pcView (worklist-pop _)                       _ = pv-suc tt (λ _ _ → refl)
pcView (worklist-check _)                     _ = pv-suc tt (λ _ _ → refl)
pcView (instr-sigop _)                        _ = pv-suc tt (λ _ _ → refl)
pcView (instr-load-const _ _)                 _ = pv-suc tt (λ _ _ → refl)
pcView (instr-load-code-addr _)               _ = pv-suc tt (λ _ _ → refl)
pcView instr-save-closure-reg                 _ = pv-suc tt (λ _ _ → refl)
pcView (instr-load-tag-lit _)                 _ = pv-suc tt (λ _ _ → refl)
pcView (instr-alloc-heap _)                   _ = pv-suc tt (λ _ _ → refl)
pcView (instr-reg-op _)                       _ = pv-suc tt (λ _ _ → refl)

-- The live stack window is the reservation IN FORCE at the current pc — the
-- CURRENT FRAME's, once frames move. Induction on `Reachable`; each step is
-- frame-free because the program is emitted (`frame-op-absurd`), so it moves
-- neither the frame stack nor the return stack (`flat-same-frames`).
--
-- THE ONE PLACE THE FLIP LANDS: the step case needs the segment in force to be
-- the same at the post-pc as at the pre-pc. Today that is `emitted-seg-const`
-- (no emitted trace holds a marker, so `seg-at` is the identity). With bodies
-- inlined it becomes two obligations — the marker steps, which move the
-- segment exactly as they move the frame, and LABEL SCOPING for the jumps.
run-seg-wf : ∀ prog (fs : FlatState) (r : RunAt prog fs)
           → SegWF prog (ir-stack-budget (run-ir r)) fs
run-seg-wf prog fs (mkRunAt ir eq hm reach) = go fs reach
  where
    B₀ = mkSeg (ir-stack-budget ir) []
    go : ∀ (fs' : FlatState) → Reachable prog (ir-stack-budget ir) fs'
       → SegWF prog (ir-stack-budget ir) fs'
    -- AT ENTRY the pc is 0 and `seg-at _ zero` is the starting state outright.
    go fs' (reach-start .fs' el eqB) =
      mkSegWF (subst (λ z → frame-slots (falloc fs') ≡ cur (seg-at prog z B₀))
                     (sym (proj₁ el)) eqB)
              (subst₂ (RetMatch prog (ir-stack-budget ir))
                      (sym (proj₁ (proj₂ (proj₂ (proj₂ el)))))
                      (sym (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ el))))))
                      rm-[])
    go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
      step (pcView i em)
      where
        em  = frame-op-absurd prog fs'' i (ir , eq) hm ftq
        ih  = go fs'' r'
        lk : trace-lookup prog (fpc fs'') ≡ just i
        lk = trans (sym (fetch≡lookup prog (fpc fs''))) ftq
        -- the segment one position along, stepped by the fetched instruction
        seg-suc : seg-at prog (suc (fpc fs'')) B₀ ≡ seg-step i (seg-at prog (fpc fs'') B₀)
        seg-suc = seg-at-suc prog (fpc fs'') B₀ lk
        step : PcView i → SegWF prog (ir-stack-budget ir) (flat-exec-instr i prog fs'')
        -- FRAME-FREE, FALLING THROUGH: frames untouched, segment unmoved.
        step (pv-suc ff adv) =
          mkSegWF
            (trans (sf-slots same) (trans (seg-cur ih) (sym stable)))
            (subst₂ (RetMatch prog (ir-stack-budget ir))
                    (sym (sf-saved same)) (sym (sf-ret same)) (seg-stack ih))
          where
            same = flat-same-frames i prog fs'' ff
            stable : cur (seg-at prog (fpc (flat-exec-instr i prog fs'')) B₀)
                   ≡ cur (seg-at prog (fpc fs'') B₀)
            stable = cong cur (trans (cong (λ z → seg-at prog z B₀) (adv prog fs''))
                              (trans seg-suc
                                     (idle-step i (ff→seg-id i ff) (seg-at prog (fpc fs'') B₀))))
        -- FRAME-FREE JUMP: frames untouched; the segment survives by LABEL
        -- SCOPING (`LabelScope.emitted-jump-in-segment`).
        step (pv-jump ff m mlab jp) =
          mkSegWF
            (trans (sf-slots same) (trans (seg-cur ih) (sym (jgo (jp prog fs'')))))
            (subst₂ (RetMatch prog (ir-stack-budget ir))
                    (sym (sf-saved same)) (sym (sf-ret same)) (seg-stack ih))
          where
            same = flat-same-frames i prog fs'' ff
            lkm : mention-at prog (fpc fs'') ≡ just m
            lkm = trans (cong mention-of lk) mlab
            jgo : JumpPost i m prog fs''
                → cur (seg-at prog (fpc (flat-exec-instr i prog fs'')) B₀)
                ≡ cur (seg-at prog (fpc fs'') B₀)
            jgo (jp-suc adv) =
              cong cur (trans (cong (λ z → seg-at prog z B₀) adv)
                       (trans seg-suc (idle-step i (ff→seg-id i ff) (seg-at prog (fpc fs'') B₀))))
            jgo (jp-halt e) = cong cur (cong (λ z → seg-at prog z B₀) e)
            jgo (jp-to q fq e) =
              cong cur (trans (cong (λ z → seg-at prog z B₀) e)
                        (subst (λ pr → seg-at pr q B₀ ≡ seg-at pr (fpc fs'') B₀) (sym eq)
                          (emitted-jump-in-segment {FS} ir (fpc fs'') q m B₀
                            (subst (λ pr → mention-at pr (fpc fs'') ≡ just m) eq lkm)
                            (subst (λ pr → find-label pr m ≡ just q) eq fq))))
        -- THE BODY MARKER: `grow-frame bb` sets `frame-slots := bb` and the
        -- static `seg-push bb` sets `cur := bb` — they agree by construction,
        -- which is the whole point of D086 putting the PUSH at the call and
        -- only the reservation here. `saved-frames`/`fret` are untouched, so
        -- `RetMatch` rides through.
        step (pv-thunk ℓ bb ieq) =
          mkSegWF (trans (cong (λ z → frame-slots (falloc (flat-exec-instr z prog fs''))) ieq)
                         (sym (cong cur (trans (cong (λ z → seg-at prog z B₀) (pc-eq ieq))
                                               (trans seg-suc (step-eq ieq))))))
                  (subst₂ (RetMatch prog (ir-stack-budget ir))
                          (sym (cong (λ z → saved-frames (falloc (flat-exec-instr z prog fs''))) ieq))
                          (sym (cong (λ z → fret (flat-exec-instr z prog fs'')) ieq))
                          (seg-stack ih))
          where
            pc-eq : i ≡ instr-ctrl (c-thunk ℓ bb)
                  → fpc (flat-exec-instr i prog fs'') ≡ suc (fpc fs'')
            pc-eq refl = refl
            step-eq : i ≡ instr-ctrl (c-thunk ℓ bb)
                    → seg-step i (seg-at prog (fpc fs'') B₀)
                      ≡ mkSeg bb (cur (seg-at prog (fpc fs'') B₀) ∷ saved (seg-at prog (fpc fs'') B₀))
            step-eq refl = refl
        -- THE RETURN: `leave-frame` restores the caller's count and the pc goes
        -- to the popped return address. That those two BELONG TOGETHER is
        -- exactly `RetMatch`, which is what it was built for.
        step (pv-ret bb ieq) = ret-step ieq
          where
            ret-step : i ≡ instr-ctrl (c-ret bb)
                     → SegWF prog (ir-stack-budget ir) (flat-exec-instr i prog fs'')
            ret-step refl = go-rm (fret fs'') (saved-frames (falloc fs'')) refl refl (seg-stack ih)
              where
                -- J-style on BOTH stacks at once: `RetMatch` pairs them, so
                -- the length-mismatch rows are absurd and the cons row hands
                -- back exactly the two facts the post-state needs — the
                -- caller's reservation (`beq`) and the tail pairing.
                go-rm : ∀ (rs : List ℕ) (frs : List (Frame × ℕ))
                      → fret fs'' ≡ rs → saved-frames (falloc fs'') ≡ frs
                      → RetMatch prog (ir-stack-budget ir) frs rs
                      → SegWF prog (ir-stack-budget ir)
                              (flat-exec-instr (instr-ctrl (c-ret bb)) prog fs'')
                -- an empty return stack HALTS with the pc unmoved, so the
                -- caller's window is this frame's and the pairing stays empty
                go-rm [] [] req feq rm-[] =
                  mkSegWF (trans (cong frame-slots (do-ret-alloc fs''))
                          (trans (leave-frame-slots-[] (falloc fs'') feq)
                          (trans (seg-cur ih)
                                 (cong (λ z → cur (seg-at prog z B₀))
                                       (sym (do-ret-pc-[] fs'' req))))))
                          (subst₂ (RetMatch prog (ir-stack-budget ir))
                                  (sym (trans (cong saved-frames (do-ret-alloc fs''))
                                              (leave-frame-saved-[] (falloc fs'') feq)))
                                  (sym (do-ret-fret-[] fs'' req)) rm-[])
                -- …and a real return takes the caller's reservation `b` and
                -- lands at `rpc`; `RetMatch` says those two belong together
                go-rm (rpc ∷ rs) ((f , b) ∷ frs) req feq (rm-∷ beq rest) =
                  mkSegWF (trans (cong frame-slots (do-ret-alloc fs''))
                          (trans (leave-frame-slots-∷ (falloc fs'') f b frs feq)
                          (trans beq (cong (λ z → cur (seg-at prog z B₀))
                                           (sym (do-ret-pc-∷ fs'' rpc rs req))))))
                          (subst₂ (RetMatch prog (ir-stack-budget ir))
                                  (sym (trans (cong saved-frames (do-ret-alloc fs''))
                                              (leave-frame-saved-∷ (falloc fs'') f b frs feq)))
                                  (sym (do-ret-fret-∷ fs'' rpc rs req)) rest)
                go-rm [] ((f , b) ∷ frs) req feq ()
                go-rm (rpc ∷ rs) [] req feq ()

-- (`run-stack-slot` — "the window is the whole trace's budget" — is GONE with
-- the flip. It is FALSE inside a closure body, whose window is the body's own
-- reservation. Its consumer wants the POSITIONAL form, which `SegWF.seg-cur`
-- already is, so the two now compose with no intermediate at all.)

------------------------------------------------------------------------
-- NOTHING EVER OWES A RETURN — the call gap, as a THEOREM about the state
-- (Plan 0.54 rung D, 2026-08-06).
--
-- `fret` and `saved-frames` are PUSHED by exactly one instruction,
-- `instr-call-closure`, whose abstract semantics is the IDENTITY
-- (`SMCore.exec-abstract instr-call-closure s alloc = s , alloc`). Every other
-- step either leaves both alone (`flat-same-frames` for the frame-free ones,
-- `grow-frame` for `c-thunk`, which moves the CURRENT frame only) or POPS them
-- (`c-ret`). `EntryLike` starts both empty. So they are empty in EVERY
-- reachable state — the model gap `events-running-call` names, measured at the
-- state rather than at the event trace.
--
-- This is the theorem the RETURN correspondence collides with; see `ret-step`.
------------------------------------------------------------------------
run-no-ret : ∀ prog (fs : FlatState) → RunAt prog fs
           → (fret fs ≡ []) × (saved-frames (falloc fs) ≡ [])
run-no-ret prog fs (mkRunAt ir eq hm reach) = go fs reach
  where
    go : ∀ (fs' : FlatState) → Reachable prog (ir-stack-budget ir) fs'
       → (fret fs' ≡ []) × (saved-frames (falloc fs') ≡ [])
    go fs' (reach-start .fs' el _) =
      proj₁ (proj₂ (proj₂ (proj₂ (proj₂ el)))) , proj₁ (proj₂ (proj₂ (proj₂ el)))
    go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
      step (pcView i (frame-op-absurd prog fs'' i (ir , eq) hm ftq))
      where
        ih = go fs'' r'
        step : PcView i
             → (fret (flat-exec-instr i prog fs'') ≡ [])
             × (saved-frames (falloc (flat-exec-instr i prog fs'')) ≡ [])
        -- FRAME-FREE (both the fall-throughs and the jumps): neither stack moves.
        step (pv-suc ff _) =
          trans (sf-ret same) (proj₁ ih) , trans (sf-saved same) (proj₂ ih)
          where same = flat-same-frames i prog fs'' ff
        step (pv-jump ff _ _ _) =
          trans (sf-ret same) (proj₁ ih) , trans (sf-saved same) (proj₂ ih)
          where same = flat-same-frames i prog fs'' ff
        -- THE BODY MARKER: `grow-frame` deepens the CURRENT frame (D086 puts the
        -- push at the call, not here), so it pushes neither stack.
        step (pv-thunk ℓ bb ieq) = thunk-go ieq
          where thunk-go : i ≡ instr-ctrl (c-thunk ℓ bb)
                         → (fret (flat-exec-instr i prog fs'') ≡ [])
                         × (saved-frames (falloc (flat-exec-instr i prog fs'')) ≡ [])
                thunk-go refl = proj₁ ih , proj₂ ih
        -- THE RETURN: pops both, and popping an empty stack leaves it empty.
        step (pv-ret bb ieq) = ret-go ieq
          where ret-go : i ≡ instr-ctrl (c-ret bb)
                       → (fret (flat-exec-instr i prog fs'') ≡ [])
                       × (saved-frames (falloc (flat-exec-instr i prog fs'')) ≡ [])
                ret-go refl =
                  do-ret-fret-[] fs'' (proj₁ ih)
                  , trans (cong saved-frames (do-ret-alloc fs''))
                          (leave-frame-saved-[] (falloc fs'') (proj₂ ih))

-- ONE FRAME-FREE STEP PRESERVES THE INVARIANT — a THEOREM for EVERY
-- constructor. Plan 0.63 step 2b SIMPLIFIED this: `lea-slot` joined
-- `FrameFreeI`'s ⊥ set (a heap-moded trace emits none), so its route is now
-- absurd like the fossils' and the whole pair-bound plumbing it used to need
-- — `emitted-lea-slot-pair`, `SlotBudget.SlotBelow`'s second field, and the
-- `run-stack-slot` transport — is gone with it.
stack-ptr-step : ∀ (i : AbstractInstr) prog (fs : FlatState) → RunAt prog fs
               → fetch prog (fpc fs) ≡ just i → EmittableI i
               → StackPtrWF fs → StackPtrWF (flat-exec-instr i prog fs)
stack-ptr-step (lea-slot slot) prog fs r ftq () wf
stack-ptr-step (lea-indexed slot) prog fs r ftq () wf
stack-ptr-step (instr-case-on-tag f g) prog fs r ftq () wf
stack-ptr-step (instr-alloc-stack n)   prog fs r ftq () wf
stack-ptr-step (instr-dealloc-stack n) prog fs r ftq () wf
stack-ptr-step (instr-push-frame cap)  prog fs r ftq () wf
stack-ptr-step instr-pop-frame         prog fs r ftq () wf
stack-ptr-step (instr-loop body)       prog fs r ftq () wf
stack-ptr-step mov-to-output prog fs r ftq ff wf =
  flat-stack-ptr mov-to-output prog fs ff wf
stack-ptr-step mov-to-input prog fs r ftq ff wf =
  flat-stack-ptr mov-to-input prog fs ff wf
stack-ptr-step mov-output-to-input2 prog fs r ftq ff wf =
  flat-stack-ptr mov-output-to-input2 prog fs ff wf
stack-ptr-step mov-input2-to-output prog fs r ftq ff wf =
  flat-stack-ptr mov-input2-to-output prog fs ff wf
stack-ptr-step load-indirect prog fs r ftq ff wf =
  flat-stack-ptr load-indirect prog fs ff wf
stack-ptr-step load-indirect-suc prog fs r ftq ff wf =
  flat-stack-ptr load-indirect-suc prog fs ff wf
stack-ptr-step (load-from-slot k) prog fs r ftq ff wf =
  flat-stack-ptr (load-from-slot k) prog fs ff wf
stack-ptr-step (store-at-slot k) prog fs r ftq ff wf =
  flat-stack-ptr (store-at-slot k) prog fs ff wf
stack-ptr-step store-indirect prog fs r ftq ff wf =
  flat-stack-ptr store-indirect prog fs ff wf
stack-ptr-step store-indirect-suc prog fs r ftq ff wf =
  flat-stack-ptr store-indirect-suc prog fs ff wf
stack-ptr-step (restore-input k) prog fs r ftq ff wf =
  flat-stack-ptr (restore-input k) prog fs ff wf
stack-ptr-step (instr-reclaim-to k) prog fs r ftq ff wf =
  flat-stack-ptr (instr-reclaim-to k) prog fs ff wf
stack-ptr-step instr-call-closure prog fs r ftq ff wf =
  flat-stack-ptr instr-call-closure prog fs ff wf
stack-ptr-step (worklist-init k) prog fs r ftq ff wf =
  flat-stack-ptr (worklist-init k) prog fs ff wf
stack-ptr-step (worklist-push k) prog fs r ftq ff wf =
  flat-stack-ptr (worklist-push k) prog fs ff wf
stack-ptr-step (worklist-pop k) prog fs r ftq ff wf =
  flat-stack-ptr (worklist-pop k) prog fs ff wf
stack-ptr-step (worklist-check k) prog fs r ftq ff wf =
  flat-stack-ptr (worklist-check k) prog fs ff wf
stack-ptr-step (instr-sigop si) prog fs r ftq ff wf =
  flat-stack-ptr (instr-sigop si) prog fs ff wf
stack-ptr-step (instr-load-const p v) prog fs r ftq ff wf =
  flat-stack-ptr (instr-load-const p v) prog fs ff wf
stack-ptr-step (instr-load-code-addr k) prog fs r ftq ff wf =
  flat-stack-ptr (instr-load-code-addr k) prog fs ff wf
stack-ptr-step instr-save-closure-reg prog fs r ftq ff wf =
  flat-stack-ptr instr-save-closure-reg prog fs ff wf
stack-ptr-step (instr-load-tag-lit k) prog fs r ftq ff wf =
  flat-stack-ptr (instr-load-tag-lit k) prog fs ff wf
stack-ptr-step (instr-alloc-heap k) prog fs r ftq ff wf =
  flat-stack-ptr (instr-alloc-heap k) prog fs ff wf
stack-ptr-step (instr-reg-op op) prog fs r ftq ff wf =
  flat-stack-ptr (instr-reg-op op) prog fs ff wf
stack-ptr-step (instr-ctrl c) prog fs r ftq ff wf =
  flat-stack-ptr (instr-ctrl c) prog fs ff wf

-- A start state satisfies the invariant vacuously: both memories are empty and
-- no register holds a pointer.
entry-stack-ptr : ∀ (fs : FlatState) → EntryLike fs → StackPtrWF fs
entry-stack-ptr fs (_ , _ , _ , _ , _ , hemp , semp , _ , noptr) = record
  { sp-regs  = λ r → go r (readReg (regs (floc fs)) r) refl
  ; sp-heap  = λ hl → subst StackPtrOK? (sym (hemp hl)) tt
  ; sp-stack = λ f k → subst StackPtrOK? (sym (semp f k)) tt }
  where go : ∀ (r : AbstractReg) (v : StoredValue FS) → readReg (regs (floc fs)) r ≡ v
           → StackPtrOK (readReg (regs (floc fs)) r)
        go r (SV-Ptr loc)  eq = ⊥-elim (noptr r loc eq)
        go r (SV-Tag t)    eq rewrite eq = tt
        go r (SV-Lit p v)  eq rewrite eq = tt
        go r (SV-Code c)   eq rewrite eq = tt

-- …and the pointer-bounds and store-WF invariants likewise (D074: the entry
-- registers are all tags, both memories empty).
entry-ptr-bounds : ∀ (fs : FlatState) → EntryLike fs → PtrBoundsWF fs
entry-ptr-bounds fs (_ , _ , _ , _ , _ , hemp , semp , _ , noptr) = record
  { pb-regs  = λ r → go r (readReg (regs (floc fs)) r) refl
  ; pb-heap  = λ hl → subst (PtrB? _) (sym (hemp hl)) tt
  ; pb-stack = λ f k → subst (PtrB? _) (sym (semp f k)) tt }
  where go : ∀ (r : AbstractReg) (v : StoredValue FS) → readReg (regs (floc fs)) r ≡ v
           → PtrB (block-size (falloc fs)) (readReg (regs (floc fs)) r)
        go r (SV-Ptr loc)  eq = ⊥-elim (noptr r loc eq)
        go r (SV-Tag t)    eq rewrite eq = tt
        go r (SV-Lit p v)  eq rewrite eq = tt
        go r (SV-Code c)   eq rewrite eq = tt

entry-flat-wf : ∀ (fs : FlatState) → EntryLike fs → FlatWF fs
entry-flat-wf fs (_ , _ , _ , _ , _ , hemp , semp , _ , noptr) = record
  { wf-regs  = λ r → go r (readReg (regs (floc fs)) r) refl
  ; wf-heap  = λ hl → subst (svm-below _) (sym (hemp hl)) tt
  ; wf-stack = λ f k → subst (svm-below _) (sym (semp f k)) tt
  ; wf-fresh = λ hl _ → hemp hl }
  where go : ∀ (r : AbstractReg) (v : StoredValue FS) → readReg (regs (floc fs)) r ≡ v
           → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) r)
        go r (SV-Ptr loc)  eq = ⊥-elim (noptr r loc eq)
        go r (SV-Tag t)    eq rewrite eq = tt
        go r (SV-Lit p v)  eq rewrite eq = tt
        go r (SV-Code c)   eq rewrite eq = tt

-- Every stack pointer in a reachable state addresses a live pair of the current
-- frame. Induction on `Reachable`, exactly like `run-stack-slot`: the entry
-- state holds no stack pointer at all (its registers hold the heap filler and
-- both memories are empty), and each step preserves the invariant because the
-- program is emitted — frame-free, and its `lea-slot`s address reserved pairs.
run-stack-ptr : ∀ prog (fs : FlatState) (r : RunAt prog fs) → StackPtrWF fs
run-stack-ptr prog fs (mkRunAt ir eq hm reach) = go fs reach
  where go : ∀ (fs' : FlatState) → Reachable prog (ir-stack-budget ir) fs' → StackPtrWF fs'
        go fs' (reach-start .fs' el _) = entry-stack-ptr fs' el
        go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
          stack-ptr-step i prog fs'' (mkRunAt ir eq hm r') ftq
            (frame-op-absurd prog fs'' i (ir , eq) hm ftq)
            (go fs'' r')

-- The two forms the block-steps ask for. Since Plan 0.63's `StackPtrWF`
-- became "there is no stack pointer", holding one in `Input1` is refuted
-- outright — these keep their signatures so nothing downstream changes, but
-- both components are now `⊥-elim`.
stack-ptr-current : ∀ prog (fs : FlatState) (f : Frame) (k : Slot) → RunAt prog fs
                  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
                  → (f ≡ current-frame (falloc fs)) × (k < frame-slots (falloc fs))
stack-ptr-current prog fs f k r eq =
  stack-ptr-frame fs Input1 f k (run-stack-ptr prog fs r) eq
  , ⊥-elim (stack-ptr-live fs Input1 f k (run-stack-ptr prog fs r) eq)

stack-ptr-current-suc : ∀ prog (fs : FlatState) (f : Frame) (k : Slot) → RunAt prog fs
                      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
                      → (f ≡ current-frame (falloc fs)) × (suc k < frame-slots (falloc fs))
stack-ptr-current-suc prog fs f k r eq =
  stack-ptr-frame fs Input1 f k (run-stack-ptr prog fs r) eq
  , ⊥-elim (stack-ptr-suc-live fs Input1 f k (run-stack-ptr prog fs r) eq)

slot-read-in-frame : ∀ prog (fs : FlatState) (slot : Slot) (i : AbstractInstr) → RunAt prog fs
                   → fetch prog (fpc fs) ≡ just i → slot-of i ≡ just slot
                   → slot < frame-slots (falloc fs)
-- the positional bound, then the two equations that place it: the segment in
-- force at this pc (constant today — `emitted-seg-const`) and the machine's own
-- window (`run-stack-slot`).
slot-read-in-frame prog fs slot i r ftq soq =
  -- the emitter's positional bound, at the machine's positional window
  subst (slot <_) (sym (seg-cur (run-seg-wf prog fs r)))
    (subst (λ pr → slot < cur (seg-at pr (fpc fs) (mkSeg (ir-stack-budget (run-ir r)) [])))
           (sym (run-emit r))
           (emitted-slot-below-budget (run-ir r) (fpc fs) i slot
             (subst (λ p → fetch p (fpc fs) ≡ just i) (run-emit r) ftq) soq))

------------------------------------------------------------------------
-- THE POINTER-BOUNDS INVARIANT IS A THEOREM (plan 0.54 rung D, item 5).
--
-- Every dynamic pointer a reachable state holds is in-bounds for its block —
-- in the PAIR form (`Once.CCC.Machine.FlatPtrBounds`). Same shape as
-- `run-stack-ptr`, with two extra inputs: the emitter's allocation discipline
-- (every emitted `instr-alloc-heap` is a 2-cell pair block, `AllocMin`) and
-- the store-WF invariant (carried through the SAME induction — an allocation
-- cannot shrink the block under a live pointer because no live pointer
-- references the fresh ref). This is what turned the in-bounds residual
-- family into theorems: `store-indirect{,-suc}-inbounds` outright, and the
-- in-bounds conjunct of `load-indirect{,-suc}-target-wf` (whose pointer-SHAPE
-- half stays the D073 site-discipline residual, now named `-target-ptr`).
------------------------------------------------------------------------

-- THE EMITTER HALF: a fetched instruction of an emitted program satisfies the
-- allocation discipline (`AllocMinI`).
emitted-alloc-min : ∀ prog (fs : FlatState) (i : AbstractInstr) → Emitted prog
                  → fetch prog (fpc fs) ≡ just i → AllocMinI i
emitted-alloc-min .(ir-to-trace ir) fs i (ir , refl) ftq = fetch-alloc-min {FS} ir ftq

-- ONE FRAME-FREE STEP PRESERVES THE INVARIANT — enumerated like
-- `stack-ptr-step` (the vacuous alloc premises need `i` concrete).
ptr-bounds-step : ∀ (i : AbstractInstr) prog (fs : FlatState) → RunAt prog fs
                → fetch prog (fpc fs) ≡ just i → EmittableI i
                → FlatWF fs
                → PtrBoundsWF fs → PtrBoundsWF (flat-exec-instr i prog fs)
ptr-bounds-step (instr-case-on-tag f g) prog fs r ftq () wfS wf
ptr-bounds-step (instr-alloc-stack n)   prog fs r ftq () wfS wf
ptr-bounds-step (instr-dealloc-stack n) prog fs r ftq () wfS wf
ptr-bounds-step (instr-push-frame cap)  prog fs r ftq () wfS wf
ptr-bounds-step instr-pop-frame         prog fs r ftq () wfS wf
ptr-bounds-step (instr-loop body)       prog fs r ftq () wfS wf
ptr-bounds-step (lea-indexed slot)      prog fs r ftq () wfS wf
-- THE PRODUCER: the emitter's alloc discipline comes in through the premise.
ptr-bounds-step (instr-alloc-heap k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-alloc-heap k) prog fs ff
    (λ n eq → subst AllocMinI eq
                (emitted-alloc-min prog fs (instr-alloc-heap k) (run-emitted r) ftq))
    wfS wf
ptr-bounds-step mov-to-output prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-to-output prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step mov-to-input prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-to-input prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step mov-output-to-input2 prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-output-to-input2 prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step mov-input2-to-output prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-input2-to-output prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step load-indirect prog fs r ftq ff wfS wf =
  flat-ptr-bounds load-indirect prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step load-indirect-suc prog fs r ftq ff wfS wf =
  flat-ptr-bounds load-indirect-suc prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (load-from-slot k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (load-from-slot k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (store-at-slot k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (store-at-slot k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step store-indirect prog fs r ftq ff wfS wf =
  flat-ptr-bounds store-indirect prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step store-indirect-suc prog fs r ftq ff wfS wf =
  flat-ptr-bounds store-indirect-suc prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (lea-slot k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (lea-slot k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (restore-input k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (restore-input k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-reclaim-to k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-reclaim-to k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step instr-call-closure prog fs r ftq ff wfS wf =
  flat-ptr-bounds instr-call-closure prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-init k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-init k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-push k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-push k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-pop k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-pop k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-check k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-check k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-sigop si) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-sigop si) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-load-const p v) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-load-const p v) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-load-code-addr k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-load-code-addr k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step instr-save-closure-reg prog fs r ftq ff wfS wf =
  flat-ptr-bounds instr-save-closure-reg prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-load-tag-lit k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-load-tag-lit k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-reg-op op) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-reg-op op) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-ctrl c) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-ctrl c) prog fs ff (λ { _ () }) wfS wf

-- THE RUN INDUCTION, carrying the store-WF invariant alongside (the alloc
-- step's freshness needs it at every PRE state, and `EntryLike` — all-tag
-- registers, empty memories — starts both off).
run-wf-ptr-bounds : ∀ prog (fs : FlatState) (r : RunAt prog fs)
                  → FlatWF fs × PtrBoundsWF fs
run-wf-ptr-bounds prog fs (mkRunAt ir eq hm reach) = go fs reach
  where go : ∀ (fs' : FlatState) → Reachable prog (ir-stack-budget ir) fs'
           → FlatWF fs' × PtrBoundsWF fs'
        go fs' (reach-start .fs' el _) = entry-flat-wf fs' el , entry-ptr-bounds fs' el
        go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
          let ih = go fs'' r' in
          flat-wf-step i prog fs'' (proj₁ ih) ,
          ptr-bounds-step i prog fs'' (mkRunAt ir eq hm r') ftq
            (frame-op-absurd prog fs'' i (ir , eq) hm ftq)
            (proj₁ ih) (proj₂ ih)

run-ptr-bounds : ∀ prog (fs : FlatState) (r : RunAt prog fs) → PtrBoundsWF fs
run-ptr-bounds prog fs r = proj₂ (run-wf-ptr-bounds prog fs r)

------------------------------------------------------------------------
-- THE DATAFLOW DISCIPLINES ARE THEOREMS (Plan 0.62 wiring, 2026-08-02).
--
-- The emitter's typed shape check (`emitted-shape-check`, M2b) accepts the
-- program; run consistency (`run-meets`, M3) puts the current state inside
-- the checker's expectation at its pc; `check-at` localizes the positive
-- check to the fetched site; and the SITE FACTS (`site-load-ptr`,
-- `site-branch-tag` — proven in `ShapeTable.Sem`) convert expectation +
-- state into exactly the residual conclusions. This is what makes the
-- whole shape layer (ShapeAt, the checker, the interpretation, the store
-- bricks) LOAD-BEARING on the apex path.
------------------------------------------------------------------------

-- the run's program passes the shape check (via `Emitted` + `HeapModed`)
run-shape-check : ∀ prog (fs : FlatState) (r : RunAt prog fs)
                → Σ LabelEnv (λ env →
                    check-shapes env (entry-expect Unit) prog ≡ true)
run-shape-check prog fs r =
  proj₁ chk ,
  subst (λ p → check-shapes (proj₁ chk) (entry-expect Unit) p ≡ true)
        (sym (run-emit r)) (proj₂ chk)
  where chk = emitted-shape-check (run-ir r) (run-heap r)

-- A SLOT READ NEVER FINDS AN UNWRITTEN SLOT (Plan 0.54 rung D).
--
-- This is what makes the `*-empty-*` routes UNREACHABLE. It replaces what the
-- OLD bidirectional `Window` supplied for free: that assertion made the
-- concrete cell unmapped wherever the abstract one was, so an empty-slot read
-- "corresponded" by getting both machines stuck. That was false on frame
-- re-entry, and with `Window` one-directional the read would be a genuine
-- DIVERGENCE — abstract halts, concrete reads the previous frame's data.
--
-- So the emitter's discipline has to rule it out, and it does: `site-ok` now
-- requires a non-`e-any` claim at every slot read, and `MeetsSlot` sends every
-- such claim at `nothing` to `⊥`. Same shape as `slot-read-in-frame` — the
-- checker's site fact, localized by `check-at`, met by `run-meets`.
--
-- `sok` is how the caller says which site this is; every call passes `λ _ → refl`.
slot-read-written : ∀ prog (fs : FlatState) (slot : Slot) (i : AbstractInstr) → RunAt prog fs
                  → fetch prog (fpc fs) ≡ just i
                  → (∀ st → ST.site-ok st i ≡ ST.not-any (ST.slot-get (ST.e-slot st) slot))
                  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ nothing → ⊥
slot-read-written prog fs slot i r ftq sok empty =
  site-slot-written (ST.slot-get (ST.e-slot st) slot) claim met
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    claim : ST.not-any (ST.slot-get (ST.e-slot st) slot) ≡ true
    claim = trans (sym (sok st))
                  (proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                            (trans (sym (fetch-at-pc prog (fpc fs))) ftq)))
    met = subst (λ m → ST.Sem.MeetsSlot FS (ST.slot-get (ST.e-slot st) slot) (falloc fs) m (floc fs))
                empty
                (proj₂ (proj₂ (proj₂ (run-meets prog fs r env chk))) slot)

load-indirect-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs
                         → fetch prog (fpc fs) ≡ just load-indirect
                         → Σ (ValueLocation FS) (λ loc →
                             readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
load-indirect-target-ptr prog fs r ftq =
  site-load-ptr (e-in1 st) ok (proj₁ (run-meets prog fs r env chk))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.is-ptr (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))

load-indirect-suc-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs
                             → fetch prog (fpc fs) ≡ just load-indirect-suc
                             → Σ (ValueLocation FS) (λ loc →
                                 readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
load-indirect-suc-target-ptr prog fs r ftq =
  site-load-ptr (e-in1 st) ok (proj₁ (run-meets prog fs r env chk))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.is-ptr (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))

-- THE STORE TARGET DISCIPLINE (2026-08-03): at an emitted store site the
-- target register holds a POINTER — the shape checker requires the block
-- under construction there (`site-ok … store-indirect = is-fresh`), which
-- is the emitter's initialization discipline (allocate, fill, then share).
-- This is what retires `store-indirect{,-suc}-bad`: the divergent route
-- (a store THROUGH a non-pointer, where the concrete `mov [rdi],rax`
-- writes at the value's encoding and continues while the abstract machine
-- halts) is UNREACHABLE in emitted code, so it needs no correspondence.
store-indirect-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs
                          → fetch prog (fpc fs) ≡ just store-indirect
                          → Σ (ValueLocation FS) (λ loc →
                              readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
store-indirect-target-ptr prog fs r ftq =
  site-store-ptr (e-in1 st) ok (proj₁ (run-meets prog fs r env chk))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.is-fresh (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))

store-indirect-suc-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs
                              → fetch prog (fpc fs) ≡ just store-indirect-suc
                              → Σ (ValueLocation FS) (λ loc →
                                  readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
store-indirect-suc-target-ptr prog fs r ftq =
  site-store-ptr (e-in1 st) ok (proj₁ (run-meets prog fs r env chk))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.is-fresh (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))

-- the non-pointer routes of a store site are absurd
store-nonptr-absurd : ∀ prog (fs : FlatState) {v : StoredValue FS} → RunAt prog fs
                    → fetch prog (fpc fs) ≡ just store-indirect
                    → readReg (regs (floc fs)) Input1 ≡ v
                    → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥)
                    → ⊥
store-nonptr-absurd prog fs r ftq i-eq nptr =
  nptr (proj₁ wits) (trans (sym i-eq) (proj₂ wits))
  where wits = store-indirect-target-ptr prog fs r ftq

store-suc-nonptr-absurd : ∀ prog (fs : FlatState) {v : StoredValue FS} → RunAt prog fs
                        → fetch prog (fpc fs) ≡ just store-indirect-suc
                        → readReg (regs (floc fs)) Input1 ≡ v
                        → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥)
                        → ⊥
store-suc-nonptr-absurd prog fs r ftq i-eq nptr =
  nptr (proj₁ wits) (trans (sym i-eq) (proj₂ wits))
  where wits = store-indirect-suc-target-ptr prog fs r ftq

branch-tag-scrutinee-wf : ∀ prog (fs : FlatState) (m : LabelId) → RunAt prog fs
                        → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero m))
                        → Σ (ValueLocation FS) (λ loc → Σ ℕ (λ k →
                            (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                            × (readLoc (floc fs) loc ≡ just (SV-Tag k))))
branch-tag-scrutinee-wf prog fs m r ftq =
  repack (site-branch-tag (e-in1 st) ok (proj₁ (run-meets prog fs r env chk)))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.tag-site-ok (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))
    repack : Σ (ValueLocation FS) (λ loc →
               (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
               × Σ ℕ (λ t → readLoc (floc fs) loc ≡ just (SV-Tag t)))
           → Σ (ValueLocation FS) (λ loc → Σ ℕ (λ k →
               (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
               × (readLoc (floc fs) loc ≡ just (SV-Tag k))))
    repack (loc , i-eq , t , r-eq) = loc , t , i-eq , r-eq

-- THE FOUR IN-BOUNDS FACTS THE BLOCK-STEPS CONSUME, now read off the
-- invariant (the store pair was residual until 2026-08-01; the load pair
-- combines the `-target-ptr` residual's pointer shape with the theorem).
store-indirect-inbounds : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunAt prog fs
                        → fetch prog (fpc fs) ≡ just store-indirect
                        → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                        → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))
store-indirect-inbounds prog fs hl r ftq eq =
  ptr-bounds-cell fs Input1 hl (run-ptr-bounds prog fs r) eq

store-indirect-suc-inbounds : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunAt prog fs
                            → fetch prog (fpc fs) ≡ just store-indirect-suc
                            → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                            → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))
store-indirect-suc-inbounds prog fs hl r ftq eq =
  ptr-bounds-suc fs Input1 hl (run-ptr-bounds prog fs r) eq

load-indirect-target-wf : ∀ prog (fs : FlatState) → RunAt prog fs
                        → fetch prog (fpc fs) ≡ just load-indirect
                        → Σ (ValueLocation FS) (λ loc →
                            (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                            × (∀ hl → loc ≡ AtDynamic hl
                               → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))))
load-indirect-target-wf prog fs r ftq with load-indirect-target-ptr prog fs r ftq
... | loc , eq = loc , eq ,
  λ hl leq → ptr-bounds-cell fs Input1 hl (run-ptr-bounds prog fs r)
               (trans eq (cong SV-Ptr leq))

load-indirect-suc-target-wf : ∀ prog (fs : FlatState) → RunAt prog fs
                            → fetch prog (fpc fs) ≡ just load-indirect-suc
                            → Σ (ValueLocation FS) (λ loc →
                                (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                                × (∀ hl → loc ≡ AtDynamic hl
                                   → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))))
load-indirect-suc-target-wf prog fs r ftq with load-indirect-suc-target-ptr prog fs r ftq
... | loc , eq = loc , eq ,
  λ hl leq → ptr-bounds-suc fs Input1 hl (run-ptr-bounds prog fs r)
               (trans eq (cong SV-Ptr leq))

-- The event-trace induction, fully with-FREE (J-style aux bridges for every case
-- split — no `with … in` goal-abstraction). `ccc-step` is the reusable CCC engine:
-- one abstract step ↦ its compiled block (block-step-any) mirrored into run-events
-- (the proven block-run-exec), then recurse (events-agree). Mutual on the fuel n.
mutual
  events-agree : ∀ {hv : HeapView} N (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                   prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs
               → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s ≡ flat-events N prog fs)
  events-agree {hv} zero    ev env prog fs s cc wf = 0 , refl
  events-agree {hv} (suc n) ev env prog fs s cc wf = go-h (halted (floc fs)) refl
    where go-h : ∀ (b : Bool) → halted (floc fs) ≡ b
              → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                           ≡ flat-events-step b n prog fs)
          go-h true  eqh = 1 , RTx.run-events-halted val-x86-64 ev env 0 (compile-trace prog) s
                                 (trans (C.halt-eq (dataCorr cc)) eqh)
          go-h false eqh = events-running n ev env prog fs s cc wf eqh

  -- Running step: `flat-events (suc n)` (halted false) reduces to the abstract
  -- fetch-dispatch; case the fetch via a J-style `go` bridge and route.
  events-running : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                     prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                              ≡ flat-events-fetch (fetch prog (fpc fs)) n prog fs)
  events-running {hv} n ev env prog fs s cc wf h = go (fetch prog (fpc fs)) refl
    where go : ∀ (mi : Maybe AbstractInstr) → fetch prog (fpc fs) ≡ mi
             → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                          ≡ flat-events-fetch mi n prog fs)
          go nothing  eqf = events-running-end   n ev env prog fs s cc wf h eqf
          go (just i) eqf = events-running-fetch n ev env prog fs s i cc wf h eqf

  -- Per-instruction dispatch (with-free constructor matching on `i`). c-label is a
  -- CCC step (event-of []; flat-exec-instr leaves `floc` unchanged so halted-post =
  -- h). All other `i` route to the residual for now.
  events-running-fetch : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                           prog fs s i → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                       → fetch prog (fpc fs) ≡ just i
                       → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                             ≡ event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs))
  -- The straight-line CCC cases: register moves / reg-ops / load-tag-lit / c-label all
  -- leave `halted` untouched (exec-abstract is a `record {regs=…}` or flat-exec-instr
  -- just bumps fpc), so halted-post = h and event-of = [] (refl). Each feeds its PROVEN
  -- block-step lemma directly to ccc-step-bs (no block-step-any dispatcher — deleted).
  events-running-fetch {hv} n ev env prog fs s mov-to-output          cc wf h ftq = ccc-step-bs n ev env prog fs s mov-to-output          (block-step-mov-to-output          prog fs s cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s mov-to-input           cc wf h ftq = ccc-step-bs n ev env prog fs s mov-to-input           (block-step-mov-to-input           prog fs s cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s mov-output-to-input2   cc wf h ftq = ccc-step-bs n ev env prog fs s mov-output-to-input2   (block-step-mov-output-to-input2   prog fs s cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s mov-input2-to-output   cc wf h ftq = ccc-step-bs n ev env prog fs s mov-input2-to-output   (block-step-mov-input2-to-output   prog fs s cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-reg-op scratch-one)        cc wf h ftq = ccc-step-bs n ev env prog fs s (instr-reg-op scratch-one)        (block-step-scratch-one        prog fs s cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-reg-op scratch-zero)       cc wf h ftq = ccc-step-bs n ev env prog fs s (instr-reg-op scratch-zero)       (block-step-scratch-zero       prog fs s cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-reg-op count-zero)        cc wf h ftq = ccc-step-bs n ev env prog fs s (instr-reg-op count-zero)        (block-step-count-zero        prog fs s cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-reg-op scratch-load-count) cc wf h ftq = ccc-step-bs n ev env prog fs s (instr-reg-op scratch-load-count) (block-step-scratch-load-count prog fs s cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-reg-op scratch-dec) cc wf h ftq = scratch-dec-step n ev env prog fs s cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s (instr-reg-op count-inc) cc wf h ftq = count-inc-step n ev env prog fs s cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s load-indirect cc wf h ftq = load-indirect-step n ev env prog fs s cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s load-indirect-suc cc wf h ftq = load-indirect-suc-step n ev env prog fs s cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s store-indirect cc wf h ftq = store-indirect-step n ev env prog fs s cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s store-indirect-suc cc wf h ftq = store-indirect-suc-step n ev env prog fs s cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s (load-from-slot slot) cc wf h ftq = load-from-slot-step n ev env prog fs s slot cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s (store-at-slot slot) cc wf h ftq =
    ccc-step-bs {hv} n ev env prog fs s (store-at-slot slot)
      (block-step-store-at-slot prog fs s slot cc h ftq
         (slot-read-in-frame prog fs slot (store-at-slot slot) (inv-run wf) ftq refl)
         (slot-heap-disj {hv} fs s (dataCorr cc) slot)) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (restore-input slot) cc wf h ftq = restore-input-step n ev env prog fs s slot cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s (worklist-push slot) cc wf h ftq =
    ccc-step-bs {hv} n ev env prog fs s (worklist-push slot)
      (block-step-worklist-push prog fs s slot cc h ftq
         (slot-read-in-frame prog fs slot (worklist-push slot) (inv-run wf) ftq refl)
         (slot-heap-disj {hv} fs s (dataCorr cc) slot)) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (worklist-pop slot) cc wf h ftq = worklist-pop-step n ev env prog fs s slot cc wf h ftq
  -- THE FOUR FRAME OPS ARE UNREACHABLE (plan 0.54 rung D, item 2): `ir-to-trace`
  -- emits none of them, and `FlatInv` carries `Emitted prog`. See `FrameFree`.
  events-running-fetch {hv} n ev env prog fs s (instr-alloc-stack k) cc wf h ftq =
    ⊥-elim (frame-op-absurd prog fs (instr-alloc-stack k) (run-emitted (inv-run wf)) (run-heap (inv-run wf)) ftq)
  events-running-fetch {hv} n ev env prog fs s (instr-alloc-heap k) cc wf h ftq =
    ccc-step-bs n ev env prog fs s (instr-alloc-heap k)
      (block-step-alloc-heap prog fs s k cc h ftq
         (wf-regs (inv-wf wf) Input1) (wf-regs (inv-wf wf) Input2)
         (wf-regs (inv-wf wf) Scratch) (wf-regs (inv-wf wf) Count)
         (λ hl _ → wf-heap (inv-wf wf) hl) (wf-stack (inv-wf wf))
         (λ hl eq → wf-fresh (inv-wf wf) hl (≤-reflexive (sym eq)))
         (heap-room prog fs s k (inv-run wf) cc ftq)) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-dealloc-stack k) cc wf h ftq =
    ⊥-elim (frame-op-absurd prog fs (instr-dealloc-stack k) (run-emitted (inv-run wf)) (run-heap (inv-run wf)) ftq)
  events-running-fetch {hv} n ev env prog fs s (instr-push-frame k) cc wf h ftq =
    ⊥-elim (frame-op-absurd prog fs (instr-push-frame k) (run-emitted (inv-run wf)) (run-heap (inv-run wf)) ftq)
  events-running-fetch {hv} n ev env prog fs s instr-pop-frame cc wf h ftq =
    ⊥-elim (frame-op-absurd prog fs instr-pop-frame (run-emitted (inv-run wf)) (run-heap (inv-run wf)) ftq)
  events-running-fetch {hv} n ev env prog fs s (instr-load-const fits-int v) cc wf h ftq =
    ccc-step-bs {hv} n ev env prog fs s (instr-load-const fits-int v)
      (block-step-load-const prog fs s v cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-load-const fits-float v) cc wf h ftq =
    ccc-step-bs {hv} n ev env prog fs s (instr-load-const fits-float v)
      (block-step-load-const-float prog fs s v cc h ftq) wf ftq h refl h
  -- plan 0.61: with stack addresses, the indexed cursor computes a real address.
  -- `lea-indexed` joined the unemittable set 2026-08-01 (heap-linked stacks,
  -- no indexed cursor) — the route is absurd, like the frame ops and the loop.
  events-running-fetch {hv} n ev env prog fs s (lea-indexed slot) cc wf h ftq =
    ⊥-elim (frame-op-absurd prog fs (lea-indexed slot) (run-emitted (inv-run wf)) (run-heap (inv-run wf)) ftq)
  -- plan 0.61: a stack POINTER now has an address, so lea-slot routes.
  events-running-fetch {hv} n ev env prog fs s (lea-slot slot) cc wf h ftq =
    ccc-step-bs {hv} n ev env prog fs s (lea-slot slot)
      (block-step-lea-slot prog fs s slot cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-load-code-addr k) cc wf h ftq =
    ccc-step-bs {hv} n ev env prog fs s (instr-load-code-addr k) (block-step-load-code-addr prog fs s k cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s instr-save-closure-reg cc wf h ftq =
    ccc-step-bs {hv} n ev env prog fs s instr-save-closure-reg (block-step-save-closure-reg prog fs s cc h ftq) wf ftq h refl h
  -- Trivial cata bookkeeping (x86-len 0, flat identity): proven block-step ⇒ ccc-step-bs.
  events-running-fetch {hv} n ev env prog fs s (worklist-init k) cc wf h ftq = ccc-step-bs n ev env prog fs s (worklist-init k) (block-step-worklist-init prog fs s k cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (worklist-check k) cc wf h ftq = ccc-step-bs n ev env prog fs s (worklist-check k) (block-step-worklist-check prog fs s k cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-reclaim-to k) cc wf h ftq = ccc-step-bs n ev env prog fs s (instr-reclaim-to k) (block-step-reclaim-to prog fs s k cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-load-tag-lit k) cc wf h ftq = ccc-step-bs n ev env prog fs s (instr-load-tag-lit k) (block-step-load-tag-lit prog fs s k cc h ftq) wf ftq h refl h
  events-running-fetch {hv} n ev env prog fs s (instr-ctrl (c-label m)) cc wf h ftq = ccc-step-bs n ev env prog fs s (instr-ctrl (c-label m)) (block-step-c-label prog fs s m cc h ftq) wf ftq h refl h
  -- Plan 0.63 step 2a: NEITHER CLOSURE MARKER HAS A PRODUCER yet
  -- (`ir-to-trace` is main-only), and both now MOVE THE FRAME — the body's
  -- `subq`/`addq` reservation rides on them. So both route absurdly, via
  -- the same `Emitted`/`FrameFreeI` fence as the frame ops themselves.
  -- What replaces these when the bodies land (2b-2d): `c-thunk` composes a
  -- `step-label` fetch with `block-step-alloc-stack` (its freshness premises
  -- coming from `untouched` + the high-water mark, plus the honest
  -- `stack-room`); `c-ret` additionally needs the `FlatCorr` component
  -- relating the ghost `fret` to the machine stack.
  events-running-fetch {hv} n ev env prog fs s (instr-ctrl (c-thunk m b)) cc wf h ftq =
    thunk-step n ev env prog fs s m b cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s (instr-ctrl (c-ret b)) cc wf h ftq =
    ret-step n ev env prog fs s b cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s (instr-ctrl (c-jmp m)) cc wf h ftq = cjmp-step n ev env prog fs s m cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s (instr-ctrl (c-branch-scratch-zero m)) cc wf h ftq = branch-step n ev env prog fs s m cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s (instr-ctrl (c-branch-tag-zero m)) cc wf h ftq = tag-branch-step n ev env prog fs s m cc wf h ftq
  events-running-fetch {hv} n ev env prog fs s (instr-sigop si) cc wf h ftq = sigop-step n ev env prog fs s si cc wf h ftq
  -- WHAT IS LEFT UNROUTED, now one clause each instead of a catch-all over `i`
  -- (2026-07-31). Naming them separately is what showed that only TWO of the
  -- three are real: `instr-loop` has no producer at all.
  --
  -- `instr-loop` — a RETIRED FOSSIL. The cata codegen compiles to flat control
  -- (`c-label`/`c-jmp`/`c-branch-*`), so `ir-to-trace` never emits it and the
  -- route is UNREACHABLE, exactly like the four frame ops.
  events-running-fetch {hv} n ev env prog fs s (instr-loop body) cc wf h ftq =
    ⊥-elim (frame-op-absurd prog fs (instr-loop body) (run-emitted (inv-run wf)) (run-heap (inv-run wf)) ftq)
  -- `instr-case-on-tag` — GENUINELY EMITTED (`case f g`, and the Tier-2 functor
  -- walks). One flat step runs a whole nested trace through `exec-case-dispatch`
  -- → `exec-trace`, while the x86 side is a `cmp`/`je`/branch-block: this needs a
  -- multi-step, TRACE-level correspondence, not a block-step. It is the last
  -- real coverage gap, and `conc-flat-sim-nested` at the apex is its other half.
  -- item 6: `case` compiles to flat control — `instr-case-on-tag` has no
  -- producer, so the route is absurd like the frame ops and the loop.
  events-running-fetch {hv} n ev env prog fs s (instr-case-on-tag f g) cc wf h ftq =
    ⊥-elim (frame-op-absurd prog fs (instr-case-on-tag f g) (run-emitted (inv-run wf)) (run-heap (inv-run wf)) ftq)
  -- `instr-call-closure` — GENUINELY EMITTED (`apply`), and a MODEL gap rather
  -- than a proof gap: the abstract semantics is the IDENTITY while the concrete
  -- `call *0x8(%r12)` transfers control. Closing it needs the abstract machine to
  -- model the call, not more proof effort here.
  events-running-fetch {hv} n ev env prog fs s instr-call-closure cc wf h ftq =
    events-running-call n ev env prog fs s cc wf h ftq

  -- The reusable CCC engine, GENERALISED to take an explicit BlockStep: one abstract
  -- step `i` (event-of i fs = [], flat step leaves the machine running: hpost) ↦ its
  -- compiled block `X.exec (x86-len i)` (the given BlockStep), mirrored into run-events
  -- (block-run-exec), then recurse via events-agree. Taking the BlockStep explicitly
  -- lets witnessed cases (c-jmp with its found-label, …) feed their PROVEN block-step
  -- lemma rather than routing through block-step-any's residual.
  -- `hv'` is the POST view, and it is the only one that appears: `BlockStepAt
  -- hv hv'` discards its first argument definitionally, so a step that LEAVES
  -- the view it arrived at needs nothing special here. `instr-alloc-heap`
  -- (extends the view) and `c-thunk` (DESCENDS it, `C.descend-view`) both feed
  -- this unchanged.
  ccc-step-bs : ∀ {hv' : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                  prog fs s i → BlockStep hv' prog fs s i → FlatInv ev env prog fs
              -- the SITE and the pre-state halt flag: what `flat-inv-step` needs to
              -- extend the run context by this step (`reach-step`)
              → fetch prog (fpc fs) ≡ just i → halted (floc fs) ≡ false
              → event-of i fs ≡ []
              → halted (floc (flat-exec-instr i prog fs)) ≡ false
              → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                    ≡ event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs))
  ccc-step-bs n ev env prog fs s i bs wf ftq h ev[] hpost = (x86-len i + proj₁ rec) , result
    where -- the post-state invariant comes from the FLAT-MACHINE theorem, once,
          -- for every instruction (`FlatStoreWF.flat-wf-step`).
          rec = events-agree n ev env prog (flat-exec-instr i prog fs) (proj₁ bs)
                             (proj₂ (proj₂ bs)) (flat-inv-step i prog fs ftq h wf)
          result : RTx.run-events val-x86-64 ev env (x86-len i + proj₁ rec) (compile-trace prog) s
                 ≡ event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs)
          result rewrite ev[] =
            trans (block-run-exec ev env (x86-len i) (proj₁ rec) (compile-trace prog) s
                     (proj₁ (proj₂ bs)) (trans (C.halt-eq (dataCorr (proj₂ (proj₂ bs)))) hpost))
                  (proj₂ rec)

  -- THE CLOSURE BODY ENTRY — `c-thunk m b` ↔ `label (thunk m) ; sub rsp, 8b`.
  --
  -- This was `events-running-thunk`, a POSTULATE, until the `Window` weakening
  -- and `do-thunk`'s frame clear (D090) made `block-step-c-thunk` provable.
  -- What is left to supply here is the LAYOUT: where the descended high-water
  -- mark lands, and the one honest resource fact that it is legal.
  --
  -- `lo'` — THE NEW HIGH-WATER MARK — is `lo hv ⊓ (%rsp ∸ 8b)`. The meet, not
  -- either side: `lo` must not RISE (it is the lowest `%rsp` EVER held, and
  -- `untouched` about `[hfront, lo)` would be a claim about cells a deeper
  -- earlier frame has written), and it must not exceed the new `%rsp` (or the
  -- reserved frame would sit inside the region called virgin). Both bounds
  -- (`lo'≤lo`, `lo'≤rsp`) are then the two meet projections.
  --
  -- `front-lo'` — that the descended mark stays above the heap — is the ONLY
  -- part that is not free, and it is exactly `stack-room`: from
  -- `hfront + 8b ≤ %rsp` truncated subtraction gives `hfront ≤ %rsp ∸ 8b`, and
  -- `front-lo hv` gives the other half of the meet. The same premise also
  -- yields `fits` (`8b ≤ %rsp`, the `sub` does not underflow) — which is why
  -- the parameter is stated additively rather than as its two consequences.
  thunk-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                 prog fs s (m : LabelId) (b : ℕ) → CompiledCorr hv prog fs s → FlatInv ev env prog fs
             → halted (floc fs) ≡ false
             → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk m b))
             → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                   ≡ event-of (instr-ctrl (c-thunk m b)) fs
                     ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-thunk m b)) prog fs))
  thunk-step {hv} n ev env prog fs s m b cc wf h ftq =
    -- (the post view is the DESCENDED one, so `ccc-step-bs`'s `hv'` is left to
    -- inference — pinning it to `hv` here would demand `lo' ≡ lo hv`)
    ccc-step-bs n ev env prog fs s (instr-ctrl (c-thunk m b))
      (block-step-c-thunk prog fs s m b cc h ftq lo' lo'≤lo front-lo' lo'≤rsp fits)
      wf ftq h refl h
    where
      -- the site's resource fact: the reservation stays above the heap frontier
      room : C.hfront hv + slots b ≤ X.readReg (X.State.regs s) rsp
      room = stack-room prog fs s m b (inv-run wf) cc ftq
      fits : slots b ≤ X.readReg (X.State.regs s) rsp
      fits = ≤-trans (m≤n+m (slots b) (C.hfront hv)) room
      front-rsp : C.hfront hv ≤ X.readReg (X.State.regs s) rsp ∸ slots b
      front-rsp = m+n≤o⇒m≤o∸n (C.hfront hv) room
      lo' : ℕ
      lo' = C.lo hv ⊓ (X.readReg (X.State.regs s) rsp ∸ slots b)
      lo'≤lo : lo' ≤ C.lo hv
      lo'≤lo = m⊓n≤m (C.lo hv) (X.readReg (X.State.regs s) rsp ∸ slots b)
      lo'≤rsp : lo' ≤ X.readReg (X.State.regs s) rsp ∸ slots b
      lo'≤rsp = m⊓n≤n (C.lo hv) (X.readReg (X.State.regs s) rsp ∸ slots b)
      front-lo' : C.hfront hv ≤ lo'
      front-lo' = ⊓-glb (C.front-lo hv) front-rsp

  -- THE RETURN — a THEOREM, by collision (2026-08-06, D091).
  --
  -- Two facts about the ABSTRACT machine meet here and cannot both hold of one
  -- state, so the route is `⊥`:
  --
  --   `ret-site-owes` — a reachable `c-ret` is inside a body some call entered,
  --                     and that call pushed the return pc: `fret` is a cons;
  --   `run-no-ret`    — a THEOREM: `fret` is `[]` in every reachable state,
  --                     because `instr-call-closure` is the identity.
  --
  -- So this is NOT the frame-op `⊥-elim` pattern (an instruction with no
  -- producer). `c-ret` IS emitted — `ir-to-trace'`'s `curry` clause emits
  -- `c-jmp end ∷ c-thunk ℓ b ∷ body ++ c-ret b ∷ c-label end ∷ []`, and the
  -- jump is exactly what stops the parent falling into the body. What is
  -- missing is the ENTRY: nothing performs the call, so the body's return runs
  -- in no reachable state, and the honest correspondence for it cannot be
  -- written before the call is modelled. Closing `events-running-call` is what
  -- makes this route live again — and then `run-no-ret` fails to typecheck,
  -- which is the check that the model really changed.
  ret-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
               prog fs s (b : ℕ) → CompiledCorr hv prog fs s → FlatInv ev env prog fs
           → halted (floc fs) ≡ false
           → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
           → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                 ≡ event-of (instr-ctrl (c-ret b)) fs
                   ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-ret b)) prog fs))
  ret-step {hv} n ev env prog fs s b cc wf h ftq =
    ⊥-elim (clash (ret-site-owes prog fs b (inv-run wf) ftq)
                  (proj₁ (run-no-ret prog fs (inv-run wf))))
    where clash : Σ ℕ (λ pc' → Σ (List ℕ) (λ rest → fret fs ≡ pc' ∷ rest))
                → fret fs ≡ [] → ⊥
          clash (pc' , rest , owes) empty = nil≢cons (trans (sym empty) owes)
            where nil≢cons : ∀ {A : Set} {x : ℕ} {xs : List ℕ} → [] ≡ x ∷ xs → A
                  nil≢cons ()

  -- CONTROL c-jmp: case the found label (J-bridge on find-label, no with). Found ⇒
  -- do-jump just bumps fpc (halted preserved: hpost=h) and the PROVEN block-step-c-jmp
  -- gives the BlockStep ⇒ ccc-step-bs. Missing ⇒ both machines halt on the missing
  -- label — the small `cjmp-miss` residual (the label-missing halt correspondence).
  cjmp-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                prog fs s m → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
              → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp m))
              → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                    ≡ event-of (instr-ctrl (c-jmp m)) fs
                      ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs))
  cjmp-step {hv} n ev env prog fs s m cc wf h ftq = go-fl (find-label prog m) refl
    where go-fl : ∀ (mj : Maybe ℕ) → find-label prog m ≡ mj
                → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                      ≡ event-of (instr-ctrl (c-jmp m)) fs
                        ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs))
          go-fl (just j) fl-eq =
            ccc-step-bs {hv} n ev env prog fs s (instr-ctrl (c-jmp m))
              (block-step-c-jmp prog fs s m j cc h ftq fl-eq) wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs)) ≡ false
                  hpost rewrite fl-eq = h
          go-fl nothing fl-eq = 2 , result
            where
              halt-s : X.State.halted s ≡ false
              halt-s = trans (C.halt-eq (dataCorr cc)) h
              fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (jmp (once m))
              fetch-x86 = trans (cong (X.fetch (compile-trace prog)) (pc-off cc))
                                (fetch-block-head prog (fpc fs) (instr-ctrl (c-jmp m)) ftq)
              s' : X.State
              s' = record s { halted = true }
              -- a concrete jump to a MISSING label HALTS (it does not get stuck)
              step-eq : X.execInstr (compile-trace prog) s (jmp (once m)) ≡ just s'
              step-eq rewrite find-label-none-corr prog m fl-eq = refl
              hpost : halted (floc (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs)) ≡ true
              hpost rewrite fl-eq = refl
              result : RTx.run-events val-x86-64 ev env 2 (compile-trace prog) s
                     ≡ event-of (instr-ctrl (c-jmp m)) fs
                       ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs)
              result =
                trans (RTx.run-events-noncall val-x86-64 ev env 1 (compile-trace prog) s
                         (jmp (once m)) halt-s fetch-x86 refl step-eq)
                      (trans (RTx.run-events-halted val-x86-64 ev env 0 (compile-trace prog) s' refl)
                             (sym (flat-events-halted n prog
                                    (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs) hpost)))

  -- CONTROL c-branch-scratch-zero: J-bridge on the Scratch value AND find-label. A tag
  -- `SV-Tag k` + a resolvable target ⇒ the PROVEN block-step-c-branch-scratch-zero (both
  -- taken k=0 and not-taken k=suc). Non-tag ⇒ IMPOSSIBLE by `FlatRegTagWF`; missing label ⇒
  -- branch-label-miss. hpost: do-branch stays running (taken jumps to the found label via
  -- fl-eq, not-taken advances) — cased on k after rewriting sc-eq (then fl-eq for k=0).
  branch-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                  prog fs s m → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
              → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero m))
              → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                    ≡ event-of (instr-ctrl (c-branch-scratch-zero m)) fs
                      ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-branch-scratch-zero m)) prog fs))
  branch-step {hv} n ev env prog fs s m cc wf h ftq = go-sv (readReg (regs (floc fs)) Scratch) refl
    where
      -- Pattern-match k (not `with`, which errors on the bound variable) so
      -- sv-is-zero (SV-Tag k) reduces: k=0 taken (do-jump the found label), k=suc
      -- not-taken (advance) — both leave the machine running.
      go-fl : ∀ k → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
            → ∀ (mj : Maybe ℕ) → find-label prog m ≡ mj
            → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                  ≡ event-of (instr-ctrl (c-branch-scratch-zero m)) fs
                    ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-branch-scratch-zero m)) prog fs))
      go-fl zero sc-eq (just j) fl-eq =
        ccc-step-bs {hv} n ev env prog fs s (instr-ctrl (c-branch-scratch-zero m))
          (block-step-c-branch-scratch-zero prog fs s m zero j cc h ftq sc-eq fl-eq) wf ftq h refl hpost
        where hpost : halted (floc (flat-exec-instr (instr-ctrl (c-branch-scratch-zero m)) prog fs)) ≡ false
              hpost rewrite sc-eq | fl-eq = h
      go-fl (suc k') sc-eq (just j) fl-eq =
        ccc-step-bs {hv} n ev env prog fs s (instr-ctrl (c-branch-scratch-zero m))
          (block-step-c-branch-scratch-zero prog fs s m (suc k') j cc h ftq sc-eq fl-eq) wf ftq h refl hpost
        where hpost : halted (floc (flat-exec-instr (instr-ctrl (c-branch-scratch-zero m)) prog fs)) ≡ false
              hpost rewrite sc-eq = h
      -- NOT TAKEN: the missing label is never consulted, so this is the ordinary
      -- fall-through step (no label premise — `block-step-c-branch-nz`).
      go-fl (suc k') sc-eq nothing fl-eq =
        ccc-step-bs {hv} n ev env prog fs s (instr-ctrl (c-branch-scratch-zero m))
          (block-step-c-branch-nz prog fs s m k' cc h ftq sc-eq) wf ftq h refl hpost
        where hpost : halted (floc (flat-exec-instr (instr-ctrl (c-branch-scratch-zero m)) prog fs)) ≡ false
              hpost rewrite sc-eq = h
      -- TAKEN + MISSING: `cmp` then a `je` whose label is absent — the concrete
      -- machine HALTS (as `jmp` does), and so does `do-jump nothing`. Both [].
      go-fl zero sc-eq nothing fl-eq = 3 , result
        where
          dc = dataCorr cc
          halt-s : X.State.halted s ≡ false
          halt-s = trans (C.halt-eq dc) h
          rbx0 : X.readReg (X.State.regs s) rbx ≡ 0
          rbx0 = trans (C.rbx-eq dc) (cong (C.enc-sv hv) sc-eq)
          fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (cmp (reg rbx) (imm 0))
          fetch-cmp = trans (cong (X.fetch (compile-trace prog)) (pc-off cc))
                            (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-scratch-zero m)) ftq)
          post-cmp : X.State
          post-cmp = record s { flags = X.mkflags (X.readReg (X.State.regs s) rbx ≡ᵇ 0)
                                                  (X.readReg (X.State.regs s) rbx X.<ᵇ 0) false
                              ; pc = X.State.pc s + 1 }
          step-cmp : X.execInstr (compile-trace prog) s (cmp (reg rbx) (imm 0)) ≡ just post-cmp
          step-cmp = b-cmp-reg-imm (compile-trace prog) s rbx 0
          fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once m))
          fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) (pc-off cc))
                           (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-scratch-zero m)) ftq)
          post-je : X.State
          post-je = record post-cmp { halted = true }
          step-je : X.execInstr (compile-trace prog) post-cmp (je (once m)) ≡ just post-je
          step-je rewrite rbx0 | find-label-none-corr prog m fl-eq = refl
          hpost : halted (floc (flat-exec-instr (instr-ctrl (c-branch-scratch-zero m)) prog fs)) ≡ true
          hpost rewrite sc-eq | fl-eq = refl
          result : RTx.run-events val-x86-64 ev env 3 (compile-trace prog) s
                 ≡ event-of (instr-ctrl (c-branch-scratch-zero m)) fs
                   ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-branch-scratch-zero m)) prog fs)
          result =
            trans (RTx.run-events-noncall val-x86-64 ev env 2 (compile-trace prog) s
                     (cmp (reg rbx) (imm 0)) halt-s fetch-cmp refl step-cmp)
            (trans (RTx.run-events-noncall val-x86-64 ev env 1 (compile-trace prog) post-cmp
                     (je (once m)) halt-s fetch-je refl step-je)
            (trans (RTx.run-events-halted val-x86-64 ev env 0 (compile-trace prog) post-je refl)
                   (sym (flat-events-halted n prog
                          (flat-exec-instr (instr-ctrl (c-branch-scratch-zero m)) prog fs) hpost))))
      go-sv : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Scratch ≡ sv
            → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                  ≡ event-of (instr-ctrl (c-branch-scratch-zero m)) fs
                    ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-branch-scratch-zero m)) prog fs))
      go-sv (SV-Tag k)    sc-eq = go-fl k sc-eq (find-label prog m) refl
      -- NON-TAG: IMPOSSIBLE, not residual. `Scratch` holds a tag in every
      -- reachable state (`FlatRegTagWF`), which is what makes the concrete
      -- `cmp rbx,0` agree with the abstract `sv-is-zero`.
      go-sv (SV-Ptr p)    sc-eq = ⊥-elim (flat-scratch-is-tag fs (SV-Ptr p) (inv-regtag wf) sc-eq)
      go-sv (SV-Lit pr v) sc-eq = ⊥-elim (flat-scratch-is-tag fs (SV-Lit pr v) (inv-regtag wf) sc-eq)
      go-sv (SV-Code c)   sc-eq = ⊥-elim (flat-scratch-is-tag fs (SV-Code c) (inv-regtag wf) sc-eq)

  -- CONTROL c-branch-tag-zero: the condition reads a tag THROUGH Input1's pointer. Chain
  -- load-indirect's witness bridge (Input1 ⇒ dynamic ptr hl; heapMem hl ⇒ just (SV-Tag k))
  -- with the branch's find-label + k pattern-match, then the PROVEN block-step-c-branch-
  -- tag-zero (both taken/not-taken). Liveness now rides `FlatCorr.dom-written`. hpost reduces
  -- flat-read-tag via i-eq/h-eq (as load-indirect), then do-branch as branch-step.
  tag-branch-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                      prog fs s m → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero m))
                  → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                        ≡ event-of (instr-ctrl (c-branch-tag-zero m)) fs
                          ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs))
  tag-branch-step {hv} n ev env prog fs s m cc wf h ftq =
    go-loc (proj₁ wits) (proj₁ (proj₂ wits))
           (proj₁ (proj₂ (proj₂ wits))) (proj₂ (proj₂ (proj₂ wits)))
    where
      -- The scrutinee discipline hands a POINTER (either residence) to a
      -- written TAG cell; the concrete read is derived per residence below
      -- and everything downstream is residence-generic.
      wits = branch-tag-scrutinee-wf prog fs m (inv-run wf) ftq
      go-fl : ∀ loc k → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
            → readLoc (floc fs) loc ≡ just (SV-Tag k)
            → X.readMem (X.State.memory s) (X.effectiveAddr s (base+disp rdi 0)) ≡ just k
            → ∀ (mj : Maybe ℕ) → find-label prog m ≡ mj
            → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                  ≡ event-of (instr-ctrl (c-branch-tag-zero m)) fs
                    ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs))
      go-fl loc zero i-eq r-eq rd (just j) fl-eq =
        ccc-step-bs {hv} n ev env prog fs s (instr-ctrl (c-branch-tag-zero m))
          (block-step-c-branch-tag-zero prog fs s m loc zero j cc h ftq i-eq r-eq rd fl-eq)
          wf ftq h refl hpost
        where hpost : halted (floc (flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs)) ≡ false
              hpost rewrite i-eq | r-eq | fl-eq = h
      go-fl loc (suc k') i-eq r-eq rd (just j) fl-eq =
        ccc-step-bs {hv} n ev env prog fs s (instr-ctrl (c-branch-tag-zero m))
          (block-step-c-branch-tag-zero prog fs s m loc (suc k') j cc h ftq i-eq r-eq rd fl-eq)
          wf ftq h refl hpost
        where hpost : halted (floc (flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs)) ≡ false
              hpost rewrite i-eq | r-eq = h
      -- MISSING LABEL, NOT TAKEN: never consults the label — the ordinary
      -- fall-through via the label-free `block-step-c-branch-tag-nz`.
      go-fl loc (suc k') i-eq r-eq rd nothing fl-eq =
        ccc-step-bs {hv} n ev env prog fs s (instr-ctrl (c-branch-tag-zero m))
          (block-step-c-branch-tag-nz prog fs s m loc k' cc h ftq i-eq r-eq rd)
          wf ftq h refl hpost
        where hpost : halted (floc (flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs)) ≡ false
              hpost rewrite i-eq | r-eq = h
      -- MISSING LABEL, TAKEN: both machines halt — the concrete `je` to an
      -- absent label sets `halted` (`find-label-none-corr`), and
      -- `do-jump nothing` halts the flat machine. Both traces [].
      go-fl loc zero i-eq r-eq rd nothing fl-eq = 3 , result
        where
          dc = dataCorr cc
          halt-s : X.State.halted s ≡ false
          halt-s = trans (C.halt-eq dc) h
          fetch-cmp : X.fetch (compile-trace prog) (X.State.pc s)
                    ≡ just (cmp (mem (base+disp rdi 0)) (imm 0))
          fetch-cmp = trans (cong (X.fetch (compile-trace prog)) (pc-off cc))
                            (fetch-block-head prog (fpc fs) (instr-ctrl (c-branch-tag-zero m)) ftq)
          post-cmp : X.State
          post-cmp = record s { flags = X.mkflags (0 ≡ᵇ 0) (0 X.<ᵇ 0) false
                              ; pc = X.State.pc s + 1 }
          step-cmp : X.execInstr (compile-trace prog) s (cmp (mem (base+disp rdi 0)) (imm 0))
                   ≡ just post-cmp
          step-cmp = execInstr-cmp-mi (compile-trace prog) s (base+disp rdi 0) 0 rd
          fetch-je : X.fetch (compile-trace prog) (X.State.pc post-cmp) ≡ just (je (once m))
          fetch-je = trans (cong (λ p → X.fetch (compile-trace prog) (p + 1)) (pc-off cc))
                           (fetch-block-2nd prog (fpc fs) (instr-ctrl (c-branch-tag-zero m)) ftq)
          post-je : X.State
          post-je = record post-cmp { halted = true }
          step-je : X.execInstr (compile-trace prog) post-cmp (je (once m)) ≡ just post-je
          step-je rewrite find-label-none-corr prog m fl-eq = refl
          hpost : halted (floc (flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs)) ≡ true
          hpost rewrite i-eq | r-eq | fl-eq = refl
          result : RTx.run-events val-x86-64 ev env 3 (compile-trace prog) s
                 ≡ event-of (instr-ctrl (c-branch-tag-zero m)) fs
                   ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs)
          result =
            trans (RTx.run-events-noncall val-x86-64 ev env 2 (compile-trace prog) s
                     (cmp (mem (base+disp rdi 0)) (imm 0)) halt-s fetch-cmp refl step-cmp)
            (trans (RTx.run-events-noncall val-x86-64 ev env 1 (compile-trace prog) post-cmp
                     (je (once m)) halt-s fetch-je refl step-je)
            (trans (RTx.run-events-halted val-x86-64 ev env 0 (compile-trace prog) post-je refl)
                   (sym (flat-events-halted n prog
                          (flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs) hpost))))
      -- THE RESIDENCE DISPATCH: derive the concrete read per residence.
      go-loc : ∀ (loc : ValueLocation FS) (k : ℕ)
             → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
             → readLoc (floc fs) loc ≡ just (SV-Tag k)
             → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                   ≡ event-of (instr-ctrl (c-branch-tag-zero m)) fs
                     ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-branch-tag-zero m)) prog fs))
      -- HEAP: the tag cell is written ⇒ mapped (`dom-written`), `heap-eq`
      -- relates it, and the address is the pointer's encoding.
      go-loc (AtDynamic hl) k i-eq r-eq =
        go-fl (AtDynamic hl) k i-eq r-eq rd-heap (find-label prog m) refl
        where
          dc = dataCorr cc
          addr-val : X.readReg (X.State.regs s) rdi + 0 ≡ haddr hv hl
          addr-val = trans (+-identityʳ (X.readReg (X.State.regs s) rdi))
                           (trans (C.rdi-eq dc) (cong (C.enc-sv hv) i-eq))
          rd-heap : X.readMem (X.State.memory s) (X.effectiveAddr s (base+disp rdi 0)) ≡ just k
          rd-heap = trans (cong (X.readMem (X.State.memory s)) addr-val)
                          (trans (C.heap-eq dc hl (C.dom-written dc hl r-eq))
                                 (cong (C.enc-maybe hv) r-eq))
      -- STACK (the probe's route): the pointer denotes `slot-addr f k'`; the
      -- live-pair theorem pins it to the current frame's live window, where
      -- `rsp-eq` + `stack-eq` relate exactly that cell.
      go-loc (AtStack f k') k i-eq r-eq =
        go-fl (AtStack f k') k i-eq r-eq rd-stack (find-label prog m) refl
        where
          dc = dataCorr cc
          spc = stack-ptr-current prog fs f k' (inv-run wf) i-eq
          st-cf : stackMem (floc fs) (current-frame (falloc fs)) k' ≡ just (SV-Tag k)
          st-cf = trans (cong (λ fr → stackMem (floc fs) fr k') (sym (proj₁ spc))) r-eq
          rdi-val : X.readReg (X.State.regs s) rdi + 0
                  ≡ X.readReg (X.State.regs s) rsp + slot-to-disp k'
          rdi-val = trans (+-identityʳ (X.readReg (X.State.regs s) rdi))
                    (trans (C.rdi-eq dc)
                    (trans (cong (C.enc-sv hv) i-eq)
                    (trans (cong (λ fr → slot-addr FS fr k') (proj₁ spc))
                    (trans (slot-addr-linear FS (current-frame (falloc fs)) k')
                           (cong₂ (λ b w' → b + k' * w') (sym (C.rsp-eq dc)) word-eq)))))
          rd-stack : X.readMem (X.State.memory s) (X.effectiveAddr s (base+disp rdi 0)) ≡ just k
          rd-stack = trans (cong (X.readMem (X.State.memory s)) rdi-val)
                           (C.stack-eq-cur dc k' (proj₂ spc) _ st-cf)

  -- REG-OP scratch-dec: case the Scratch value (J-bridge, no with). A tag ⇒ the PROVEN
  -- block-step-scratch-dec applies (reg-op preserves halted: hpost=h) ⇒ ccc-step-bs.
  -- A non-tag ⇒ the WF residual (a loop counter is always a tag at scratch-dec).
  scratch-dec-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                       prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-dec)
                   → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                         ≡ event-of (instr-reg-op scratch-dec) fs
                           ++ flat-events n prog (flat-exec-instr (instr-reg-op scratch-dec) prog fs))
  scratch-dec-step {hv} n ev env prog fs s cc wf h ftq = go-sv (readReg (regs (floc fs)) Scratch) refl
    where go-sv : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Scratch ≡ sv
                → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                      ≡ event-of (instr-reg-op scratch-dec) fs
                        ++ flat-events n prog (flat-exec-instr (instr-reg-op scratch-dec) prog fs))
          go-sv (SV-Tag k)   sc-eq =
            ccc-step-bs {hv} n ev env prog fs s (instr-reg-op scratch-dec)
              (block-step-scratch-dec prog fs s k cc h ftq sc-eq) wf ftq h refl h
          -- NON-TAG: IMPOSSIBLE (`FlatRegTagWF`). Abstractly `sv-pred` of a
          -- non-tag COERCES to `SV-Tag 0` while the concrete `sub rbx,1`
          -- decrements the encoding — the two only agree on a tag.
          go-sv (SV-Ptr p)    sc-eq = ⊥-elim (flat-scratch-is-tag fs (SV-Ptr p) (inv-regtag wf) sc-eq)
          go-sv (SV-Lit pr v) sc-eq = ⊥-elim (flat-scratch-is-tag fs (SV-Lit pr v) (inv-regtag wf) sc-eq)
          go-sv (SV-Code c)   sc-eq = ⊥-elim (flat-scratch-is-tag fs (SV-Code c) (inv-regtag wf) sc-eq)

  -- REG-OP count-inc: mirror of scratch-dec on the tally register Count.
  count-inc-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                      prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                  → fetch prog (fpc fs) ≡ just (instr-reg-op count-inc)
                  → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                        ≡ event-of (instr-reg-op count-inc) fs
                          ++ flat-events n prog (flat-exec-instr (instr-reg-op count-inc) prog fs))
  count-inc-step {hv} n ev env prog fs s cc wf h ftq = go-sv (readReg (regs (floc fs)) Count) refl
    where go-sv : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Count ≡ sv
                → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                      ≡ event-of (instr-reg-op count-inc) fs
                        ++ flat-events n prog (flat-exec-instr (instr-reg-op count-inc) prog fs))
          go-sv (SV-Tag k)   i2-eq =
            ccc-step-bs {hv} n ev env prog fs s (instr-reg-op count-inc)
              (block-step-count-inc prog fs s k cc h ftq i2-eq) wf ftq h refl h
          -- NON-TAG: IMPOSSIBLE (`FlatRegTagWF`) — the tally register `Count`
          -- is written only by `count-zero` / `count-inc`, both tag producers.
          go-sv (SV-Ptr p)    i2-eq = ⊥-elim (flat-count-is-tag fs (SV-Ptr p) (inv-regtag wf) i2-eq)
          go-sv (SV-Lit pr v) i2-eq = ⊥-elim (flat-count-is-tag fs (SV-Lit pr v) (inv-regtag wf) i2-eq)
          go-sv (SV-Code c)   i2-eq = ⊥-elim (flat-count-is-tag fs (SV-Code c) (inv-regtag wf) i2-eq)

  -- MEMORY load-indirect (D073: every route is a theorem now). The load-site
  -- discipline (`load-indirect-target-wf`) hands the pointer + dynamic
  -- in-bounds witnesses; a WRITTEN cell is the PROVEN block-step, an EMPTY
  -- cell halts both machines (`*-empty-stuck` + `run-events-stuck` — the
  -- concrete read is unmapped via `dom-sized`+`heap-eq` / `stack-eq`).
  load-indirect-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                         prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                     → fetch prog (fpc fs) ≡ just load-indirect
                     → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                           ≡ event-of load-indirect fs ++ flat-events n prog (flat-exec-instr load-indirect prog fs))
  load-indirect-step {hv} n ev env prog fs s cc wf h ftq =
    go-loc (proj₁ wits) (proj₁ (proj₂ wits)) (proj₂ (proj₂ wits))
    where wits = load-indirect-target-wf prog fs (inv-run wf) ftq
          go-mem : ∀ hl → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                 → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))
                 → ∀ (mw : Maybe (StoredValue FS)) → heapMem (floc fs) hl ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of load-indirect fs ++ flat-events n prog (flat-exec-instr load-indirect prog fs))
          go-mem hl i-eq ib (just w) h-eq =
            ccc-step-bs {hv} n ev env prog fs s load-indirect
              (block-step-load-indirect prog fs s hl w cc h ftq i-eq
                 (C.dom-written (dataCorr cc) hl h-eq) h-eq)
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr load-indirect prog fs)) ≡ false
                  hpost rewrite i-eq | h-eq = h
          go-mem hl i-eq ib nothing h-eq = 1 , result
            where stuckp = load-indirect-heap-empty-stuck prog fs s hl cc ftq i-eq
                             (C.dom-sized (dataCorr cc) hl ib) h-eq
                  halt-s : X.State.halted s ≡ false
                  halt-s = trans (C.halt-eq (dataCorr cc)) h
                  hpost : halted (floc (flat-exec-instr load-indirect prog fs)) ≡ true
                  hpost rewrite i-eq | h-eq = refl
                  result : RTx.run-events val-x86-64 ev env 1 (compile-trace prog) s
                         ≡ event-of load-indirect fs ++ flat-events n prog (flat-exec-instr load-indirect prog fs)
                  result = trans (RTx.run-events-stuck val-x86-64 ev env 0 (compile-trace prog) s
                                    (mov (reg rax) (mem (base rdi))) halt-s (proj₁ stuckp) refl (proj₂ stuckp))
                                 (sym (flat-events-halted n prog (flat-exec-instr load-indirect prog fs) hpost))
          go-stack : ∀ f k → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
                   → (f ≡ current-frame (falloc fs)) × (k < frame-slots (falloc fs))
                   → ∀ (mw : Maybe (StoredValue FS))
                   → stackMem (floc fs) (current-frame (falloc fs)) k ≡ mw
                   → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                         ≡ event-of load-indirect fs ++ flat-events n prog (flat-exec-instr load-indirect prog fs))
          go-stack f k i-eq (f-eq , k<ss) (just w) st-eq =
            ccc-step-bs {hv} n ev env prog fs s load-indirect
              (block-step-load-indirect-stack prog fs s f k w cc h ftq i-eq f-eq k<ss st-eq)
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr load-indirect prog fs)) ≡ false
                  hpost rewrite i-eq | f-eq | st-eq = h
          -- UNREACHABLE (Plan 0.54 rung D): under heap mode `StackPtrWF` says there
          -- is NO stack pointer, so `Input1` holding one is refuted outright —
          -- the same `⊥` that `stack-ptr-current` already returns for `k<ss`.
          -- This used to route through `load-indirect-stack-empty-stuck`, which
          -- needed the old bidirectional `Window` to claim the concrete cell was
          -- unmapped too. That claim is gone; the branch was impossible anyway.
          go-stack f k i-eq (f-eq , k<ss) nothing st-eq =
            ⊥-elim (stack-ptr-live fs Input1 f k (run-stack-ptr prog fs (inv-run wf)) i-eq)
          go-loc : ∀ (loc : ValueLocation FS) → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
                 → (∀ hl → loc ≡ AtDynamic hl
                    → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl)))
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of load-indirect fs ++ flat-events n prog (flat-exec-instr load-indirect prog fs))
          go-loc (AtDynamic hl) i-eq ib = go-mem hl i-eq (ib hl refl) (heapMem (floc fs) hl) refl
          -- Plan 0.61: a load THROUGH A STACK POINTER is an ordinary step —
          -- the pointer denotes `slot-addr f k`, and for the CURRENT frame's live
          -- slots (`stack-ptr-current`, a THEOREM) `rsp-eq` + `stack-eq` relate
          -- exactly that cell.
          go-loc (AtStack f k)  i-eq ib =
            go-stack f k i-eq (stack-ptr-current prog fs f k (inv-run wf) i-eq)
                     (stackMem (floc fs) (current-frame (falloc fs)) k) refl

  -- MEMORY load-indirect-suc: as load-indirect but the SECOND cell (sucHL hl).
  load-indirect-suc-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                             prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                         → fetch prog (fpc fs) ≡ just load-indirect-suc
                         → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                               ≡ event-of load-indirect-suc fs ++ flat-events n prog (flat-exec-instr load-indirect-suc prog fs))
  load-indirect-suc-step {hv} n ev env prog fs s cc wf h ftq =
    go-loc (proj₁ wits) (proj₁ (proj₂ wits)) (proj₂ (proj₂ wits))
    where wits = load-indirect-suc-target-wf prog fs (inv-run wf) ftq
          go-mem : ∀ hl → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                 → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))
                 → ∀ (mw : Maybe (StoredValue FS)) → heapMem (floc fs) (sucHL hl) ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of load-indirect-suc fs ++ flat-events n prog (flat-exec-instr load-indirect-suc prog fs))
          go-mem hl i-eq ib (just w) h-eq =
            ccc-step-bs {hv} n ev env prog fs s load-indirect-suc
              (block-step-load-indirect-suc prog fs s hl w cc h ftq i-eq
                 (C.dom-written (dataCorr cc) (sucHL hl) h-eq) h-eq)
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr load-indirect-suc prog fs)) ≡ false
                  hpost rewrite i-eq | h-eq = h
          go-mem hl i-eq ib nothing h-eq = 1 , result
            where stuckp = load-indirect-suc-heap-empty-stuck prog fs s hl cc ftq i-eq
                             (C.dom-sized (dataCorr cc) (sucHL hl) ib) h-eq
                  halt-s : X.State.halted s ≡ false
                  halt-s = trans (C.halt-eq (dataCorr cc)) h
                  hpost : halted (floc (flat-exec-instr load-indirect-suc prog fs)) ≡ true
                  hpost rewrite i-eq | h-eq = refl
                  result : RTx.run-events val-x86-64 ev env 1 (compile-trace prog) s
                         ≡ event-of load-indirect-suc fs ++ flat-events n prog (flat-exec-instr load-indirect-suc prog fs)
                  result = trans (RTx.run-events-stuck val-x86-64 ev env 0 (compile-trace prog) s
                                    (mov (reg rax) (mem (base+disp rdi slot-size))) halt-s (proj₁ stuckp) refl (proj₂ stuckp))
                                 (sym (flat-events-halted n prog (flat-exec-instr load-indirect-suc prog fs) hpost))
          -- SECOND cell of a stack pair: `[rdi+8]` is slot `suc k` of the same frame.
          go-stack : ∀ f k → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
                   → (f ≡ current-frame (falloc fs)) × (suc k < frame-slots (falloc fs))
                   → ∀ (mw : Maybe (StoredValue FS))
                   → stackMem (floc fs) (current-frame (falloc fs)) (suc k) ≡ mw
                   → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                         ≡ event-of load-indirect-suc fs ++ flat-events n prog (flat-exec-instr load-indirect-suc prog fs))
          go-stack f k i-eq (f-eq , sk<ss) (just w) st-eq =
            ccc-step-bs {hv} n ev env prog fs s load-indirect-suc
              (block-step-load-indirect-suc-stack prog fs s f k w cc h ftq i-eq f-eq sk<ss st-eq)
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr load-indirect-suc prog fs)) ≡ false
                  hpost rewrite i-eq | f-eq | st-eq = h
          -- UNREACHABLE, same as the `load-indirect` case above: heap mode admits
          -- no stack pointer at all, so `Input1` holding one is `⊥`.
          go-stack f k i-eq (f-eq , sk<ss) nothing st-eq =
            ⊥-elim (stack-ptr-suc-live fs Input1 f k (run-stack-ptr prog fs (inv-run wf)) i-eq)
          go-loc : ∀ (loc : ValueLocation FS) → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
                 → (∀ hl → loc ≡ AtDynamic hl
                    → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl))))
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of load-indirect-suc fs ++ flat-events n prog (flat-exec-instr load-indirect-suc prog fs))
          go-loc (AtDynamic hl) i-eq ib = go-mem hl i-eq (ib hl refl) (heapMem (floc fs) (sucHL hl)) refl
          go-loc (AtStack f k)  i-eq ib =
            go-stack f k i-eq (stack-ptr-current-suc prog fs f k (inv-run wf) i-eq)
                     (stackMem (floc fs) (current-frame (falloc fs)) (suc k)) refl

  -- STACK load-from-slot: J-bridge on the slot's abstract value. `just w` ⇒ the PROVEN
  -- block-step-load-from-slot (the stack read pinned by stack-eq) ⇒ ccc-step-bs; the
  -- empty-slot `nothing` ⇒ `load-from-slot-empty` (both machines halt — WF residual).
  load-from-slot-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                          prog fs s slot → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                      → fetch prog (fpc fs) ≡ just (load-from-slot slot)
                      → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                            ≡ event-of (load-from-slot slot) fs ++ flat-events n prog (flat-exec-instr (load-from-slot slot) prog fs))
  load-from-slot-step {hv} n ev env prog fs s slot cc wf h ftq =
    go-mem (stackMem (floc fs) (current-frame (falloc fs)) slot) refl
    where go-mem : ∀ (mw : Maybe (StoredValue FS)) → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (load-from-slot slot) fs ++ flat-events n prog (flat-exec-instr (load-from-slot slot) prog fs))
          go-mem (just w) st-eq =
            ccc-step-bs {hv} n ev env prog fs s (load-from-slot slot)
              (block-step-load-from-slot prog fs s slot w cc h ftq (slot-read-in-frame prog fs slot _ (inv-run wf) ftq refl) st-eq)
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr (load-from-slot slot) prog fs)) ≡ false
                  hpost rewrite st-eq = h
          go-mem nothing st-eq =
            -- UNREACHABLE (Plan 0.54 rung D): `site-ok` requires a non-`e-any`
            -- claim at every slot READ, and `MeetsSlot` sends such a claim at
            -- `nothing` to `⊥`. So a checked program never reads an unwritten
            -- slot — which is what the old bidirectional `Window` used to paper
            -- over by declaring the concrete cell unmapped as well.
            ⊥-elim (slot-read-written prog fs slot (load-from-slot slot) (inv-run wf) ftq (λ _ → refl) st-eq)

  -- STACK restore-input: identical to load-from-slot but writes Input1 (rdi).
  restore-input-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                         prog fs s slot → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                     → fetch prog (fpc fs) ≡ just (restore-input slot)
                     → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                           ≡ event-of (restore-input slot) fs ++ flat-events n prog (flat-exec-instr (restore-input slot) prog fs))
  restore-input-step {hv} n ev env prog fs s slot cc wf h ftq =
    go-mem (stackMem (floc fs) (current-frame (falloc fs)) slot) refl
    where go-mem : ∀ (mw : Maybe (StoredValue FS)) → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (restore-input slot) fs ++ flat-events n prog (flat-exec-instr (restore-input slot) prog fs))
          go-mem (just w) st-eq =
            ccc-step-bs {hv} n ev env prog fs s (restore-input slot)
              (block-step-restore-input prog fs s slot w cc h ftq (slot-read-in-frame prog fs slot _ (inv-run wf) ftq refl) st-eq)
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr (restore-input slot) prog fs)) ≡ false
                  hpost rewrite st-eq = h
          go-mem nothing st-eq =
            -- UNREACHABLE (Plan 0.54 rung D): `site-ok` requires a non-`e-any`
            -- claim at every slot READ, and `MeetsSlot` sends such a claim at
            -- `nothing` to `⊥`. So a checked program never reads an unwritten
            -- slot — which is what the old bidirectional `Window` used to paper
            -- over by declaring the concrete cell unmapped as well.
            ⊥-elim (slot-read-written prog fs slot (restore-input slot) (inv-run wf) ftq (λ _ → refl) st-eq)

  -- STACK worklist-pop: identical to load-from-slot (same abstract sem + lowering).
  worklist-pop-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                        prog fs s slot → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                    → fetch prog (fpc fs) ≡ just (worklist-pop slot)
                    → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                          ≡ event-of (worklist-pop slot) fs ++ flat-events n prog (flat-exec-instr (worklist-pop slot) prog fs))
  worklist-pop-step {hv} n ev env prog fs s slot cc wf h ftq =
    go-mem (stackMem (floc fs) (current-frame (falloc fs)) slot) refl
    where go-mem : ∀ (mw : Maybe (StoredValue FS)) → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (worklist-pop slot) fs ++ flat-events n prog (flat-exec-instr (worklist-pop slot) prog fs))
          go-mem (just w) st-eq =
            ccc-step-bs {hv} n ev env prog fs s (worklist-pop slot)
              (block-step-worklist-pop prog fs s slot w cc h ftq (slot-read-in-frame prog fs slot _ (inv-run wf) ftq refl) st-eq)
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr (worklist-pop slot) prog fs)) ≡ false
                  hpost rewrite st-eq = h
          go-mem nothing st-eq =
            -- UNREACHABLE (Plan 0.54 rung D): `site-ok` requires a non-`e-any`
            -- claim at every slot READ, and `MeetsSlot` sends such a claim at
            -- `nothing` to `⊥`. So a checked program never reads an unwritten
            -- slot — which is what the old bidirectional `Window` used to paper
            -- over by declaring the concrete cell unmapped as well.
            ⊥-elim (slot-read-written prog fs slot (worklist-pop slot) (inv-run wf) ftq (λ _ → refl) st-eq)

  -- MEMORY store-indirect: case the Output-target pointer. A live dynamic pointer ⇒ the
  -- PROVEN block-step-store-indirect (HDom from dom-sized ∘ store-indirect-inbounds; the writeLoc↔heap
  -- guard from store-indirect-guard) ⇒ ccc-step-bs. Bad shapes ⇒ store-indirect-bad.
  store-indirect-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                          prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                      → fetch prog (fpc fs) ≡ just store-indirect
                      → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                            ≡ event-of store-indirect fs ++ flat-events n prog (flat-exec-instr store-indirect prog fs))
  store-indirect-step {hv} n ev env prog fs s cc wf h ftq = go-ptr (readReg (regs (floc fs)) Input1) refl
    where go-ptr : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Input1 ≡ sv
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of store-indirect fs ++ flat-events n prog (flat-exec-instr store-indirect prog fs))
          go-ptr (SV-Ptr (AtDynamic hl)) i-eq =
            ccc-step-bs {hv} n ev env prog fs s store-indirect
              (block-step-store-indirect prog fs s hl cc h ftq i-eq
                 (C.dom-sized (dataCorr cc) hl (store-indirect-inbounds prog fs hl (inv-run wf) ftq i-eq)) (store-guard fs hl))
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr store-indirect prog fs)) ≡ false
                  hpost rewrite i-eq = trans (writeLoc-halted (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)) h
          -- STORE through a stack pointer: `writeLoc … (AtStack f k)` is the plain
          -- stack write (no cross-region guard needed — that is the heap branch),
          -- and the x86 writes at `rsp + 8·k`.
          go-ptr (SV-Ptr (AtStack f k))  i-eq =
            ccc-step-bs {hv} n ev env prog fs s store-indirect
              (block-step-store-indirect-stack prog fs s f k cc h ftq i-eq
                 (proj₁ (stack-ptr-current prog fs f k (inv-run wf) i-eq))
                 (proj₂ (stack-ptr-current prog fs f k (inv-run wf) i-eq))
                 (slot-heap-disj {hv} fs s (dataCorr cc) k))
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr store-indirect prog fs)) ≡ false
                  hpost rewrite i-eq = trans (writeLoc-halted (floc fs) (AtStack f k) (readReg (regs (floc fs)) Output)) h
          go-ptr (SV-Tag _)   i-eq =
            ⊥-elim (store-nonptr-absurd prog fs (inv-run wf) ftq i-eq (λ { _ () }))
          go-ptr (SV-Lit _ _) i-eq =
            ⊥-elim (store-nonptr-absurd prog fs (inv-run wf) ftq i-eq (λ { _ () }))
          go-ptr (SV-Code _)  i-eq =
            ⊥-elim (store-nonptr-absurd prog fs (inv-run wf) ftq i-eq (λ { _ () }))

  -- MEMORY store-indirect-suc: as store-indirect but the SECOND cell (sucHL hl).
  store-indirect-suc-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                              prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                          → fetch prog (fpc fs) ≡ just store-indirect-suc
                          → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                                ≡ event-of store-indirect-suc fs ++ flat-events n prog (flat-exec-instr store-indirect-suc prog fs))
  store-indirect-suc-step {hv} n ev env prog fs s cc wf h ftq = go-ptr (readReg (regs (floc fs)) Input1) refl
    where go-ptr : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Input1 ≡ sv
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of store-indirect-suc fs ++ flat-events n prog (flat-exec-instr store-indirect-suc prog fs))
          go-ptr (SV-Ptr (AtDynamic hl)) i-eq =
            ccc-step-bs {hv} n ev env prog fs s store-indirect-suc
              (block-step-store-indirect-suc prog fs s hl cc h ftq i-eq
                 (C.dom-sized (dataCorr cc) (sucHL hl) (store-indirect-suc-inbounds prog fs hl (inv-run wf) ftq i-eq)) (store-guard fs (sucHL hl)))
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr store-indirect-suc prog fs)) ≡ false
                  hpost rewrite i-eq = trans (writeLoc-halted (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)) h
          -- STORE-SUC through a stack pointer: the pair's SECOND slot, `suc k`,
          -- reserved by the same prologue (`stack-ptr-current`) — an ordinary step.
          go-ptr (SV-Ptr (AtStack f k))  i-eq =
            ccc-step-bs {hv} n ev env prog fs s store-indirect-suc
              (block-step-store-indirect-suc-stack prog fs s f k cc h ftq i-eq
                 (proj₁ (stack-ptr-current prog fs f k (inv-run wf) i-eq))
                 (proj₂ (stack-ptr-current-suc prog fs f k (inv-run wf) i-eq))
                 (slot-heap-disj {hv} fs s (dataCorr cc) (suc k)))
              wf ftq h refl hpost
            where hpost : halted (floc (flat-exec-instr store-indirect-suc prog fs)) ≡ false
                  hpost rewrite i-eq = trans (writeLoc-halted (floc fs) (AtStack f (suc k)) (readReg (regs (floc fs)) Output)) h
          go-ptr (SV-Tag _)   i-eq =
            ⊥-elim (store-suc-nonptr-absurd prog fs (inv-run wf) ftq i-eq (λ { _ () }))
          go-ptr (SV-Lit _ _) i-eq =
            ⊥-elim (store-suc-nonptr-absurd prog fs (inv-run wf) ftq i-eq (λ { _ () }))
          go-ptr (SV-Code _)  i-eq =
            ⊥-elim (store-suc-nonptr-absurd prog fs (inv-run wf) ftq i-eq (λ { _ () }))

  -- SIGOP engine. Split on effect si (J-bridge, no with): Pure ⇒ arith — the run-events
  -- mechanics are PROVEN (sigop-run-arith: pc-align + run-events-arith), event-of is []
  -- (event-of-pure), recurse via events-agree on the flat post-state; the only residual
  -- is `arith-sigop-contract` (the offline arith obligation). Emits/Halts ⇒ external
  -- (sigop-external-rest, the value-carrying observable — next).
  sigop-step : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                 prog fs s {A B} (si : SigOpInfo A B) → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
               → fetch prog (fpc fs) ≡ just (instr-sigop si)
               → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                     ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs))
  sigop-step {hv} n ev env prog fs s {A} {B} si cc wf h ftq = go-eff (effect si) refl
    where go-eff : ∀ (e : EffectShape B) → effect si ≡ e
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs))
          go-eff Pure eqe = suc (proj₁ rec) , goal
            where contract = arith-sigop-contract env prog fs s si (inv-run wf) (inv-env wf) eqe cc ftq
                  pl  = proj₁ contract
                  rec = events-agree n ev env prog (flat-exec-instr (instr-sigop si) prog fs)
                          (uncurry (dispatch-arith val-x86-64) pl s) (proj₂ (proj₂ contract))
                          (flat-inv-step (instr-sigop si) prog fs ftq h wf)
                  goal : RTx.run-events val-x86-64 ev env (suc (proj₁ rec)) (compile-trace prog) s
                       ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs)
                  goal rewrite event-of-pure si fs eqe =
                    trans (sigop-run-arith ev env (proj₁ rec) prog fs s si pl cc h ftq (proj₁ (proj₂ contract)))
                          (proj₂ rec)
          go-eff (Emits _) eqe = sigop-external n ev env prog fs s si cc wf h ftq
          go-eff (Halts _) eqe = sigop-external n ev env prog fs s si cc wf h ftq

  -- EXTERNAL SIGOP engine: run-events-external EMITS `ev lbl s` then continues past the
  -- call (sigop-run-external, PROVEN); the external contract pins `ev ≡ event-of` and the
  -- ret-past state; recurse via events-agree. The only residual is external-sigop-contract
  -- (the honest per-target observable obligation). Emits AND Halts share this — for Halts
  -- the flat post-state is halted and both tails run to [] (events-agree's halted case).
  sigop-external : ∀ {hv : HeapView} n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                     prog fs s {A B} (si : SigOpInfo A B) → CompiledCorr hv prog fs s → FlatInv ev env prog fs → halted (floc fs) ≡ false
                 → fetch prog (fpc fs) ≡ just (instr-sigop si)
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs))
  sigop-external n ev env prog fs s si cc wf h ftq = suc (proj₁ rec) , goal
    where contract = external-sigop-contract ev env prog fs s si (inv-run wf) (inv-ev wf) (inv-env wf) cc ftq
          rec = events-agree n ev env prog (flat-exec-instr (instr-sigop si) prog fs)
                  (RTx.ret-past s) (proj₂ (proj₂ contract))
                  (flat-inv-step (instr-sigop si) prog fs ftq h wf)
          goal : RTx.run-events val-x86-64 ev env (suc (proj₁ rec)) (compile-trace prog) s
               ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs)
          goal = trans (sigop-run-external ev env (proj₁ rec) prog fs s si cc h ftq (proj₁ contract))
                 (trans (cong (_++ RTx.run-events val-x86-64 ev env (proj₁ rec) (compile-trace prog) (RTx.ret-past s))
                              (proj₁ (proj₂ contract)))
                        (cong (event-of (instr-sigop si) fs ++_) (proj₂ rec)))
