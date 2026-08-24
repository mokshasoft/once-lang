-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
  ( slot-size; slots; Program; Instr; Reg; Operand; reg; imm; mem; base; base+disp; rsp; rbp; rax; rdi; rbx; r14
  ; mov; lea; add; sub; cmp; test; jmp; je; jne; call; call-sym
  ; ret; push; pop; nop; ud2; syscall; label )
open import Data.Nat using (ℕ; suc; _+_; _*_; _<_; _≤_; _∸_; _≡ᵇ_; _⊓_)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; <-transˡ; <-irrefl; m≤m+n; m≤n+m; m∸n≤m
                                      ; ⊓-glb; m⊓n≤m; m⊓n≤n; m+n≤o⇒m≤o∸n; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_)
-- …and the pieces the RESOURCE parameter's type needs. Imported UNAPPLIED, so
-- the module's own `FS`/`word-eq` can be threaded into them by Agda's
-- telescoping (`RC.RunAt o FS word-eq …`) — a parameter's type is elaborated
-- before the body, where the applied `open import … FS word-eq` has not run.
open import Data.Maybe using (just)
-- …and the pieces the LITERAL parameters' types need (phase D), likewise
-- imported before the module header.
open import Once.Type using (fits-int; fits-float)
open import Once.Word using (Carrier)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Once.Float.Dyadic using (binary32; binary64)
open import Once.Float.Decimal using (Decimal; round)
open import Data.Integer using (ℤ)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; instr-alloc-heap; instr-ctrl; c-thunk; c-ret; instr-call-closure
        ; instr-reg-op; scratch-dec; count-inc; instr-dealloc-stack
        ; instr-load-tag-lit; instr-load-const)
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
  -- …and the float format pinned to this target's, the companion of `word-eq`
  -- (plan 0.73, D113). Passed straight through to `FlatSimulation`, which is
  -- where the emitter's `round binary64` and the machine's `float-format FS`
  -- have to be shown to be the same number.
  (fmt-eq : FrameSemantics.float-format FS ≡ binary64)
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
             → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
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
              → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
              → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
                ≡ just (instr-ctrl (c-thunk m b))
              → FC.hfront hv + slots b ≤ X.readReg (X.State.regs s) rsp)
  -- CALL DEPTH (D098), the third of the family and the smallest: room for the
  -- ONE slot a call spends on the return address. See `ResourceBounds.CallRoom`.
  (call-room : ∀ {hv : FC.HeapView FS word-eq}
                 (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS}) (s : X.State)
             → RC.RunAt o FS word-eq prog fs
             → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
             → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
               ≡ just instr-call-closure
             → FC.hfront hv + slot-size ≤ X.readReg (X.State.regs s) rsp)
  -- PLAN 0.70 PHASE C: the machine is finite. Both D087-class. Spelled out
  -- against this module's own `FS`, exactly as the three rooms are — the
  -- `…X86-64.ResourceBounds` copies pin `x86-64-frame-semantics` and are the
  -- types the APEX threads, which is a different job.
  (reg-range : ∀ {hv : FC.HeapView FS word-eq}
                 (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
                 (s : X.State) (r : Reg)
             → RC.RunAt o FS word-eq prog fs
             → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
             → X.readReg (X.State.regs s) r < X.W.modulus)
  (scratch-dec-guarded : ∀ {hv : FC.HeapView FS word-eq}
                           (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
                           (s : X.State)
                       → RC.RunAt o FS word-eq prog fs
                       → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
                       → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
                           ≡ just (instr-reg-op scratch-dec)
                       → 1 ≤ X.readReg (X.State.regs s) rbx)
  -- THE ADDRESS SPACE DOES NOT WRAP at the four emitted `add` sites (plan 0.70
  -- phase C). `execInstr`'s `add` computes `W.⊕` unconditionally, because D054
  -- makes wraparound *correct, defined* Once semantics — so no no-overflow
  -- precondition may sit on the instruction, and the range obligation lands
  -- here instead. NOT a claim about user arithmetic: every `add` the compiler
  -- emits computes an address or the observable counter; a user `Int` addition
  -- goes through the Arith backend over `Once.Word` and wraps there by design.
  -- These are `…ResourceBounds.AddrNoWrap`'s four fields.
  (ret-no-wrap : ∀ {hv : FC.HeapView FS word-eq}
                   (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
                   (s : X.State) (b : ℕ)
               → RC.RunAt o FS word-eq prog fs
               → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
               → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
                   ≡ just (instr-ctrl (c-ret b))
               -- `suc b`: the representable quantity is THE CALLER'S FRAME
               -- BASE, frame AND the slot the call spent. x86-64 only needs the
               -- weaker half here; riscv64, which adds both in one `addi`,
               -- needs this one. See `Resources.ret-no-wrap`.
               → X.readReg (X.State.regs s) rsp + slots (suc b) < X.W.modulus)
  (count-no-wrap : ∀ {hv : FC.HeapView FS word-eq}
                     (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
                     (s : X.State)
                 → RC.RunAt o FS word-eq prog fs
                 → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
                 → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
                     ≡ just (instr-reg-op count-inc)
                 → X.readReg (X.State.regs s) r14 + 1 < X.W.modulus)
  -- THE LITERAL SEAM (phase D): an emitted immediate fits in a machine word.
  -- `…ResourceBounds.LitFits`'s three fields.
  (tag-fits : ∀ {hv : FC.HeapView FS word-eq}
                (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
                (s : X.State) (n : ℕ)
            → RC.RunAt o FS word-eq prog fs
            → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
            → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
                ≡ just (instr-load-tag-lit n)
            → n < X.W.modulus)
  (lit-fits : ∀ {hv : FC.HeapView FS word-eq}
                (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
                (s : X.State) (v : ℤ)
            → RC.RunAt o FS word-eq prog fs
            → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
            → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
                ≡ just (instr-load-const fits-int v)
            → Once.CCC.Machine.SMCore.AbstractExec.lit-value {FS} fits-int v < X.W.modulus)
  (float-fits : ∀ {hv : FC.HeapView FS word-eq}
                  (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
                  (s : X.State) (v : Decimal)
              → RC.RunAt o FS word-eq prog fs
              → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
              → FlatMachine.fetch {FS} prog (FlatMachine.fpc {FS} fs)
                  ≡ just (instr-load-const fits-float v)
              → Once.CCC.Machine.SMCore.AbstractExec.lit-value {FS} fits-float v < X.W.modulus)
  (lo-fits : ∀ {hv : FC.HeapView FS word-eq}
               (prog : AbstractTrace) (fs : FlatMachine.FlatState {FS})
               (s : X.State)
           → RC.RunAt o FS word-eq prog fs
           → FSim.CompiledCorr o FS word-eq fmt-eq hv prog fs s
           → FC.lo hv < X.W.modulus)
  where

open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst; subst₂)

open import Once.CCC.Machine.SMCore
open MemOps {FS} using (writeLoc; writeLocToHeap; writeLoc-halted; readLoc)
open FrameSemantics FS using (Frame)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X

open import Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation o FS word-eq fmt-eq public
open import Once.CCC.Machine.FlatStoreWF FS using
  (FlatWF; flat-wf-step; cl-step; wf-regs; wf-heap; wf-stack; wf-fresh; sv-below; svm-below)
open import Once.CCC.Machine.FlatRegTagWF FS using
  (FlatRegTag; flat-regtag-step; flat-scratch-is-tag; flat-count-is-tag; scratch-tag)
open C using (HeapView; haddr; HDom; hfront; lo) public
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Once.Adequacy.ArchCorrectness.X86-64.FlatComposition FS
  using (blk-len; blk-off; drop-compile; fetch-drop; drop-[]; fetch-block-head
        ; find-label-none-corr; fetch-block-2nd; find-thunk-corr
        -- …and the ISA VIEW this arch supplies to the generic layers: the label
        -- scan's four laws plus the lowering enumeration. `FlatComposition`
        -- already took them; the engine takes the same ones (slice 3).
        ; is-label?; skip-law; label-hit; label-miss; headView)
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

------------------------------------------------------------------------
-- HOW FUEL PEELS, as six premise-free readouts (plan 0.65 G2 item 4, slice 3).
--
-- The generic engine cannot compute with `exec` — to it that is an opaque
-- parameter — so the equations it needs come across as these. Each is `refl`
-- once the boolean and the fetch have been rewritten; what they say is exactly
-- `Semantics.exec`'s five clauses, read out one branch at a time.
------------------------------------------------------------------------
x-exec-zero : ∀ prog s → X.exec 0 prog s ≡ just s
x-exec-zero prog s = refl

x-exec-halted : ∀ n prog s → X.State.halted s ≡ true → X.exec (suc n) prog s ≡ just s
x-exec-halted n prog s h rewrite h = refl

-- past the end: the machine halts IN PLACE, so whatever `exec` lands on is halted
x-exec-end : ∀ n prog s {s'} → X.State.halted s ≡ false
           → X.fetch prog (X.State.pc s) ≡ nothing
           → X.exec (suc n) prog s ≡ just s' → X.State.halted s' ≡ true
x-exec-end n prog s {s'} h ftn eq =
  sym (cong X.State.halted (just-injective (trans (sym step) eq)))
  where step : X.exec (suc n) prog s ≡ just (record s { halted = true })
        step rewrite h | ftn = refl

x-exec-stuck : ∀ n prog s j → X.State.halted s ≡ false
             → X.fetch prog (X.State.pc s) ≡ just j
             → X.execInstr prog s j ≡ nothing → X.exec (suc n) prog s ≡ nothing
x-exec-stuck n prog s j h ftq exn rewrite h | ftq | exn = refl

x-exec-step-halt : ∀ n prog s j s₁ → X.State.halted s ≡ false
                 → X.fetch prog (X.State.pc s) ≡ just j
                 → X.execInstr prog s j ≡ just s₁ → X.State.halted s₁ ≡ true
                 → X.exec (suc n) prog s ≡ just s₁
x-exec-step-halt n prog s j s₁ h ftq exq h1 rewrite h | ftq | exq | h1 = refl

x-exec-step-run : ∀ n prog s j s₁ → X.State.halted s ≡ false
                → X.fetch prog (X.State.pc s) ≡ just j
                → X.execInstr prog s j ≡ just s₁ → X.State.halted s₁ ≡ false
                → X.exec (suc n) prog s ≡ X.exec n prog s₁
x-exec-step-run n prog s j s₁ h ftq exq h1 rewrite h | ftq | exq | h1 = refl

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
-- `Reachable` is DATA, so it is inhabited by construction: a postulated
-- predicate could be empty, which trades inconsistency for conditional
-- vacuity. `reach-start` admits any state a loader could hand `main`;
-- `reach-step` is one flat step.
------------------------------------------------------------------------

-- (The run context — `EntryLike`, `Reachable`, `Emitted`, `RunAt` — now
-- lives in `…X86-64.RunContext`, one layer down, so that the resource bounds
-- can be MODULE PARAMETERS here rather than postulates. See that module.)
open import Once.Adequacy.ArchCorrectness.X86-64.RunContext o FS word-eq public


------------------------------------------------------------------------
-- THE GENERIC EVENT ENGINE, instantiated (plan 0.65 G2 item 4, slice 3).
--
-- Everything below this line that USED to be written here and is now written
-- once, for every arch, comes through `EE`. What x86-64 supplies is the four
-- things the engine is generic OVER: the emitter's law surface (the same one
-- `FlatComposition` takes), the machine's step and how its fuel peels, the
-- trace loop's telescope (which `RunTrace` already had), and the one ISA
-- enumeration — `nonhalt-noncall`.
--
-- NOT opened `public` wholesale: the engine re-exports `FlatComposition`,
-- `CompiledCorrespondence` and `RunContext`, all three of which this module
-- already has in scope by another path. Only what the engine ADDS is named.
------------------------------------------------------------------------
import Once.Adequacy.ArchCorrectness.FlatCore.EventEngine as Engine
import Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch as Dispatch
import Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface as EI
import Once.CCC.Target.X86-64.Syntax as XS
open import Data.List using (List)
open import Once.Adequacy.ArchCorrectness.X86-64.RegRoles using (x86-64-roles)
-- x86-64 filling `EngineInterface`'s three records. What was a 49-argument
-- module application is three values now, for the memory reason recorded in
-- `EngineInterface`; the contents are identical.
x86-64-emitter : EI.Emitter FS Reg
x86-64-emitter = record
  { Instr = XS.Instr
  ; compile-abstract = compile-abstract ; compile-trace = compile-trace
  ; ct-nil = refl ; ct-cons = λ _ _ → refl
  ; mfetch = X.fetch
  ; mfetch-nil = λ _ → refl ; mfetch-zero = λ _ _ → refl ; mfetch-suc = λ _ _ _ → refl
  ; is-label? = is-label? ; mk-label = label ; find-label-go = X.find-label-go
  ; find-label-nil = λ _ _ → refl ; skip-law = skip-law
  ; label-hit = label-hit ; label-miss = label-miss ; headView = headView
  ; find-label = X.find-label ; find-label-def = λ _ _ → refl
  }

x86-64-machine : EI.Machine FS Reg x86-64-emitter
x86-64-machine = record
  { State = X.State ; rreg = xrreg ; memory = X.State.memory
  ; xhalted = X.State.halted ; xpc = X.State.pc
  -- x86-64's `call` PUSHES the return address, so an unspilled return is
  -- already in its stack cell: the link claim IS the memory claim.
  ; link-claim = x86-64-link-claim
  ; mexecInstr = X.execInstr ; exec = X.exec
  ; exec-zero = x-exec-zero ; exec-halted = x-exec-halted ; exec-end = x-exec-end
  ; exec-stuck = x-exec-stuck ; exec-step-halt = x-exec-step-halt
  ; exec-step-run = x-exec-step-run
  }

x86-64-traceloop : EI.TraceLoop FS Reg x86-64-emitter x86-64-machine
x86-64-traceloop = record
  { Payload = List XInstr × ℕ
  ; matchCall = RTx.matchCall ; ret-past = RTx.ret-past
  ; dispatchArith = uncurry (dispatch-arith val-x86-64)
  ; ev-arch = ev-x86-64 ; arith-env = arith-env-x86-64
  ; sigop-call = call-sym ; sigop-lowering = λ _ → refl ; sigop-matchCall = λ _ → refl
  ; nonhalt-noncall = nonhalt-noncall
  }

module EE = Engine o FS slot-size word-eq Reg x86-64-roles X.W.modulus
                   x86-64-emitter x86-64-machine x86-64-traceloop

open EE using (FlatInv; mkFlatInv; inv-wf; inv-closure; inv-regtag; inv-ev; inv-env
              ; inv-run; flat-inv-step; block-run-exec
              ; events-running-end; sigop-concrete-fetch; sigop-run-arith
              ; sigop-run-external; event-of-pure) public


-- (`FlatInv` and `flat-inv-step` moved to `FlatCore.EventEngine` — the two
-- invariants they bundle are the ABSTRACT machine's, and the run context was
-- already generic. Re-exported from `EE` above.)

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

-- (`ptr-heap-disj` — the same fact with the heap stores' argument order —
-- DELETED with Plan 0.63's D085: a heap store no longer takes stack
-- disjointness as a premise, it derives it for EVERY live frame from the frame
-- list's floor (`C.windows-heap-store`).)


-- (`block-run-exec` moved to `FlatCore.EventEngine` with the six `exec`
-- readouts above: given how fuel peels, the argument is the same on every
-- machine, and `nonhalt-noncall` is the only ISA fact in it.)

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

-- fetch prog k ≡ just i ⇒ dropping k blocks exposes i at the head. The abstract-
-- side ingredient for the per-instruction pc-alignment (concrete fetch = the
-- compiled head of the fetched abstract instruction).

-- (`sigop-concrete-fetch` / `sigop-run-arith` moved to `FlatCore.EventEngine`:
-- a SigOp lowers to ONE call-by-symbol on every target, which is the whole
-- content of the arith/external dispatch — see its `sigop-lowering`.)

-- `execInstr` at a memory-compare with a known read (aux helper — a
-- `rewrite` inside the deep tag-branch where-block does not abstract).
execInstr-cmp-mi : ∀ prog (s : X.State) a v
  → X.readMem (X.State.memory s) (X.effectiveAddr s a) ≡ just v
  → X.execInstr prog s (cmp (mem a) (imm 0))
    ≡ just (record s { flags = X.mkflags (v ≡ᵇ 0) (v X.<ᵇ 0) false
                     ; pc = X.State.pc s + 1 })
execInstr-cmp-mi prog s a v rd rewrite rd = refl

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
-- (`store-guard` moved to FlatCore.CompiledCorrespondence — arch-free.)

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
-- (`sigop-run-external` and `events-running-end` moved to the engine too.)


------------------------------------------------------------------------
-- THE STUCK ROUTES, x86-64's half (plan 0.65 G2 item 4, slice 3).
--
-- The engine asks only for the CONCRETE claim — that nothing more comes out
-- of this machine — and discharges the abstract half itself
-- (`EE.stuck-result`: the flat machine has halted, so `flat-events` is []).
-- These five are that concrete claim, and they are where the instruction
-- names live: a `mov rax,[rdi]` faulting on an unmapped address, a `jmp`/`je`
-- to a label the compiled program does not contain.
------------------------------------------------------------------------
stuck-load-indirect : ∀ {hv : HeapView} ev env prog fs s hl → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → C.HDom hv hl
  → heapMem (floc fs) hl ≡ nothing
  → EE.StuckAt ev env (compile-trace prog) s
stuck-load-indirect ev env prog fs s hl cc h ftq i-eq dom h-eq =
  1 , RTx.run-events-stuck val-x86-64 ev env 0 (compile-trace prog) s
        (mov (reg rax) (mem (base rdi)))
        (trans (C.halt-eq (dataCorr cc)) h) (proj₁ stuckp) refl (proj₂ stuckp)
  where stuckp = load-indirect-heap-empty-stuck prog fs s hl cc ftq i-eq dom h-eq

stuck-load-indirect-suc : ∀ {hv : HeapView} ev env prog fs s hl → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just load-indirect-suc
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → C.HDom hv (sucHL hl)
  → heapMem (floc fs) (sucHL hl) ≡ nothing
  → EE.StuckAt ev env (compile-trace prog) s
stuck-load-indirect-suc ev env prog fs s hl cc h ftq i-eq dom h-eq =
  1 , RTx.run-events-stuck val-x86-64 ev env 0 (compile-trace prog) s
        (mov (reg rax) (mem (base+disp rdi slot-size)))
        (trans (C.halt-eq (dataCorr cc)) h) (proj₁ stuckp) refl (proj₂ stuckp)
  where stuckp = load-indirect-suc-heap-empty-stuck prog fs s hl cc ftq i-eq dom h-eq

-- a concrete jump to a MISSING label HALTS (it does not get stuck), so the
-- trace takes one step and then emits nothing.
stuck-c-jmp : ∀ {hv : HeapView} ev env prog fs s m → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp m))
  → find-label prog m ≡ nothing
  → EE.StuckAt ev env (compile-trace prog) s
stuck-c-jmp ev env prog fs s m cc h ftq fl-eq =
  2 , trans (RTx.run-events-noncall val-x86-64 ev env 1 (compile-trace prog) s
               (jmp (once m)) halt-s fetch-x86 refl step-eq)
            (RTx.run-events-halted val-x86-64 ev env 0 (compile-trace prog) s' refl)
  where
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq (dataCorr cc)) h
    fetch-x86 : X.fetch (compile-trace prog) (X.State.pc s) ≡ just (jmp (once m))
    fetch-x86 = trans (cong (X.fetch (compile-trace prog)) (pc-off cc))
                      (fetch-block-head prog (fpc fs) (instr-ctrl (c-jmp m)) ftq)
    s' : X.State
    s' = record s { halted = true }
    step-eq : X.execInstr (compile-trace prog) s (jmp (once m)) ≡ just s'
    step-eq rewrite find-label-none-corr prog m fl-eq = refl

-- the two TAKEN branches whose label is absent: `cmp` then a `je` that halts.
stuck-c-branch-scratch-zero : ∀ {hv : HeapView} ev env prog fs s m → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero m))
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag 0
  → find-label prog m ≡ nothing
  → EE.StuckAt ev env (compile-trace prog) s
stuck-c-branch-scratch-zero {hv} ev env prog fs s m cc h ftq sc-eq fl-eq =
  3 , trans (RTx.run-events-noncall val-x86-64 ev env 2 (compile-trace prog) s
               (cmp (reg rbx) (imm 0)) halt-s fetch-cmp refl step-cmp)
      (trans (RTx.run-events-noncall val-x86-64 ev env 1 (compile-trace prog) post-cmp
               (je (once m)) halt-s fetch-je refl step-je)
             (RTx.run-events-halted val-x86-64 ev env 0 (compile-trace prog) post-je refl))
  where
    dc = dataCorr cc
    halt-s : X.State.halted s ≡ false
    halt-s = trans (C.halt-eq dc) h
    rbx0 : X.readReg (X.State.regs s) rbx ≡ 0
    rbx0 = trans (C.scratch-eq dc) (cong (C.enc-sv hv) sc-eq)
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

stuck-c-branch-tag-zero : ∀ {hv : HeapView} ev env prog fs s m loc → CompiledCorr hv prog fs s
  → halted (floc fs) ≡ false
  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero m))
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
  → readLoc (floc fs) loc ≡ just (SV-Tag 0)
  → X.readMem (X.State.memory s) (X.readReg (X.State.regs s) rdi + 0) ≡ just 0
  → find-label prog m ≡ nothing
  → EE.StuckAt ev env (compile-trace prog) s
stuck-c-branch-tag-zero ev env prog fs s m loc cc h ftq i-eq r-eq rd fl-eq =
  3 , trans (RTx.run-events-noncall val-x86-64 ev env 2 (compile-trace prog) s
               (cmp (mem (base+disp rdi 0)) (imm 0)) halt-s fetch-cmp refl step-cmp)
      (trans (RTx.run-events-noncall val-x86-64 ev env 1 (compile-trace prog) post-cmp
               (je (once m)) halt-s fetch-je refl step-je)
             (RTx.run-events-halted val-x86-64 ev env 0 (compile-trace prog) post-je refl))
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

-- …and the supply record itself. Same role as `x86-64-block-steps`: the field
-- types come FROM the record, so an interface weakened to fit one arch breaks
-- here rather than silently.
x86-64-stuck-steps : EE.StuckSteps
x86-64-stuck-steps = record
  { st-load-indirect         = stuck-load-indirect
  ; st-load-indirect-suc     = stuck-load-indirect-suc
  ; st-c-jmp                 = stuck-c-jmp
  ; st-c-branch-scratch-zero = stuck-c-branch-scratch-zero
  ; st-c-branch-tag-zero     = stuck-c-branch-tag-zero
  }

postulate
  -- PER-INSTRUCTION DISPATCH residual for the cases not yet routed to `ccc-step`
  -- (instr-sigop arith/external, control jmp/branch, memory/frame/slot). Shrinks as
  -- each is wired (arith→run-events-arith, external→run-events-external+contract, …).
  -- `events-running-case` RETIRED (Plan 0.54 item 6, 2026-08-01): `case`
  -- compiles to FLAT control, `instr-case-on-tag` has no producer, and the
  -- nested-trace correspondence it demanded is not needed at all — the
  -- dispatch clause is `⊥`-elim like the frame ops.
  -- THE CALL SITE'S SHAPE (D098). `events-running-call` is GONE — the
  -- correspondence for the call is the theorem `call-step` below, over the
  -- proven `block-step-call`. What is left is the DATAFLOW at the site, in the
  -- `branch-tag-zero`/D073 mould: at an emitted `instr-call-closure` the
  -- closure register holds a live heap pointer whose SECOND cell holds a code
  -- address naming a body that exists.
  --
  -- Every conjunct is what the emitter arranges: `apply`'s trace loads the
  -- closure pointer into `%r12` (`instr-save-closure-reg`) after the `curry`
  -- clause built the record with `instr-alloc-heap 2` and wrote
  -- `instr-load-code-addr (ℓ o this)` into its second cell — and emitted the
  -- matching `c-thunk (ℓ o this)`. No `X.State` in the type: this is a fact
  -- about the ABSTRACT machine, and its discharge is the typed shape checker
  -- (the same route the other dataflow disciplines take) plus the
  -- `emitted-thunk-guarded` induction for the body's existence.
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
-- THE FLAT MACHINE'S WELL-FORMEDNESS LAYER IS ARCH-GENERIC (Plan 0.65 G1d).
--
-- 1,099 lines lived here and mentioned the machine ZERO times — no `X.State`,
-- no register, no state literal, and not even the correspondence. They are
-- facts about the ABSTRACT machine and the EMITTER, which all three arches
-- share, so they now live in `FlatCore.RunWF` and this module INSTANTIATES
-- them. Ten of the imports above are machine-specific and none of them is
-- needed there; that is the same statement, mechanically.
--
-- The three obligations it consumes stay HERE, as the residuals the ledger
-- already records, and are passed in.
------------------------------------------------------------------------
-- …and the seven ARCH-GENERIC RESIDUALS moved with them (G1d step 2). They are
-- assumed once in the core now, so riscv64 and x86-32 consume the same seven
-- instead of each declaring their own copy. What stayed here is the two that
-- really are x86-64s — arith-sigop-contract and external-sigop-contract, both
-- quantified over HeapView and the x86-64 arith runtime.
open import Once.Adequacy.ArchCorrectness.FlatCore.RunWF o FS slot-size word-eq
  public

-- The event-trace induction, fully with-FREE (J-style aux bridges for every case
-- split — no `with … in` goal-abstraction). `ccc-step` is the reusable CCC engine:
-- one abstract step ↦ its compiled block (block-step-any) mirrored into run-events
-- (the proven block-run-exec), then recurse (events-agree). Mutual on the fuel n.
------------------------------------------------------------------------
-- THE DISPATCH IS THE CORE'S NOW (plan 0.65 G2 item 4, slice 3).
--
-- What was ~900 lines here — `events-agree`, `events-running-fetch`,
-- `ccc-step-bs` and the fifteen per-instruction helpers — is written once in
-- `FlatCore.EventDispatch`. x86-64 supplies the record below and gets the
-- whole induction back.
------------------------------------------------------------------------
x86-64-supply : EE.Supply
x86-64-supply = record
  { bss = x86-64-block-steps ; sts = x86-64-stuck-steps
  ; heap-room = heap-room ; stack-room = stack-room ; call-room = call-room
  ; reg-range = reg-range ; scratch-dec-guarded = scratch-dec-guarded
  ; ret-no-wrap = ret-no-wrap ; count-no-wrap = count-no-wrap
  ; tag-fits = tag-fits ; lit-fits = lit-fits ; float-fits = float-fits
  ; lo-fits = lo-fits
  ; arith-sigop-contract = arith-sigop-contract
  ; external-sigop-contract = external-sigop-contract
  }

module ED = Dispatch o FS slot-size word-eq Reg x86-64-roles X.W.modulus
                     x86-64-emitter x86-64-machine x86-64-traceloop
open ED.Dispatch x86-64-supply public
