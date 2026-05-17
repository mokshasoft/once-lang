-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRTraceCorrect  (Plan 0.10 Phase E, shared)
--
-- IR-side (semantic) correctness of the `ir-to-trace` lowering. This
-- proves: when the trace produced by `ir-to-trace ir` is executed on
-- the abstract LocState/AllocState machine, the result is a state in
-- which `eval ir x` is represented.
--
-- The theorem and ALL its per-IR sub-cases are FrameSemantics-only —
-- they do not depend on the target arch. Each architecture's
-- `Once.CCC.Target.<arch>.CompileCorrect` imports this module and only
-- has to add its own arch-specific `compile-trace-correct` (proven via
-- the per-arch `Simulation.trace-sim`).
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Per-IR audit status
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
--   id, fst, snd, terminal, initial, arr  — DISCHARGED via SimpleWFImpl
--                                            run-X + transport-trivial
--   out-μ, Out                            — DISCHARGED via SumRecWFImpl
--                                            run-X (Lambek identity)
--   free-heap                             — DISCHARGED via SimpleWFImpl
--                                            run-free-heap
--   _∘_                                   — POSTULATED (structural IH;
--                                            blocked on slot-frontier
--                                            invariance for sub-IRs)
--   ⟨_,_⟩, curry, apply                   — POSTULATED (slot-frontier
--                                            alignment between
--                                            ir-to-trace's static `n`
--                                            and run-X's `next-slot
--                                            alloc`). Plan 0.14: Heap
--                                            variants have run-pair-heap /
--                                            run-curry-heap producers
--                                            with matching trace shapes;
--                                            still blocked on frontier.
--   inl, inr                              — Plan 0.14, 2026-05-17:
--                                            EXPLICITLY ROUTED via named
--                                            postulates (`ir-to-trace-
--                                            correct-inl`/`-inr`) instead
--                                            of the catchall. Same
--                                            slot-frontier mismatch as
--                                            pair/curry; Heap variants
--                                            have run-inl-heap / run-inr-
--                                            heap producers with matching
--                                            shapes.
--   case                                  — Plan 0.14, 2026-05-17:
--                                            EXPLICITLY ROUTED via named
--                                            postulate (relies on
--                                            SumRecWF.case-dispatch-{output,
--                                            alloc}-independent).
--   SigOp                                 — DERIVED from
--                                            `exec-sigop-respects-semM`
--                                            (Plan 0.11 task A); the
--                                            remaining trusted-base
--                                            axiom is the value-flow
--                                            obligation pinning
--                                            `result-loc = exec-sigop-
--                                            output si s`.
--   In, Cata, Para, in-ν, Ana, Hylo, Fuse
--                                         — POSTULATED catchall
--                                            (recursion schemes; routed
--                                            via `ir-to-trace-correct-
--                                            non-layer0`).
------------------------------------------------------------------------

module Once.CCC.Codegen.IRTraceCorrect where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; trans; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open FrameSemantics using (Frame)

open import Once.Type using (Type; _*_; _+_)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
  using (IR; AllocMode; Stack; Heap;
         id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
         curry; apply; arr;
         In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
         free-heap; SigOp)
open import Once.CCC.Eval using (eval)

open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; halted; regs; readReg; Input1;
         StoredValue; SV-Ptr;
         AbstractTrace; AbstractInstr;
         mov-to-output; mov-to-input;
         load-indirect; load-indirect-suc)
open import Once.CCC.Machine.Allocation using (AllocState; current-frame; next-slot)

open import Once.CCC.Codegen.IRToTrace using (ir-to-trace; ir-to-trace-at-frontier)

-- Plan 0.14 (2026-05-17): Dispatcher import for pair/curry/apply/case
-- discharges. The Dispatcher provides `run-ir-wf` which dispatches
-- any IR to its WF producer with the appropriate rec-wf threading.
-- IRTraceCorrect uses it as a recursive black-box for the complex
-- IR constructors that need RecDispatcherWF parameters.
import Once.CCC.Machine.Dispatcher as DispatcherModule
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat using (_<_)

------------------------------------------------------------------------
-- The proof framework is parameterized by FrameSemantics + program-bound,
-- + the recursive-dispatcher's well-founded accessibility + SigOp contract.
-- The latter two are required to discharge pair/curry/apply/case (which
-- internally invoke recursive dispatch on sub-IRs).
------------------------------------------------------------------------

module IRTraceCorrectness {FS : FrameSemantics} (program-bound : ℕ)
  (acc-pb : Acc _<_ program-bound)
  (sigOp-proof : DispatcherModule.SigOpContract.Provider {FS} program-bound)
  where

  open Once.CCC.Machine.SMCore.MemOps {FS}
  open Once.CCC.Machine.SMCore.ExecFinal {FS}
  open Once.CCC.Machine.SMCore.AbstractExec {FS}

  -- exec-abstract preservation helpers (for load-indirect / load-indirect-suc
  -- which case-split on sv-as-loc and need explicit alloc-preserved proofs).
  open import Once.CCC.Machine.SMPrimitives as SMP hiding (AllocMode)
  open SMP.RecSchemeSemantics {FS}
    using (exec-abstract-load-indirect-preserves-alloc;
           exec-abstract-load-indirect-suc-preserves-alloc)
  open import Once.CCC.SigOp.Info using (SigOpInfo; semM)
  open import Once.CCC.Machine.SMCore using (mkLocState; stackMem; heapMem; writeReg; Output; instr-sigop)

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; place-loc; place-valid)

  open Once.CCC.Machine.Allocation.FrontierInvariant {FS}
    using (BeforeFrontier)

  -- For per-IR discharges we instantiate run-X helpers from the
  -- existing WF modules. Their traces match `ir-to-trace`'s exactly;
  -- the theorem follows by extracting `result-valid-wf` from the
  -- returned `IRResultAWF` and transporting along
  --   `proj₂ (exec-trace (i ∷ []) s alloc) ≡ alloc`.
  import Once.CCC.Machine.IR.SimpleWF as SimpleWFModule
  open SimpleWFModule.SimpleWFImpl {FS} program-bound
    using (run-id; run-fst; run-snd; run-terminal; run-arr; run-free-heap)

  import Once.CCC.Machine.IR.SumRecWF as SumRecWFModule
  open SumRecWFModule.SumRecWFImpl {FS} program-bound
    using (run-initial; run-out-μ; run-Out; run-inl; run-inr)

  -- Heap-mode IR producers — used by the layer-2 heap bridges below.
  import Once.CCC.Machine.IR.SumInlHeapWF as SumInlHeapWFModule
  open SumInlHeapWFModule.SumInlHeapWFImpl {FS} program-bound
    using (run-inl-heap)

  import Once.CCC.Machine.IR.SumInrHeapWF as SumInrHeapWFModule
  open SumInrHeapWFModule.SumInrHeapWFImpl {FS} program-bound
    using (run-inr-heap)

  import Once.CCC.Machine.IR.CurryHeapWF as CurryHeapWFModule
  open CurryHeapWFModule.CurryHeapWFImpl {FS} program-bound
    using (run-curry-heap)

  -- Dispatcher: provides run-ir-wf as a well-founded recursive
  -- dispatcher for sub-IR computation. Used by pair/curry/apply/case
  -- to satisfy their RecDispatcherWF parameter.
  open DispatcherModule.Dispatcher {FS} program-bound acc-pb sigOp-proof
    using (run-ir-wf)
  open import Data.Nat.Properties using (<-trans)
  open import Once.CCC.IR.Size using (ir-size)

  -- Construct RecDispatcherWF at any size bound `n` from acc-pb +
  -- `n < program-bound`. Mirrors Dispatcher.make-rec-wf: given the
  -- predecessor-accessibility extracted from acc-pb at this bound,
  -- delegate to run-ir-wf for each sub-IR with the threaded accessibility.
  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (RecDispatcherWF) public

  -- Helper: destructure acc-pb to peel off accessibility at any smaller size.
  -- Mirrors Dispatcher.make-rec-wf's internal Acc threading. Implemented
  -- via direct application of Acc's `rs` projection (since `with acc-pb`
  -- isn't allowed — acc-pb is bound in the module telescope).
  acc-rs : ∀ {n} → Acc _<_ n → ∀ {m} → m < n → Acc _<_ m
  acc-rs (acc rs) lt = rs lt

  make-rec-wf : ∀ {n} (n<bound : n < program-bound) → RecDispatcherWF n
  make-rec-wf {n} n<bound mIn ir lt x' input-loc' s' alloc' valid' before' not-halted' rdi-eq' =
    let acc-n : Acc _<_ n
        acc-n = acc-rs acc-pb n<bound
        acc-ir : Acc _<_ (ir-size ir)
        acc-ir = acc-rs acc-n lt
    in run-ir-wf mIn ir (<-trans lt n<bound) x' input-loc' s' alloc'
         valid' before' not-halted' rdi-eq' acc-ir

  ----------------------------------------------------------------------
  -- Theorem signature, factored out so per-IR cases can refer to it.
  ----------------------------------------------------------------------

  -- Plan 0.14 (2026-05-17): trace is taken at the alloc's current
  -- frontier so it matches the slot indexing run-X helpers in IR/*WF
  -- use. At the runtime entry point (compile-correct, next-slot = 0)
  -- this reduces to `ir-to-trace ir`.
  --
  -- ir<bound precondition: the IR's size is bounded by the program's
  -- total size. Needed by pair/curry/apply/case discharges to invoke
  -- the Dispatcher's well-founded run-ir-wf for sub-IR computation.
  -- For non-recursive constructors (id/fst/snd/etc.) the witness is
  -- unused — they thread it through without inspection.
  IRTraceCorrect : ∀ {A B} → IR A B → Set
  IRTraceCorrect {A} {B} ir =
    ir-size ir < program-bound →
    ∀ (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    let result = exec-trace (ir-to-trace-at-frontier (next-slot alloc) ir) s alloc
        final-s = proj₁ result
        final-alloc = proj₂ result
    in ∃[ mOut ] ∃[ result-loc ]
       ValidAtWF mOut final-alloc (eval ir x) result-loc final-s

  ----------------------------------------------------------------------
  -- Trivial discharges via SimpleWFImpl + the transport helper.
  ----------------------------------------------------------------------

  private
    -- Convert `ValidAtWF m alloc v loc state` (what IRResultAWF gives,
    -- since run-X always sets `final-alloc = alloc` for non-allocating
    -- IRs) into `ValidAtWF m (proj₂ (exec-trace (i ∷ []) s alloc)) v
    -- loc (proj₁ (exec-trace (i ∷ []) s alloc))`. The state position
    -- is already definitionally equal because run-X defines
    -- `final-state = proj₁ (exec-trace trace s alloc)`.
    --
    -- Caller supplies `alloc-eq : proj₂ (exec-abstract i s alloc) ≡
    -- alloc`, which holds definitionally for non-allocating
    -- instructions (mov-to-output, load-indirect, load-indirect-suc).
    transport-trivial :
      ∀ {A B} {m : AllocMode}
        (i : AbstractInstr) (ir : IR A B) (x : ⟦ A ⟧)
        (loc : ValueLocation FS)
        (s : LocState FS) (alloc : AllocState {FS}) →
      halted s ≡ false →
      proj₂ (exec-abstract i s alloc) ≡ alloc →
      ValidAtWF m alloc (eval ir x) loc (proj₁ (exec-trace (i ∷ []) s alloc)) →
      let result = exec-trace (i ∷ []) s alloc
      in ValidAtWF m (proj₂ result) (eval ir x) loc (proj₁ result)
    transport-trivial i ir x loc s alloc not-halted alloc-eq v =
      let trace-eq : exec-trace (i ∷ []) s alloc ≡ exec-abstract i s alloc
          trace-eq = exec-trace-single i s alloc not-halted
          alloc-fix : proj₂ (exec-trace (i ∷ []) s alloc) ≡ alloc
          alloc-fix = trans (cong proj₂ trace-eq) alloc-eq
      in subst (λ a → ValidAtWF _ a (eval ir x) loc
                        (proj₁ (exec-trace (i ∷ []) s alloc)))
               (sym alloc-fix)
               v

  ir-to-trace-correct-id : ∀ {A} → IRTraceCorrect (id {A})
  ir-to-trace-correct-id _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-id x input-loc s alloc valid before not-halted rdi-eq
    in mIn , place-loc (IRResultAWF.result-place r) ,
       transport-trivial mov-to-output id x input-loc s alloc
         not-halted refl (place-valid (IRResultAWF.result-place r))

  ir-to-trace-correct-fst : ∀ {A B} → IRTraceCorrect (fst {A} {B})
  ir-to-trace-correct-fst _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let (mA , r) = run-fst x input-loc s alloc valid before not-halted rdi-eq
    in mA , place-loc (IRResultAWF.result-place r) ,
       transport-trivial load-indirect fst x (place-loc (IRResultAWF.result-place r)) s alloc
         not-halted
         (exec-abstract-load-indirect-preserves-alloc s alloc)
         (place-valid (IRResultAWF.result-place r))

  ir-to-trace-correct-snd : ∀ {A B} → IRTraceCorrect (snd {A} {B})
  ir-to-trace-correct-snd _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let (mB , r) = run-snd x input-loc s alloc valid before not-halted rdi-eq
    in mB , place-loc (IRResultAWF.result-place r) ,
       transport-trivial load-indirect-suc snd x (place-loc (IRResultAWF.result-place r)) s alloc
         not-halted
         (exec-abstract-load-indirect-suc-preserves-alloc s alloc)
         (place-valid (IRResultAWF.result-place r))

  ir-to-trace-correct-terminal : ∀ {A} → IRTraceCorrect (terminal {A})
  ir-to-trace-correct-terminal {A} _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-terminal {mIn} {A} x input-loc s alloc valid before not-halted rdi-eq
    -- terminal emits []; exec-trace [] s alloc = (s, alloc) so
    -- place-valid threads directly without transport.
    in mIn , place-loc (IRResultAWF.result-place r) ,
       place-valid (IRResultAWF.result-place r)

  -- initial: input type is Void, so caller can never invoke us with a
  -- valid x. Absurd-eliminated.
  ir-to-trace-correct-initial : ∀ {A} → IRTraceCorrect (initial {A})
  ir-to-trace-correct-initial _ mIn () _ _ _ _ _ _ _

  ir-to-trace-correct-arr : ∀ {A B q} → IRTraceCorrect (arr {A} {B} {q})
  ir-to-trace-correct-arr {A} {B} {q} _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-arr {mIn} {A} {B} {q} x input-loc s alloc valid before not-halted rdi-eq
    in mIn , place-loc (IRResultAWF.result-place r) ,
       transport-trivial mov-to-output (arr {A} {B} {q}) x
         (place-loc (IRResultAWF.result-place r)) s alloc
         not-halted refl (place-valid (IRResultAWF.result-place r))

  ir-to-trace-correct-free-heap : (ref : _) → IRTraceCorrect (free-heap ref)
  ir-to-trace-correct-free-heap ref _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-free-heap ref x input-loc s alloc valid before not-halted rdi-eq
    in mIn , place-loc (IRResultAWF.result-place r) ,
       transport-trivial mov-to-output (free-heap ref) x
         (place-loc (IRResultAWF.result-place r)) s alloc
         not-halted refl (place-valid (IRResultAWF.result-place r))

  -- out-μ / Out: μ/ν Lambek inverses, semantically the identity. run-X
  -- emits `mov-to-output ∷ []`; ir-to-trace mirrors. Same shape as
  -- id/arr/free-heap discharges.
  ir-to-trace-correct-out-μ : ∀ {F} (wf : _) → IRTraceCorrect (out-μ {F} wf)
  ir-to-trace-correct-out-μ {F} wf _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-out-μ wf mIn x input-loc s alloc valid before not-halted rdi-eq
    in _ , place-loc (IRResultAWF.result-place r) ,
       transport-trivial mov-to-output (out-μ wf) x
         (place-loc (IRResultAWF.result-place r)) s alloc
         not-halted refl (place-valid (IRResultAWF.result-place r))

  ir-to-trace-correct-Out : ∀ {F} (wf : _) → IRTraceCorrect (Out {F} wf)
  ir-to-trace-correct-Out {F} wf _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-Out wf mIn x input-loc s alloc valid before not-halted rdi-eq
    in _ , place-loc (IRResultAWF.result-place r) ,
       transport-trivial mov-to-output (Out wf) x
         (place-loc (IRResultAWF.result-place r)) s alloc
         not-halted refl (place-valid (IRResultAWF.result-place r))

  ----------------------------------------------------------------------
  -- Plan 0.14 (2026-05-17): inl/inr discharges via the run-X helpers.
  -- After the slot-frontier alignment refactor (ir-to-trace-at-frontier
  -- in IRToTrace.agda), the trace emitted by IRToTrace with the alloc's
  -- frontier definitionally matches the run-X-{,heap} trace. The bridge
  -- then transports `place-valid (result-place r)` (which lives at
  -- `(final-state r, final-alloc r)`) to the IRTraceCorrect outer goal
  -- (which lives at `(proj₁ exec-trace, proj₂ exec-trace)`) via
  -- `trace-correct` and `alloc-correct`.
  --
  -- For heap-mode constructors, `alloc-correct` is currently SMP.!! in
  -- the run-X-heap modules (deep Phase C obligation). The discharge
  -- here uses that postulate as a black box — when Phase C lands, the
  -- bridge becomes a real proof end-to-end.
  ----------------------------------------------------------------------

  -- Stack-mode inl postulated pending SumRecWF.inl-trace shape alignment
  -- with IRToTrace (SumRecWF currently emits `instr-alloc-stack ∷ ...`
  -- while IRToTrace omits it since the function prologue handles slot
  -- allocation). Not reached at runtime — elaborator emits `inl Heap`
  -- (Desugar.agda:64). Discharging requires either dropping
  -- instr-alloc-stack from SumRecWF.inl-trace (ripples to
  -- inl-inr-trace-alloc-correct + alloc-final) or adding it back to
  -- IRToTrace (changes runtime).
  postulate
    ir-to-trace-correct-inl-stack :
      ∀ {A B} → IRTraceCorrect (inl {A} {B} Stack)
    ir-to-trace-correct-inr-stack :
      ∀ {A B} → IRTraceCorrect (inr {A} {B} Stack)

  ir-to-trace-correct-inl :
    ∀ {A B} (m : AllocMode) → IRTraceCorrect (inl {A} {B} m)
  ir-to-trace-correct-inl Stack = ir-to-trace-correct-inl-stack
  ir-to-trace-correct-inl {A} {B} Heap _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-inl-heap {A} {B} mIn x input-loc s alloc valid before not-halted rdi-eq
        pv = place-valid (IRResultAWF.result-place r)
        tc = IRResultAWF.trace-correct r
        ac = IRResultAWF.alloc-correct r
        trace = ir-to-trace-at-frontier (next-slot alloc) (inl {A} {B} Heap)
    in Heap , place-loc (IRResultAWF.result-place r) ,
       subst (λ st → ValidAtWF Heap (proj₂ (exec-trace trace s alloc))
                                (eval (inl Heap) x)
                                (place-loc (IRResultAWF.result-place r)) st)
             (sym tc)
             (subst (λ al → ValidAtWF Heap al (eval (inl Heap) x)
                                (place-loc (IRResultAWF.result-place r))
                                (IRResultAWF.final-state r))
                    (sym ac)
                    pv)

  ir-to-trace-correct-inr :
    ∀ {A B} (m : AllocMode) → IRTraceCorrect (inr {A} {B} m)
  ir-to-trace-correct-inr Stack = ir-to-trace-correct-inr-stack
  ir-to-trace-correct-inr {A} {B} Heap _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-inr-heap {A} {B} mIn x input-loc s alloc valid before not-halted rdi-eq
        pv = place-valid (IRResultAWF.result-place r)
        tc = IRResultAWF.trace-correct r
        ac = IRResultAWF.alloc-correct r
        trace = ir-to-trace-at-frontier (next-slot alloc) (inr {A} {B} Heap)
    in Heap , place-loc (IRResultAWF.result-place r) ,
       subst (λ st → ValidAtWF Heap (proj₂ (exec-trace trace s alloc))
                                (eval (inr Heap) x)
                                (place-loc (IRResultAWF.result-place r)) st)
             (sym tc)
             (subst (λ al → ValidAtWF Heap al (eval (inr Heap) x)
                                (place-loc (IRResultAWF.result-place r))
                                (IRResultAWF.final-state r))
                    (sym ac)
                    pv)

  ----------------------------------------------------------------------
  -- Postulated per-IR cases. Audit handles for future discharges.
  ----------------------------------------------------------------------

  postulate
    -- Plan 0.14 (2026-05-17): the slot-frontier alignment (the IRTraceCorrect
    -- signature now uses ir-to-trace-at-frontier (next-slot alloc) ir) and
    -- Dispatcher import (make-rec-wf above) UNBLOCK the discharge framework
    -- for these four. The remaining obstacle is per-IR trace-shape alignment
    -- between IRToTrace and the WF spec:
    --
    --   - PairHeapWF.setup-trace contains `instr-alloc-stack pair-heap-overhead`
    --     which IRToTrace omits (function prologue handles slot allocation).
    --   - CurryHeapWF uses `instr-load-code-addr 0` (placeholder label);
    --     IRToTrace uses `instr-load-code-addr this-label` (the actual
    --     parent-emitted label counter value).
    --   - case's run-case dispatcher chains through SumRecWF.case-dispatch-
    --     {output,alloc}-independent (themselves postulates).
    --   - compose's discharge needs trace-decomposition: ir-to-trace (g ∘ f)
    --     = ft ++ mov-to-input ∷ gt, with the sub-IH applied separately to
    --     f at frontier n and g at frontier n1. Doable structurally but
    --     requires several intermediate lemmas.
    --
    -- Each is mechanical once the WF specs are aligned with IRToTrace.
    -- Postulates kept here as the named handles for those alignments.
    ir-to-trace-correct-compose : ∀ {A B C} (g : IR B C) (f : IR A B) →
      IRTraceCorrect (g ∘ f)
    ir-to-trace-correct-pair :
      ∀ {A B C} (m : AllocMode) (f : IR A B) (g : IR A C) →
      IRTraceCorrect (⟨_,_⟩ {A} {B} {C} f g m)
    -- Stack-mode curry: postulated. CurryWF (Stack) emits
    -- `lea-slot closure-stash` for the code-pointer cell, which
    -- produces SV-Ptr (self-reference fiction). After the Option 1
    -- refactor, valid-closure-wf requires SV-Code at closure[1] —
    -- CurryWF's result-valid-wf' uses SMP.!! at that slot. Until
    -- CurryWF is migrated (or deleted; the elaborator never emits
    -- `curry _ Stack`), Stack-mode curry stays postulated.
    ir-to-trace-correct-curry-stack :
      ∀ {k A B C} (f : IR (A * B) C) →
      IRTraceCorrect (curry {k = k} {A} {B} {C} f Stack)

    -- Apply: same RecDispatcherWF threading as curry, plus closure-
    -- invariant + body-correct work. Postulated.
    ir-to-trace-correct-apply : ∀ {k A B} →
      IRTraceCorrect (apply {A} {B} {k})

    -- case: sum eliminator. Trace dispatches via instr-case-on-tag,
    -- with two branches each prefixed by load-indirect-suc + mov-to-input.
    -- Discharge via SumRecWF.case-trace-state-correct + case-trace-alloc-correct
    -- (themselves postulates on the case-dispatch-output-independent /
    -- alloc-independent axioms). Routed explicitly so this case isn't
    -- absorbed into the catchall.
    ir-to-trace-correct-case :
      ∀ {A B C} (f : IR A C) (g : IR B C) → IRTraceCorrect (case f g)

  ----------------------------------------------------------------------
  -- Plan 0.14 (2026-05-17): curry Heap discharge via run-curry-heap +
  -- make-rec-wf. The body label `0` in CurryHeapWF.curry-heap-trace
  -- matches IRToTrace's `this-label = 0` (since ir-to-trace-at-frontier
  -- always passes l=0 at the top), so the traces are definitionally
  -- equal. The bridge then transports place-valid through trace-correct
  -- and alloc-correct, exactly like inl/inr Heap above.
  ----------------------------------------------------------------------

  ir-to-trace-correct-curry :
    ∀ {k A B C} (f : IR (A * B) C) (m : AllocMode) →
    IRTraceCorrect (curry {k = k} {A} {B} {C} f m)
  ir-to-trace-correct-curry f Stack = ir-to-trace-correct-curry-stack f
  ir-to-trace-correct-curry {k} {A} {B} {C} f Heap ir<bound mIn x input-loc s alloc
                            valid before not-halted rdi-eq =
    let rec-wf = make-rec-wf ir<bound
        r = run-curry-heap {A} {B} {C} {k} mIn f ir<bound rec-wf x input-loc s alloc
              valid before not-halted rdi-eq
        pv = place-valid (IRResultAWF.result-place r)
        tc = IRResultAWF.trace-correct r
        ac = IRResultAWF.alloc-correct r
        trace = ir-to-trace-at-frontier (next-slot alloc) (curry {k = k} f Heap)
    in Heap , place-loc (IRResultAWF.result-place r) ,
       subst (λ st → ValidAtWF Heap (proj₂ (exec-trace trace s alloc))
                                (eval (curry {k = k} f Heap) x)
                                (place-loc (IRResultAWF.result-place r)) st)
             (sym tc)
             (subst (λ al → ValidAtWF Heap al (eval (curry {k = k} f Heap) x)
                                (place-loc (IRResultAWF.result-place r))
                                (IRResultAWF.final-state r))
                    (sym ac)
                    pv)

  postulate
    -- Plan 0.11 Task A — SigOp value-flow trusted-base axiom.
    --
    -- After Plan 0.11 task A's structuring of `exec-abstract
    -- (instr-sigop si)` (now consults `exec-sigop-output` and
    -- `exec-sigop-halts`), the post-state `final-s` is definitionally
    --   record s { regs   = writeReg (regs s) Output (exec-sigop-output si s)
    --            ; halted = exec-sigop-halts si s }
    -- and `final-alloc = alloc`.
    --
    -- The remaining trusted-base obligation is: at this `final-s`,
    -- the location `exec-sigop-output si s` is `ValidAtWF` for
    -- `semM si x` at some output mode. Per-name discharge replaces
    -- this with per-(name) lemmas tied to `SigOpInfo.semM`.
    --
    -- This axiom is more constrained than the older
    -- `ir-to-trace-correct-sigop` postulate: it pre-commits the
    -- `result-loc` to `exec-sigop-output si s` instead of leaving it
    -- existential. That makes per-name discharge tractable — the
    -- per-name implementor only needs to prove validity for one
    -- specific location, not invent one.
    --
    -- Paired with `Simulation.sigop-codegen-faithful` (one per arch),
    -- which links the codegen output of `compile-sigOp name` to
    -- `exec-abstract (instr-sigop si)`. The two together close the
    -- semantic chain for SigOps.
    -- Plan 0.14 (2026-05-17): exec-sigop-output returns StoredValue, not
    -- ValueLocation, after Plan 0.2.4.5 Stage B Input1-as-StoredValue.
    -- The result-loc claimed by the SigOp validity now lives in
    -- StoredValue space; we existentialize it for the proof to make
    -- the SigOp bridge re-typecheck. Per-name SigOp discharge can
    -- pin this when needed.
    exec-sigop-respects-semM :
      ∀ {A B} (si : SigOpInfo A B)
        (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
        (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF mIn alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) Input1 ≡ SV-Ptr input-loc →
      ∃[ mOut ] ∃[ result-loc ]
        ValidAtWF mOut alloc (semM si x) result-loc
          (mkLocState (writeReg (regs s) Output (exec-sigop-output si s))
                      (stackMem s) (heapMem s)
                      (exec-sigop-halts si s))

    -- Sums and recursion schemes (Layer 0 doesn't use; ir-to-trace
    -- stubs all to []). Catchall named postulate; should be split
    -- per-IR when Layer 1+ work begins.
    ir-to-trace-correct-non-layer0 : ∀ {A B} (ir : IR A B) → IRTraceCorrect ir

  ----------------------------------------------------------------------
  -- Plan 0.11 Task A — DERIVED from `exec-sigop-respects-semM`.
  --
  -- This was previously the postulate `ir-to-trace-correct-sigop`.
  -- Now it is a real derivation: given the trusted-base axiom about
  -- the post-state's Output validity, the IRTraceCorrect obligation
  -- follows by pinning `result-loc = exec-sigop-output si s` and
  -- transporting the validity through `exec-trace`'s definitional
  -- reduction on a single-instruction trace.
  ----------------------------------------------------------------------

  ir-to-trace-correct-sigop : ∀ {A B} (si : SigOpInfo A B) →
    IRTraceCorrect (SigOp {A} {B} si)
  ir-to-trace-correct-sigop si _ mIn x input-loc s alloc valid before not-halted rdi-eq =
    let
      (mOut , result-loc , v) = exec-sigop-respects-semM si mIn x input-loc s alloc
                                  valid before not-halted rdi-eq
      -- exec-trace (instr-sigop si ∷ []) s alloc reduces to
      -- exec-abstract (instr-sigop si) s alloc when not halted.
      trace-eq : exec-trace (instr-sigop si ∷ []) s alloc
               ≡ exec-abstract (instr-sigop si) s alloc
      trace-eq = exec-trace-single (instr-sigop si) s alloc not-halted
    in mOut , result-loc ,
       subst (λ result → ValidAtWF mOut (proj₂ result) (semM si x)
                                   result-loc (proj₁ result))
             (sym trace-eq)
             v

  ----------------------------------------------------------------------
  -- Aggregate `ir-to-trace-correct` dispatching on IR.
  ----------------------------------------------------------------------

  ir-to-trace-correct : ∀ {A B} (ir : IR A B) → IRTraceCorrect ir
  ir-to-trace-correct id            = ir-to-trace-correct-id
  ir-to-trace-correct fst           = ir-to-trace-correct-fst
  ir-to-trace-correct snd           = ir-to-trace-correct-snd
  ir-to-trace-correct terminal      = ir-to-trace-correct-terminal
  ir-to-trace-correct initial       = ir-to-trace-correct-initial
  ir-to-trace-correct arr           = ir-to-trace-correct-arr
  ir-to-trace-correct (free-heap r) = ir-to-trace-correct-free-heap r
  ir-to-trace-correct (g ∘ f)       = ir-to-trace-correct-compose g f
  ir-to-trace-correct (⟨ f , g ⟩ m) = ir-to-trace-correct-pair m f g
  ir-to-trace-correct (curry f m)   = ir-to-trace-correct-curry f m
  ir-to-trace-correct apply         = ir-to-trace-correct-apply
  ir-to-trace-correct (SigOp si)    = ir-to-trace-correct-sigop si
  ir-to-trace-correct (out-μ wf)    = ir-to-trace-correct-out-μ wf
  ir-to-trace-correct (Out wf)      = ir-to-trace-correct-Out wf
  -- Layer 2 sum constructors (Plan 0.14, 2026-05-17): explicit clauses
  -- via the heap-mode IRToTrace alignment + run-inl-heap / run-inr-heap.
  ir-to-trace-correct (inl m)       = ir-to-trace-correct-inl m
  ir-to-trace-correct (inr m)       = ir-to-trace-correct-inr m
  ir-to-trace-correct (case f g)    = ir-to-trace-correct-case f g
  -- Remaining IR ctors (recursion schemes, transformations) — Layer 0/1/2
  -- don't use them. Routed through the named catchall postulate.
  {-# CATCHALL #-}
  ir-to-trace-correct ir            = ir-to-trace-correct-non-layer0 ir
