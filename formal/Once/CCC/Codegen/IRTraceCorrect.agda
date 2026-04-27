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
--   _∘_                                   — POSTULATED (structural IH;
--                                            blocked on slot-frontier
--                                            invariance for sub-IRs)
--   ⟨_,_⟩, curry, apply                   — POSTULATED (slot-frontier
--                                            alignment between
--                                            ir-to-trace's static `n`
--                                            and run-X's `next-slot
--                                            alloc`)
--   SigOp                                 — POSTULATED (delegated to
--                                            RuntimeContract.sigOp-proof)
--   free-heap                             — POSTULATED (empty-trace
--                                            transport)
--   inl, inr, case, In, out-μ, Cata,
--     Para, Out, in-ν, Ana, Hylo, Fuse    — POSTULATED catchall (Layer 0
--                                            doesn't use; ir-to-trace
--                                            stubs to [])
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
  using (IR; AllocMode;
         id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
         curry; apply; arr;
         In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
         free-heap; SigOp)
open import Once.CCC.Eval using (eval)

open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; halted; regs; readReg; Input;
         AbstractTrace; AbstractInstr;
         mov-to-output; mov-to-input;
         load-indirect; load-indirect-suc)
open import Once.CCC.Machine.Allocation using (AllocState; current-frame)

open import Once.CCC.Codegen.IRToTrace using (ir-to-trace)

------------------------------------------------------------------------
-- The proof framework is parameterized by FrameSemantics + program-bound,
-- matching the per-IR run-X helpers in SimpleWFImpl/SumRecWFImpl.
------------------------------------------------------------------------

module IRTraceCorrectness {FS : FrameSemantics} (program-bound : ℕ) where

  open Once.CCC.Machine.SMCore.MemOps {FS}
  open Once.CCC.Machine.SMCore.ExecFinal {FS}
  open Once.CCC.Machine.SMCore.AbstractExec {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF)

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
    using (run-initial; run-out-μ; run-Out)

  ----------------------------------------------------------------------
  -- Theorem signature, factored out so per-IR cases can refer to it.
  ----------------------------------------------------------------------

  IRTraceCorrect : ∀ {A B} → IR A B → Set
  IRTraceCorrect {A} {B} ir =
    ∀ (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    let result = exec-trace (ir-to-trace ir) s alloc
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
  ir-to-trace-correct-id mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-id x input-loc s alloc valid before not-halted rdi-eq
    in mIn , IRResultAWF.result-loc r ,
       transport-trivial mov-to-output id x input-loc s alloc
         not-halted refl (IRResultAWF.result-valid-wf r)

  ir-to-trace-correct-fst : ∀ {A B} → IRTraceCorrect (fst {A} {B})
  ir-to-trace-correct-fst mIn x input-loc s alloc valid before not-halted rdi-eq =
    let (mA , r) = run-fst x input-loc s alloc valid before not-halted rdi-eq
    in mA , IRResultAWF.result-loc r ,
       transport-trivial load-indirect fst x (IRResultAWF.result-loc r) s alloc
         not-halted refl (IRResultAWF.result-valid-wf r)

  ir-to-trace-correct-snd : ∀ {A B} → IRTraceCorrect (snd {A} {B})
  ir-to-trace-correct-snd mIn x input-loc s alloc valid before not-halted rdi-eq =
    let (mB , r) = run-snd x input-loc s alloc valid before not-halted rdi-eq
    in mB , IRResultAWF.result-loc r ,
       transport-trivial load-indirect-suc snd x (IRResultAWF.result-loc r) s alloc
         not-halted refl (IRResultAWF.result-valid-wf r)

  ir-to-trace-correct-terminal : ∀ {A} → IRTraceCorrect (terminal {A})
  ir-to-trace-correct-terminal {A} mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-terminal {mIn} {A} x input-loc s alloc valid before not-halted rdi-eq
    in mIn , IRResultAWF.result-loc r ,
       transport-trivial mov-to-output (terminal {A}) x (IRResultAWF.result-loc r) s alloc
         not-halted refl (IRResultAWF.result-valid-wf r)

  -- initial: input type is Void, so caller can never invoke us with a
  -- valid x. Absurd-eliminated.
  ir-to-trace-correct-initial : ∀ {A} → IRTraceCorrect (initial {A})
  ir-to-trace-correct-initial mIn () _ _ _ _ _ _ _

  ir-to-trace-correct-arr : ∀ {A B q} → IRTraceCorrect (arr {A} {B} {q})
  ir-to-trace-correct-arr {A} {B} {q} mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-arr {mIn} {A} {B} {q} x input-loc s alloc valid before not-halted rdi-eq
    in mIn , IRResultAWF.result-loc r ,
       transport-trivial mov-to-output (arr {A} {B} {q}) x
         (IRResultAWF.result-loc r) s alloc
         not-halted refl (IRResultAWF.result-valid-wf r)

  ir-to-trace-correct-free-heap : (ref : _) → IRTraceCorrect (free-heap ref)
  ir-to-trace-correct-free-heap ref mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-free-heap ref x input-loc s alloc valid before not-halted rdi-eq
    in mIn , IRResultAWF.result-loc r ,
       transport-trivial mov-to-output (free-heap ref) x
         (IRResultAWF.result-loc r) s alloc
         not-halted refl (IRResultAWF.result-valid-wf r)

  -- out-μ / Out: μ/ν Lambek inverses, semantically the identity. run-X
  -- emits `mov-to-output ∷ []`; ir-to-trace mirrors. Same shape as
  -- id/arr/free-heap discharges.
  ir-to-trace-correct-out-μ : ∀ {F} (wf : _) → IRTraceCorrect (out-μ {F} wf)
  ir-to-trace-correct-out-μ {F} wf mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-out-μ wf mIn x input-loc s alloc valid before not-halted rdi-eq
    in _ , IRResultAWF.result-loc r ,
       transport-trivial mov-to-output (out-μ wf) x
         (IRResultAWF.result-loc r) s alloc
         not-halted refl (IRResultAWF.result-valid-wf r)

  ir-to-trace-correct-Out : ∀ {F} (wf : _) → IRTraceCorrect (Out {F} wf)
  ir-to-trace-correct-Out {F} wf mIn x input-loc s alloc valid before not-halted rdi-eq =
    let r = run-Out wf mIn x input-loc s alloc valid before not-halted rdi-eq
    in _ , IRResultAWF.result-loc r ,
       transport-trivial mov-to-output (Out wf) x
         (IRResultAWF.result-loc r) s alloc
         not-halted refl (IRResultAWF.result-valid-wf r)

  ----------------------------------------------------------------------
  -- Postulated per-IR cases. Audit handles for future discharges.
  ----------------------------------------------------------------------

  postulate
    -- Compose: structural IH. Trace = ft ++ mov-to-input ∷ gt where
    -- ft = ir-to-trace f, but gt = ir-to-trace' n1 g (slot-shifted),
    -- so IH on g doesn't directly apply unless g is frontier-invariant.
    ir-to-trace-correct-compose : ∀ {A B C} (g : IR B C) (f : IR A B) →
      IRTraceCorrect (g ∘ f)

    -- Pair, curry, apply: ir-to-trace uses `0` as its slot frontier
    -- base, while run-X uses `next-slot alloc`. Discharge requires
    -- precondition `next-slot alloc ≡ 0` or refactoring ir-to-trace
    -- to take the alloc's frontier.
    ir-to-trace-correct-pair :
      ∀ {A B C} (m : AllocMode) (f : IR A B) (g : IR A C) →
      IRTraceCorrect (⟨_,_⟩ {A} {B} {C} f g m)
    ir-to-trace-correct-curry :
      ∀ {k A B C} (f : IR (A * B) C) (m : AllocMode) →
      IRTraceCorrect (curry {k = k} f m)
    ir-to-trace-correct-apply : ∀ {k A B} →
      IRTraceCorrect (apply {A} {B} {k})

    -- SigOp: TRACE SHAPE MISMATCH between ir-to-trace and Dispatcher.
    -- ir-to-trace emits `instr-sigop name ∷ []` (decoded by per-arch
    -- compile-abstract to actual syscall sequences), while
    -- Dispatcher.run-sigOp emits `mov-to-output ∷ []` (treats SigOp as
    -- a pure pass-through value-flow). The two views are about
    -- DIFFERENT objects: the verified Dispatcher proves correctness of
    -- the abstract (no-op) semantics; ir-to-trace adds a new layer
    -- (real syscall codegen). Discharging this postulate requires
    -- either strengthening `exec-abstract (instr-sigop _)` to model
    -- the operation's effect on Output, or aligning ir-to-trace's
    -- SigOp clause with Dispatcher's `mov-to-output` (which would lose
    -- the syscall codegen path). Tracked as part of trusted base.
    ir-to-trace-correct-sigop : ∀ {A B} (si : _) →
      IRTraceCorrect (SigOp {A} {B} si)

    -- Sums and recursion schemes (Layer 0 doesn't use; ir-to-trace
    -- stubs all to []). Catchall named postulate; should be split
    -- per-IR when Layer 1+ work begins.
    ir-to-trace-correct-non-layer0 : ∀ {A B} (ir : IR A B) → IRTraceCorrect ir

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
  -- All remaining IR ctors (sums, allocating recursion schemes,
  -- transformations) — Layer 0 doesn't use them. Routed through the
  -- named catchall postulate.
  {-# CATCHALL #-}
  ir-to-trace-correct ir            = ir-to-trace-correct-non-layer0 ir
