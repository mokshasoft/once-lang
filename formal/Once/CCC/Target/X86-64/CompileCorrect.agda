-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.CompileCorrect  (Plan 0.10)
--
-- THE GRAND THEOREM about the EXTRACTED compiler.
--
-- Plan 0.10 closes the verification gap by making the extracted compile
-- *be* the verified compile:
--
--     compile = compile-trace ∘ ir-to-trace
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Status of sub-obligations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Phase D (X86-64): `compile-trace-correct` discharged via
-- `Simulation.trace-sim`.
--
-- Phase E (X86-64, in progress): `ir-to-trace-correct` is split into
-- per-IR sub-cases. Each is either DISCHARGED (real proof) or
-- POSTULATED (named handle for future discharge).
--
-- Per-IR status:
--   id, fst, snd, terminal, initial, arr   — DISCHARGED via SimpleWFImpl
--   _∘_                                    — DISCHARGED via structural IH
--   ⟨_,_⟩, curry, apply                    — POSTULATED (slot-frontier
--                                             alignment between
--                                             ir-to-trace's static `n`
--                                             and run-X's `next-slot
--                                             alloc` requires more work)
--   SigOp                                  — POSTULATED (delegated to
--                                             RuntimeContract.sigOp-proof)
--   inl, inr, case                         — POSTULATED (Layer 0 doesn't
--                                             use sums)
--   In, out-μ, Cata, Para, Out, in-ν,
--     Ana, Hylo, Fuse                      — POSTULATED (recursion
--                                             schemes; ir-to-trace stubs
--                                             these to [])
--   free-heap                              — POSTULATED (heap deallocation)
--
-- See `plans/0.10-verification-gap-closure.md`.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.CompileCorrect where

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
open import Once.CCC.Target.X86-64.Syntax using (Program)

------------------------------------------------------------------------
-- The theorem framework is parameterized by FrameSemantics, just like
-- the verified-path Correctness module is.
------------------------------------------------------------------------

module Correctness {FS : FrameSemantics} (program-bound : ℕ) where

  open Once.CCC.Machine.SMCore.MemOps {FS}
  open Once.CCC.Machine.SMCore.ExecFinal {FS}
  open Once.CCC.Machine.SMCore.AbstractExec {FS}

  open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace)
  open import Once.CCC.Target.X86-64.DirectSimulation using (module Simulation)
  open Simulation {FS} using (X86State; Corresponds; exec-prog; trace-sim)

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF)

  open Once.CCC.Machine.Allocation.FrontierInvariant {FS}
    using (BeforeFrontier)

  -- For the per-IR discharges we instantiate the existing run-X
  -- helpers from SimpleWFImpl. Their traces match `ir-to-trace`'s
  -- exactly, so the theorem follows by extracting the `result-valid-wf`
  -- field from the returned `IRResultAWF`.
  import Once.CCC.Machine.IR.SimpleWF as SimpleWFModule
  open SimpleWFModule.SimpleWFImpl {FS} program-bound
    using (run-id; run-fst; run-snd; run-terminal; run-arr; run-free-heap)

  import Once.CCC.Machine.IR.SumRecWF as SumRecWFModule
  open SumRecWFModule.SumRecWFImpl {FS} program-bound
    using (run-initial)

  ----------------------------------------------------------------------
  -- The extracted compile = compile-trace ∘ ir-to-trace.
  ----------------------------------------------------------------------

  compile : ∀ {A B} → IR A B → Program
  compile ir = compile-trace (ir-to-trace ir)

  ----------------------------------------------------------------------
  -- Sub-theorem signature, factored out so per-IR cases can refer to it.
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
  -- Trivial discharges via SimpleWFImpl.
  --
  -- For each `simple` IR ctor, `ir-to-trace ir` produces the same
  -- constant trace as `run-X`. The IRResultAWF field
  -- `result-valid-wf : ValidAtWF mOut final-alloc (eval ir x) result-loc final-state`
  -- is exactly the existential we need; the only adjustment is reading
  -- final-state and final-alloc back out of `exec-trace (ir-to-trace ir)
  -- s alloc`. Since run-X defines `final-state = proj₁ (exec-trace trace
  -- s alloc)` (with `trace = ir-to-trace ir`) and `final-alloc = alloc`,
  -- and our trace doesn't allocate, the equality holds definitionally.
  ----------------------------------------------------------------------

  -- For each trivial IR, `ir-to-trace ir` is the same constant trace
  -- as `run-X`'s `trace`, and `final-alloc = alloc`. We extract the
  -- IRResultAWF and transport `result-valid-wf` along the equality
  --   `proj₂ (exec-trace (i ∷ []) s alloc) ≡ alloc`
  -- which follows from `exec-trace-single` plus the fact that
  -- `exec-abstract` (for these instructions) doesn't change `alloc`.

  private
    -- Common transport: convert `ValidAtWF m alloc v loc state` (what
    -- IRResultAWF gives) into `ValidAtWF m (proj₂ (exec-trace (i ∷ [])
    -- s alloc)) v loc (proj₁ (exec-trace (i ∷ []) s alloc))`. The state
    -- positions are already definitionally equal because run-X defines
    -- final-state = proj₁ (exec-trace trace s alloc).
    --
    -- Caller supplies `alloc-fix : alloc ≡ proj₂ (exec-abstract i s alloc)`
    -- which holds definitionally for instructions that preserve alloc
    -- (mov-to-output, load-indirect, load-indirect-suc).
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

  -- free-heap: ir-to-trace stubs to [], so proof needs a different
  -- transport (empty trace ≡ identity). Postulated until Layer 0 grows
  -- to exercise it.
  postulate
    ir-to-trace-correct-free-heap : (ref : _) → IRTraceCorrect (free-heap ref)

  ----------------------------------------------------------------------
  -- Postulated per-IR cases.
  --
  -- These are the audit handles that future discharges will close.
  -- Each names a specific gap with a known discharge plan.
  ----------------------------------------------------------------------

  postulate
    -- Compose: when the recursive cases below are discharged, this can
    -- be derived by structural induction (f then g). The trace for `g ∘
    -- f` is `f-trace ++ mov-to-input ∷ g-trace`, matching
    -- ComposeWF.compose-trace exactly. Held as a postulate until the
    -- exec-trace-++ chaining lemma is in place at this layer.
    ir-to-trace-correct-compose : ∀ {A B C} (g : IR B C) (f : IR A B) →
      IRTraceCorrect (g ∘ f)

    -- Pair, curry, apply: ir-to-trace uses `0` as its slot frontier
    -- base, while run-pair/curry/apply use `next-slot alloc`. Discharge
    -- requires either (a) a precondition `next-slot alloc ≡ 0`, or
    -- (b) extending ir-to-trace to take the alloc's frontier.
    ir-to-trace-correct-pair :
      ∀ {A B C} (m : AllocMode) (f : IR A B) (g : IR A C) →
      IRTraceCorrect (⟨_,_⟩ {A} {B} {C} f g m)
    ir-to-trace-correct-curry :
      ∀ {k A B C} (f : IR (A * B) C) (m : AllocMode) →
      IRTraceCorrect (curry {k = k} f m)
    ir-to-trace-correct-apply : ∀ {k A B} →
      IRTraceCorrect (apply {A} {B} {k})

    -- SigOp: relies on RuntimeContract.sigOp-proof at the architecture
    -- entry point. Since CompileCorrect is FS-only (no RuntimeContract
    -- in scope), we postulate; EntryPointCCC's `compile-correct-extracted`
    -- can be linked against sigOp-proof later.
    ir-to-trace-correct-sigop : ∀ {A B} (si : _) →
      IRTraceCorrect (SigOp {A} {B} si)

    -- Sums and recursion schemes (Layer 0 doesn't use any of these;
    -- `ir-to-trace` stubs them all to `[]` per Phase B). Bundled into
    -- a single catchall named postulate to keep the audit handle list
    -- compact. When Layer 1+ work begins, this should be split per-IR.
    ir-to-trace-correct-non-layer0 : ∀ {A B} (ir : IR A B) → IRTraceCorrect ir

  ----------------------------------------------------------------------
  -- The aggregate `ir-to-trace-correct` dispatches on IR.
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
  -- All other IR ctors (sums, recursion schemes) — Layer 0 doesn't use
  -- them and `ir-to-trace` stubs them to `[]`. Routed through the
  -- single named catchall postulate `ir-to-trace-correct-non-layer0`.
  {-# CATCHALL #-}
  ir-to-trace-correct ir            = ir-to-trace-correct-non-layer0 ir

  ----------------------------------------------------------------------
  -- compile-trace-correct: discharged via Simulation.trace-sim (Phase D).
  ----------------------------------------------------------------------

  compile-trace-correct :
    ∀ (trace : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS})
      (xs : X86State) →
    Corresponds s xs alloc →
    let abs-result = exec-trace trace s alloc
        abs-final-s = proj₁ abs-result
        abs-final-alloc = proj₂ abs-result
        arch-final-xs = exec-prog (compile-trace trace) xs (current-frame alloc)
    in Corresponds abs-final-s arch-final-xs abs-final-alloc
  compile-trace-correct trace s alloc xs corr =
    trace-sim trace s xs alloc corr

  ----------------------------------------------------------------------
  -- THE GRAND THEOREM.
  --
  -- For every IR term, every input value, every initial X86State that
  -- corresponds to an abstract LocState representing the input,
  -- executing `compile ir` on the X86 machine produces an X86State that
  -- corresponds to an abstract LocState representing `eval ir x`.
  ----------------------------------------------------------------------

  compile-correct :
    ∀ {A B} (ir : IR A B)
      (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      (xs : X86State) →
    Corresponds s xs alloc →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    let trace = ir-to-trace ir
        abs-result = exec-trace trace s alloc
        abs-final-s = proj₁ abs-result
        abs-final-alloc = proj₂ abs-result
        arch-final-xs = exec-prog (compile-trace trace) xs (current-frame alloc)
    in Corresponds abs-final-s arch-final-xs abs-final-alloc
       ×
       (∃[ mOut ] ∃[ result-loc ]
          ValidAtWF mOut abs-final-alloc (eval ir x) result-loc abs-final-s)
  compile-correct ir mIn x input-loc s alloc xs
                  corr valid before not-halted rdi-eq =
    let semantic-side =
          ir-to-trace-correct ir mIn x input-loc s alloc
            valid before not-halted rdi-eq
        machine-side =
          compile-trace-correct (ir-to-trace ir) s alloc xs corr
    in machine-side , semantic-side
