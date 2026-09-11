-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.IR.SumRecWF
--
-- IR handlers for sum types (inl, inr, case, initial) and
-- recursion schemes (In, Cata, Out, Ana, Hylo).
--
-- OCP-0003: Renamed from SumFixWF. Old fold/unfold handlers removed
-- in favor of structured recursion schemes that guarantee totality
-- (Cata) and productivity (Ana via GuardedT).
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.IR.SumRecWF (o : CanonicalName) where

open import Data.Nat using (ℕ; _<_; _≤_; suc; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; n<1+n; +-monoʳ-≤; m≤m*n; m<m+n; *-monoʳ-≤; ≤-irrelevant; <⇒≢; +-comm)
open import Data.Bool using (false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂; module ≡-Reasoning; ≢-sym)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
-- Plan 0.52 M2: machine values are IRTy values (⟦_⟧ᴵ), renamed to ⟦_⟧ locally.
open import Once.Semantics.Machine using () renaming (⟦_⟧ᴵ to ⟦_⟧)
open import Once.IR
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
-- Plan 0.52 M2: the IR tier's functor witness is `WellFormedFI`, from Once.IR.
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.Memory.TypeSlots using (type-slots)
open import Once.IRTy using (⌈_⌉)

-- Import SMPrimitives qualified for trace predicates
import Once.CCC.Machine.SMPrimitives as SMP

-- Import consolidated postulates (shared with RecCoreWF, ParaWF, AnaWF)
import Once.CCC.Machine.IR.RecSchemePostulates o as RSP

-- Import Lambek validity lemmas for In/Out operations
import Once.CCC.Machine.IR.LambekValidity o as LV

------------------------------------------------------------------------
-- Sum and Fix IR implementations
------------------------------------------------------------------------

-- Plan 0.52 M2: `Once.Semantics.Machine`'s `sem-inl`/`sem-inr` are Type-tier
-- (their implicits are `Type`), and this module's objects are `IRTy`. They are
-- literally `inj₁`/`inj₂`, so re-establishing the two names at the IR tier
-- leaves all fifteen call sites — implicit arguments included — unchanged.
sem-inl : ∀ {A B : IRTy} → ⟦ A ⟧ → ⟦ A + B ⟧
sem-inl = inj₁

sem-inr : ∀ {A B : IRTy} → ⟦ B ⟧ → ⟦ A + B ⟧
sem-inr = inj₂

module SumRecWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (Once.CCC.FrameSemantics.fs-numerics FS)

  open FrontierInvariant {FS}
  open MemOps {FS}
  -- D148: `readLoc-writeLoc-same` (the tag write's read-back) lives here.
  open MemoryOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS

  -- Open SMPrimitives modules for trace predicates
  open SMP.TracePrimitives {FS}
  open SMP.RecSchemeSemantics {FS}

  open import Once.CCC.Machine.ClosureWellFormed o
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc; RecDispatcherWF; InputPlace; in-at-loc; in-at-reg; in-unit; Place; valid-unit-wf;
           mk-IRResultAWF-via-bump;
           validityWF-mem-only; validityWF-frontier-advance;
           validityWF-alloc-advance; validityWF-mem-preserved;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-write-sv-at-frontier; validityWF-write-sv-at-suc-frontier;
           input-sv; input-read; InlineRep; rep-prim; rep-unit;
           decomposePairWF; PairValidWF;
           valid-inl-wf; valid-inr-wf; valid-inl-reg-wf; valid-inr-reg-wf;
           decomposeInlWF; decomposeInrWF;
           PayloadAt; payload-at-loc; payload-in-reg; payload-sv; payload-read;
           InlValidWF; InrValidWF)

  open import Once.CCC.Machine.TraceEvaluator
  open TraceEvaluatorDef {FS}
  -- OCP-0003: valid-fold-wf, decomposeFoldWF, FoldValidWF removed.
  -- Use In/Cata/Out/Ana handlers instead.

  -- Import frontier lemmas
  open import Once.CCC.Machine.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (frontier-same-heap; at-frontier-becomes-before)

  -- Import write operations
  open import Once.CCC.Machine.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import suc<+2 lemma for Heap mode proofs
  open import Once.CCC.Machine.DispatcherArithmeticLemma using (suc<+2)

  ------------------------------------------------------------------------
  -- Trace state correctness
  --
  -- Each sum operation has a specific trace:
  -- - inl/inr: mov-to-output, store-at-slot, lea-slot (write payload, return sum addr)
  -- - case: dispatch trace (f-trace or g-trace depending on inl/inr)
  --
  -- Recursion schemes (In, Cata, Out, Ana, Hylo) are postulated.
  --
  -- Note: trace-correct now proves proj₁ (exec-trace trace s alloc) ≡ final-state
  -- This separates runtime state from compile-time allocation tracking.
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Trace correctness lemmas
  --
  -- These show that specific instruction sequences produce the expected
  -- final state by unfolding exec-trace and exec-abstract definitions.
  ------------------------------------------------------------------------

  -- lea-slot state equality: executing lea-slot sets Output to the slot address
  lea-slot-state-eq : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (lea-slot slot ∷ []) s alloc) ≡
    record s { regs = writeReg (regs s) Output (SV-Ptr (AtStack (current-frame alloc) slot)) }
  lea-slot-state-eq slot s alloc not-halted =
    cong proj₁ (exec-trace-single (lea-slot slot) s alloc not-halted)

  -- load-indirect state equality: executing load-indirect dereferences Input1
  -- TODO (post-scaffold): under StoredValue, exec-abstract load-indirect
  -- splits on sv-as-loc Input1; restate accordingly.
  postulate
    -- D175: was `= SMP.!!`. Under `StoredValue`, `exec-abstract load-indirect`
    -- splits on `sv-as-loc Input1`, so this needs restating before it can be
    -- proved; named rather than holed in the meantime.
    load-indirect-state-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
      halted s ≡ false →
      proj₁ (exec-trace (load-indirect ∷ []) s alloc) ≡ exec (load Output (IndReg Input1)) s

  -- Postulate: trace correctness for inl/inr (Plan 0.13.1 tag-aware shape).
  --
  -- 5-instruction trace (matches `ir-to-trace`'s output for inl/inr):
  --   1. instr-load-tag-lit tag : Output := SV-Tag tag      (0 for inl, 1 for inr)
  --   2. store-at-slot result-slot : mem[result-slot] := SV-Tag tag
  --   3. mov-to-output : Output := Input1 = SV-Ptr input-loc (payload pointer)
  --   4. store-at-slot payload-slot : mem[payload-slot] := SV-Ptr input-loc
  --   5. lea-slot result-slot : Output := SV-Ptr result-loc
  --
  -- After all 5 steps:
  --   mem[result-slot] = SV-Tag tag
  --   mem[payload-slot] = SV-Ptr input-loc
  --   regs[Output] = SV-Ptr result-loc
  --   regs[Input1] = SV-Ptr input-loc (unchanged)
  --   halted = false (unchanged from precondition)
  --
  -- Note: the s-final shape on the caller side ONLY models the payload
  -- write and the Output register update (matching the pre-Plan-0.13.1
  -- s-final construction used by run-inl/run-inr). The tag write at
  -- result-slot is folded into this postulate's soundness debt: the
  -- proven equation is exec-trace = s-final-as-constructed, but
  -- s-final-as-constructed has the original (pre-tag) memory at
  -- result-slot, not SV-Tag tag. Migrating callers to a tag-aware
  -- 0.86 stage E (D147): THE STACK SUM HELPERS ARE GONE.
  -- `inl-inr-trace-{state,alloc}-correct` described a trace that opened with
  -- `instr-alloc-stack sum-slots` and closed with `lea-slot` — the stack
  -- lowering stage G deleted when `AllocMode` left `inl`/`inr`. Nothing
  -- outside the two stack constructors used them, and between them they
  -- carried one `SMP.!!` and the `next-slot` mismatch that kept this module
  -- red.

  -- OCP-0003: fold-trace-state-correct removed (fold/unfold replaced by In/Cata/Out/Ana/Hylo)

  ------------------------------------------------------------------------
  -- Case Dispatch Trace Correctness Postulate
  --
  -- The case dispatch trace is: load-indirect-suc ∷ mov-to-input ∷ dispatch-trace
  --
  -- After execution:
  --   1. load-indirect-suc: Output := *(sucLoc Input1) = payload-loc
  --   2. mov-to-input: Input1 := Output = payload-loc
  --   3. Execute dispatch-trace with Input1 = payload-loc
  --
  -- Key insight (Output-independence):
  --   After steps 1-2, the state differs from s-setup only in Output:
  --   - Both have Input1 = payload-loc
  --   - Both have same stackMem, heapMem, halted
  --   - Actual state has Output = payload-loc
  --   - s-setup has Output = original Output
  --
  --   IR dispatch traces are Output-independent:
  --   - They read from Input1 to get input value
  --   - They may read from memory (stackMem, heapMem)
  --   - They write their result to Output (overwriting initial value)
  --   - They never READ the initial Output value
  --
  -- Therefore: exec-trace dispatch-trace s₂ alloc ≡ exec-trace dispatch-trace s-setup alloc
  --
  -- Justification (why this is PROVABLE):
  --   1. Define TraceOutputIndependent predicate
  --   2. Prove IR dispatch traces satisfy this predicate
  --   3. Prove exec-trace is insensitive to Output for such traces
  ------------------------------------------------------------------------
  -- Plan 0.13.2 StoredValue restate: input-loc threaded via SV-Ptr.
  --
  -- Stage F: these are parameterised by the payload cell's STORED VALUE, not
  -- by a payload LOCATION. `load-indirect-suc ∷ mov-to-input` copies the cell
  -- into `Input1` whatever it holds — a pointer for a located payload, the
  -- value itself for an inline one — so naming a location here was both
  -- narrower than the machine and unstatable for an inline payload.
  postulate
    case-dispatch-output-independent : ∀ (dispatch-trace : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS})
      (input-loc : ValueLocation FS) (pv : StoredValue FS)
      (s-setup : LocState FS) (s-final : LocState FS) →
      readReg (regs s) Input1 ≡ SV-Ptr input-loc →
      readLoc s (sucLoc input-loc) ≡ just pv →
      s-setup ≡ record s { regs = writeReg (regs s) Input1 pv } →
      proj₁ (exec-trace dispatch-trace s-setup alloc) ≡ s-final →
      halted s ≡ false →
      proj₁ (exec-trace (load-indirect-suc ∷ mov-to-input ∷ dispatch-trace) s alloc) ≡ s-final

  -- case trace correctness - delegated to postulate (Plan 0.13.2 restated)
  case-trace-state-correct : ∀ (dispatch-trace : AbstractTrace)
    (s : LocState FS) (alloc : AllocState {FS})
    (input-loc : ValueLocation FS) (pv : StoredValue FS)
    (s-setup : LocState FS) (s-final : LocState FS) →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    readLoc s (sucLoc input-loc) ≡ just pv →
    s-setup ≡ record s { regs = writeReg (regs s) Input1 pv } →
    proj₁ (exec-trace dispatch-trace s-setup alloc) ≡ s-final →
    halted s ≡ false →
    proj₁ (exec-trace (load-indirect-suc ∷ mov-to-input ∷ dispatch-trace) s alloc) ≡ s-final
  case-trace-state-correct = case-dispatch-output-independent

  -- Plan 0.14: alloc-correct sibling for the case dispatch trace.
  -- The 2-prefix (load-indirect-suc, mov-to-input) preserves alloc
  -- definitionally; alloc is the same whether dispatch-trace runs at
  -- s-setup (the construction-time state) or at the state-after-prefix
  -- (the runtime state) — alloc output is state-invariant for the
  -- instruction set used. Postulated for the same reason
  -- case-dispatch-output-independent is.
  postulate
    case-dispatch-alloc-independent : ∀ (dispatch-trace : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS})
      (input-loc : ValueLocation FS) (pv : StoredValue FS)
      (s-setup : LocState FS) (alloc-final : AllocState {FS}) →
      readReg (regs s) Input1 ≡ SV-Ptr input-loc →
      readLoc s (sucLoc input-loc) ≡ just pv →
      s-setup ≡ record s { regs = writeReg (regs s) Input1 pv } →
      proj₂ (exec-trace dispatch-trace s-setup alloc) ≡ alloc-final →
      halted s ≡ false →
      proj₂ (exec-trace (load-indirect-suc ∷ mov-to-input ∷ dispatch-trace) s alloc) ≡ alloc-final

  case-trace-alloc-correct : ∀ (dispatch-trace : AbstractTrace)
    (s : LocState FS) (alloc : AllocState {FS})
    (input-loc : ValueLocation FS) (pv : StoredValue FS)
    (s-setup : LocState FS) (alloc-final : AllocState {FS}) →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    readLoc s (sucLoc input-loc) ≡ just pv →
    s-setup ≡ record s { regs = writeReg (regs s) Input1 pv } →
    proj₂ (exec-trace dispatch-trace s-setup alloc) ≡ alloc-final →
    halted s ≡ false →
    proj₂ (exec-trace (load-indirect-suc ∷ mov-to-input ∷ dispatch-trace) s alloc) ≡ alloc-final
  case-trace-alloc-correct = case-dispatch-alloc-independent

  -- OCP-0003: sem-fold-injective removed (fold/unfold replaced by recursion schemes)

  -- Helper: sem-inl is injective
  -- D175: THE CLUSTER'S CENTRAL ASSUMPTION, NAMED.
  --
  -- `trace-is-ir-to-trace` is the field that says "the trace this module
  -- hand-writes IS what the emitter emits". It is the only thing that would
  -- let a `*WF` proof discharge an apex `obs-correct-*`, and it is ASSUMED at
  -- every runner here — six sites below, plus `ComposeWF`, `ApplyWF` and
  -- `PairWF`. (`SimpleWF` and `CurryWF` try to prove it with `refl` and are
  -- red since D159 made `ir-to-trace-at-frontier` return a LINKED image.)
  --
  -- Stated generically because the six uses differ only in the IR and trace;
  -- naming it is the point — as `SMP.!!` this was invisible, and the layer
  -- appeared to establish a correspondence it never had.
  postulate
    ASSUMED-trace-is-ir-to-trace :
      ∀ {A B} (ir : IR A B) (trace : AbstractTrace) (alloc : AllocState {FS}) →
      trace ≡ ir-to-trace-at-frontier (next-slot alloc) ir
    ASSUMED-mem-preserved-before :
      ∀ (final-state s : LocState FS) (alloc : AllocState {FS})
        (loc : ValueLocation FS) → BeforeFrontier alloc loc →
      readLoc final-state loc ≡ readLoc s loc
    ASSUMED-trace-wf :
      ∀ (trace : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
      TraceWF s alloc trace

  sem-inl-injective : ∀ {A B} {a b : ⟦ A ⟧} → sem-inl {A} {B} a ≡ sem-inl {A} {B} b → a ≡ b
  sem-inl-injective refl = refl

  -- Helper: sem-inr is injective
  sem-inr-injective : ∀ {A B} {a b : ⟦ B ⟧} → sem-inr {A} {B} a ≡ sem-inr {A} {B} b → a ≡ b
  sem-inr-injective refl = refl

  ------------------------------------------------------------------------
  -- Initial: absurd elimination (input is Void, so never executed)
  ------------------------------------------------------------------------

  -- Stage F: the input is an `InputPlace`.
  run-initial : ∀ {m A}
    (x : ⟦ Void ⟧)
    (s : LocState FS) (alloc : AllocState {FS}) →
    InputPlace m alloc x s →
    halted s ≡ false →
    ∃[ mOut ] IRResultAWF mOut (initial {A}) x s alloc
  run-initial () _ _ _ _  -- x : ⟦ Void ⟧ = ⊥, so pattern match is absurd

  -- OCP-0003: run-unfold removed (replaced by Out handler for ν-types)

  ------------------------------------------------------------------------
  -- Inl: inject left into sum type
  --
  -- Creates a sum value (inl x) by:
  -- 1. Allocating type-slots (A + B) slots at frontier
  -- 2. Writing input-loc (payload pointer) to sucLoc sum-loc
  -- 3. Returning sum-loc
  --
  -- Memory layout: sum-loc stores tag (implicit), sucLoc sum-loc stores payload ptr
  ------------------------------------------------------------------------

  -- Helper: type-slots (A + B) > 0.
  -- Plan 0.52 M2: `type-slots` is Type-tier, and this module's objects are
  -- `IRTy`. The slot count of an IR object is that of its canonical
  -- representative `⌈ A ⌉` — `⌈_⌉` only invents an arrow grade, which layout
  -- does not read, and it is structural everywhere else.
  sum-slots-pos : ∀ {A B} → 0 < type-slots ⌈ A + B ⌉
  sum-slots-pos {A} {B} = s≤s z≤n

  -- 0.86 stage E (D147): `run-inl`/`run-inr` (STACK) ARE GONE.
  -- One lowering survives per injection — the 10-instruction heap build in
  -- `ir-to-trace'` — witnessed by `run-inl-heap`/`run-inr-heap`. What stays
  -- in this module is everything that was never mode-specific:
  -- `run-initial`, `run-case`, `run-In`, `run-out-μ`, `run-Out`, `run-in-ν`.

  -- ir-size (case f g) = suc (ir-size f + ir-size g)
  ------------------------------------------------------------------------

  -- Stage F: the input is an `InputPlace`. `case`'s input is a SUM, and
  -- `FitsInRegI` inhabits only `Int`/`Float`, so a register-resident input is
  -- absurd; so is a Unit one (`_+_` and `Unit` are distinct `IRTy` heads).
  run-case : ∀ {m A B C} (f : IR A C) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (case f g)))
    (x : ⟦ A + B ⟧)
    (s : LocState FS) (alloc : AllocState {FS}) →
    InputPlace m alloc x s →
    (dest : Place) →
    halted s ≡ false →
    ∃[ mOut ] IRResultAWF mOut (case f g) x s alloc
  run-case _ _ _ _ _ _ (in-at-reg () _) _ _
  run-case _ _ _ _ _ _ (in-unit ()) _ _

  -- Case for inl: dispatch to f
  run-case {m} {A} {B} {C} f g rec-wf (inj₁ a) s alloc
           (in-at-loc input-loc input-valid-wf input-before rdi-eq) dest not-halted =
    mF ,
    mk-IRResultAWF-via-bump
      (IRResultAWF.final-state result-f)
      (IRResultAWF.final-alloc result-f)
      case-inl-trace
      (IRResultAWF.bump result-f)
      refl
      (ASSUMED-trace-is-ir-to-trace _ _ _)                       -- trace-is-ir-to-trace
      case-inl-trace-correct
      case-inl-alloc-correct
      (IRResultAWF.result-place result-f)
      (IRResultAWF.not-halted result-f)
      (TraceEvaluator.mem-preserved-before case-inl-trace-eval)
      (TraceEvaluator.trace-wf case-inl-trace-eval)
      (exec-trace-preserves-halted-WF case-inl-trace)
      (tt , tt , IRResultAWF.trace-no-frame-ops result-f)
      (record
        { max-slot-written = IRResultAWF.max-slot-written result-f
        ; stack-budget = IRResultAWF.stack-budget result-f
        ; bump-fits-stack-budget = IRResultAWF.bump-fits-stack-budget result-f
        ; max-slot-geq-final = IRResultAWF.max-slot-geq-final result-f
        ; max-slot-usage-bound = IRResultAWF.max-slot-usage-bound result-f
        ; frontier-slot-stable = case-frontier-stable
        ; trace-writes-above = IRResultAWF.trace-writes-above result-f
        ; trace-slot-reads-above = IRResultAWF.trace-slot-reads-above result-f
        ; trace-writes-below = IRResultAWF.trace-writes-below result-f
        ; trace-slot-reads-below = IRResultAWF.trace-slot-reads-below result-f
        ; scratch-budget = IRResultAWF.scratch-budget result-f
        ; scratch-bounded = IRResultAWF.scratch-bounded result-f
        })
      (record
        { heap-budget = IRResultAWF.heap-budget result-f
        ; max-heap-ref-written = IRResultAWF.max-heap-ref-written result-f
        ; bump-fits-heap-budget = IRResultAWF.bump-fits-heap-budget result-f
        ; max-heap-ref-geq-final = IRResultAWF.max-heap-ref-geq-final result-f
        ; max-heap-usage-bound = IRResultAWF.max-heap-usage-bound result-f
        })
    where
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-case = ir-stack-requirement (case f g)

      -- Decompose sum validity
      inl-decomp = decomposeInlWF input-valid-wf
      a' = InlValidWF.a inl-decomp
      pd' = InlValidWF.payload inl-decomp

      -- v-is-inl : inl a ≡ inl a', so a ≡ a' by sem-inl-injective
      a-eq : a' ≡ a
      a-eq = sem-inl-injective (sym (InlValidWF.v-is-inl inl-decomp))

      -- Stage F: transport the payload's RESIDENCE. Where it lives is what
      -- varies; the old code transported a validity proof because it assumed
      -- the payload was always in memory.
      pd : PayloadAt alloc a input-loc s
      pd = subst (λ x → PayloadAt alloc x input-loc s) a-eq pd'

      -- Capacity bound for f
      -- case-stack-req: ir-stack-requirement (case f g) = rf + rg
      -- So rf ≤ req-case, hence slot + rf ≤ slot + req-case
      cap-f-bound : next-slot alloc +ℕ rf ≤ next-slot alloc +ℕ req-case
      cap-f-bound = +-monoʳ-≤ (next-slot alloc) (m≤m+n rf rg)

      -- Stage F: the setup moves the payload CELL into Input1, whatever it
      -- holds — exactly what `load-indirect-suc ∷ mov-to-input` does.
      s-setup = record s { regs = writeReg (regs s) Input1 (payload-sv pd) }

      -- s-setup preserves memory from s (only regs changed)
      mem-setup-eq : ∀ loc → readLoc s-setup loc ≡ readLoc s loc
      mem-setup-eq loc = readLoc-stackMem-eq s-setup s loc refl refl

      rdi-payload : readReg (regs s-setup) Input1 ≡ payload-sv pd
      rdi-payload = writeReg-same (regs s) Input1 (payload-sv pd)

      not-halted-setup : halted s-setup ≡ false
      not-halted-setup = not-halted

      -- The branch's input place, by residence. A helper TAKING the register
      -- equation, not a `with` on `pd`: a `with` would abstract `pd` in the
      -- goal but not in `rdi-payload`, bound outside it. An inline payload
      -- carries no mode, so the mode comes back WITH the place.
      mk-input : (q : PayloadAt alloc a input-loc s)
               → readReg (regs s-setup) Input1 ≡ payload-sv q
               → Σ AllocMode (λ mI → InputPlace mI alloc a s-setup)
      mk-input (payload-at-loc {mA = mP} pl pp pb pv) eq =
        mP , in-at-loc pl (validityWF-mem-only a pl s s-setup refl refl pv) pb eq
      -- Stage F: the inline forms round-trip. A register-fitting payload
      -- becomes a register-resident input; a UNIT payload becomes `in-unit`,
      -- which discards `eq` — nothing may depend on what that cell held.
      mk-input (payload-in-reg (rep-prim fit) pp) eq = Stack , in-at-reg fit eq
      mk-input (payload-in-reg (rep-unit u _) pp) eq = Stack , in-unit u

      the-input = mk-input pd rdi-payload

      -- Dispatch to f via recursive dispatch
      -- Note: cap-f argument removed in Phase 3
      f-exec-result : ∃[ mOut ] IRResultAWF mOut f a s-setup alloc
      -- Stage F: the four memory facts are now bundled as an `InputPlace`.
      -- Stage F: the taken branch produces CASE's result, so it inherits
      -- case's own destination. (Not yet binding — see RecDispatcherWF.)
      f-exec-result = rec-wf (proj₁ the-input) f (case-f-smaller f g) a s-setup alloc
                        (proj₂ the-input) dest not-halted-setup
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result

      -- Case (inl branch) trace:
      -- 1. Load payload pointer from sucLoc input-loc into Output
      -- 2. mov-to-input to set Input1 := payload-loc
      -- 3. Execute f's trace
      -- Note: The actual Dispatcher sets Input1 directly, we approximate with load + mov
      f-trace = IRResultAWF.trace result-f
      case-inl-trace : AbstractTrace
      case-inl-trace = load-indirect-suc ∷  -- Output := *(Input1+1) = payload-loc
                       mov-to-input ∷       -- Input1 := Output = payload-loc
                       f-trace

      -- Plan 0.16: shared derivations of trace-correct / alloc-correct
      -- so both the IRResultBase fields and the TraceEvaluator below
      -- reference the same proof object (avoids duplicating the long
      -- case-trace-*-correct call sites).
      case-inl-trace-correct :
        proj₁ (exec-trace case-inl-trace s alloc) ≡ IRResultAWF.final-state result-f
      case-inl-trace-correct = case-trace-state-correct f-trace s alloc input-loc
                                (payload-sv pd) s-setup (IRResultAWF.final-state result-f)
                                rdi-eq
                                (payload-read pd)
                                refl
                                (IRResultAWF.trace-correct result-f) not-halted

      case-inl-alloc-correct :
        proj₂ (exec-trace case-inl-trace s alloc) ≡ IRResultAWF.final-alloc result-f
      case-inl-alloc-correct = case-trace-alloc-correct f-trace s alloc input-loc
                                 (payload-sv pd) s-setup (IRResultAWF.final-alloc result-f)
                                 rdi-eq
                                 (payload-read pd)
                                 refl
                                 (IRResultAWF.alloc-correct result-f) not-halted

      ------------------------------------------------------------------
      -- Plan 0.16 TraceEvaluator: bundles per-step state trajectory
      -- for the case-inl trace. `exec-state-eq` / `exec-alloc-eq` reuse
      -- the existing case-trace-*-correct derivations; `trace-wf` and
      -- `mem-preserved-before` remain scaffolded.
      ------------------------------------------------------------------
      case-inl-trace-eval : TraceEvaluator case-inl-trace s alloc
      case-inl-trace-eval = mk-trace-evaluator
        (IRResultAWF.final-state result-f)
        (IRResultAWF.final-alloc result-f)
        (ASSUMED-trace-wf _ _ _)     -- trace-wf
        case-inl-trace-correct       -- exec-state-eq
        case-inl-alloc-correct       -- exec-alloc-eq
        (ASSUMED-mem-preserved-before _ _ _)             -- mem-preserved-before

      -- Frontier slot stability for case (inl branch)
      -- Return uncertain (inj₂ (inj₂ tt)) since f may allocate at the frontier slot.
      -- This is safe: compose handles uncertainty correctly by propagating it.
      case-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input1 ≡ SV-Ptr input-loc' →
        readLoc s' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      case-frontier-stable _ _ _ _ _ = inj₂ (inj₂ tt)

  -- Case for inr: dispatch to g
  run-case {m} {A} {B} {C} f g rec-wf (inj₂ b) s alloc
           (in-at-loc input-loc input-valid-wf input-before rdi-eq) dest not-halted =
    mG ,
    mk-IRResultAWF-via-bump
      (IRResultAWF.final-state result-g)
      (IRResultAWF.final-alloc result-g)
      case-inr-trace
      (IRResultAWF.bump result-g)
      refl
      (ASSUMED-trace-is-ir-to-trace _ _ _)                       -- trace-is-ir-to-trace
      case-inr-trace-correct
      case-inr-alloc-correct
      (IRResultAWF.result-place result-g)
      (IRResultAWF.not-halted result-g)
      (TraceEvaluator.mem-preserved-before case-inr-trace-eval)
      (TraceEvaluator.trace-wf case-inr-trace-eval)
      (exec-trace-preserves-halted-WF case-inr-trace)
      (tt , tt , IRResultAWF.trace-no-frame-ops result-g)
      (record
        { max-slot-written = IRResultAWF.max-slot-written result-g
        ; stack-budget = IRResultAWF.stack-budget result-g
        ; bump-fits-stack-budget = IRResultAWF.bump-fits-stack-budget result-g
        ; max-slot-geq-final = IRResultAWF.max-slot-geq-final result-g
        ; max-slot-usage-bound = IRResultAWF.max-slot-usage-bound result-g
        ; frontier-slot-stable = case-frontier-stable
        ; trace-writes-above = IRResultAWF.trace-writes-above result-g
        ; trace-slot-reads-above = IRResultAWF.trace-slot-reads-above result-g
        ; trace-writes-below = IRResultAWF.trace-writes-below result-g
        ; trace-slot-reads-below = IRResultAWF.trace-slot-reads-below result-g
        ; scratch-budget = IRResultAWF.scratch-budget result-g
        ; scratch-bounded = IRResultAWF.scratch-bounded result-g
        })
      (record
        { heap-budget = IRResultAWF.heap-budget result-g
        ; max-heap-ref-written = IRResultAWF.max-heap-ref-written result-g
        ; bump-fits-heap-budget = IRResultAWF.bump-fits-heap-budget result-g
        ; max-heap-ref-geq-final = IRResultAWF.max-heap-ref-geq-final result-g
        ; max-heap-usage-bound = IRResultAWF.max-heap-usage-bound result-g
        })
    where
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-case = ir-stack-requirement (case f g)

      -- Decompose sum validity
      inr-decomp = decomposeInrWF input-valid-wf
      b' = InrValidWF.b inr-decomp
      pd' = InrValidWF.payload inr-decomp

      -- v-is-inr : inr b ≡ inr b', so b ≡ b' by sem-inr-injective
      b-eq : b' ≡ b
      b-eq = sem-inr-injective (sym (InrValidWF.v-is-inr inr-decomp))

      -- Stage F: transport the payload's RESIDENCE. Where it lives is what
      -- varies; the old code transported a validity proof because it assumed
      -- the payload was always in memory.
      pd : PayloadAt alloc b input-loc s
      pd = subst (λ x → PayloadAt alloc x input-loc s) b-eq pd'

      -- Capacity bound for g
      -- case-stack-req: ir-stack-requirement (case f g) = rf + rg
      -- So rg ≤ req-case, hence slot + rg ≤ slot + req-case
      cap-g-bound : next-slot alloc +ℕ rg ≤ next-slot alloc +ℕ req-case
      cap-g-bound = +-monoʳ-≤ (next-slot alloc) (m≤n+m rg rf)

      -- Stage F: the setup moves the payload CELL into Input1, whatever it
      -- holds — exactly what `load-indirect-suc ∷ mov-to-input` does.
      s-setup = record s { regs = writeReg (regs s) Input1 (payload-sv pd) }

      -- s-setup preserves memory from s (only regs changed)
      mem-setup-eq : ∀ loc → readLoc s-setup loc ≡ readLoc s loc
      mem-setup-eq loc = readLoc-stackMem-eq s-setup s loc refl refl

      rdi-payload : readReg (regs s-setup) Input1 ≡ payload-sv pd
      rdi-payload = writeReg-same (regs s) Input1 (payload-sv pd)

      not-halted-setup : halted s-setup ≡ false
      not-halted-setup = not-halted

      -- The branch's input place, by residence. A helper TAKING the register
      -- equation, not a `with` on `pd`: a `with` would abstract `pd` in the
      -- goal but not in `rdi-payload`, bound outside it. An inline payload
      -- carries no mode, so the mode comes back WITH the place.
      mk-input : (q : PayloadAt alloc b input-loc s)
               → readReg (regs s-setup) Input1 ≡ payload-sv q
               → Σ AllocMode (λ mI → InputPlace mI alloc b s-setup)
      mk-input (payload-at-loc {mA = mP} pl pp pb pv) eq =
        mP , in-at-loc pl (validityWF-mem-only b pl s s-setup refl refl pv) pb eq
      -- Stage F: the inline forms round-trip. A register-fitting payload
      -- becomes a register-resident input; a UNIT payload becomes `in-unit`,
      -- which discards `eq` — nothing may depend on what that cell held.
      mk-input (payload-in-reg (rep-prim fit) pp) eq = Stack , in-at-reg fit eq
      mk-input (payload-in-reg (rep-unit u _) pp) eq = Stack , in-unit u

      the-input = mk-input pd rdi-payload

      -- Dispatch to g via recursive dispatch
      -- Note: cap-g argument removed in Phase 3
      g-exec-result : ∃[ mOut ] IRResultAWF mOut g b s-setup alloc
      g-exec-result = rec-wf (proj₁ the-input) g (case-g-smaller f g) b s-setup alloc
                        (proj₂ the-input) dest not-halted-setup
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result

      -- Case (inr branch) trace:
      -- 1. Load payload pointer from sucLoc input-loc into Output
      -- 2. mov-to-input to set Input1 := payload-loc
      -- 3. Execute g's trace
      g-trace = IRResultAWF.trace result-g
      case-inr-trace : AbstractTrace
      case-inr-trace = load-indirect-suc ∷  -- Output := *(Input1+1) = payload-loc
                       mov-to-input ∷       -- Input1 := Output = payload-loc
                       g-trace

      -- Plan 0.16: shared derivations for both the IRResultBase fields
      -- and the TraceEvaluator below.
      case-inr-trace-correct :
        proj₁ (exec-trace case-inr-trace s alloc) ≡ IRResultAWF.final-state result-g
      case-inr-trace-correct = case-trace-state-correct g-trace s alloc input-loc
                                (payload-sv pd) s-setup (IRResultAWF.final-state result-g)
                                rdi-eq
                                (payload-read pd)
                                refl
                                (IRResultAWF.trace-correct result-g) not-halted

      case-inr-alloc-correct :
        proj₂ (exec-trace case-inr-trace s alloc) ≡ IRResultAWF.final-alloc result-g
      case-inr-alloc-correct = case-trace-alloc-correct g-trace s alloc input-loc
                                 (payload-sv pd) s-setup (IRResultAWF.final-alloc result-g)
                                 rdi-eq
                                 (payload-read pd)
                                 refl
                                 (IRResultAWF.alloc-correct result-g) not-halted

      ------------------------------------------------------------------
      -- Plan 0.16 TraceEvaluator (mirror of case-inl branch).
      ------------------------------------------------------------------
      case-inr-trace-eval : TraceEvaluator case-inr-trace s alloc
      case-inr-trace-eval = mk-trace-evaluator
        (IRResultAWF.final-state result-g)
        (IRResultAWF.final-alloc result-g)
        (ASSUMED-trace-wf _ _ _)     -- trace-wf
        case-inr-trace-correct       -- exec-state-eq
        case-inr-alloc-correct       -- exec-alloc-eq
        (ASSUMED-mem-preserved-before _ _ _)             -- mem-preserved-before

      -- Frontier slot stability for case (inr branch)
      -- Return uncertain (inj₂ (inj₂ tt)) since g may allocate at the frontier slot.
      case-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input1 ≡ SV-Ptr input-loc' →
        readLoc s' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      case-frontier-stable _ _ _ _ _ = inj₂ (inj₂ tt)

  ------------------------------------------------------------------------
  ------------------------------------------------------------------------
  -- OCP-0003: Recursion Scheme Handlers
  --
  -- These handlers implement machine-level code generation for the
  -- recursion scheme constructors: In, Cata, Out, Ana, Hylo.
  --
  -- The semantic correctness is established in:
  --   - Once/Category/Laws.agda (categorical laws)
  --
  -- Implementation strategy:
  --   - In/out-μ: trivial pass-through (μ-type is representationally
  --               identical to F(μ-type) by Lambek's Lemma)
  --   - Out/in-ν: trivial pass-through (ν-type is representationally
  --               identical to F(ν-type) by dual Lambek's Lemma)
  --   - Cata: iterative consumption of μ-type (RecCoreWF)
  --   - Ana: lazy/demand-driven production of ν-type (thunk)
  --   - Hylo: fused cata ∘ ana without intermediate allocation
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Semantic Correctness for Isomorphism Operations
  --
  -- Uses targeted Lambek validity lemmas instead of general postulate.
  -- See LambekValidity.agda for documentation and justification.
  ------------------------------------------------------------------------
  open LV.LambekValidityImpl {FS} program-bound
    using (In-valid-bf; out-μ-valid; in-ν-valid; Out-valid)

  ------------------------------------------------------------------------
  -- In: wrap functor layer into μ-type
  --
  -- By Lambek's Lemma, In : F(μF) → μF is an isomorphism, so the
  -- runtime representation of F(μF) IS the representation of μF.
  -- This is a trivial identity operation at the machine level.
  --
  -- The only work: if AllocMode requests allocation, store at slot.
  -- For Stack mode, we store input at frontier slot and return pointer.
  -- For Heap mode (currently same as Stack in reference model).
  ------------------------------------------------------------------------

  run-In : ∀ {F} (wf : WellFormedFI F) (mIn : AllocMode) (m : AllocMode)
    (x : ⟦ ⟦ F ⟧TI (μ-type F) ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    -- Option 3: In is mode-rigid identity — the μ-value lives at the
    -- layer's location and mode (mIn), so the result mode is mIn.
    IRResultAWF mIn (In {F} wf m) x s alloc
  run-In {F} wf mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mk-IRResultAWF-via-bump
      s' alloc in-trace bump-0 refl
      (ASSUMED-trace-is-ir-to-trace _ _ _)                       -- trace-is-ir-to-trace (mov-to-output; upgrade to refl once proj-trace frontier reduces)
      refl
      (cong proj₂ (exec-trace-single mov-to-output s alloc not-halted))
      (at-loc input-loc result-valid input-before rax-eq result-valid input-before)
      not-halted'
      (ASSUMED-mem-preserved-before _ _ _)
      (twf-∷ tt twf-[])
      (exec-trace-preserves-halted-WF in-trace)
      _
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = ir-stack-requirement (In {F} wf m)
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) (ir-stack-requirement (In {F} wf m))
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (In {F} wf m)
        ; scratch-bounded = m≤m+n (next-slot alloc) (ir-scratch-requirement (In {F} wf m))
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      -- Plan 0.27 Phase B: heap-identity In. The F-layer node IS the
      -- μ-value (same pointer); `mov-to-output` passes it through — no
      -- slot, no allocation (bump-0), result at the input loc. Validity
      -- is now REAL (In-valid-bf via the layer→μlayer kernel), replacing
      -- the hypothesis-free In-trace-valid postulate.
      in-trace : AbstractTrace
      in-trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace in-trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input1) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      -- In is representational identity; the F-layer's validity +
      -- frontier-membership give the μ-value's validity at the SAME loc,
      -- transported across mov-to-output (memory-preserving).
      result-valid : ValidAtWF mIn alloc (eval (In wf m) x) input-loc s'
      result-valid =
        subst (λ st → ValidAtWF mIn alloc (eval (In wf m) x) input-loc st) (sym s'-eq)
          (validityWF-mem-only (eval (In wf m) x) input-loc s (exec (mov Output Input1) s)
            refl refl (In-valid-bf wf m x input-valid-wf))

      rax-eq : readReg (regs s') Output ≡ SV-Ptr input-loc
      rax-eq = trans (passthrough-output-is-input s alloc not-halted) rdi-eq

      not-halted' : halted s' ≡ false
      not-halted' = passthrough-preserves-halted s alloc not-halted

      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- out-μ: destruct μ-type to get functor layer (Lambek inverse of In)
  --
  -- By Lambek's Lemma, this is the inverse of In. At runtime, μF and
  -- F(μF) have identical representation, so this is identity.
  ------------------------------------------------------------------------

  run-out-μ : ∀ {F} (wf : WellFormedFI F) (mIn : AllocMode)
    (x : ⟦ μ-type F ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    -- Option 3: out-μ is mode-rigid identity — result mode = input mode.
    IRResultAWF mIn (out-μ {F} wf) x s alloc
  run-out-μ {F} wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mk-IRResultAWF-via-bump
      s' alloc out-μ-trace bump-0 refl
      (ASSUMED-trace-is-ir-to-trace _ _ _)                       -- trace-is-ir-to-trace
      refl
      (cong proj₂ (exec-trace-single mov-to-output s alloc not-halted))
      (at-loc input-loc result-valid input-before rax-eq result-valid input-before)
      not-halted'
      (ASSUMED-mem-preserved-before _ _ _)
      (twf-∷ tt twf-[])
      (exec-trace-preserves-halted-WF out-μ-trace)
      _
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = ir-stack-requirement (out-μ {F} wf)
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (out-μ {F} wf)
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      -- ir-stack-requirement (out-μ _) = 0, so no allocation
      -- Trace: just pass through input to output
      out-μ-trace : AbstractTrace
      out-μ-trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace out-μ-trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input1) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      -- Option 3: out-μ is representational identity (unwrap). The input
      -- μ-value's stored layer ValidAtWF IS the result, transported across
      -- mov-to-output (memory-preserving). Replaces out-μ-trace-valid.
      result-valid : ValidAtWF mIn alloc (eval (out-μ wf) x) input-loc s'
      result-valid =
        subst (λ st → ValidAtWF mIn alloc (eval (out-μ wf) x) input-loc st) (sym s'-eq)
          (validityWF-mem-only (eval (out-μ wf) x) input-loc s (exec (mov Output Input1) s)
            refl refl (out-μ-valid wf x input-valid-wf))

      -- mov-to-output sets Output := Input1 = SV-Ptr input-loc
      rax-eq : readReg (regs s') Output ≡ SV-Ptr input-loc
      rax-eq = trans (passthrough-output-is-input s alloc not-halted) rdi-eq

      -- mov-to-output preserves halted
      not-halted' : halted s' ≡ false
      not-halted' = passthrough-preserves-halted s alloc not-halted

      -- mov-to-output doesn't write memory
      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc bf = passthrough-mem-preserved s alloc loc not-halted

      -- IR doesn't allocate, return inj₁ refl
      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Out: observe ν-type to extract functor layer
  --
  -- By dual Lambek's Lemma, Out : νF → F(νF) is an isomorphism.
  -- At runtime, νF and F(νF) have identical representation.
  -- This is a trivial identity operation.
  ------------------------------------------------------------------------

  run-Out : ∀ {F} (wf : WellFormedFI F) (mIn : AllocMode)
    (x : ⟦ ν-type F ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    -- Option 3: Out is mode-rigid identity — result mode = input mode.
    IRResultAWF mIn (Out {F} wf) x s alloc
  run-Out {F} wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mk-IRResultAWF-via-bump
      s' alloc out-trace bump-0 refl
      (ASSUMED-trace-is-ir-to-trace _ _ _)                       -- trace-is-ir-to-trace
      refl
      (cong proj₂ (exec-trace-single mov-to-output s alloc not-halted))
      (at-loc input-loc result-valid input-before rax-eq result-valid input-before)
      not-halted'
      (ASSUMED-mem-preserved-before _ _ _)
      (twf-∷ tt twf-[])
      (exec-trace-preserves-halted-WF out-trace)
      _
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = ir-stack-requirement (Out {F} wf)
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) 0
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (Out {F} wf)
        ; scratch-bounded = m≤m+n (next-slot alloc) 0
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      -- ir-stack-requirement (Out _) = 0, so no allocation
      out-trace : AbstractTrace
      out-trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace out-trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input1) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      -- Option 3: Out is representational identity (unwrap), transported
      -- across mov-to-output. Replaces Out-trace-valid.
      result-valid : ValidAtWF mIn alloc (eval (Out wf) x) input-loc s'
      result-valid =
        subst (λ st → ValidAtWF mIn alloc (eval (Out wf) x) input-loc st) (sym s'-eq)
          (validityWF-mem-only (eval (Out wf) x) input-loc s (exec (mov Output Input1) s)
            refl refl (Out-valid wf x input-valid-wf))

      -- rax-eq: Output = Input1 (from passthrough) = SV-Ptr input-loc (from rdi-eq)
      rax-eq : readReg (regs s') Output ≡ SV-Ptr input-loc
      rax-eq = trans (passthrough-output-is-input s alloc not-halted) rdi-eq

      not-halted' : halted s' ≡ false
      not-halted' = passthrough-preserves-halted s alloc not-halted

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc _ = passthrough-mem-preserved s alloc loc not-halted

      -- IR doesn't allocate, return inj₁ refl
      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- in-ν: wrap functor layer into ν-type (Lambek inverse of Out)
  --
  -- By dual Lambek's Lemma, this is the inverse of Out. At runtime,
  -- F(νF) and νF have identical representation, so this is identity.
  -- Like In, if AllocMode requests allocation, we store at slot.
  ------------------------------------------------------------------------

  run-in-ν : ∀ {F} (wf : WellFormedFI F) (mIn : AllocMode) (m : AllocMode)
    (x : ⟦ ⟦ F ⟧TI (ν-type F) ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    -- Option 3: in-ν is mode-rigid identity — result mode = input mode.
    IRResultAWF mIn (in-ν {F} wf m) x s alloc
  run-in-ν {F} wf mIn m x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mk-IRResultAWF-via-bump
      s' alloc in-ν-trace bump-0 refl
      (ASSUMED-trace-is-ir-to-trace _ _ _)                       -- trace-is-ir-to-trace
      refl
      (cong proj₂ (exec-trace-single mov-to-output s alloc not-halted))
      (at-loc input-loc result-valid input-before rax-eq result-valid input-before)
      not-halted'
      (ASSUMED-mem-preserved-before _ _ _)
      (twf-∷ tt twf-[])
      (exec-trace-preserves-halted-WF in-ν-trace)
      _
      (record
        { max-slot-written = next-slot alloc
        ; stack-budget = ir-stack-requirement (in-ν {F} wf m)
        ; bump-fits-stack-budget = z≤n
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) (ir-stack-requirement (in-ν {F} wf m))
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = tt
        ; trace-slot-reads-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (in-ν {F} wf m)
        ; scratch-bounded = m≤m+n (next-slot alloc) (ir-scratch-requirement (in-ν {F} wf m))
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      -- Plan 0.27 Option 3: heap-identity in-ν (dual of run-In). The
      -- F-layer node IS the ν-value (same pointer); mov-to-output passes
      -- it through — no slot, no alloc (bump-0), result at input-loc.
      in-ν-trace : AbstractTrace
      in-ν-trace = mov-to-output ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace in-ν-trace s alloc)

      s'-eq : s' ≡ exec (mov Output Input1) s
      s'-eq = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      result-valid : ValidAtWF mIn alloc (eval (in-ν wf m) x) input-loc s'
      result-valid =
        subst (λ st → ValidAtWF mIn alloc (eval (in-ν wf m) x) input-loc st) (sym s'-eq)
          (validityWF-mem-only (eval (in-ν wf m) x) input-loc s (exec (mov Output Input1) s)
            refl refl (in-ν-valid wf m x input-valid-wf))

      rax-eq : readReg (regs s') Output ≡ SV-Ptr input-loc
      rax-eq = trans (passthrough-output-is-input s alloc not-halted) rdi-eq

      not-halted' : halted s' ≡ false
      not-halted' = passthrough-preserves-halted s alloc not-halted

      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable _ _ _ _ _ = inj₁ refl

  ------------------------------------------------------------------------
  -- Cata/Ana/Hylo/Fuse/Para: Complex recursion schemes
  --
  -- These are handled by separate modules:
  --   - RecCoreWF.agda: Unified core for Cata, Fuse, Hylo
  --   - ParaWF.agda: Paramorphism with subterm preservation
  --   - AnaWF.agda: Lazy corecursive production
  --
  -- See Dispatcher.agda for wiring.
  ------------------------------------------------------------------------