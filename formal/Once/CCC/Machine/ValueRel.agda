-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.ValueRel (was ClosureWellFormed's body)
--
-- Well-formedness predicate for closures with pre-computed body proofs.
--
-- This is the key to eliminating termination issues in Apply.
-- Instead of Apply calling run-ir recursively, it uses a pre-computed
-- proof stored in the closure.
--
-- Pattern from X86:
-- 1. Curry constructs ClosureWellFormed with body-correct proof
-- 2. body-correct is built using rec (the recursive dispatcher)
-- 3. Apply extracts and uses body-correct instead of calling run-ir
--
-- This breaks the recursive cycle: Apply doesn't call run-ir,
-- it just uses the stored proof.
------------------------------------------------------------------------

-- plan 0.135 S3 (FnRuns): TABLE-FREE. A function's body is proved in its own
-- table's environment (`tableEnv-at` evaluates an entry in the entries after
-- it), and its caller in a longer one, so the values they hand each other must
-- be related by ONE relation. Nothing here reads the table: a closure is
-- indexed by the function its block computes (`CallRuns` pins it), and the
-- μ/ν layers go through `out-μ`/`Out`, whose meaning ignores the environment.
-- The datatypes live in this UNPARAMETERISED module (a parameterised one makes
-- a distinct type per instantiation); `IRObsCorrect.Prelude` re-exports it.
open import Data.List using (List; []; _∷_; _++_)
open import Once.Denotation.Program using (IRFun; tableEnv)
module Once.CCC.Machine.ValueRel where


open import Data.Nat using (ℕ; _<_; _≤_; _≥_; suc)
import Data.Nat as ℕ
open import Data.Nat.Properties using (≤-antisym; ≤-trans; +-identityʳ; m≤n+m; +-monoʳ-≤; +-comm)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; _×_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Once.CCC.Machine.MuRep using (mu-rep; mu-box; Unboxed; box-not-unboxed)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)
open LocState using (regs; ev-log; halted; stackMem; heapMem)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
import Once.CCC.Machine.SMPrimitives as SMP
-- Plan 0.52 M2: machine values are IRTy values (⟦_⟧ᴵ), renamed to ⟦_⟧ locally.
-- D179: `⟦_⟧` in this module is now the MONADIC domain. `ValidAtWF` and
-- `ResultPlace` index on it, so an arrow means a Kleisli arrow and a ν means a
-- suspension — which is what lets `IRObsCorrectF` quantify over inputs that
-- can carry effects. The two domains COINCIDE at first order (checked), so
-- the eleven first-order constructors below are unaffected; only
-- `valid-closure-wf` sees a different index.
open import Once.Denotation.ValueDomain using () renaming (⟦_⟧ᴰᴵ to ⟦_⟧)
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM
open import Once.IR.Semantics.Iterative using (T∞; valueNow)
-- Plan 0.54 Phase B rung A: the Type-level `fits-int`/`fits-float` for the stored
-- `SV-Lit` (SMCore's `SV-Lit` is Type-indexed) in the strengthened primitive leaves.
open import Once.Type using () renaming (fits-int to fits-intˢ; fits-float to fits-floatˢ)
open import Once.IR
open import Once.IRTy using (IRTy; IRFunctor; FitsInRegI; fits-int; fits-float; Unit; _*_; _⇛_; WellFormedFI; ⟦_⟧TI; ν-type; _+_; μ-type; Int; Float)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
import Once.Semantics.Machine as EvV
open import Once.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation
open import Once.CCC.Machine.SMPrimitives using (module TracePrimitives; TraceWritesAbove; TraceSlotReadsAbove; TraceWritesBelow; TraceSlotReadsBelow; TraceNoHeapWrites)


-- Plan 0.52 M2: μ-type/ν-type/WellFormedFI/⟦_⟧TI now come from Once.IR (IRTy tier)
-- via its public re-export of Once.IRTy — no surface Once.Type import needed.


------------------------------------------------------------------------
-- BodyResult: Result type for body execution
--
-- When a closure body executes with (env, arg), it produces this result.
-- This is essentially IRResultA specialized to the body.
------------------------------------------------------------------------

-- plan 0.135 S1: the arrow case states a callee's RUN, so the relation needs
-- the flat machine and the observation vocabulary.
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open import Once.Denotation.Approx using (Ap; approx; NotCut; budgetLeft; done)
open import Once.Res using (Res; returns; is-stopped)
open import Once.IR.Semantics.Event using (SigOpEvent)
open import Once.IRTy using (Void; IRFunctor; K; Id; _⊕_; _⊗_; IsBaseTypeI; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; wf-K; wf-Id; wf-Sum; wf-Prod; WellFormedFI-irrelevant)

module ClosureWellFormedBase {FS : FrameSemantics} where
  -- D179: the MONADIC evaluator, named the same way and for the same reason.
  -- `ValidAtWF` indexes on `⟦_⟧ᴰᴵ`, so a closure's meaning is a Kleisli arrow
  -- and must come from `evalᴰ`, not the pure `eval`.
  evalᴰ : ∀ {A B} → IR A B → ⟦ A ⟧ → T∞ ⟦ B ⟧
  evalᴰ = DT.evalᴰ (Once.CCC.FrameSemantics.fs-numerics FS) (tableEnv (Once.CCC.FrameSemantics.fs-numerics FS) (Once.CCC.FrameSemantics.fs-ffi FS) [])

  -- Plan 0.105: a meaning is a tree, and its value is the value of its RUN —
  -- against the machine's interpretation, after the calls already made (the
  -- state's log). A pure IR (`out-μ`, `Ana`) returns the same value at every
  -- history; those sites read it at the empty one.
  ιᶠ : TM.Interp
  ιᶠ = Once.CCC.FrameSemantics.FrameSemantics.fs-interp FS

  open import Once.CCC.Machine.Validity
  open ReadLocEq {FS}
    using (readLoc-stack-heap-eq)
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open AbstractExec {FS}
  open TracePrimitives {FS}
  open FrameSemantics FS

  -- Plan 0.52 M2: μValid/νValid (surface MuValidity) are unused here — the
  -- the valid-μ-wf constructor carries the layer's own ValidAtWF
  -- (Option 3), so the MuValidity dependency is severed.

  -- Import write operations for validity preservation proofs
  open import Once.CCC.Machine.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- NOTE: Old static capacity reasoning (CapacityInvariant, SlotInWorking) has been removed.
  -- Dynamic capacity is now per-closure via BodyCorrect.body-capacity.

  ------------------------------------------------------------------------
  -- Mutual block for ValidAtWF, IRResultAWF, BodyCorrect
  --
  -- ValidAtWF is indexed by AllocMode as FIRST parameter.
  -- Each constructor FIXES its output mode in the type:
  --   valid-pair-boxed-wf  : ... → ValidAtWF Heap alloc {A * B} ...
  --   valid-pair-unboxed-wf : ... → ValidAtWF Stack alloc {A * B} ...
  --
  -- This enforces correct representation at the type level:
  -- - Handler for ⟨ f , g ⟩ Stack MUST produce ValidAtWF Stack (unboxed)
  -- - Handler for ⟨ f , g ⟩ Heap MUST produce ValidAtWF Heap (boxed)
  --
  -- Non-allocating handlers (fst, snd, id, etc.) pattern match on input
  -- ValidAtWF to discover the mode, and return the same mode.
  ------------------------------------------------------------------------

  -- The sum-tag invariant the cata descend reads (`c-branch-tag-zero`).
  -- HEAP-mode sums store the tag at `sum-loc` (run-inl/inr's `store-
  -- indirect`); STACK-mode sums are reference-based and don't, so the
  -- obligation is vacuous there. Mode-conditional so each producer
  -- discharges what its representation actually guarantees.
  -- MODE-INDEPENDENT since D078 (2026-08-02): the emitted code writes the
  -- tag in BOTH modes (`inl/inr Stack` = `instr-load-tag-lit t ∷
  -- store-at-slot sum-slot ∷ …` — the D077 probe proved it reachable), so
  -- `SumTag Stack = ⊤` UNDERSTATED the representation and made the branch
  -- scrutinee's tag fact underivable for stack sums. The mode argument is
  -- kept for signature compatibility.
  SumTag : AllocMode → ℕ → LocState FS → ValueLocation FS → Set
  SumTag Heap  t s loc = readLoc s loc ≡ just (SV-Tag t)
  SumTag Stack t s loc = readLoc s loc ≡ just (SV-Tag t)

  -- Transport `SumTag` across a state change preserving the cell's read.
  transport-SumTag : ∀ {m t s₁ s₂ loc}
                   → readLoc s₂ loc ≡ readLoc s₁ loc
                   → SumTag m t s₁ loc → SumTag m t s₂ loc
  transport-SumTag {Heap}  eq tg = trans eq tg
  transport-SumTag {Stack} eq tg = trans eq tg

  -- Plan 0.54 Phase B rung A (A2): the primitive-storage bridge. Crosses the
  -- 0.52-M2 IRTy/Type seam ONCE (the IRTy value `v : ⟦ B ⟧ᴵ` is stored as the
  -- Type-indexed `SV-Lit`), so the strengthened primitive-value premise reads
  -- uniformly `readLoc s loc ≡ just (prim-sv fit v)` — the stored machine value
  -- IS the semantic value. `fits-int`/`fits-float` here are the IRTy `FitsInRegI`
  -- constructors; `fits-intˢ`/`fits-floatˢ` the Type-level ones `SV-Lit` wants.
  prim-sv : ∀ {B : IRTy} → FitsInRegI B → ⟦ B ⟧ → StoredValue FS
  prim-sv fits-int   v = SV-Lit fits-intˢ   v
  prim-sv fits-float v = SV-Lit fits-floatˢ v

  ------------------------------------------------------------------------
  -- Stage F: how a sum's payload CELL stands for its payload, when the
  -- payload has no block of its own. Two ways, and the reason this is a
  -- PARAMETER rather than a second pair of constructors is that every
  -- transport below passes the witness through opaquely — widening the
  -- witness costs those sites nothing, adding a constructor would cost each
  -- of them a clause.
  --
  --   `rep-prim` — the payload FITS IN A REGISTER, so the cell holds the
  --     value itself, `prim-sv fit a`.
  --   `rep-unit` — the payload is `Unit`, which has one inhabitant and
  --     therefore carries no information. The cell holds whatever the trace
  --     happened to copy there (`store-at-slot` after `mov-to-output`, and
  --     `Input1` is unconstrained for a unit input), so the witness records
  --     that value rather than pretending to constrain it. This is the same
  --     stance as `in-unit` and `unit-result`: Unit has NO residence.
  ------------------------------------------------------------------------
  data InlineRep (A : IRTy) : Set where
    rep-prim : FitsInRegI A → InlineRep A
    rep-unit : A ≡ Unit → StoredValue FS → InlineRep A

  inline-sv : ∀ {A : IRTy} → InlineRep A → ⟦ A ⟧ → StoredValue FS
  inline-sv (rep-prim fit)  a = prim-sv fit a
  inline-sv (rep-unit _ sv) _ = sv



  ------------------------------------------------------------------------
  -- plan 0.135 S1: `ValidAtWF` IS A FUNCTION ON THE TYPE.
  --
  -- It was a `data` indexed by the type, so a constructor could assert only
  -- facts about cells, never what a closure DOES (D217: one cell valid at two
  -- denotations). An arrow case that says what the block computes takes a
  -- valid INPUT as a premise, i.e. it is negative in the relation, which no
  -- `data` accepts. So each case is a small NON-recursive `data` parameterised
  -- by the validity of its components (`VTy`), and `ValidAtWF` (in
  -- `ClosureWellFormedDef`) only dispatches on the type. A negative occurrence
  -- of a PARAMETER is allowed; the recursion is structural on the type.
  -- At a known type `ValidAtWF` reduces, so the constructor names below build
  -- and match exactly as before.
  ------------------------------------------------------------------------
  VTy : IRTy → Set₁
  VTy A = AllocMode → AllocState {FS} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set

  -- plan 0.135 S2: VALUES LIVE ON THE HEAP. Pointers go stack → heap and
  -- heap → heap, never into the stack (no `lea-slot` is emitted, and a call
  -- through an `SV-Ptr (AtStack …)` halts). So every location INSIDE a value
  -- is a heap location, and its liveness is the heap frontier's alone: a
  -- call's `enter-call` and a return's `leave-frame` move frames, not the
  -- heap, so they cannot make a value's cells dead. (Inside a callee the
  -- caller's frame is an ancestor, hence `BeforeFrontier`; after the return
  -- it is the current frame again, which `next-slot ≡ 0` makes dead. With
  -- stack cells allowed here, a callee's result could not survive `c-ret`.)
  Live : AllocState {FS} → ValueLocation FS → Set
  Live alloc (AtStack _ _)  = ⊥
  Live alloc (AtDynamic hl) = BeforeFrontier alloc (AtDynamic hl)

  live→bf : ∀ {alloc l} → Live alloc l → BeforeFrontier alloc l
  live→bf {l = AtDynamic _} b = b

  bf→live : ∀ {alloc l} → LocMatchesMode Heap l → BeforeFrontier alloc l → Live alloc l
  bf→live {l = AtDynamic _} _ b = b

  live-heap : ∀ {alloc l} → Live alloc l → LocMatchesMode Heap l
  live-heap {l = AtDynamic _} _ = tt

  -- a frontier fact about one location, carried to its `Live` form
  live-lift : ∀ {a₁ a₂ : AllocState {FS}} {l} → (BeforeFrontier a₁ l → BeforeFrontier a₂ l) → Live a₁ l → Live a₂ l
  live-lift {l = AtDynamic _} f b = f b

  -- the same, from a frontier map that is only asked about heap cells
  live-map : ∀ {a₁ a₂ : AllocState {FS}}
           → (∀ hl → BeforeFrontier a₁ (AtDynamic hl) → BeforeFrontier a₂ (AtDynamic hl))
           → ∀ l → Live a₁ l → Live a₂ l
  live-map f (AtDynamic hl) b = f hl b

  -- …and a live cell is live whatever the stack frontier is.
  live-ns : ∀ {alloc : AllocState {FS}} (m : ℕ) {l} → Live alloc l → BeforeFrontier (record alloc { next-slot = m }) l
  live-ns m {AtDynamic _} (BeforeFrontier.heap-before r<h) = BeforeFrontier.heap-before r<h

  -- D187: where a compound's component lives — a pointer to a cell valid at
  -- the component's type, or the component inline.
  data CellAtP {C : IRTy} (VC : VTy C) (alloc : AllocState {FS}) :
       ⟦ C ⟧ → ValueLocation FS → LocState FS → Set where
    cell-ptr : ∀ {c : ⟦ C ⟧} {cell-loc comp-loc : ValueLocation FS}
                 {s : LocState FS} {mC : AllocMode} →
               readLoc s cell-loc ≡ just (SV-Ptr comp-loc) →
               Live alloc comp-loc →
               VC mC alloc c comp-loc s →
               CellAtP {C} VC alloc c cell-loc s
    cell-inline : ∀ {c : ⟦ C ⟧} {cell-loc : ValueLocation FS}
                    {s : LocState FS} (rep : InlineRep C) →
               readLoc s cell-loc ≡ just (inline-sv rep c) →
               CellAtP {C} VC alloc c cell-loc s

  data UnitV : AllocMode → AllocState {FS} → ⟦ Unit ⟧ → ValueLocation FS → LocState FS → Set where
    unit-wf : ∀ {m alloc loc s} → UnitV m alloc tt loc s

  -- `⟦ Void ⟧` is empty, and so is its relation.
  data VoidV : AllocMode → AllocState {FS} → ⟦ Void ⟧ → ValueLocation FS → LocState FS → Set where

  data PairV {A B : IRTy} (VA : VTy A) (VB : VTy B) :
       AllocMode → AllocState {FS} → ⟦ A * B ⟧ → ValueLocation FS → LocState FS → Set where
    pair-wf : ∀ {m} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
      {alloc : AllocState {FS}} {pair-loc : ValueLocation FS} {s : LocState FS} →
      LocMatchesMode m pair-loc →
      Live alloc (sucLoc pair-loc) →
      CellAtP {A} VA alloc a pair-loc s →
      CellAtP {B} VB alloc b (sucLoc pair-loc) s →
      PairV {A} {B} VA VB m alloc (a , b) pair-loc s

  data SumV {A B : IRTy} (VA : VTy A) (VB : VTy B) :
       AllocMode → AllocState {FS} → ⟦ A + B ⟧ → ValueLocation FS → LocState FS → Set where
    inl-wf : ∀ {m} {a : ⟦ A ⟧} {alloc : AllocState {FS}}
      {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} {mA : AllocMode} →
      LocMatchesMode m sum-loc →
      SumTag m 0 s sum-loc →
      readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
      Live alloc payload-loc →
      Live alloc (sucLoc sum-loc) →
      VA mA alloc a payload-loc s →
      SumV {A} {B} VA VB m alloc (inj₁ a) sum-loc s
    inr-wf : ∀ {m} {b : ⟦ B ⟧} {alloc : AllocState {FS}}
      {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} {mB : AllocMode} →
      LocMatchesMode m sum-loc →
      SumTag m 1 s sum-loc →
      readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
      Live alloc payload-loc →
      Live alloc (sucLoc sum-loc) →
      VB mB alloc b payload-loc s →
      SumV {A} {B} VA VB m alloc (inj₂ b) sum-loc s
    -- Stage F: an inline payload has no cell of its own to be valid at.
    inl-reg-wf : ∀ {m} {a : ⟦ A ⟧} {alloc : AllocState {FS}}
      {sum-loc : ValueLocation FS} {s : LocState FS} →
      LocMatchesMode m sum-loc →
      SumTag m 0 s sum-loc →
      (rep : InlineRep A) →
      readLoc s (sucLoc sum-loc) ≡ just (inline-sv rep a) →
      Live alloc (sucLoc sum-loc) →
      SumV {A} {B} VA VB m alloc (inj₁ a) sum-loc s
    inr-reg-wf : ∀ {m} {b : ⟦ B ⟧} {alloc : AllocState {FS}}
      {sum-loc : ValueLocation FS} {s : LocState FS} →
      LocMatchesMode m sum-loc →
      SumTag m 1 s sum-loc →
      (rep : InlineRep B) →
      readLoc s (sucLoc sum-loc) ≡ just (inline-sv rep b) →
      Live alloc (sucLoc sum-loc) →
      SumV {A} {B} VA VB m alloc (inj₂ b) sum-loc s

  -- Plan 0.54 Phase B rung A: the stored value IS the semantic value.
  data IntV : AllocMode → AllocState {FS} → ⟦ Int ⟧ → ValueLocation FS → LocState FS → Set where
    int-wf : ∀ {m} {n : ⟦ Int ⟧} {alloc : AllocState {FS}}
      {loc : ValueLocation FS} {s : LocState FS} →
      Live alloc loc →
      readLoc s loc ≡ just (prim-sv fits-int n) →
      IntV m alloc n loc s

  data FloatV : AllocMode → AllocState {FS} → ⟦ Float ⟧ → ValueLocation FS → LocState FS → Set where
    float-wf : ∀ {m} {x : ⟦ Float ⟧} {alloc : AllocState {FS}}
      {loc : ValueLocation FS} {s : LocState FS} →
      Live alloc loc →
      readLoc s loc ≡ just (prim-sv fits-float x) →
      FloatV m alloc x loc s

  -- Where a result is, for a validity `VB` (the arrow case's callee result).
  -- `ResultPlace` (ClosureWellFormedDef) is the same at `ValidAtWF`, as an
  -- indexed `data`; `rp→place` converts.
  data ResultPlaceP {B : IRTy} (VB : VTy B) :
       AllocMode → AllocState {FS} → AllocState {FS} → ⟦ B ⟧ → LocState FS → Set where
    rp-unit : ∀ {m alloc ca v s} → B ≡ Unit → ResultPlaceP {B} VB m alloc ca v s
    rp-loc  : ∀ {m alloc ca v s} (loc : ValueLocation FS)
            → VB m alloc v loc s
            → Live alloc loc
            → readReg (regs s) Output ≡ SV-Ptr loc
            → VB m ca v loc s
            → Live ca loc
            → ResultPlaceP {B} VB m alloc ca v s
    rp-reg  : ∀ {m alloc ca v s} (fit : FitsInRegI B)
            → readReg (regs s) Output ≡ prim-sv fit v
            → ResultPlaceP {B} VB m alloc ca v s

  ------------------------------------------------------------------------
  -- μ is FIRST-ORDER data: `WellFormedFI` allows only `IsBaseTypeI` under
  -- `K`, so no `⇛`/`ν` is reachable. Its layer `⟦ F ⟧TI (μ-type F)` contains
  -- `μ-type F` again, so it is not structural on the type; it is an ordinary
  -- (nested) inductive relation instead, reusing the case datas above.
  ------------------------------------------------------------------------
  data ValidFO : AllocMode → AllocState {FS} →
       {A : IRTy} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set where
    fo-unit  : ∀ {m alloc v loc s} → UnitV m alloc v loc s → ValidFO m alloc {Unit} v loc s
    fo-pair  : ∀ {A B m alloc v loc s} →
               PairV {A} {B} (λ m′ a′ → ValidFO m′ a′ {A}) (λ m′ a′ → ValidFO m′ a′ {B}) m alloc v loc s →
               ValidFO m alloc {A * B} v loc s
    fo-sum   : ∀ {A B m alloc v loc s} →
               SumV {A} {B} (λ m′ a′ → ValidFO m′ a′ {A}) (λ m′ a′ → ValidFO m′ a′ {B}) m alloc v loc s →
               ValidFO m alloc {A + B} v loc s
    fo-int   : ∀ {m alloc v loc s} → IntV m alloc v loc s → ValidFO m alloc {Int} v loc s
    fo-float : ∀ {m alloc v loc s} → FloatV m alloc v loc s → ValidFO m alloc {Float} v loc s
    -- Plan 0.27 Option 3: the layer's own validity at the same location —
    -- for a functor whose layer is already a pointer (D364: `Unboxed`).
    fo-μwf : ∀ {m F}
      {alloc : AllocState {FS}} {loc : ValueLocation FS} {s : LocState FS}
      (ub : Unboxed F) (wf : WellFormedFI F) (x : ⟦ μ-type F ⟧) →
      ValidFO m alloc {⟦ F ⟧TI (μ-type F)} (valueNow (evalᴰ (out-μ wf) x)) loc s →
      ValidFO m alloc {μ-type F} x loc s
    -- D364: a BOXED μ (`K Int`/`K Float`, `MuRep.mu-box`) is a block whose
    -- first cell holds the layer — the layer itself, or a pointer to it, as
    -- any cell may (D187). `In` builds it; `out-μ` and the cata read it back.
    fo-μbox : ∀ {m F}
      {alloc : AllocState {FS}} {loc : ValueLocation FS} {s : LocState FS}
      (bx : mu-rep F ≡ mu-box) (wf : WellFormedFI F) (x : ⟦ μ-type F ⟧) →
      CellAtP {⟦ F ⟧TI (μ-type F)} (λ m′ a′ → ValidFO m′ a′ {⟦ F ⟧TI (μ-type F)}) alloc
              (valueNow (evalᴰ (out-μ wf) x)) loc s →
      ValidFO m alloc {μ-type F} x loc s

  -- plan 0.135 S1: a FORCED ν LAYER, `⟦ G ⟧TI X`, at the validity `R` of its
  -- recursive positions (the spike's `NuLayer`). Recursion on the functor
  -- code, so `NuV` can pass ITSELF as `R`; the case datas are the ones
  -- `ValidAtWF` uses. A constant position is first-order (`WellFormedFI`
  -- limits `K` to `IsBaseTypeI`), so it is `ValidFO`, never `ValidAtWF`:
  -- that keeps `NuV` out of the arrow case's negative occurrence.
  LayerV : (G : IRFunctor) {X : IRTy} → VTy X → VTy (⟦ G ⟧TI X)
  LayerV (K A)   R m alloc = ValidFO m alloc {A}
  LayerV Id      R         = R
  LayerV (G ⊕ H) {X} R     = SumV {⟦ G ⟧TI X} {⟦ H ⟧TI X} (LayerV G R) (LayerV H R)
  LayerV (G ⊗ H) {X} R     = PairV {⟦ G ⟧TI X} {⟦ H ⟧TI X} (LayerV G R) (LayerV H R)

  -- The types `ValidFO` speaks about.
  data FOTy : IRTy → Set where
    fo-Unit  : FOTy Unit
    fo-Void  : FOTy Void
    fo-Int   : FOTy Int
    fo-Float : FOTy Float
    fo-*     : ∀ {A B} → FOTy A → FOTy B → FOTy (A * B)
    fo-+     : ∀ {A B} → FOTy A → FOTy B → FOTy (A + B)
    fo-μ     : ∀ {F} → FOTy (μ-type F)

  fo-base : ∀ {A} → IsBaseTypeI A → FOTy A
  fo-base base-Unit        = fo-Unit
  fo-base base-Void        = fo-Void
  fo-base base-Int         = fo-Int
  fo-base base-Float       = fo-Float
  fo-base (base-Prod a b)  = fo-* (fo-base a) (fo-base b)
  fo-base (base-Sum a b)   = fo-+ (fo-base a) (fo-base b)

  fo-layer : ∀ {G X} → WellFormedFI G → FOTy X → FOTy (⟦ G ⟧TI X)
  fo-layer (wf-K ib)      _  = fo-base ib
  fo-layer wf-Id          fx = fx
  fo-layer (wf-Sum f g)   fx = fo-+ (fo-layer f fx) (fo-layer g fx)
  fo-layer (wf-Prod f g)  fx = fo-* (fo-layer f fx) (fo-layer g fx)

  -- `ValidAtWF` is a FUNCTION, so it is not injective in its indices and
  -- Agda could not infer the type of a witness from it. Wrapping every case
  -- in this NON-recursive record restores that: the indices are record
  -- parameters. Pattern synonyms (`valid-pair-wf = wrap (pair-wf …)`) keep
  -- the constructor names every consumer uses.
  record Wrap (p : AbstractTrace) (A : IRTy) (m : AllocMode) (alloc : AllocState {FS}) (v : ⟦ A ⟧)
              (loc : ValueLocation FS) (s : LocState FS) (P : Set) : Set where
    constructor wrap
    field unwrap : P

  ------------------------------------------------------------------------
  -- The observation vocabulary a callee's run is stated in (moved here from
  -- `IRObsCorrect.Interface`, which now reuses it): plan 0.105's run of a
  -- tree against `ιᶠ` from the state's log, and plan 0.119's approximation.
  ------------------------------------------------------------------------
  runAt : ∀ {X} → LocState FS → TM.T X → TM.Run X
  runAt s m = TM.run ιᶠ (LocState.ev-log s) m

  eventsAt : ∀ {X} → LocState FS → TM.T X → List SigOpEvent
  eventsAt s m = proj₁ (runAt s m)

  resultAt : ∀ {X} → LocState FS → TM.T X → Res X
  resultAt s m = proj₂ (runAt s m)

  stopsAt : ∀ {X} → LocState FS → TM.T X → Bool
  stopsAt s m = is-stopped (resultAt s m)

  ⟪_⟫_ : ∀ {X} → T∞ X → ℕ → TM.T (Ap X)
  ⟪ m ⟫ k = approx k m



-- plan 0.135 S1: everything that mentions `ValidAtWF` is relative to the
-- PROGRAM, because the arrow case says the closure's label resolves in it.
module ClosureWellFormedDef {FS : FrameSemantics} {prog : AbstractTrace} where
  open ClosureWellFormedBase {FS}
  open FlatMachine {FS} using (FlatState; fpc; floc; fret; falloc; flink; find-thunk; enter-call)
  open FlatStepsAPI {FS} using (FlatSteps)
  open FlatEventTrace {FS} using (chain-events; chain-ctrls)
  open import Once.CCC.Machine.Validity
  open ReadLocEq {FS}
    using (readLoc-stack-heap-eq)
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open AbstractExec {FS}
  open TracePrimitives {FS}
  open FrameSemantics FS

  -- Plan 0.52 M2: μValid/νValid (surface MuValidity) are unused here — the
  -- the valid-μ-wf constructor carries the layer's own ValidAtWF
  -- (Option 3), so the MuValidity dependency is severed.

  -- Import write operations for validity preservation proofs
  open import Once.CCC.Machine.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  ------------------------------------------------------------------------
  -- A CALLED BLOCK'S RUN (moved from `IRObsCorrect.Interface`; field
  -- commentary there, D198–D357). Parameterised by where the result is
  -- (`R`), so the arrow case below can state it at its own codomain's
  -- validity; `Interface.CalleeRun` is this at `ResultPlace`.
  ------------------------------------------------------------------------
  record CalleeRunP {B : IRTy}
                    (R : AllocMode → AllocState {FS} → AllocState {FS} → ⟦ B ⟧ → LocState FS → Set)
                    (fs : FlatState) (ret-pc : ℕ) (rs : List ℕ)
                    (comp : T∞ ⟦ B ⟧) (k : ℕ) : Set where
    constructor callee-run
    field
      steps      : ℕ
      settle     : FlatState
      out-mode   : AllocMode
      cont-alloc : AllocState {FS}
      run        : FlatSteps prog steps fs settle
      live       : stopsAt (floc fs) (⟪ comp ⟫ k) ≡ false → halted (floc settle) ≡ false
      returned   : ∀ {v r} → resultAt (floc fs) (⟪ comp ⟫ k) ≡ returns (done v r) → fpc settle ≡ ret-pc
      stops      : stopsAt (floc fs) (⟪ comp ⟫ k) ≡ true  → halted (floc settle) ≡ true × LocState.left (floc settle) ≡ LocState.left (floc fs)
      no-ret     : ∀ {v r} → resultAt (floc fs) (⟪ comp ⟫ k) ≡ returns (done v r) → fret settle ≡ rs
      no-link    : NotCut (resultAt (floc fs) (⟪ comp ⟫ k)) → flink settle ≡ nothing
      place      : ∀ {v r} → resultAt (floc fs) (⟪ comp ⟫ k) ≡ returns (done v r)
                 → R out-mode (falloc settle) cont-alloc v (floc settle)
      events     : chain-events run ≡ eventsAt (floc fs) (⟪ comp ⟫ k)
      log        : LocState.ev-log (floc settle) ≡ LocState.ev-log (floc fs) ++ eventsAt (floc fs) (⟪ comp ⟫ k)
      progress   : k ≤ budgetLeft k (resultAt (floc fs) (⟪ comp ⟫ k)) ℕ.+ chain-ctrls run
      mem-pres   : NotCut (resultAt (floc fs) (⟪ comp ⟫ k)) → ∀ (pre : AllocState {FS}) (m : ℕ) → falloc fs ≡ enter-call pre
                 → ∀ (loc : ValueLocation FS)
                 → BeforeFrontier (record pre { next-slot = m }) loc
                 → readLoc (floc settle) loc ≡ readLoc (floc fs) loc
      frame-pres : ∀ {v r} → resultAt (floc fs) (⟪ comp ⟫ k) ≡ returns (done v r) → ∀ (pre : AllocState {FS}) → falloc fs ≡ enter-call pre
                 → current-frame (falloc settle) ≡ current-frame pre
      bf-mono    : NotCut (resultAt (floc fs) (⟪ comp ⟫ k)) → ∀ (pre : AllocState {FS}) (m : ℕ) → falloc fs ≡ enter-call pre
                 → ∀ (loc : ValueLocation FS)
                 → BeforeFrontier (record pre { next-slot = m }) loc
                 → BeforeFrontier (record (falloc settle) { next-slot = m }) loc
      frames-pres : ∀ {v r} → resultAt (floc fs) (⟪ comp ⟫ k) ≡ returns (done v r) → ∀ (pre : AllocState {FS}) → falloc fs ≡ enter-call pre
                  → saved-frames (falloc settle) ≡ saved-frames pre

  -- A run is a run whatever is said about where its result is.
  crun-map : ∀ {B} {R R′ : AllocMode → AllocState {FS} → AllocState {FS} → ⟦ B ⟧ → LocState FS → Set}
           → (∀ {m a₁ a₂ v s} → R m a₁ a₂ v s → R′ m a₁ a₂ v s)
           → ∀ {fs ret-pc rs comp k} → CalleeRunP {B} R fs ret-pc rs comp k → CalleeRunP {B} R′ fs ret-pc rs comp k
  crun-map f (callee-run st se om ca ru li re sp nr nl pl ev lg pr mp fp bm fsp) =
    callee-run st se om ca ru li re sp nr nl (λ e → f (pl e)) ev lg pr mp fp bm fsp

  ------------------------------------------------------------------------
  -- plan 0.135 S1: WHAT A CLOSURE DOES, as a fact about the value.
  --
  -- Entering the block `j` from a call (`enter-call pre`), with `Input1`
  -- pointing at a heap pair whose cell 0 holds what THIS closure's env cell
  -- holds and whose cell 1 holds a VALID argument, runs `f a` and returns
  -- (`CalleeRunP`). The environment stays opaque: its type is hidden in the
  -- closure, so its validity is not a subterm of `A ⇛ B`. What makes it still
  -- valid at the call is the caller's guarantee that everything live when the
  -- closure was built (`BeforeFrontier alloc`) still reads the same and is
  -- still live (plan 0.93 spike finding 2: `HeapAgree`/`HeapMono`). `curry`
  -- proves this from its body's correctness (S3); `apply` spends it.
  ------------------------------------------------------------------------
  CallRuns : ∀ {A B : IRTy} → VTy A → VTy B → AllocState {FS} → LocState FS
           → ValueLocation FS → ℕ → ⟦ A ⇛ B ⟧ → Set
  CallRuns {A} {B} VA VB alloc s cloc j f =
    ∀ (fs : FlatState) (pre : AllocState {FS}) (a : ⟦ A ⟧) (pair-loc : ValueLocation FS)
      (ret-pc k : ℕ) (rs : List ℕ)
    → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ rs
    → falloc fs ≡ enter-call pre
    → next-slot pre ≡ 0
    → (∀ l → Live alloc l → Live pre l)
    → (∀ l → Live alloc l → readLoc (floc fs) l ≡ readLoc s l)
    → readReg (regs (floc fs)) Input1 ≡ SV-Ptr pair-loc
    → Live pre pair-loc
    → Live pre (sucLoc pair-loc)
    → readLoc (floc fs) pair-loc ≡ readLoc s cloc
    → CellAtP {A} VA pre a (sucLoc pair-loc) (floc fs)
    → CalleeRunP {B} (ResultPlaceP {B} VB) fs ret-pc rs (f a) k

  -- D170/D181/D184: the two closure records (boxed / inline env), heap only.
  -- The env's own validity is GONE (see `CallRuns`); the code cell's label
  -- now resolves (`find-thunk`) and the block's behaviour is `runs`.
  data ArrowV {A B : IRTy} (VA : VTy A) (VB : VTy B) :
       AllocMode → AllocState {FS} → ⟦ A ⇛ B ⟧ → ValueLocation FS → LocState FS → Set where
    closure-wf : ∀ {f : ⟦ A ⇛ B ⟧}
      {alloc : AllocState {FS}}
      {closure-loc env-loc : ValueLocation FS} {s : LocState FS}
      {body-label : LabelId} {j : ℕ} →
      LocMatchesMode Heap closure-loc →
      readLoc s closure-loc ≡ just (SV-Ptr env-loc) →
      readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label) →
      Live alloc env-loc →
      Live alloc (sucLoc closure-loc) →
      find-thunk prog body-label ≡ just j →
      CallRuns {A} {B} VA VB alloc s closure-loc j f →
      ArrowV {A} {B} VA VB Heap alloc f closure-loc s
    closure-reg-wf : ∀ {EnvType} {f : ⟦ A ⇛ B ⟧} {env : ⟦ EnvType ⟧}
      {alloc : AllocState {FS}}
      {closure-loc : ValueLocation FS} {s : LocState FS}
      {body-label : LabelId} {j : ℕ} →
      LocMatchesMode Heap closure-loc →
      (rep : InlineRep EnvType) →
      readLoc s closure-loc ≡ just (inline-sv rep env) →
      readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label) →
      Live alloc (sucLoc closure-loc) →
      find-thunk prog body-label ≡ just j →
      CallRuns {A} {B} VA VB alloc s closure-loc j f →
      ArrowV {A} {B} VA VB Heap alloc f closure-loc s

  ------------------------------------------------------------------------
  -- plan 0.135 S1: A ν IS WHAT FORCING IT DOES (the spike's `RelNu`, path (a)).
  --
  -- Two heap cells (D189): cell 0 the seed's stored value, cell 1 the code
  -- of the block that forces it. The seed stays OPAQUE: its type is not a
  -- subterm of `ν-type F` (an `Ana` seed is any `E * A`, an `in-ν` seed is a
  -- layer containing `ν-type F`), so its validity cannot be stated here; as
  -- with a closure's environment, what keeps it valid at the force is the
  -- caller's guarantee that everything live at construction still reads the
  -- same and is still live.
  --
  -- `nu-force` is the arrow case's `CallRuns` minus the pair-packing (`Out`
  -- hands the block the seed cell's CONTENT in `Input1`), and its result is
  -- a LAYER whose recursive positions are again `NuV`. That occurrence is
  -- under a field of a COINDUCTIVE record — the guard — and it is the only
  -- one: no index, no step count (the spike, STEP 3). The value `v` occurs
  -- only in the conclusion (`evalᴰ (Out wf) v`), so one cell cannot be valid
  -- at two νs that force differently (D217). Every functor witness gives the
  -- same `Out` (`WellFormedFI-irrelevant`); quantifying over it keeps the
  -- witness the suspension was built with away from the one at the `Out`.
  ------------------------------------------------------------------------
  -- What forcing a ν does, at the validity `R` of the layer's recursive
  -- positions (`NuV` passes itself).
  ForceRuns : ∀ {F : IRFunctor} → VTy (ν-type F) → AllocState {FS} → LocState FS
            → StoredValue FS → ℕ → ⟦ ν-type F ⟧ → Set
  ForceRuns {F} R alloc s seed j v =
    ∀ (wf : WellFormedFI F) (fs : FlatState) (pre : AllocState {FS})
      (ret-pc k : ℕ) (rs : List ℕ)
    → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ rs
    → falloc fs ≡ enter-call pre
    → next-slot pre ≡ 0
    → (∀ l → Live alloc l → Live pre l)
    → (∀ l → Live alloc l → readLoc (floc fs) l ≡ readLoc s l)
    → readReg (regs (floc fs)) Input1 ≡ seed
    → CalleeRunP {⟦ F ⟧TI (ν-type F)}
        (ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} R))
        fs ret-pc rs (evalᴰ (Out wf) v) k

  record NuV {F : IRFunctor} (m : AllocMode) (alloc : AllocState {FS}) (v : ⟦ ν-type F ⟧)
             (ν-loc : ValueLocation FS) (s : LocState FS) : Set where
    coinductive
    field
      nu-mode  : m ≡ Heap
      nu-heap  : LocMatchesMode Heap ν-loc
      nu-seed  : StoredValue FS
      nu-lbl   : LabelId
      nu-j     : ℕ
      nu-cell0 : readLoc s ν-loc ≡ just nu-seed
      nu-cell1 : readLoc s (sucLoc ν-loc) ≡ just (SV-Code nu-lbl)
      nu-live1 : Live alloc (sucLoc ν-loc)
      nu-code  : find-thunk prog nu-lbl ≡ just nu-j
      nu-force : ForceRuns {F} (λ m′ a′ v′ l′ s′ → NuV {F} m′ a′ v′ l′ s′) alloc s nu-seed nu-j v
  open NuV

  ------------------------------------------------------------------------
  -- THE COINDUCTION PRINCIPLE for `NuV`. A predicate `P` on ν cells whose
  -- every force yields a layer of `P`s (`NuStep P`) implies `NuV`. This is
  -- the only corecursion: the producers (`Ana`) prove a one-layer step about
  -- an INDUCTIVE `P`, so their proofs never have to be guarded. The layer
  -- conversion is written out inside the mutual block (first-order), which is
  -- what lets the termination checker see the guard (a map passed to a
  -- higher-order helper hides it).
  ------------------------------------------------------------------------
  record NuStep {F : IRFunctor} (P : VTy (ν-type F)) (m : AllocMode) (alloc : AllocState {FS})
                (v : ⟦ ν-type F ⟧) (ν-loc : ValueLocation FS) (s : LocState FS) : Set where
    field
      st-mode  : m ≡ Heap
      st-heap  : LocMatchesMode Heap ν-loc
      st-seed  : StoredValue FS
      st-lbl   : LabelId
      st-j     : ℕ
      st-cell0 : readLoc s ν-loc ≡ just st-seed
      st-cell1 : readLoc s (sucLoc ν-loc) ≡ just (SV-Code st-lbl)
      st-live1 : Live alloc (sucLoc ν-loc)
      st-code  : find-thunk prog st-lbl ≡ just st-j
      st-force : ForceRuns {F} P alloc s st-seed st-j v

  module NuCoind {F : IRFunctor} (P : VTy (ν-type F))
                 (step : ∀ {m a v l s} → P m a v l s → NuStep {F} P m a v l s) where
    mutual
      coind : ∀ {m a v l s} → P m a v l s → NuV {F} m a v l s
      nu-mode  (coind p) = NuStep.st-mode  (step p)
      nu-heap  (coind p) = NuStep.st-heap  (step p)
      nu-seed  (coind p) = NuStep.st-seed  (step p)
      nu-lbl   (coind p) = NuStep.st-lbl   (step p)
      nu-j     (coind p) = NuStep.st-j     (step p)
      nu-cell0 (coind p) = NuStep.st-cell0 (step p)
      nu-cell1 (coind p) = NuStep.st-cell1 (step p)
      nu-live1 (coind p) = NuStep.st-live1 (step p)
      nu-code  (coind p) = NuStep.st-code  (step p)
      nu-force (coind p) wf fs pre ret-pc k rs pc nh fr fa ns incl agree i1 =
        crun-conv (NuStep.st-force (step p) wf fs pre ret-pc k rs pc nh fr fa ns incl agree i1)

      crun-conv : ∀ {fs ret-pc rs comp k}
                → CalleeRunP {⟦ F ⟧TI (ν-type F)} (ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} P)) fs ret-pc rs comp k
                → CalleeRunP {⟦ F ⟧TI (ν-type F)}
                    (ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} (λ m′ a′ v′ l′ s′ → NuV {F} m′ a′ v′ l′ s′)))
                    fs ret-pc rs comp k
      crun-conv (callee-run st se om ca ru li re sp nr nl pl ev lg pr mp fp bm fsp) =
        callee-run st se om ca ru li re sp nr nl (λ e → rp-conv (pl e)) ev lg pr mp fp bm fsp

      rp-conv : ∀ {m a₁ a₂ v s}
              → ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} P) m a₁ a₂ v s
              → ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} (λ m′ a′ v′ l′ s′ → NuV {F} m′ a′ v′ l′ s′)) m a₁ a₂ v s
      rp-conv (rp-unit e) = rp-unit e
      rp-conv (rp-loc loc v bf rax cv cbf) = rp-loc loc (lay F v) bf rax (lay F cv) cbf
      rp-conv (rp-reg fit rax) = rp-reg fit rax

      lay : ∀ (G : IRFunctor) {m a v l s}
          → LayerV G {ν-type F} P m a v l s → LayerV G {ν-type F} (λ m′ a′ v′ l′ s′ → NuV {F} m′ a′ v′ l′ s′) m a v l s
      lay (K A) lv = lv
      lay Id    lv = coind lv
      lay (G ⊕ H) (inl-wf lmm tg pp pb slb pv) = inl-wf lmm tg pp pb slb (lay G pv)
      lay (G ⊕ H) (inr-wf lmm tg pp pb slb pv) = inr-wf lmm tg pp pb slb (lay H pv)
      lay (G ⊕ H) (inl-reg-wf lmm tg rep pp slb) = inl-reg-wf lmm tg rep pp slb
      lay (G ⊕ H) (inr-reg-wf lmm tg rep pp slb) = inr-reg-wf lmm tg rep pp slb
      lay (G ⊗ H) (pair-wf lmm slb c₁ c₂) = pair-wf lmm slb (cell G c₁) (cell H c₂)

      cell : ∀ (G : IRFunctor) {a c cl s}
           → CellAtP {⟦ G ⟧TI (ν-type F)} (LayerV G {ν-type F} P) a c cl s
           → CellAtP {⟦ G ⟧TI (ν-type F)} (LayerV G {ν-type F} (λ m′ a′ v′ l′ s′ → NuV {F} m′ a′ v′ l′ s′)) a c cl s
      cell G (cell-ptr r bf v) = cell-ptr r bf (lay G v)
      cell G (cell-inline rep r) = cell-inline rep r

  ------------------------------------------------------------------------
  -- THE RELATION. Structural on the type; no pragma.
  ------------------------------------------------------------------------
  mutual
    VCase : (A : IRTy) → VTy A
    VCase Unit       = UnitV
    VCase Void       = VoidV
    VCase (A * B)    = PairV {A} {B} (VAt A) (VAt B)
    VCase (A + B)    = SumV {A} {B} (VAt A) (VAt B)
    VCase (A ⇛ B)    = ArrowV {A} {B} (VAt A) (VAt B)
    VCase (μ-type F) = λ m alloc → ValidFO m alloc {μ-type F}
    VCase (ν-type F) = NuV {F}
    VCase Int        = IntV
    VCase Float      = FloatV

    ValidAtWF : AllocMode → AllocState {FS} →
                {A : IRTy} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set
    ValidAtWF m alloc {A} v loc s = Wrap prog A m alloc v loc s (VCase A m alloc v loc s)

    VAt : (A : IRTy) → VTy A
    VAt A m alloc = ValidAtWF m alloc {A}

  pattern valid-unit-wf = wrap unit-wf
  pattern valid-pair-wf {pair-loc} lmm slb c₁ c₂ = wrap (pair-wf {pair-loc = pair-loc} lmm slb c₁ c₂)
  pattern valid-inl-wf {m} {a} {sum-loc} {payload-loc} {mA} lmm tg pp pb slb pv =
    wrap (inl-wf {m = m} {a = a} {sum-loc = sum-loc} {payload-loc = payload-loc} {mA = mA} lmm tg pp pb slb pv)
  pattern valid-inr-wf {m} {b} {sum-loc} {payload-loc} {mB} lmm tg pp pb slb pv =
    wrap (inr-wf {m = m} {b = b} {sum-loc = sum-loc} {payload-loc = payload-loc} {mB = mB} lmm tg pp pb slb pv)
  pattern valid-inl-reg-wf {m} {a} {sum-loc} lmm tg rep pp slb =
    wrap (inl-reg-wf {m = m} {a = a} {sum-loc = sum-loc} lmm tg rep pp slb)
  pattern valid-inr-reg-wf {m} {b} {sum-loc} lmm tg rep pp slb =
    wrap (inr-reg-wf {m = m} {b = b} {sum-loc = sum-loc} lmm tg rep pp slb)
  pattern valid-closure-wf {f} {closure-loc} {env-loc} lmm ep cp eb slb fd runs =
    wrap (closure-wf {f = f} {closure-loc = closure-loc} {env-loc = env-loc} lmm ep cp eb slb fd runs)
  pattern valid-closure-reg-wf {f} {env} {closure-loc} lmm rep ep cp slb fd runs =
    wrap (closure-reg-wf {f = f} {env = env} {closure-loc = closure-loc} lmm rep ep cp slb fd runs)
  pattern valid-ν-wf nv = wrap nv
  pattern valid-int-wf {loc} bf rl = wrap (int-wf {loc = loc} bf rl)
  pattern valid-float-wf {loc} bf rl = wrap (float-wf {loc = loc} bf rl)
  pattern valid-μ-wf ub wf x lv = wrap (fo-μwf ub wf x lv)
  pattern valid-μbox-wf bx wf x c = wrap (fo-μbox bx wf x c)

  CellAt : AllocState {FS} → (C : IRTy) → ⟦ C ⟧ → ValueLocation FS → LocState FS → Set
  CellAt alloc C = CellAtP {C} (VAt C) alloc

  -- The first-order bridge (μ layers).
  mutual
    fo→valid : ∀ {m alloc A v loc s} → ValidFO m alloc {A} v loc s → ValidAtWF m alloc {A} v loc s
    fo→valid (fo-unit u) = wrap u
    fo→valid (fo-pair (pair-wf lmm slb c₁ c₂)) =
      valid-pair-wf lmm slb (fo→cell c₁) (fo→cell c₂)
    fo→valid (fo-sum (inl-wf lmm tg pp pb slb pv)) = valid-inl-wf lmm tg pp pb slb (fo→valid pv)
    fo→valid (fo-sum (inr-wf lmm tg pp pb slb pv)) = valid-inr-wf lmm tg pp pb slb (fo→valid pv)
    fo→valid (fo-sum (inl-reg-wf lmm tg rep pp slb)) = valid-inl-reg-wf lmm tg rep pp slb
    fo→valid (fo-sum (inr-reg-wf lmm tg rep pp slb)) = valid-inr-reg-wf lmm tg rep pp slb
    fo→valid (fo-int i) = wrap i
    fo→valid (fo-float f) = wrap f
    fo→valid w@(fo-μwf _ _ _ _) = wrap w
    fo→valid w@(fo-μbox _ _ _ _) = wrap w

    fo→cell : ∀ {alloc C c cl s} → CellAtP {C} (λ m′ a′ → ValidFO m′ a′ {C}) alloc c cl s → CellAt alloc C c cl s
    fo→cell (cell-ptr r bf v) = cell-ptr r bf (fo→valid v)
    fo→cell (cell-inline rep r) = cell-inline rep r

  mutual
    valid→fo : ∀ {m alloc A v loc s} → FOTy A → ValidAtWF m alloc {A} v loc s → ValidFO m alloc {A} v loc s
    valid→fo fo-Unit (wrap u) = fo-unit u
    valid→fo fo-Void (wrap ())
    valid→fo fo-Int (wrap i) = fo-int i
    valid→fo fo-Float (wrap f) = fo-float f
    valid→fo (fo-* fa fb) (valid-pair-wf lmm slb c₁ c₂) =
      fo-pair (pair-wf lmm slb (cell→fo fa c₁) (cell→fo fb c₂))
    valid→fo (fo-+ fa fb) (valid-inl-wf lmm tg pp pb slb pv) = fo-sum (inl-wf lmm tg pp pb slb (valid→fo fa pv))
    valid→fo (fo-+ fa fb) (valid-inr-wf lmm tg pp pb slb pv) = fo-sum (inr-wf lmm tg pp pb slb (valid→fo fb pv))
    valid→fo (fo-+ fa fb) (valid-inl-reg-wf lmm tg rep pp slb) = fo-sum (inl-reg-wf lmm tg rep pp slb)
    valid→fo (fo-+ fa fb) (valid-inr-reg-wf lmm tg rep pp slb) = fo-sum (inr-reg-wf lmm tg rep pp slb)
    valid→fo fo-μ (wrap w) = w

    cell→fo : ∀ {alloc C c cl s} → FOTy C → CellAt alloc C c cl s → CellAtP {C} (λ m′ a′ → ValidFO m′ a′ {C}) alloc c cl s
    cell→fo fc (cell-ptr r bf v) = cell-ptr r bf (valid→fo fc v)
    cell→fo fc (cell-inline rep r) = cell-inline rep r

  -- The μ layer, read and written through the bridge: at an UNBOXED functor
  -- the layer is valid where the μ is.
  μ-layer : ∀ {m alloc F wf x loc s} → Unboxed F → ValidAtWF m alloc {μ-type F} x loc s
          → ValidAtWF m alloc {⟦ F ⟧TI (μ-type F)} (valueNow (evalᴰ (out-μ wf) x)) loc s
  μ-layer {wf = wf} u (valid-μ-wf ub wf′ x lv) rewrite WellFormedFI-irrelevant wf wf′ = fo→valid lv
  μ-layer u (valid-μbox-wf bx wf′ x c) = ⊥-elim (box-not-unboxed bx u)

  valid-μ : ∀ {m alloc F loc s} (ub : Unboxed F) (wf : WellFormedFI F) (x : ⟦ μ-type F ⟧)
          → ValidAtWF m alloc {⟦ F ⟧TI (μ-type F)} (valueNow (evalᴰ (out-μ wf) x)) loc s
          → ValidAtWF m alloc {μ-type F} x loc s
  valid-μ ub wf x lv = valid-μ-wf ub wf x (valid→fo (fo-layer wf fo-μ) lv)

  -- D364: …and at a BOXED one, the layer is the box's first cell.
  μ-box-cell : ∀ {m alloc F wf x loc s} → mu-rep F ≡ mu-box → ValidAtWF m alloc {μ-type F} x loc s
             → CellAt alloc (⟦ F ⟧TI (μ-type F)) (valueNow (evalᴰ (out-μ wf) x)) loc s
  μ-box-cell bx (valid-μ-wf ub wf′ x lv) = ⊥-elim (box-not-unboxed bx ub)
  μ-box-cell {wf = wf} bx (valid-μbox-wf bx′ wf′ x c) rewrite WellFormedFI-irrelevant wf wf′ = fo→cell c

  valid-μbox : ∀ {m alloc F loc s} (bx : mu-rep F ≡ mu-box) (wf : WellFormedFI F) (x : ⟦ μ-type F ⟧)
             → CellAt alloc (⟦ F ⟧TI (μ-type F)) (valueNow (evalᴰ (out-μ wf) x)) loc s
             → ValidAtWF m alloc {μ-type F} x loc s
  valid-μbox bx wf x c = valid-μbox-wf bx wf x (cell→fo (fo-layer wf fo-μ) c)


  -- The case datas are functorial in their components' validities.
  cell-map : ∀ {C} {V W : VTy C} → (∀ {m a c l s} → V m a c l s → W m a c l s)
           → ∀ {alloc c cl s} → CellAtP {C} V alloc c cl s → CellAtP {C} W alloc c cl s
  cell-map f (cell-ptr r bf v) = cell-ptr r bf (f v)
  cell-map f (cell-inline rep r) = cell-inline rep r

  pair-map : ∀ {A B} {VA WA : VTy A} {VB WB : VTy B}
           → (∀ {m a c l s} → VA m a c l s → WA m a c l s)
           → (∀ {m a c l s} → VB m a c l s → WB m a c l s)
           → ∀ {m alloc v loc s} → PairV {A} {B} VA VB m alloc v loc s → PairV {A} {B} WA WB m alloc v loc s
  pair-map f g (pair-wf lmm slb c₁ c₂) = pair-wf lmm slb (cell-map f c₁) (cell-map g c₂)

  sum-map : ∀ {A B} {VA WA : VTy A} {VB WB : VTy B}
          → (∀ {m a c l s} → VA m a c l s → WA m a c l s)
          → (∀ {m a c l s} → VB m a c l s → WB m a c l s)
          → ∀ {m alloc v loc s} → SumV {A} {B} VA VB m alloc v loc s → SumV {A} {B} WA WB m alloc v loc s
  sum-map f g (inl-wf lmm tg pp pb slb pv) = inl-wf lmm tg pp pb slb (f pv)
  sum-map f g (inr-wf lmm tg pp pb slb pv) = inr-wf lmm tg pp pb slb (g pv)
  sum-map f g (inl-reg-wf lmm tg rep pp slb) = inl-reg-wf lmm tg rep pp slb
  sum-map f g (inr-reg-wf lmm tg rep pp slb) = inr-reg-wf lmm tg rep pp slb

  -- A forced layer IS a valid value of the layer type, and back where the
  -- functor is well formed (the constant positions are first-order).
  layer→valid : ∀ (G : IRFunctor) {X} {R : VTy X}
              → (∀ {m a v l s} → R m a v l s → ValidAtWF m a {X} v l s)
              → ∀ {m a v l s} → LayerV G R m a v l s → ValidAtWF m a {⟦ G ⟧TI X} v l s
  layer→valid (K A)   f lv = fo→valid lv
  layer→valid Id      f lv = f lv
  layer→valid (G ⊕ H) f lv = wrap (sum-map (layer→valid G f) (layer→valid H f) lv)
  layer→valid (G ⊗ H) f lv = wrap (pair-map (layer→valid G f) (layer→valid H f) lv)

  valid→layer : ∀ {G : IRFunctor} → WellFormedFI G → ∀ {X} {R : VTy X}
              → (∀ {m a v l s} → ValidAtWF m a {X} v l s → R m a v l s)
              → ∀ {m a v l s} → ValidAtWF m a {⟦ G ⟧TI X} v l s → LayerV G R m a v l s
  valid→layer (wf-K ib)     f lv = valid→fo (fo-base ib) lv
  valid→layer wf-Id         f lv = f lv
  valid→layer (wf-Sum g h)  f (wrap lv) = sum-map (valid→layer g f) (valid→layer h f) lv
  valid→layer (wf-Prod g h) f (wrap lv) = pair-map (valid→layer g f) (valid→layer h f) lv

  -- …so a forced ν layer is a valid result.
  rp-map : ∀ {B} {V W : VTy B} → (∀ {m a v l s} → V m a v l s → W m a v l s)
         → ∀ {m a₁ a₂ v s} → ResultPlaceP {B} V m a₁ a₂ v s → ResultPlaceP {B} W m a₁ a₂ v s
  rp-map f (rp-unit e) = rp-unit e
  rp-map f (rp-loc loc v bf rax cv cbf) = rp-loc loc (f v) bf rax (f cv) cbf
  rp-map f (rp-reg fit rax) = rp-reg fit rax


  --------------------------------------------------------------------
  -- valid-primitive-wf: Dispatch on FitsInReg evidence
  --
  -- For register-fittable primitive types, ValidAtWF only needs
  -- BeforeFrontier. Plan 0.2.4.5: legacy IsPrimitive retired —
  -- Unit is erased (no slot), Str/Buffer are 2-slot compounds with
  -- their own valid-str-wf / valid-buffer-wf witnesses. The only
  -- inhabitants left are Int and Float.
  --------------------------------------------------------------------

  valid-primitive-wf : ∀ {m} {B : IRTy} {v : ⟦ B ⟧}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS} →
    (fit : FitsInRegI B) →
    Live alloc loc →
    readLoc s loc ≡ just (prim-sv fit v) →
    ValidAtWF m alloc {B} v loc s
  valid-primitive-wf fits-int   bf rl = valid-int-wf bf rl
  valid-primitive-wf fits-float bf rl = valid-float-wf bf rl

  --------------------------------------------------------------------
  -- IRResultAWF: Mode-indexed IR execution result
  --
  -- Indexed by output mode m. For allocating IRs:
  --   run-pair for ⟨ f , g ⟩ Stack → IRResultAWF Stack ...
  --   run-pair for ⟨ f , g ⟩ Heap  → IRResultAWF Heap ...
  --
  -- For non-allocating IRs (fst, snd, id, etc.), the mode comes
  -- from pattern matching on input validity.
  --------------------------------------------------------------------

  -- Plan 0.2.4.5 D1 (Unit erasure): result placement is type-aware.
  --
  -- For Unit-typed results, the value is genuinely "nowhere" — no
  -- register, no slot, no observable content. So the data that
  -- normally pins down "where the result is" (a ValueLocation +
  -- validity at it + before-frontier proof + Output equation) has
  -- nothing to talk about. Encoded structurally:
  --
  --   `unit-result` : Unit-typed result; carries no location.
  --   `at-loc loc valid-wf before output-eq` : non-Unit result;
  --     bundles all four facts about the location at once.
  --
  -- This subsumes the old separate fields (`result-loc`,
  -- `result-valid-wf`, `result-before`, `rax-is-result`) into a
  -- single `result-place` field, and removes the redundancy where
  -- `rax-is-result` was bridging `result-loc` to `Output`.
  -- Consumers (compose, pair, RecTrace) pattern-match on the
  -- constructor; the type system forces them to handle Unit
  -- separately — there's no loc to extract from `unit-result`.
  -- The continuation-alloc shape: caller's frame, with `next-slot`
  -- and `next-heap-ref` taken from the IR's `final-alloc` — i.e., the
  -- alloc state the caller resumes with after the callee returns.
  -- Carrying it in the type lets a single `at-loc` constructor share
  -- its `loc` between post-IR and continuation invariants — consumers
  -- don't need a separate "loc-eq" lemma to bridge two parallel
  -- ResultPlaces.
  --
  -- Previously named `reclaim-alloc`; that baked in a stack-only
  -- mental model. The field never represented heap reclamation
  -- (heap blocks aren't freed by IRs), only the caller's
  -- continuation view of consumed resources.
  data ResultPlace : (B : IRTy) (m : AllocMode)
                     (alloc continuation-alloc : AllocState {FS})
                     (v : ⟦ B ⟧) (s : LocState FS) → Set where
    unit-result : ∀ {m alloc continuation-alloc s} →
                  ResultPlace Unit m alloc continuation-alloc tt s
    at-loc      : ∀ {B m alloc continuation-alloc v s}
                  (loc : ValueLocation FS)
                → ValidAtWF m alloc {B} v loc s
                → Live alloc loc
                -- Plan 0.13.2: Output register stores StoredValue;
                -- a result location is reified as SV-Ptr loc.
                → readReg (regs s) Output ≡ SV-Ptr loc
                → ValidAtWF m continuation-alloc {B} v loc s
                → Live continuation-alloc loc
                → ResultPlace B m alloc continuation-alloc v s
    -- Force-it: register-resident primitive result. The value `v` lives in
    -- Output as a register literal (abstract sentinel `unit-storedvalue`;
    -- the real bits are the per-arch Simulation's job), NOT as a pointer.
    -- Validity is location-only (`valid-primitive-wf`), so a witness `loc`
    -- carries `ValidAtWF`/`BeforeFrontier`, while the rax field HONESTLY
    -- records `Output ≡ unit-storedvalue` — provable, unlike the refutable
    -- `SV-Ptr` claim `at-loc` would force on a sentinel.
    -- Plan 0.54 rung A (A2.5): register-resident primitive result. The value `v`
    -- lives in `Output` as its REAL literal `prim-sv fit v` (was the sentinel
    -- `unit-storedvalue` — the register half of killing the sentinel). This is the
    -- fast-path residence; spilled primitives use `at-loc` instead.
    -- NOTE (rung A): `at-reg` carries NO `ValidAtWF`. Since `valid-int/float-wf`
    -- now force a stored value (`readLoc … ≡ just (prim-sv fit v)`), a memory
    -- witness would demand a cell that a register-resident result does not have
    -- (`ir-to-trace (SigOp si) = instr-sigop si ∷ []` stores nothing). The value
    -- witness for this residence IS the register equation below. Shape dictated
    -- by the consumer `comp-step`, which reads only the register equation.
    -- Stage F: the `loc` field and its two `BeforeFrontier` witnesses are
    -- GONE. A register-resident result has no cell, so the location was
    -- always a placeholder — every producer passed its own `input-loc`,
    -- which does not hold the value — and the frontier bounds were bounds on
    -- that placeholder. Carrying them invited consumers to project a
    -- location out of a place that has none, which is what `place-loc` did
    -- and why it was deleted.
    --
    -- What remains is the whole content of this residence: the value fits a
    -- register, and `Output` holds it.
    at-reg      : ∀ {B m alloc continuation-alloc v s}
                  (fit : FitsInRegI B)
                → readReg (regs s) Output ≡ prim-sv fit v
                → ResultPlace B m alloc continuation-alloc v s

  -- (The place-* extraction helpers are gone. `place-sv`/`place-rax` were the
  -- last two: dead since the clause proofs read a place by matching on it,
  -- and `place-rax` at `unit-result` rested on a postulate quantified over
  -- every state (`readReg (regs s) Output ≡ SV-Ptr unit-result-sv-loc`),
  -- which no machine invariant makes true. Deleted with their two postulates
  -- (plan 0.135 merge review). Every earlier accessor (`place-valid`,
  -- `place-loc`, …) went the same way: a `Place` is not always a location.)

  -- plan 0.135 S1: a closure's `runs` states its result at `ResultPlaceP`
  -- (the arrow case is a parameterised data); a caller's obligations are at
  -- `ResultPlace`. Same constructors, same fields.
  rp→place : ∀ {B m a₁ a₂ v s} → ResultPlaceP {B} (VAt B) m a₁ a₂ v s → ResultPlace B m a₁ a₂ v s
  rp→place (rp-unit refl)               = unit-result
  rp→place (rp-loc loc v bf rax cv cbf) = at-loc loc v bf rax cv cbf
  rp→place (rp-reg fit rax)             = at-reg fit rax

  ν-layer-place : ∀ {F m a₁ a₂ v s}
                → ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} (λ m′ a′ v′ l′ s′ → NuV {F} m′ a′ v′ l′ s′)) m a₁ a₂ v s
                → ResultPlace (⟦ F ⟧TI (ν-type F)) m a₁ a₂ v s
  ν-layer-place {F} rp = rp→place (rp-map (layer→valid F valid-ν-wf) rp)


------------------------------------------------------------------------
-- Decomposition for ValidAtWF closures
------------------------------------------------------------------------

------------------------------------------------------------------------
-- D181: WHERE a closure's ENVIRONMENT lives, read out of the closure's
-- first cell. The exact shape `PayloadAt` has for a sum's payload, asked one
-- cell earlier — and for the same reason: the emitter writes whatever
-- `Input1` held, so the cell may hold a pointer OR the value itself.
  ------------------------------------------------------------------------
  -- plan 0.135 S1: the env's validity is gone from the closure (its type is
  -- hidden, so it is not a subterm of `A ⇛ B`); only where the env cell
  -- points is left. What the body does with it is `runs`.
  data EnvAt (alloc : AllocState {FS}) {E : IRTy} (env : ⟦ E ⟧)
             (closure-loc : ValueLocation FS) (s : LocState FS) : Set where
    env-at-loc  : (env-loc : ValueLocation FS)
                → readLoc s closure-loc ≡ just (SV-Ptr env-loc)
                → BeforeFrontier alloc env-loc
                → EnvAt alloc env closure-loc s
    env-in-cell : (rep : InlineRep E)
                → readLoc s closure-loc ≡ just (inline-sv rep env)
                → EnvAt alloc env closure-loc s

  record ClosureValidWF (alloc : AllocState {FS}) {A B : IRTy}
                        (f : ⟦ A ⇛ B ⟧)
                        (closure-loc : ValueLocation FS)
                        (s : LocState FS) : Set where
    field
      EnvType : IRTy
      env : ⟦ EnvType ⟧
      body-label : LabelId
      loc-mode : LocMatchesMode Heap closure-loc
      env-at : EnvAt alloc {EnvType} env closure-loc s
      code-ptr : readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label)
      sucLoc-before : BeforeFrontier alloc (sucLoc closure-loc)
      -- plan 0.135 S1: the label resolves, and the block computes `f`.
      code-j : ℕ
      code-found : find-thunk prog body-label ≡ just code-j
      runs : CallRuns {A} {B} (VAt A) (VAt B) alloc s closure-loc code-j f

  decomposeClosureWF : ∀ {m alloc A B} {f : ⟦ A ⇛ B ⟧} {loc s} →
    ValidAtWF m alloc {A ⇛ B} f loc s → ClosureValidWF alloc {A} {B} f loc s
  decomposeClosureWF (valid-closure-wf {env-loc = el} lmm ep cp eb slb fd rn) = record
    { EnvType = Unit ; env = tt ; body-label = _ ; loc-mode = lmm
    ; env-at = env-at-loc el ep (live→bf eb) ; code-ptr = cp ; sucLoc-before = live→bf slb
    ; code-j = _ ; code-found = fd ; runs = rn }
  decomposeClosureWF (valid-closure-reg-wf {env = env} lmm rep ep cp slb fd rn) = record
    { EnvType = _ ; env = env ; body-label = _ ; loc-mode = lmm
    ; env-at = env-in-cell rep ep ; code-ptr = cp ; sucLoc-before = live→bf slb
    ; code-j = _ ; code-found = fd ; runs = rn }

  data Place : Set where
    AtStorage : ValueLocation FS → Place
    InReg     : AbstractReg → Place

  ------------------------------------------------------------------------
  -- Stage F (plan 0.2.4.5): `InputPlace`, the INPUT-side mirror of
  -- `ResultPlace`.
  --
  -- `ir-to-trace (f ∘ g) = ft ++ mov-to-input ∷ gt` does NOT spill, so after a
  -- primitive-returning `f` the intermediate reaches `g` in `Input1` AS A
  -- VALUE. The flat machine already models this (`IRObsCorrectFlat.InputAt`'s
  -- `in-reg`, and `pure-sigop-out-aux`'s register-resident branch, whose
  -- comment records that it was "forced top-down by `comp-step`").
  --
  -- The structured dispatcher could not. Its precondition was
  -- `loc + ValidAtWF + BeforeFrontier + readReg Input1 ≡ SV-Ptr loc`, which
  -- expresses ONLY memory residence — and that is exactly why
  -- `ComposeWF.FFacts` had no case for an `at-reg` intermediate.
  --
  -- Shaped like `ResultPlace`: `in-at-loc` carries the memory witnesses;
  -- `in-at-reg` carries the register equation and NO `ValidAtWF`, because
  -- there is no cell for it to be valid at. That is the same reason plan 0.54
  -- rung A deleted `place-valid` rather than making it total.
  ------------------------------------------------------------------------
  data InputPlace {A : IRTy} (m : AllocMode) (alloc : AllocState {FS})
                  (v : ⟦ A ⟧) (s : LocState FS) : Set where
    in-at-loc : (loc : ValueLocation FS)
              → ValidAtWF m alloc {A} v loc s
              → BeforeFrontier alloc loc
              → readReg (regs s) Input1 ≡ SV-Ptr loc
              → InputPlace m alloc v s
    in-at-reg : (fit : FitsInRegI A)
              → readReg (regs s) Input1 ≡ prim-sv fit v
              → InputPlace m alloc v s
    -- D074, mirrored from `InputAt`: a UNIT input has NO residence. `Input1`
    -- may hold anything (the entry state's tag filler; after `f : IR A Unit`
    -- in a composition, `f`'s unit output is likewise unconstrained). The
    -- machine never reads it — `readTyped Unit` and `readReg-typed Unit` both
    -- materialise `tt` regardless. Carrying a location here is what forced
    -- consumers to assume one.
    in-unit : A ≡ Unit → InputPlace m alloc v s

  -- What `Input1` HOLDS, and the proof that it holds it — the input-side twin
  -- of `payload-sv`/`payload-read`. A pointer for a located input, the value
  -- itself for a register-resident one, and for a unit input whatever happens
  -- to be there: `in-unit` constrains nothing, but the register still has
  -- SOME contents, and naming them is what keeps this accessor TOTAL.
  --
  -- Totality is the point. Any consumer that only MOVES the input (which is
  -- all `run-inl`/`run-inr` do — `mov-to-output` then `store-at-slot`) can
  -- use these and never case-split on the residence.
  input-sv : ∀ {A m alloc} {v : ⟦ A ⟧} {s} → InputPlace {A} m alloc v s → StoredValue FS
  input-sv (in-at-loc loc _ _ _)  = SV-Ptr loc
  input-sv {v = v} (in-at-reg fit _) = prim-sv fit v
  input-sv {s = s} (in-unit _)    = readReg (regs s) Input1

  input-read : ∀ {A m alloc} {v : ⟦ A ⟧} {s} (ip : InputPlace {A} m alloc v s)
             → readReg (regs s) Input1 ≡ input-sv ip
  input-read (in-at-loc _ _ _ eq) = eq
  input-read (in-at-reg _ eq)     = eq
  input-read (in-unit _)          = refl


  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF pairs (any mode)
  --
  -- D187: TWO CELLS, each carrying its own residence. The five fields that
  -- described a POINTER pair (`fst-loc`/`snd-loc`/`mA`/`mB`/`fst-ptr`/…) are
  -- gone with the constructor's; what a consumer gets is what the cell holds,
  -- and it splits on that only if it cares.
  ------------------------------------------------------------------------

  record PairValidWF (alloc : AllocState {FS}) {A B : IRTy}
                     (p : ⟦ A * B ⟧)
                     (pair-loc : ValueLocation FS)
                     (s : LocState FS) : Set where
    field
      sucLoc-before : BeforeFrontier alloc (sucLoc pair-loc)
      fst-cell : CellAt alloc A (proj₁ p) pair-loc s
      snd-cell : CellAt alloc B (proj₂ p) (sucLoc pair-loc) s

  decomposePairWF : ∀ {m alloc A B} {p : ⟦ A * B ⟧} {loc s} →
    ValidAtWF m alloc {A * B} p loc s → PairValidWF alloc {A} {B} p loc s
  decomposePairWF (valid-pair-wf lmm slb fc sc) = record
    { sucLoc-before = live→bf slb
    ; fst-cell = fc
    ; snd-cell = sc
    }

  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF sum types (inl/inr) - any mode
  --
  -- Reference-based model: tag + payload-ptr (identical for all modes)
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Stage F: WHERE an inl/inr payload lives, read out of the sum's second
  -- cell. Shaped from its consumer (`run-case`), which needs exactly enough to
  -- build an `InputPlace` for the branch it dispatches to, and nothing more.
  ------------------------------------------------------------------------
  data PayloadAt (alloc : AllocState {FS}) {A : IRTy} (a : ⟦ A ⟧)
                 (sum-loc : ValueLocation FS) (s : LocState FS) : Set where
    payload-at-loc : ∀ {mA : AllocMode} (payload-loc : ValueLocation FS)
                   → readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc)
                   → BeforeFrontier alloc payload-loc
                   → ValidAtWF mA alloc {A} a payload-loc s
                   → PayloadAt alloc a sum-loc s
    payload-in-reg : (rep : InlineRep A)
                   → readLoc s (sucLoc sum-loc) ≡ just (inline-sv rep a)
                   → PayloadAt alloc a sum-loc s

  -- The uniform accessors: what the payload CELL holds, and the proof that it holds it. A
  -- pointer for a located payload, the value itself for an inline one. Every
  -- consumer that only needs to move the cell's contents (which is all
  -- `run-case` does — `load-indirect-suc` then `mov-to-input`) can use these
  -- and never case-split.
  payload-sv : ∀ {alloc A} {a : ⟦ A ⟧} {sum-loc s}
             → PayloadAt alloc {A} a sum-loc s → StoredValue FS
  payload-sv (payload-at-loc pl _ _ _)      = SV-Ptr pl
  payload-sv {a = a} (payload-in-reg rep _) = inline-sv rep a

  payload-read : ∀ {alloc A} {a : ⟦ A ⟧} {sum-loc s} (pd : PayloadAt alloc {A} a sum-loc s)
               → readLoc s (sucLoc sum-loc) ≡ just (payload-sv pd)
  payload-read (payload-at-loc _ pp _ _) = pp
  payload-read (payload-in-reg _ pp)     = pp

  record InlValidWF (alloc : AllocState {FS}) {A B : IRTy}
                    (v : ⟦ A + B ⟧)
                    (sum-loc : ValueLocation FS)
                    (s : LocState FS) : Set where
    field
      a : ⟦ A ⟧
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload : PayloadAt alloc {A} a sum-loc s
      v-is-inl : v ≡ inj₁ a

  record InrValidWF (alloc : AllocState {FS}) {A B : IRTy}
                    (v : ⟦ A + B ⟧)
                    (sum-loc : ValueLocation FS)
                    (s : LocState FS) : Set where
    field
      b : ⟦ B ⟧
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload : PayloadAt alloc {B} b sum-loc s
      v-is-inr : v ≡ inj₂ b

  decomposeInlWF : ∀ {m alloc A B} {a : ⟦ A ⟧} {loc s} →
    ValidAtWF m alloc {A + B} (inj₁ a) loc s → InlValidWF alloc {A} {B} (inj₁ a) loc s
  decomposeInlWF (valid-inl-wf {a = a} {payload-loc = pl} {mA = mA} lmm _ pp pb slb pv) = record
    { a = a ; sucLoc-before = live→bf slb
    ; payload = payload-at-loc {mA = mA} pl pp (live→bf pb) pv ; v-is-inl = refl }
  decomposeInlWF (valid-inl-reg-wf {a = a} lmm _ fit pp slb) = record
    { a = a ; sucLoc-before = live→bf slb
    ; payload = payload-in-reg fit pp ; v-is-inl = refl }

  decomposeInrWF : ∀ {m alloc A B} {b : ⟦ B ⟧} {loc s} →
    ValidAtWF m alloc {A + B} (inj₂ b) loc s → InrValidWF alloc {A} {B} (inj₂ b) loc s
  decomposeInrWF (valid-inr-wf {b = b} {payload-loc = pl} {mB = mB} lmm _ pp pb slb pv) = record
    { b = b ; sucLoc-before = live→bf slb
    ; payload = payload-at-loc {mA = mB} pl pp (live→bf pb) pv ; v-is-inr = refl }
  decomposeInrWF (valid-inr-reg-wf {b = b} lmm _ fit pp slb) = record
    { b = b ; sucLoc-before = live→bf slb
    ; payload = payload-in-reg fit pp ; v-is-inr = refl }

  ------------------------------------------------------------------------
  -- OCP-0003: FoldValidWF record and decomposeFoldWF removed.
  -- Use μ-type/ν-type validity instead.

  ------------------------------------------------------------------------
  -- Lift ValidAt to ValidAtWF for non-closure types
  --
  -- For Unit and pairs of non-closures, we can convert ValidAt to ValidAtWF.
  -- This is used when we don't have body-correct info but need ValidAtWF.
  ------------------------------------------------------------------------

  valid-to-validWF-unit : ∀ {m alloc loc s} →
    ValidAtWF m alloc {Unit} tt loc s
  valid-to-validWF-unit = valid-unit-wf

  ------------------------------------------------------------------------
  -- plan 0.135 S1: ONE TRANSPORT. Every `validityWF-*` below is an instance.
  --
  -- A witness reads only cells it can name: the top cell (`Q loc`) and cells
  -- before the frontier. So it moves to any state that agrees on a set `Q`
  -- covering both, and to any allocator whose frontier includes the old one.
  -- Proved once by recursion on the type (`v-tr`) and once on the first-order
  -- witness (`fo-tr`, μ). The arrow case retargets its callee premises:
  -- what was live and unchanged for the old state is so for the new one.
  ------------------------------------------------------------------------
  module Transport {a₁ a₂ : AllocState {FS}} {s₁ s₂ : LocState FS}
           (Q : ValueLocation FS → Set)
           (q-bf : ∀ l → Live a₁ l → Q l)
           (rd : ∀ l → Q l → readLoc s₂ l ≡ readLoc s₁ l)
           (bft : ∀ l → Live a₁ l → Live a₂ l) where

    mutual
      fo-tr : ∀ {m A v loc} → Q loc → ValidFO m a₁ {A} v loc s₁ → ValidFO m a₂ {A} v loc s₂
      fo-tr q (fo-unit unit-wf) = fo-unit unit-wf
      fo-tr q (fo-pair (pair-wf lmm slb c₁ c₂)) =
        fo-pair (pair-wf lmm (bft _ slb) (fo-cell q c₁) (fo-cell (q-bf _ slb) c₂))
      fo-tr q (fo-sum (inl-wf lmm tg pp pb slb pv)) =
        fo-sum (inl-wf lmm (transport-SumTag (rd _ q) tg) (trans (rd _ (q-bf _ slb)) pp)
                             (bft _ pb) (bft _ slb) (fo-tr (q-bf _ pb) pv))
      fo-tr q (fo-sum (inr-wf lmm tg pp pb slb pv)) =
        fo-sum (inr-wf lmm (transport-SumTag (rd _ q) tg) (trans (rd _ (q-bf _ slb)) pp)
                             (bft _ pb) (bft _ slb) (fo-tr (q-bf _ pb) pv))
      fo-tr q (fo-sum (inl-reg-wf lmm tg rep pp slb)) =
        fo-sum (inl-reg-wf lmm (transport-SumTag (rd _ q) tg) rep (trans (rd _ (q-bf _ slb)) pp) (bft _ slb))
      fo-tr q (fo-sum (inr-reg-wf lmm tg rep pp slb)) =
        fo-sum (inr-reg-wf lmm (transport-SumTag (rd _ q) tg) rep (trans (rd _ (q-bf _ slb)) pp) (bft _ slb))
      fo-tr q (fo-int (int-wf bf rl)) = fo-int (int-wf (bft _ bf) (trans (rd _ q) rl))
      fo-tr q (fo-float (float-wf bf rl)) = fo-float (float-wf (bft _ bf) (trans (rd _ q) rl))
      fo-tr q (fo-μwf ub wf x lv) = fo-μwf ub wf x (fo-tr q lv)
      fo-tr q (fo-μbox bx wf x c) = fo-μbox bx wf x (fo-cell q c)

      fo-cell : ∀ {C c cl} → Q cl → CellAtP {C} (λ m′ a′ → ValidFO m′ a′ {C}) a₁ c cl s₁
              → CellAtP {C} (λ m′ a′ → ValidFO m′ a′ {C}) a₂ c cl s₂
      fo-cell q (cell-ptr r bf v) = cell-ptr (trans (rd _ q) r) (bft _ bf) (fo-tr (q-bf _ bf) v)
      fo-cell q (cell-inline rep r) = cell-inline rep (trans (rd _ q) r)

    runs-tr : ∀ {A B} {VA : VTy A} {VB : VTy B} {cloc j f} → Q cloc
            → CallRuns {A} {B} VA VB a₁ s₁ cloc j f → CallRuns {A} {B} VA VB a₂ s₂ cloc j f
    runs-tr q r fs pre a pl ret-pc k rs pc nh fr fa ns incl agree i1 lmm slb c0 c1 =
      r fs pre a pl ret-pc k rs pc nh fr fa ns
        (λ l b → incl l (bft l b))
        (λ l b → trans (agree l (bft l b)) (rd l (q-bf l b)))
        i1 lmm slb (trans c0 (rd _ q)) c1

    -- A ν, like a closure, only retargets its force's premises; the forced
    -- layer is the same run, so nothing is corecursive here.
    nu-tr : ∀ {F m v loc} → Q loc → NuV {F} m a₁ v loc s₁ → NuV {F} m a₂ v loc s₂
    nu-mode  (nu-tr q n) = nu-mode n
    nu-heap  (nu-tr q n) = nu-heap n
    nu-seed  (nu-tr q n) = nu-seed n
    nu-lbl   (nu-tr q n) = nu-lbl n
    nu-j     (nu-tr q n) = nu-j n
    nu-cell0 (nu-tr q n) = trans (rd _ q) (nu-cell0 n)
    nu-cell1 (nu-tr q n) = trans (rd _ (q-bf _ (nu-live1 n))) (nu-cell1 n)
    nu-live1 (nu-tr q n) = bft _ (nu-live1 n)
    nu-code  (nu-tr q n) = nu-code n
    nu-force (nu-tr q n) wf fs pre ret-pc k rs pc nh fr fa ns incl agree i1 =
      nu-force n wf fs pre ret-pc k rs pc nh fr fa ns
        (λ l b → incl l (bft l b))
        (λ l b → trans (agree l (bft l b)) (rd l (q-bf l b)))
        i1

    mutual
      v-tr : ∀ {m} A {v loc} → Q loc → ValidAtWF m a₁ {A} v loc s₁ → ValidAtWF m a₂ {A} v loc s₂
      v-tr Unit q valid-unit-wf = valid-unit-wf
      v-tr Void q (wrap ())
      v-tr (A * B) q (valid-pair-wf lmm slb c₁ c₂) =
        valid-pair-wf lmm (bft _ slb) (v-cell A q c₁) (v-cell B (q-bf _ slb) c₂)
      v-tr (A + B) q (valid-inl-wf lmm tg pp pb slb pv) =
        valid-inl-wf lmm (transport-SumTag (rd _ q) tg) (trans (rd _ (q-bf _ slb)) pp)
                     (bft _ pb) (bft _ slb) (v-tr A (q-bf _ pb) pv)
      v-tr (A + B) q (valid-inr-wf lmm tg pp pb slb pv) =
        valid-inr-wf lmm (transport-SumTag (rd _ q) tg) (trans (rd _ (q-bf _ slb)) pp)
                     (bft _ pb) (bft _ slb) (v-tr B (q-bf _ pb) pv)
      v-tr (A + B) q (valid-inl-reg-wf lmm tg rep pp slb) =
        valid-inl-reg-wf lmm (transport-SumTag (rd _ q) tg) rep (trans (rd _ (q-bf _ slb)) pp) (bft _ slb)
      v-tr (A + B) q (valid-inr-reg-wf lmm tg rep pp slb) =
        valid-inr-reg-wf lmm (transport-SumTag (rd _ q) tg) rep (trans (rd _ (q-bf _ slb)) pp) (bft _ slb)
      v-tr (A ⇛ B) q (valid-closure-wf lmm ep cp eb slb fd runs) =
        valid-closure-wf lmm (trans (rd _ q) ep) (trans (rd _ (q-bf _ slb)) cp) (bft _ eb) (bft _ slb)
                         fd (runs-tr q runs)
      v-tr (A ⇛ B) q (valid-closure-reg-wf {env = env} lmm rep ep cp slb fd runs) =
        valid-closure-reg-wf {env = env} lmm rep (trans (rd _ q) ep) (trans (rd _ (q-bf _ slb)) cp) (bft _ slb)
                             fd (runs-tr q runs)
      v-tr (μ-type F) q (wrap w) = wrap (fo-tr q w)
      v-tr (ν-type F) q (valid-ν-wf n) = valid-ν-wf (nu-tr q n)
      v-tr Int q (valid-int-wf bf rl) = valid-int-wf (bft _ bf) (trans (rd _ q) rl)
      v-tr Float q (valid-float-wf bf rl) = valid-float-wf (bft _ bf) (trans (rd _ q) rl)

      v-cell : ∀ C {c cl} → Q cl → CellAt a₁ C c cl s₁ → CellAt a₂ C c cl s₂
      v-cell C q (cell-ptr r bf v) = cell-ptr (trans (rd _ q) r) (bft _ bf) (v-tr C (q-bf _ bf) v)
      v-cell C q (cell-inline rep r) = cell-inline rep (trans (rd _ q) r)

  -- The general transport, by its three facts.
  validityWF-transport : ∀ {m A} {a₁ a₂ : AllocState {FS}} {s₁ s₂ : LocState FS}
    (Q : ValueLocation FS → Set) →
    (∀ l → BeforeFrontier a₁ l → Q l) →
    (∀ l → Q l → readLoc s₂ l ≡ readLoc s₁ l) →
    (∀ l → BeforeFrontier a₁ l → BeforeFrontier a₂ l) →
    ∀ (v : ⟦ A ⟧) loc → Q loc →
    ValidAtWF m a₁ {A} v loc s₁ → ValidAtWF m a₂ {A} v loc s₂
  validityWF-transport {A = A} Q q-bf rd bft _ _ q =
    Transport.v-tr Q (λ l b → q-bf l (live→bf b)) rd (λ l b → bf→live (live-heap b) (bft l (live→bf b))) A q

  -- plan 0.135 S2: …and since a value's cells are heap cells, only the HEAP
  -- frontier and heap memory matter. This is what crosses a call and a return.
  validityWF-heap-transport : ∀ {m A} {a₁ a₂ : AllocState {FS}} {s₁ s₂ : LocState FS}
    (Q : ValueLocation FS → Set) →
    (∀ l → Live a₁ l → Q l) →
    (∀ l → Q l → readLoc s₂ l ≡ readLoc s₁ l) →
    (∀ l → Live a₁ l → Live a₂ l) →
    ∀ (v : ⟦ A ⟧) loc → Q loc →
    ValidAtWF m a₁ {A} v loc s₁ → ValidAtWF m a₂ {A} v loc s₂
  validityWF-heap-transport {A = A} Q q-bf rd bft _ _ q = Transport.v-tr Q q-bf rd bft A q

  cellWF-heap-transport : ∀ {C} {a₁ a₂ : AllocState {FS}} {s₁ s₂ : LocState FS}
    (Q : ValueLocation FS → Set) →
    (∀ l → Live a₁ l → Q l) →
    (∀ l → Q l → readLoc s₂ l ≡ readLoc s₁ l) →
    (∀ l → Live a₁ l → Live a₂ l) →
    ∀ (c : ⟦ C ⟧) cl → Q cl →
    CellAt a₁ C c cl s₁ → CellAt a₂ C c cl s₂
  cellWF-heap-transport {C} Q q-bf rd bft _ _ q = Transport.v-cell Q q-bf rd bft C q

  private
    all : ValueLocation FS → Set
    all _ = ⊤
    same-alloc : ∀ {a : AllocState {FS}} l → BeforeFrontier a l → BeforeFrontier a l
    same-alloc _ b = b

  -- ValidAtWF only depends on memory, not registers.
  validityWF-mem-only : ∀ {m alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    stackMem s₂ ≡ stackMem s₁ →
    heapMem s₂ ≡ heapMem s₁ →
    ValidAtWF m alloc {A} v loc s₁ → ValidAtWF m alloc {A} v loc s₂
  validityWF-mem-only v loc s₁ s₂ se he =
    validityWF-transport all (λ _ _ → tt) (λ l _ → readLoc-stack-heap-eq s₂ s₁ l se he) same-alloc v loc tt

  validityWF-write-at-frontier : ∀ {m alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAtWF m alloc {A} v loc s →
    ValidAtWF m alloc {A} v loc (write-loc s (AtStack (current-frame alloc) (next-slot alloc)) val)
  validityWF-write-at-frontier {alloc = alloc} v loc s val lb =
    validityWF-transport (BeforeFrontier alloc) (λ _ b → b)
      (λ l b → write-at-frontier-preserves-before s alloc l val b) same-alloc v loc lb

  validityWF-write-at-suc-frontier : ∀ {m alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAtWF m alloc {A} v loc s →
    ValidAtWF m alloc {A} v loc (write-loc s (AtStack (current-frame alloc) (suc (next-slot alloc))) val)
  validityWF-write-at-suc-frontier {alloc = alloc} v loc s val lb =
    validityWF-transport (BeforeFrontier alloc) (λ _ b → b)
      (λ l b → write-at-suc-frontier-preserves-before s alloc l val b) same-alloc v loc lb

  validityWF-write-sv-at-frontier : ∀ {m alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (stored : StoredValue FS) →
    BeforeFrontier alloc loc →
    ValidAtWF m alloc {A} v loc s →
    ValidAtWF m alloc {A} v loc (writeLoc s (AtStack (current-frame alloc) (next-slot alloc)) stored)
  validityWF-write-sv-at-frontier {alloc = alloc} v loc s stored lb =
    validityWF-transport (BeforeFrontier alloc) (λ _ b → b)
      (λ l b → write-sv-at-frontier-preserves-before s alloc l stored b) same-alloc v loc lb

  validityWF-write-sv-at-suc-frontier : ∀ {m alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (stored : StoredValue FS) →
    BeforeFrontier alloc loc →
    ValidAtWF m alloc {A} v loc s →
    ValidAtWF m alloc {A} v loc (writeLoc s (AtStack (current-frame alloc) (suc (next-slot alloc))) stored)
  validityWF-write-sv-at-suc-frontier {alloc = alloc} v loc s stored lb =
    validityWF-transport (BeforeFrontier alloc) (λ _ b → b)
      (λ l b → write-sv-at-suc-frontier-preserves-before s alloc l stored b) same-alloc v loc lb

  validityWF-with-bf-transfer : ∀ {m A} (v : ⟦ A ⟧) loc (s : LocState FS)
    (a₁ a₂ : AllocState {FS})
    (bf-transfer : ∀ loc' → BeforeFrontier a₁ loc' → BeforeFrontier a₂ loc') →
    ValidAtWF m a₁ {A} v loc s →
    ValidAtWF m a₂ {A} v loc s
  validityWF-with-bf-transfer v loc s a₁ a₂ bft =
    validityWF-transport all (λ _ _ → tt) (λ _ _ → refl) bft v loc tt

  validityWF-alloc-advance : ∀ {m alloc A} (v : ⟦ A ⟧) loc s (n : ℕ) →
    ValidAtWF m alloc {A} v loc s →
    let alloc' = record alloc { next-slot = next-slot alloc ℕ.+ n }
    in ValidAtWF m alloc' v loc s
  validityWF-alloc-advance {alloc = alloc} v loc s n =
    validityWF-with-bf-transfer v loc s _ _ (stack-alloc-advances alloc n)

  validityWF-frontier-advance : ∀ {m alloc alloc' A} (v : ⟦ A ⟧) loc (s : LocState FS) →
    current-frame alloc' ≡ current-frame alloc →
    next-slot alloc ≤ next-slot alloc' →
    next-heap-ref alloc ≤ next-heap-ref alloc' →
    ValidAtWF m alloc {A} v loc s →
    ValidAtWF m alloc' v loc s
  validityWF-frontier-advance {alloc = alloc} {alloc' = alloc'} v loc s cf-eq slot-≤ heap-≤ =
    validityWF-with-bf-transfer v loc s _ _ (frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤)

  validityWF-mem-preserved : ∀ {m alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    BeforeFrontier alloc loc →
    (∀ loc' → BeforeFrontier alloc loc' → readLoc s₂ loc' ≡ readLoc s₁ loc') →
    ValidAtWF m alloc {A} v loc s₁ →
    ValidAtWF m alloc {A} v loc s₂
  validityWF-mem-preserved {alloc = alloc} v loc s₁ s₂ lb mem-eq =
    validityWF-transport (BeforeFrontier alloc) (λ _ b → b) mem-eq same-alloc v loc lb


  inputPlace-transport : ∀ {A m alloc alloc'} {x : ⟦ A ⟧} {s s'}
    (ip : InputPlace {A} m alloc x s)
    → current-frame alloc' ≡ current-frame alloc
    → next-slot alloc ≤ next-slot alloc'
    → next-heap-ref alloc ≤ next-heap-ref alloc'
    → (∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc)
    → readReg (regs s') Input1 ≡ input-sv ip
    → InputPlace {A} m alloc' x s'
  inputPlace-transport {x = x} {s = s} {s' = s'}
      (in-at-loc loc valid before _) cf-eq slot-≤ heap-≤ mem-eq eq' =
    in-at-loc loc
      (validityWF-frontier-advance x loc s' cf-eq slot-≤ heap-≤
        (validityWF-mem-preserved x loc s s' before mem-eq valid))
      (frontier-monotone _ _ (sym cf-eq) slot-≤ heap-≤ loc before)
      eq'
  inputPlace-transport (in-at-reg fit _) _ _ _ _ eq' = in-at-reg fit eq'
  inputPlace-transport (in-unit u)       _ _ _ _ _   = in-unit u

  -- (D270: the memory-gap validity transfers — `validityWF-mem-preserved-
  -- excluding`/`-in-regions`/`-in-regions-strong`, `LocInRegions`/
  -- `LocsInRegions` and the `μ-validity-in-regions-stub` they rested on — were
  -- deleted unused. The stub moved validity between ARBITRARY states.)

  ------------------------------------------------------------------------
  -- Stack Reclamation
  --
  -- After an IR completes, only the result needs to persist. Intermediate
  -- allocations can be reclaimed by creating a new allocation state with
  -- next-slot = reclaimable-slot.
  --
  -- Key property: BeforeFrontier is preserved since reclaimable-slot ≥ next-slot
  -- (from reclaim-monotone).
  ------------------------------------------------------------------------

  -- Create reclaimed allocation state
  reclaim-alloc : (alloc : AllocState {FS}) (reclaim-slot : ℕ) →
    AllocState {FS}
  reclaim-alloc alloc rs = record alloc { next-slot = rs }

  -- BeforeFrontier is preserved after reclamation (frontier only advances)
  reclaim-preserves-frontier : ∀ (alloc : AllocState {FS}) reclaim-slot
    (monotone : next-slot alloc ≤ reclaim-slot)
    (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    BeforeFrontier (reclaim-alloc alloc reclaim-slot) loc
  reclaim-preserves-frontier alloc rs monotone loc bf =
    stack-alloc-advances' alloc rs monotone loc bf
    where
      -- Helper using existing stack-alloc-advances pattern
      stack-alloc-advances' : ∀ (alloc : AllocState {FS}) (rs : ℕ)
        (monotone : next-slot alloc ≤ rs)
        (loc : ValueLocation FS) →
        BeforeFrontier alloc loc →
        BeforeFrontier (record alloc { next-slot = rs }) loc
      stack-alloc-advances' alloc rs monotone (AtStack f k) (stack-before refl k<next) =
        stack-before refl (<-≤-trans k<next monotone)
        where open import Data.Nat.Properties using (<-≤-trans)
      stack-alloc-advances' alloc rs monotone (AtStack f k) (stack-ancestor cf≺f src) =
        stack-ancestor cf≺f src  -- Frame ordering and provenance unchanged (same current-frame)
      stack-alloc-advances' alloc rs monotone (AtDynamic hl) (heap-before r<next) =
        heap-before r<next

  -- ValidAtWF is preserved after reclamation
  validityWF-reclaim : ∀ {m alloc A} (v : ⟦ A ⟧) loc s reclaim-slot
    (monotone : next-slot alloc ≤ reclaim-slot)
    (loc-before : BeforeFrontier alloc loc) →
    ValidAtWF m alloc {A} v loc s →
    ValidAtWF m (reclaim-alloc alloc reclaim-slot) v loc s
  validityWF-reclaim {m} {alloc} v loc s rs mono loc-bf valid =
    validityWF-frontier-advance v loc s refl mono ≤-refl valid
    where
      open import Data.Nat.Properties using (≤-refl)

  ------------------------------------------------------------------------
  -- Trace-Based Validity Preservation
  --
  -- KEY LEMMA: If a trace writes only at slots ≥ n (TraceWritesAbove n),
  -- and all sub-locations of a valid value are at slots < n (captured by
  -- BeforeFrontier with appropriate next-slot), then validity is preserved.
  --
  -- This is the core insight for PairWF and similar proofs:
  --   - IR results have sub-locations at slots < reclaimable-slot
  --   - Subsequent traces write at slots ≥ reclaimable-slot
  --   - Therefore validity is preserved through those traces
  --
  -- The proof combines:
  --   1. derive-mem-preserved: memory at BeforeFrontier locations preserved
  --   2. validityWF-mem-preserved: validity transfers when memory preserved
  ------------------------------------------------------------------------

  -- Phase 2 Core: Derive memory preservation from trace write bounds
  --
  -- This is the UNIFIED derivation function that routes to the appropriate
  -- positive characterization lemma based on BeforeFrontier constructor:
  --   - stack-before: exec-trace-preserves-slot-below (slot < frontier)
  --   - stack-ancestor: exec-trace-preserves-ancestor (ancestor frame)
  --   - heap-before: exec-trace-preserves-heap-loc (heap location)
  --
  -- Usage: Instead of storing mem-preserved-before in IRResultAWF,
  -- callers can derive it using this function from trace-writes-above
  -- and trace-no-heap-writes.

  -- General variant: derive preservation for slots below an explicit boundary
  -- Useful for composition where the boundary may differ from next-slot alloc
  derive-mem-preserved-at : ∀ (alloc : AllocState {FS}) (start : ℕ)
    (trace : AbstractTrace) (s : LocState FS) →
    TraceWritesAbove start trace →
    TraceNoHeapWrites trace →
    (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    start ≥ next-slot alloc →  -- start is at or above frontier
    readLoc (proj₁ (exec-trace trace s alloc)) loc ≡ readLoc s loc
  derive-mem-preserved-at alloc start trace s twa tnhw (AtStack f k) (stack-before f≡cf k<next) start≥frontier =
    -- k < next-slot alloc ≤ start, so k < start and slot k is below write region
    subst (λ f' → readLoc (proj₁ (exec-trace trace s alloc)) (AtStack f' k) ≡
                  readLoc s (AtStack f' k))
          (sym f≡cf)
          (exec-trace-preserves-slot-below trace s alloc start k twa tnhw k<start)
    where
      open import Data.Nat.Properties using (<-≤-trans)
      k<start = <-≤-trans k<next start≥frontier
  derive-mem-preserved-at alloc start trace s twa tnhw (AtStack f k) (stack-ancestor cf≺f _) _ =
    -- f is an ancestor frame (current-frame alloc ≺ f)
    exec-trace-preserves-ancestor trace s alloc f k cf≺f tnhw
  derive-mem-preserved-at alloc start trace s twa tnhw (AtDynamic h) (heap-before _) _ =
    -- Heap location
    exec-trace-preserves-heap-loc trace s alloc h tnhw

  -- Standard variant: derive preservation for slots below next-slot alloc
  derive-mem-preserved : ∀ (alloc : AllocState {FS})
    (trace : AbstractTrace) (s : LocState FS) →
    TraceWritesAbove (next-slot alloc) trace →
    TraceNoHeapWrites trace →
    (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    readLoc (proj₁ (exec-trace trace s alloc)) loc ≡ readLoc s loc
  derive-mem-preserved alloc trace s twa tnhw loc bf =
    derive-mem-preserved-at alloc (next-slot alloc) trace s twa tnhw loc bf ≤-refl
    where open import Data.Nat.Properties using (≤-refl)

  -- Main lemma: trace preserves validity when writing above frontier
  -- Now uses derive-mem-preserved instead of inline proof
  validityWF-trace-preserves : ∀ {m A} (alloc : AllocState {FS})
    (trace : AbstractTrace) (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) →
    -- Validity at start
    BeforeFrontier alloc loc →
    ValidAtWF m alloc {A} v loc s →
    -- Trace only writes at slots ≥ next-slot alloc
    TraceWritesAbove (next-slot alloc) trace →
    TraceNoHeapWrites trace →
    -- Validity preserved after trace
    ValidAtWF m alloc {A} v loc (proj₁ (exec-trace trace s alloc))
  validityWF-trace-preserves alloc trace v loc s loc-bf valid twa tnhw =
    validityWF-mem-preserved v loc s (proj₁ (exec-trace trace s alloc)) loc-bf
      (derive-mem-preserved alloc trace s twa tnhw) valid

  ------------------------------------------------------------------------
  -- Phase 4: Derive mem-preserved from IRResultAWF
  --
  -- This function replaces the stored mem-preserved-before field.
  -- It derives preservation from trace-writes-above and trace-no-heap-writes,
  -- using trace-correct to translate from exec-trace to final-state.
  ------------------------------------------------------------------------


  -- Plan 0.14: helper for stack-only producers. Their traces still
  -- syntactically satisfy TraceNoHeapWrites + TraceWritesAbove; this
  -- helper packages the derivation, so each producer's
  -- `mem-preserved-before` is one line instead of inlining the chain.
  mem-preserved-from-tnhw : ∀ (alloc : AllocState {FS})
    (trace : AbstractTrace) (s final-state : LocState FS) →
    proj₁ (exec-trace trace s alloc) ≡ final-state →
    TraceWritesAbove (next-slot alloc) trace →
    TraceNoHeapWrites trace →
    (loc : ValueLocation FS) → BeforeFrontier alloc loc →
    readLoc final-state loc ≡ readLoc s loc
  mem-preserved-from-tnhw alloc trace s fs tc twa tnhw loc bf =
    subst (λ st → readLoc st loc ≡ readLoc s loc) tc
      (derive-mem-preserved alloc trace s twa tnhw loc bf)
    where open import Relation.Binary.PropositionalEquality using (subst)

  ------------------------------------------------------------------------
  -- BeforeFrontier monotonicity (compose two preservation proofs)
  --
  -- Replaces the syntactic TraceNoHeapWrites chaining in producers:
  -- every consumer that previously chained sub-IR `trace-no-heap-writes`
  -- now composes sub-IR `mem-preserved-before` directly via this helper.
  -- See `feedback_consequence_form_invariants` — the syntactic predicate
  -- was a stand-in; this is the consequence form composers actually need.
  ------------------------------------------------------------------------

  -- A `BeforeFrontier alloc₁ loc` proof carries over to a `BeforeFrontier alloc₂ loc`
  -- proof when alloc₂ extends alloc₁ monotonically (same current-frame, ≥ next-slot,
  -- ≥ next-heap-ref).
  before-frontier-monotone : ∀ (alloc₁ alloc₂ : AllocState {FS}) {loc : ValueLocation FS} →
    current-frame alloc₁ ≡ current-frame alloc₂ →
    next-slot alloc₁ ≤ next-slot alloc₂ →
    next-heap-ref alloc₁ ≤ next-heap-ref alloc₂ →
    BeforeFrontier alloc₁ loc →
    BeforeFrontier alloc₂ loc
  before-frontier-monotone alloc₁ alloc₂ cf-eq slot-≤ heap-≤
    (FrontierInvariant.stack-before {f} {k} f≡cf₁ k<ns₁) =
    FrontierInvariant.stack-before (trans f≡cf₁ cf-eq) (≤-trans-< k<ns₁ slot-≤)
    where
      open import Data.Nat.Properties using () renaming (<-≤-trans to ≤-trans-<)
  before-frontier-monotone alloc₁ alloc₂ cf-eq slot-≤ heap-≤
    (FrontierInvariant.stack-ancestor {f = f} cf₁≺f src) =
    FrontierInvariant.stack-ancestor (subst (λ cf → cf ≺ f) cf-eq cf₁≺f) src
    where
      open import Relation.Binary.PropositionalEquality using (subst)
  before-frontier-monotone alloc₁ alloc₂ cf-eq slot-≤ heap-≤
    (FrontierInvariant.heap-before r<nhr₁) =
    FrontierInvariant.heap-before (≤-trans-< r<nhr₁ heap-≤)
    where
      open import Data.Nat.Properties using () renaming (<-≤-trans to ≤-trans-<)

  -- Compose two mem-preserved-before proofs (f then g). The first preserves
  -- locations in alloc₁'s view; the second preserves locations in
  -- alloc₂'s (wider) view; together they preserve alloc₁'s view across
  -- both runs. Replaces TNHW chaining in Compose/SumRec/Apply/etc.
  mem-preserved-compose : ∀ (alloc₁ alloc₂ : AllocState {FS})
    (s₁ s₂ s₃ : LocState FS) →
    current-frame alloc₁ ≡ current-frame alloc₂ →
    next-slot alloc₁ ≤ next-slot alloc₂ →
    next-heap-ref alloc₁ ≤ next-heap-ref alloc₂ →
    (f-pres : ∀ loc → BeforeFrontier alloc₁ loc → readLoc s₂ loc ≡ readLoc s₁ loc) →
    (g-pres : ∀ loc → BeforeFrontier alloc₂ loc → readLoc s₃ loc ≡ readLoc s₂ loc) →
    (∀ loc → BeforeFrontier alloc₁ loc → readLoc s₃ loc ≡ readLoc s₁ loc)
  mem-preserved-compose alloc₁ alloc₂ s₁ s₂ s₃ cf-eq slot-≤ heap-≤ f-pres g-pres loc bf₁ =
    trans (g-pres loc (before-frontier-monotone alloc₁ alloc₂ cf-eq slot-≤ heap-≤ bf₁))
          (f-pres loc bf₁)

  -- plan 0.135 S3: WHERE A FRAGMENT'S INPUT IS (was `Interface.InputAt`). Here,
  -- beside `ResultPlace`, rather than in the table-parameterised interface, so
  -- that `FnRuns` — what a caller at one table asks of a callee proved at its
  -- suffix — is one type.
  data InputAt {A : IRTy} (mIn : AllocMode) (alloc : AllocState {FS})
               (v : ⟦ A ⟧) (s : LocState FS) : Set where
    in-loc : (loc : ValueLocation FS)
           → ValidAtWF mIn alloc {A} v loc s
           → Live alloc loc
           → readReg (regs s) Input1 ≡ SV-Ptr loc → InputAt mIn alloc v s
    in-reg : (fit : FitsInRegI A) → readReg (regs s) Input1 ≡ prim-sv fit v
           → InputAt mIn alloc v s
    -- D074: a UNIT input has no residence at all — `Input1` may hold anything
    -- (the entry state's tag filler; after `f : IR A Unit` in a composition,
    -- `f`'s unit output is likewise unconstrained, so a residence premise
    -- would make `comp-step`'s IH inapplicable). The machine never reads a
    -- unit input: `readTyped Unit` and `readReg-typed Unit` both materialise
    -- `tt` regardless of what is there.
    in-unit : A ≡ Unit → InputAt mIn alloc v s


-- plan 0.135 S1: the constructor names, for USERS. A pattern synonym declared
-- inside `ClosureWellFormedDef` is abstracted over its `{prog}` parameter,
-- which its body does not mention, so an expression use leaves `prog`
-- unsolved. Declared here, at the top level, where there is no parameter to
-- abstract over (the constructors' own `FS` and `prog` are fixed by the
-- expected type).
open ClosureWellFormedBase using (wrap; unit-wf; pair-wf; inl-wf; inr-wf; inl-reg-wf; inr-reg-wf; int-wf; float-wf; fo-μwf; fo-μbox)
open ClosureWellFormedDef using (closure-wf; closure-reg-wf)
pattern valid-unit-wf = wrap unit-wf
pattern valid-pair-wf {pair-loc} lmm slb c₁ c₂ = wrap (pair-wf {pair-loc = pair-loc} lmm slb c₁ c₂)
pattern valid-inl-wf {m} {a} {sum-loc} {payload-loc} {mA} lmm tg pp pb slb pv =
  wrap (inl-wf {m = m} {a = a} {sum-loc = sum-loc} {payload-loc = payload-loc} {mA = mA} lmm tg pp pb slb pv)
pattern valid-inr-wf {m} {b} {sum-loc} {payload-loc} {mB} lmm tg pp pb slb pv =
  wrap (inr-wf {m = m} {b = b} {sum-loc = sum-loc} {payload-loc = payload-loc} {mB = mB} lmm tg pp pb slb pv)
pattern valid-inl-reg-wf {m} {a} {sum-loc} lmm tg rep pp slb =
  wrap (inl-reg-wf {m = m} {a = a} {sum-loc = sum-loc} lmm tg rep pp slb)
pattern valid-inr-reg-wf {m} {b} {sum-loc} lmm tg rep pp slb =
  wrap (inr-reg-wf {m = m} {b = b} {sum-loc = sum-loc} lmm tg rep pp slb)
pattern valid-closure-wf {f} {closure-loc} {env-loc} lmm ep cp eb slb fd runs =
  wrap (closure-wf {f = f} {closure-loc = closure-loc} {env-loc = env-loc} lmm ep cp eb slb fd runs)
pattern valid-closure-reg-wf {f} {env} {closure-loc} lmm rep ep cp slb fd runs =
  wrap (closure-reg-wf {f = f} {env = env} {closure-loc = closure-loc} lmm rep ep cp slb fd runs)
pattern valid-ν-wf nv = wrap nv
pattern valid-int-wf {loc} bf rl = wrap (int-wf {loc = loc} bf rl)
pattern valid-float-wf {loc} bf rl = wrap (float-wf {loc = loc} bf rl)
pattern valid-μ-wf ub wf x lv = wrap (fo-μwf ub wf x lv)
pattern valid-μbox-wf bx wf x c = wrap (fo-μbox bx wf x c)
