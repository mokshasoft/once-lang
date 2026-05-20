-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.ClosureWellFormed
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

module Once.CCC.Machine.ClosureWellFormed where

open import Data.Nat using (ℕ; _<_; _≤_; _≥_; suc; zero) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-antisym; ≤-trans; +-identityʳ)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
import Once.CCC.Machine.SMPrimitives as SMP
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Plan 0.14 structural-gap-elimination (2026-05-18): IRResultBase
-- references `ir-to-trace-at-frontier` to force each producer's trace
-- to equal what IRToTrace emits at the alloc's frontier. The previously-
-- free `trace` field becomes structurally constrained.
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace-at-frontier)

-- Import μ-type/ν-type and WellFormedF for recursive type validity
open import Once.Type using (μ-type; ν-type; Functor)
open import Once.Functor.Translate using (WellFormedF)

-- Import MuValidity for μValid/νValid
import Once.CCC.Machine.IR.MuValidity as MV

------------------------------------------------------------------------
-- BodyResult: Result type for body execution
--
-- When a closure body executes with (env, arg), it produces this result.
-- This is essentially IRResultA specialized to the body.
------------------------------------------------------------------------

module ClosureWellFormedDef {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.CCC.Machine.Validity
  open ValidityDef {FS} program-bound
    using (readLoc-stack-heap-eq)
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open AbstractExec {FS}
  open TracePrimitives {FS}
  open FrameSemantics FS

  -- Import μValid/νValid and preservation lemmas from MuValidity
  open MV.MuValidityImpl {FS} program-bound
    using (μValid; νValid;
           μValid-mem-only; νValid-mem-only;
           μValid-frontier-advance; νValid-frontier-advance;
           μValid-bf-transfer; νValid-bf-transfer;
           μValid-mem-preserved; νValid-mem-preserved)

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

  mutual
    --------------------------------------------------------------------
    -- ValidAtWF: Mode-indexed validity
    --
    -- First parameter is AllocMode - determines memory representation.
    -- Constructor choice is FORCED by the mode:
    --   Stack → must use unboxed constructors
    --   Heap  → must use boxed constructors
    --------------------------------------------------------------------

    data ValidAtWF : AllocMode → AllocState {FS} →
         {A : Type} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set where

      -- Unit: valid at any mode (no representation difference)
      valid-unit-wf : ∀ {m alloc loc s} →
        ValidAtWF m alloc {Unit} tt loc s

      -- Pair (any mode): two pointers at pair-loc, sucLoc pair-loc
      -- Reference-based model: Stack and Heap use identical representation
      -- Plan 0.13.2: pointer reads in memory wrap as SV-Ptr.
      -- Plan 0.14 (Camp 2): the mode-shape link `LocMatchesMode m pair-loc`
      -- is now a constructor precondition. Stack-mode pairs live at
      -- AtStack; Heap-mode pairs at AtDynamic. The Place stage's
      -- discipline is surfaced into the proof here.
      valid-pair-wf : ∀ {m A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
        {alloc : AllocState {FS}}
        {pair-loc fst-loc snd-loc : ValueLocation FS} {s : LocState FS}
        {mA mB : AllocMode} →
        LocMatchesMode m pair-loc →
        readLoc s pair-loc ≡ just (SV-Ptr fst-loc) →
        readLoc s (sucLoc pair-loc) ≡ just (SV-Ptr snd-loc) →
        BeforeFrontier alloc fst-loc →
        BeforeFrontier alloc snd-loc →
        BeforeFrontier alloc (sucLoc pair-loc) →
        ValidAtWF mA alloc a fst-loc s →
        ValidAtWF mB alloc b snd-loc s →
        ValidAtWF m alloc {A * B} (a , b) pair-loc s

      -- Plan 0.14 (post-Phase-D, 2026-05-17): closure[1] holds an
      -- SV-Code label, not an SV-Ptr to a ValueLocation. Code
      -- addresses are categorically distinct from data pointers
      -- (StoredValue already reflects this via SV-Code). This change
      -- removes the lying `SV-Ptr code-loc` invariant — the self-
      -- reference "fiction" CurryWF and CurryHeapWF used to invent
      -- a `code-loc` to satisfy the type. Runtime emits
      -- `instr-load-code-addr this-label` which produces SV-Code.
      valid-closure-wf : ∀ {EnvType k A B}
        {body : IR (EnvType * A) B}
        {env : ⟦ EnvType ⟧}
        {alloc : AllocState {FS}}
        (body<bound : ir-size body < program-bound) →
        {closure-loc env-loc : ValueLocation FS} {s : LocState FS}
        {mEnv : AllocMode}
        {body-label : ℕ} →
        LocMatchesMode Heap closure-loc →
        readLoc s closure-loc ≡ just (SV-Ptr env-loc) →
        readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label) →
        BeforeFrontier alloc env-loc →
        BeforeFrontier alloc (sucLoc closure-loc) →
        ValidAtWF mEnv alloc env env-loc s →
        BodyCorrect body env env-loc program-bound →
        ValidAtWF Heap alloc {A ⇒[ k ] B} (λ arg → eval body (pair env arg)) closure-loc s

      valid-inl-wf : ∀ {m A B} {a : ⟦ A ⟧}
        {alloc : AllocState {FS}}
        {sum-loc payload-loc : ValueLocation FS} {s : LocState FS}
        {mA : AllocMode} →
        LocMatchesMode m sum-loc →
        readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
        BeforeFrontier alloc payload-loc →
        BeforeFrontier alloc (sucLoc sum-loc) →
        ValidAtWF mA alloc a payload-loc s →
        ValidAtWF m alloc {A + B} (sem-inl a) sum-loc s

      valid-inr-wf : ∀ {m A B} {b : ⟦ B ⟧}
        {alloc : AllocState {FS}}
        {sum-loc payload-loc : ValueLocation FS} {s : LocState FS}
        {mB : AllocMode} →
        LocMatchesMode m sum-loc →
        readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
        BeforeFrontier alloc payload-loc →
        BeforeFrontier alloc (sucLoc sum-loc) →
        ValidAtWF mB alloc b payload-loc s →
        ValidAtWF m alloc {A + B} (sem-inr b) sum-loc s

      -- OCP-0003: μ-type and ν-type validity via MuValidity predicates
      -- These wrap μValid/νValid from MuValidity, avoiding pattern matching issues
      -- by keeping the layer type opaque to ValidAtWF pattern matching.
      valid-μ-wf : ∀ {m F}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS}
        (wf : WellFormedF F)
        (x : ⟦ μ-type F ⟧) →
        μValid alloc wf x loc s →
        ValidAtWF m alloc {μ-type F} x loc s

      valid-ν-wf : ∀ {m F}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS}
        (wf : WellFormedF F)
        (x : ⟦ ν-type F ⟧) →
        νValid alloc wf x loc s →
        ValidAtWF m alloc {ν-type F} x loc s

      -- Primitive types: valid at any mode if location is before frontier
      -- Primitives are single-slot values (Int, Float, Str, Buffer).
      -- No structural constraints needed - just location validity.
      valid-int-wf : ∀ {m} {n : ⟦ Int ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        ValidAtWF m alloc {Int} n loc s

      valid-float-wf : ∀ {m} {x : ⟦ Float ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        ValidAtWF m alloc {Float} x loc s

      valid-str-wf : ∀ {m} {x : ⟦ Str ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        ValidAtWF m alloc {Str} x loc s

      valid-buffer-wf : ∀ {m} {x : ⟦ Buffer ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        BeforeFrontier alloc loc →
        ValidAtWF m alloc {Buffer} x loc s

      -- Effectful morphism: runtime-identical to a pure closure.
      -- `arr` coerces a pure closure (A ⇒[ mk-kind q pure ] B) to the effect-tagged
      -- shape (A ⇒[ mk-kind Many eff ] B) without altering the witness.
      valid-coerce-kind-wf : ∀ {m A B q}
        {f : ⟦ A ⟧ → ⟦ B ⟧}
        {alloc : AllocState {FS}}
        {loc : ValueLocation FS} {s : LocState FS} →
        ValidAtWF m alloc {A ⇒[ mk-kind q pure ] B} f loc s →
        ValidAtWF m alloc {A ⇒[ mk-kind Many eff ] B} f loc s

    --------------------------------------------------------------------
    -- valid-primitive-wf: Dispatch on FitsInReg evidence
    --
    -- For register-fittable primitive types, ValidAtWF only needs
    -- BeforeFrontier. Plan 0.2.4.5: legacy IsPrimitive retired —
    -- Unit is erased (no slot), Str/Buffer are 2-slot compounds with
    -- their own valid-str-wf / valid-buffer-wf witnesses. The only
    -- inhabitants left are Int and Float.
    --------------------------------------------------------------------

    valid-primitive-wf : ∀ {m} {B : Type} {v : ⟦ B ⟧}
      {alloc : AllocState {FS}}
      {loc : ValueLocation FS} {s : LocState FS} →
      FitsInReg B →
      BeforeFrontier alloc loc →
      ValidAtWF m alloc {B} v loc s
    valid-primitive-wf fits-int   bf = valid-int-wf bf
    valid-primitive-wf fits-float bf = valid-float-wf bf

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
    data ResultPlace : (B : Type) (m : AllocMode)
                       (alloc continuation-alloc : AllocState {FS})
                       (v : ⟦ B ⟧) (s : LocState FS) → Set where
      unit-result : ∀ {m alloc continuation-alloc s} →
                    ResultPlace Unit m alloc continuation-alloc tt s
      at-loc      : ∀ {B m alloc continuation-alloc v s}
                    (loc : ValueLocation FS)
                  → ValidAtWF m alloc v loc s
                  → BeforeFrontier alloc loc
                  -- Plan 0.13.2: Output register stores StoredValue;
                  -- a result location is reified as SV-Ptr loc.
                  → readReg (regs s) Output ≡ SV-Ptr loc
                  → ValidAtWF m continuation-alloc v loc s
                  → BeforeFrontier continuation-alloc loc
                  → ResultPlace B m alloc continuation-alloc v s

    -- Plan 0.2.4.5 D1 trust points: place-* extraction helpers.
    --
    -- These project facts out of a `ResultPlace` into the plain
    -- shape that consumers (compose, pair, RecTrace cata) and
    -- `rec-wf`'s preconditions still expect:
    --
    --   * `place-loc rp` — a `ValueLocation FS`.
    --   * `place-valid rp` — `ValidAtWF` at `place-loc rp`.
    --   * `place-before rp` — `BeforeFrontier alloc (place-loc rp)`.
    --   * `place-rax rp` — `readReg s Output ≡ place-loc rp`.
    --   * `place-cont-valid rp` / `place-cont-before rp` —
    --     same but for the continuation-side alloc state.
    --
    -- For `at-loc`, all six are constructor projections (no trust).
    -- For `unit-result`, each is postulated, encoding the
    -- structural fact that "Unit values don't observably reside
    -- anywhere" — there's nothing to extract.
    --
    -- Each postulate is sound for Unit because:
    --   * Unit values carry no observable content.
    --   * `valid-unit-wf` is loc-agnostic (works at any loc).
    --   * BeforeFrontier on a Unit's mythical loc is vacuous.
    --   * Output's value at a Unit boundary is irrelevant.
    --
    -- The postulates are TRANSITIONAL. They go away when either:
    --   (a) `rec-wf`'s preconditions become type-aware — for
    --       Unit-typed IRs, drop `BeforeFrontier alloc input-loc`
    --       and `readReg s Input1 ≡ input-loc` (both vacuous).
    --   (b) Each consumer (compose, pair, RecTrace cata)
    --       case-splits on the `result-place` constructor and takes
    --       a Unit-aware code path that doesn't go through place-*.
    --
    -- Either route requires a deeper proof restructure than the
    -- spec migration covered. Tracked as Plan 0.2.4.5 D1 task #28.
    place-loc : ∀ {B m a₁ a₂ v s} → ResultPlace B m a₁ a₂ v s → ValueLocation FS
    place-loc (at-loc loc _ _ _ _ _) = loc
    place-loc {Unit} unit-result = unit-result-loc-stub
      where postulate unit-result-loc-stub : ValueLocation FS

    place-valid : ∀ {B m a₁ a₂ v s} (rp : ResultPlace B m a₁ a₂ v s) →
                  ValidAtWF m a₁ v (place-loc rp) s
    place-valid (at-loc _ valid _ _ _ _) = valid
    place-valid {Unit} {m} {a₁} {_} {tt} {s} unit-result = valid-unit-stub
      where postulate valid-unit-stub : ValidAtWF m a₁ {Unit} tt _ s

    place-before : ∀ {B m a₁ a₂ v s} (rp : ResultPlace B m a₁ a₂ v s) →
                   BeforeFrontier a₁ (place-loc rp)
    place-before (at-loc _ _ before _ _ _) = before
    place-before {Unit} {_} {a₁} unit-result = before-stub
      where postulate before-stub : BeforeFrontier a₁ _

    place-rax : ∀ {B m a₁ a₂ v s} (rp : ResultPlace B m a₁ a₂ v s) →
                readReg (regs s) Output ≡ SV-Ptr (place-loc rp)
    place-rax (at-loc _ _ _ rax _ _) = rax
    place-rax {Unit} {_} {_} {_} {_} {s} unit-result = rax-stub
      where postulate rax-stub : readReg (regs s) Output ≡ SV-Ptr _

    place-cont-valid : ∀ {B m a₁ a₂ v s} (rp : ResultPlace B m a₁ a₂ v s) →
                       ValidAtWF m a₂ v (place-loc rp) s
    place-cont-valid (at-loc _ _ _ _ cvalid _) = cvalid
    place-cont-valid {Unit} {m} {_} {a₂} {tt} {s} unit-result = valid-unit-cs
      where postulate valid-unit-cs : ValidAtWF m a₂ {Unit} tt _ s

    place-cont-before : ∀ {B m a₁ a₂ v s} (rp : ResultPlace B m a₁ a₂ v s) →
                       BeforeFrontier a₂ (place-loc rp)
    place-cont-before (at-loc _ _ _ _ _ cbefore) = cbefore
    place-cont-before {Unit} {_} {_} {a₂} unit-result = before-cs
      where postulate before-cs : BeforeFrontier a₂ _

    --------------------------------------------------------------------
    -- Plan 0.14 Phase B.0: factored IRResultAWF.
    --
    -- Three sub-records by allocator world:
    --   IRResultBase   — common fields every IR result must provide
    --                    (state/alloc/trace + result-place + halt/frame
    --                     + per-instruction WF chain).
    --   IRStackBudget  — stack-allocator invariants (next-slot bumps,
    --                    slot writes/reads, scratch budget).
    --   IRHeapBudget   — heap-allocator invariants (next-heap-ref bumps,
    --                    heap budget, existing-heap-preservation).
    --
    -- IRResultAWF bundles all three. `open … public` re-exposes each
    -- sub-record's fields at the bundle level so consumers can still
    -- write `r .final-state`, `r .slot-monotone`, `r .heap-monotone`
    -- without going through `.base.` / `.stack-inv.` / `.heap-inv.`.
    --
    -- Stack-only IRs fill the heap sub-record trivially
    -- (heap-monotone = ≤-refl, heap-budget = 0, trace-no-heap-writes = tt).
    -- Heap-allocating IRs (run-pair-heap and friends) contribute
    -- non-trivially to the heap sub-record while filling the stack
    -- sub-record with whatever scratch they use.
    --
    -- Future InReg-allocating IRs add an IRRegBudget sub-record and
    -- one new bundle field; the existing two sub-records stay untouched.
    --------------------------------------------------------------------

    -- Plan 0.17: type-level alloc effect.
    --
    -- Each producer declares its `bump` (delta on next-slot and
    -- next-heap-ref). `final-alloc` is a DERIVED projection:
    -- `final-alloc = apply-bump bump alloc`. Inconsistencies between
    -- the bump and the trace's actual alloc effect are caught by
    -- `alloc-correct` (which ties trace to apply-bump). Inconsistencies
    -- between the heap-result/stack-result discipline (e.g. a
    -- heap-result producer that bumps next-slot) are caught by
    -- `result-place`'s BeforeFrontier proofs.
    --
    -- See `plans/0.17-type-level-alloc-effect.md`.
    record IRResultBase (m : AllocMode)
                        {A B : Type}
                        (ir : IR A B)
                        (x : ⟦ A ⟧)
                        (s : LocState FS)
                        (alloc : AllocState {FS}) : Set where
      inductive
      field
        final-state : LocState FS
        trace : AbstractTrace
        -- Plan 0.17: declared alloc effect. The single source of truth
        -- for how this IR transforms the AllocState. `final-alloc` is
        -- derived from this + alloc (see derived projections below).
        bump : AllocBump
        -- Plan 0.14 (2026-05-18): structural gap elimination. The
        -- trace MUST equal what IRToTrace emits at this alloc's
        -- frontier. Spec/runtime divergence becomes a type error.
        -- Producers discharge with `refl` when shapes match definitionally;
        -- those needing alignment work surface as visible postulates.
        trace-is-ir-to-trace :
          trace ≡ ir-to-trace-at-frontier (next-slot alloc) ir
        trace-correct : proj₁ (exec-trace trace s alloc) ≡ final-state
        -- Plan 0.17: alloc-correct ties trace's runtime alloc to
        -- `apply-bump bump alloc`. A producer whose trace bumps
        -- next-slot while declaring next-slot-delta = 0 cannot
        -- discharge this — type error.
        alloc-correct :
          proj₂ (exec-trace trace s alloc) ≡ apply-bump bump alloc
        -- continuation-alloc: caller's frame, but next-slot and
        -- next-heap-ref both inherited from apply-bump bump alloc
        -- (the resources the IR consumed). Bumping next-heap-ref here
        -- is what makes heap-mode pair / inl / inr's fresh AtDynamic
        -- result satisfy BeforeFrontier on the continuation side.
        result-place : ResultPlace B m (apply-bump bump alloc)
          (record alloc
            { next-slot     = next-slot     (apply-bump bump alloc)
            ; next-heap-ref = next-heap-ref (apply-bump bump alloc) })
          (eval ir x) final-state
        not-halted : halted final-state ≡ false
        -- Plan 0.14: consequence-form memory preservation. Locations
        -- valid in the caller's view (BeforeFrontier alloc) read the
        -- same after the IR runs as before. Subsumes the old
        -- TraceNoHeapWrites + TraceWritesAbove combo. Each producer
        -- proves this from whatever shape its trace has; place-stage
        -- locality keeps the obligation tractable.
        mem-preserved-before :
          (loc : ValueLocation FS) → BeforeFrontier alloc loc →
          readLoc final-state loc ≡ readLoc s loc
        trace-twf : TraceWF s alloc trace
        trace-preserves-halted :
          ∀ (s' : LocState FS) (alloc' : AllocState {FS}) →
          halted s' ≡ false →
          TraceWF s' alloc' trace →
          halted (proj₁ (exec-trace trace s' alloc')) ≡ false

      -- Plan 0.17: derived projection for backward-compat.
      -- Consumers reading `IRResultBase.final-alloc r` get
      -- `apply-bump bump alloc` — the same AllocState they got before,
      -- just constructed from the declared bump rather than free-form.
      final-alloc : AllocState {FS}
      final-alloc = apply-bump bump alloc

      -- Plan 0.17: derived (was a field). apply-bump only updates
      -- next-slot / next-heap-ref via record syntax, so current-frame
      -- is preserved by definition.
      frame-preserved : current-frame final-alloc ≡ current-frame alloc
      frame-preserved = apply-bump-preserves-frame bump alloc

    record IRStackBudget (alloc final-alloc : AllocState {FS})
                         (trace : AbstractTrace)
                         (s : LocState FS) : Set where
      inductive
      field
        slot-monotone : next-slot alloc ≤ next-slot final-alloc
        max-slot-written : ℕ
        max-slot-geq-final : next-slot final-alloc ≤ max-slot-written
        stack-budget : ℕ
        max-slot-usage-bound : max-slot-written ≤ next-slot alloc +ℕ stack-budget
        slot-stays-in-budget : next-slot final-alloc ≤ next-slot alloc +ℕ stack-budget
        frontier-slot-stable : ∀ (s' : LocState FS) (input-loc : ValueLocation FS) →
          halted s' ≡ false →
          readReg (regs s') Input1 ≡ SV-Ptr input-loc →
          readLoc s' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc) →
          (next-slot alloc ≡ next-slot final-alloc) ⊎
          ((readLoc (proj₁ (exec-trace trace s' alloc))
                   (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc)) ⊎ ⊤)
        trace-writes-above : TraceWritesAbove (next-slot alloc) trace
        trace-slot-reads-above : TraceSlotReadsAbove (next-slot alloc) trace
        trace-writes-below : TraceWritesBelow max-slot-written trace
        trace-slot-reads-below : TraceSlotReadsBelow max-slot-written trace
        scratch-budget : ℕ
        scratch-bounded : max-slot-written ≤ next-slot final-alloc +ℕ scratch-budget

    record IRHeapBudget (alloc final-alloc : AllocState {FS})
                        (trace : AbstractTrace) : Set where
      inductive
      field
        -- Plan 0.14: heap-monotone replaces the old heap-preserved (≡).
        -- ≤ accommodates instr-alloc-heap-bearing traces.
        heap-monotone : next-heap-ref alloc ≤ next-heap-ref final-alloc
        heap-budget : ℕ
        max-heap-ref-written : ℕ
        max-heap-ref-geq-final : next-heap-ref final-alloc ≤ max-heap-ref-written
        max-heap-usage-bound : max-heap-ref-written ≤ next-heap-ref alloc +ℕ heap-budget
        -- Plan 0.14 follow-up: the SYNTACTIC field `trace-no-heap-writes`
        -- has been removed. Stack-only producers prove TraceNoHeapWrites
        -- LOCALLY for their trace shape and feed it to `mem-preserved-from-tnhw`
        -- to discharge `IRResultBase.mem-preserved-before` — the actual
        -- consequence-form invariant downstream needs (see
        -- `feedback_consequence_form_invariants`). Composers compose
        -- `mem-preserved-before` via `mem-preserved-compose` rather than
        -- chaining the syntactic predicate.

    record IRResultAWF (m : AllocMode)
                       {A B : Type}
                       (ir : IR A B)
                       (x : ⟦ A ⟧)
                       (s : LocState FS)
                       (alloc : AllocState {FS}) : Set where
      inductive
      field
        base       : IRResultBase m ir x s alloc
        stack-inv  : IRStackBudget alloc (IRResultBase.final-alloc base) (IRResultBase.trace base) s
        heap-inv   : IRHeapBudget  alloc (IRResultBase.final-alloc base) (IRResultBase.trace base)
      open IRResultBase   base       public
      open IRStackBudget  stack-inv  public
      open IRHeapBudget   heap-inv   public

    --------------------------------------------------------------------
    -- BodyCorrect: Pre-computed body execution proof
    --
    -- Input1 pair is constructed by Apply as Heap (boxed).
    -- Output mode comes from body's actual output.
    --------------------------------------------------------------------

    {-# NO_POSITIVITY_CHECK #-}
    record BodyCorrect {EnvType A B : Type}
                       (body : IR (EnvType * A) B)
                       (env : ⟦ EnvType ⟧)
                       (env-loc : ValueLocation FS)
                       (bound : ℕ) : Set where
      inductive
      field
        body-capacity : ℕ
        body-cap-eq : body-capacity ≡ ir-stack-requirement body

        -- Execute returns mode-indexed result
        -- Input1 pair is Heap (boxed) - constructed by Apply
        -- Output mode is existentially quantified (body decides)
        -- Note: capacity precondition removed in Phase 3 (frame-capacity removed)
        execute : ∀ (arg : ⟦ A ⟧) (arg-loc pair-loc : ValueLocation FS)
          (s : LocState FS) (alloc : AllocState {FS})
          (mPair : AllocMode) →
          ValidAtWF mPair alloc (pair env arg) pair-loc s →
          BeforeFrontier alloc pair-loc →
          halted s ≡ false →
          readReg (regs s) Input1 ≡ SV-Ptr pair-loc →
          ∃[ mOut ] IRResultAWF mOut body (pair env arg) s alloc

  open IRResultAWF public
  open BodyCorrect public

  --------------------------------------------------------------------
  -- Backward-compat helper: derive exact heap-preservation (≡) when
  -- the IR result's heap-budget is 0. Replaces the old field
  -- `heap-preserved : ≡` for consumers that need exact equality.
  -- Stack-only IRs (the default) set heap-budget = 0, so the equality
  -- is derivable. Heap-allocating IRs (Phase B+) cannot use this.
  --------------------------------------------------------------------
  heap-preserved-of : ∀ {m A B} {ir : IR A B} {x : ⟦ A ⟧}
                       {s : LocState FS} {alloc : AllocState {FS}}
                       (r : IRResultAWF m ir x s alloc) →
    IRResultAWF.heap-budget r ≡ 0 →
    next-heap-ref (IRResultAWF.final-alloc r) ≡ next-heap-ref alloc
  heap-preserved-of {alloc = alloc} r budget-eq = ≤-antisym
    (≤-trans (IRResultAWF.max-heap-ref-geq-final r) bound-alloc)
    (IRResultAWF.heap-monotone r)
    where
      -- After substituting budget = 0 and applying +-identityʳ to
      -- collapse `n +ℕ 0` to `n`, we get the desired bound.
      bound-via-budget : IRResultAWF.max-heap-ref-written r ≤ next-heap-ref alloc +ℕ 0
      bound-via-budget = subst
        (λ b → IRResultAWF.max-heap-ref-written r ≤ next-heap-ref alloc +ℕ b)
        budget-eq
        (IRResultAWF.max-heap-usage-bound r)

      bound-alloc : IRResultAWF.max-heap-ref-written r ≤ next-heap-ref alloc
      bound-alloc = subst (IRResultAWF.max-heap-ref-written r ≤_)
                          (+-identityʳ (next-heap-ref alloc))
                          bound-via-budget

  ------------------------------------------------------------------------
  -- ClosureWellFormed: Closure with pre-computed body execution proof
  --
  -- This extends the basic closure validity with body-correct.
  -- Curry constructs this, Apply uses it.
  ------------------------------------------------------------------------

  record ClosureWellFormed {EnvType A B : Type}
                           (body : IR (EnvType * A) B)
                           (env : ⟦ EnvType ⟧)
                           (body<bound : ir-size body < program-bound)
                           (closure-loc env-loc code-loc : ValueLocation FS)
                           (s : LocState FS)
                           (alloc : AllocState {FS}) : Set where
    field
      -- Memory layout
      env-ptr : readLoc s closure-loc ≡ just (SV-Ptr env-loc)
      code-ptr : readLoc s (sucLoc closure-loc) ≡ just (SV-Ptr code-loc)
      -- Frontier tracking
      env-before : BeforeFrontier alloc env-loc
      code-before : BeforeFrontier alloc code-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc closure-loc)
      -- Env validity (now using ValidAtWF with mode)
      mEnv : AllocMode
      env-valid : ValidAtWF mEnv alloc env env-loc s
      -- PRE-COMPUTED body execution proof with program-bound
      body-correct : BodyCorrect body env env-loc program-bound

  open ClosureWellFormed public

  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF closures
  ------------------------------------------------------------------------

  record ClosureValidWF (alloc : AllocState {FS}) {k : ArrowKind} {A B : Type}
                        (f : ⟦ A ⇒[ k ] B ⟧)
                        (closure-loc : ValueLocation FS)
                        (s : LocState FS) : Set where
    field
      EnvType : Type
      body : IR (EnvType * A) B
      env : ⟦ EnvType ⟧
      body<bound : ir-size body < program-bound
      env-loc : ValueLocation FS
      body-label : ℕ
      mEnv : AllocMode  -- Mode of env
      env-ptr : readLoc s closure-loc ≡ just (SV-Ptr env-loc)
      code-ptr : readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label)
      env-before : BeforeFrontier alloc env-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc closure-loc)
      env-valid : ValidAtWF mEnv alloc env env-loc s
      -- THE KEY: body-correct is extracted with program-bound!
      body-correct : BodyCorrect body env env-loc program-bound
      f-is-closure : f ≡ (λ arg → eval body (pair env arg))

  -- Closures are always Heap mode. Kind-polymorphic: works for both pure
  -- (⇒[ mk-kind q pure ]) and effectful (Eff) arrows, unwrapping valid-coerce-kind-wf
  -- as needed.
  decomposeClosureWF : ∀ {alloc k A B} {f : ⟦ A ⇒[ k ] B ⟧} {loc s} →
    ValidAtWF Heap alloc {A ⇒[ k ] B} f loc s → ClosureValidWF alloc {k = k} f loc s
  decomposeClosureWF (valid-closure-wf {EnvType} {_} {_} {_} {body} {env} {_}
                       bb {_} {el} {_} {mE} {bl} lmm ep cp eb slb ev bc) = record
    { EnvType = EnvType
    ; body = body
    ; env = env
    ; body<bound = bb
    ; env-loc = el
    ; body-label = bl
    ; mEnv = mE
    ; env-ptr = ep
    ; code-ptr = cp
    ; env-before = eb
    ; sucLoc-before = slb
    ; env-valid = ev
    ; body-correct = bc
    ; f-is-closure = refl
    }
  decomposeClosureWF (valid-coerce-kind-wf {q = _} cv) with decomposeClosureWF cv
  ... | inner = record
    { EnvType = ClosureValidWF.EnvType inner
    ; body = ClosureValidWF.body inner
    ; env = ClosureValidWF.env inner
    ; body<bound = ClosureValidWF.body<bound inner
    ; env-loc = ClosureValidWF.env-loc inner
    ; body-label = ClosureValidWF.body-label inner
    ; mEnv = ClosureValidWF.mEnv inner
    ; env-ptr = ClosureValidWF.env-ptr inner
    ; code-ptr = ClosureValidWF.code-ptr inner
    ; env-before = ClosureValidWF.env-before inner
    ; sucLoc-before = ClosureValidWF.sucLoc-before inner
    ; env-valid = ClosureValidWF.env-valid inner
    ; body-correct = ClosureValidWF.body-correct inner
    ; f-is-closure = ClosureValidWF.f-is-closure inner
    }

  -- Closures are always Heap mode - extract mode equality from validity proof
  -- Works for both valid-closure-wf (direct) and valid-coerce-kind-wf (eff wrapper).
  closure-mode-is-heap-proof : ∀ {m alloc k A B} {f : ⟦ A ⇒[ k ] B ⟧} {loc s} →
    ValidAtWF m alloc {A ⇒[ k ] B} f loc s → m ≡ Heap
  closure-mode-is-heap-proof (valid-closure-wf _ _ _ _ _ _ _ _) = refl
  closure-mode-is-heap-proof (valid-coerce-kind-wf cv) = closure-mode-is-heap-proof cv

  ------------------------------------------------------------------------
  -- RecDispatcherWF: Recursive dispatcher interface with ValidAtWF
  --
  -- Used by Curry to construct BodyCorrect.
  -- Takes ValidAtWF input and returns IRResultAWF with ValidAtWF output.
  --
  -- SIMPLIFIED: Only needs linear capacity (pair-slots * ir-size).
  -- No global invariants needed - capacity is threaded dynamically per closure.
  ------------------------------------------------------------------------

  -- Note: capacity precondition removed in Phase 3 (frame-capacity removed)
  RecDispatcherWF : ℕ → Set
  RecDispatcherWF bound = ∀ {A B} (mIn : AllocMode) (ir : IR A B) →
    ir-size ir < bound →
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS) (s : LocState FS)
    (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ mOut ] IRResultAWF mOut ir x s alloc

  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF pairs (any mode)
  --
  -- Reference-based model: two pointers at pair-loc and sucLoc pair-loc
  ------------------------------------------------------------------------

  record PairValidWF (alloc : AllocState {FS}) {A B : Type}
                     (p : ⟦ A * B ⟧)
                     (pair-loc : ValueLocation FS)
                     (s : LocState FS) : Set where
    field
      fst-loc : ValueLocation FS
      snd-loc : ValueLocation FS
      mA : AllocMode  -- Component A mode
      mB : AllocMode  -- Component B mode
      fst-ptr : readLoc s pair-loc ≡ just (SV-Ptr fst-loc)
      snd-ptr : readLoc s (sucLoc pair-loc) ≡ just (SV-Ptr snd-loc)
      fst-before : BeforeFrontier alloc fst-loc
      snd-before : BeforeFrontier alloc snd-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc pair-loc)
      fst-valid : ValidAtWF mA alloc (proj₁ p) fst-loc s
      snd-valid : ValidAtWF mB alloc (proj₂ p) snd-loc s

  decomposePairWF : ∀ {m alloc A B} {p : ⟦ A * B ⟧} {loc s} →
    ValidAtWF m alloc p loc s → PairValidWF alloc p loc s
  decomposePairWF (valid-pair-wf {_} {_} {_} {_} {_} {_} {_} {fl} {sl} {_} {mA} {mB}
                    lmm fp sp fb sb slb fv sv) = record
    { fst-loc = fl
    ; snd-loc = sl
    ; mA = mA
    ; mB = mB
    ; fst-ptr = fp
    ; snd-ptr = sp
    ; fst-before = fb
    ; snd-before = sb
    ; sucLoc-before = slb
    ; fst-valid = fv
    ; snd-valid = sv
    }

  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF sum types (inl/inr) - any mode
  --
  -- Reference-based model: tag + payload-ptr (identical for all modes)
  ------------------------------------------------------------------------

  record InlValidWF (alloc : AllocState {FS}) {A B : Type}
                    (v : ⟦ A + B ⟧)
                    (sum-loc : ValueLocation FS)
                    (s : LocState FS) : Set where
    field
      a : ⟦ A ⟧
      mA : AllocMode
      payload-loc : ValueLocation FS
      payload-ptr : readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc)
      payload-before : BeforeFrontier alloc payload-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload-valid : ValidAtWF mA alloc a payload-loc s
      v-is-inl : v ≡ sem-inl a

  record InrValidWF (alloc : AllocState {FS}) {A B : Type}
                    (v : ⟦ A + B ⟧)
                    (sum-loc : ValueLocation FS)
                    (s : LocState FS) : Set where
    field
      b : ⟦ B ⟧
      mB : AllocMode
      payload-loc : ValueLocation FS
      payload-ptr : readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc)
      payload-before : BeforeFrontier alloc payload-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload-valid : ValidAtWF mB alloc b payload-loc s
      v-is-inr : v ≡ sem-inr b

  decomposeInlWF : ∀ {m alloc A B} {a : ⟦ A ⟧} {loc s} →
    ValidAtWF m alloc {A + B} (sem-inl a) loc s → InlValidWF alloc {A} {B} (sem-inl a) loc s
  decomposeInlWF {A = A} {B = B} (valid-inl-wf {_} {_} {_} {a} {_} {_} {pl} {_} {mA} lmm pp pb slb pv) = record
    { a = a
    ; mA = mA
    ; payload-loc = pl
    ; payload-ptr = pp
    ; payload-before = pb
    ; sucLoc-before = slb
    ; payload-valid = pv
    ; v-is-inl = refl
    }

  decomposeInrWF : ∀ {m alloc A B} {b : ⟦ B ⟧} {loc s} →
    ValidAtWF m alloc {A + B} (sem-inr b) loc s → InrValidWF alloc {A} {B} (sem-inr b) loc s
  decomposeInrWF {A = A} {B = B} (valid-inr-wf {_} {_} {_} {b} {_} {_} {pl} {_} {mB} lmm pp pb slb pv) = record
    { b = b
    ; mB = mB
    ; payload-loc = pl
    ; payload-ptr = pp
    ; payload-before = pb
    ; sucLoc-before = slb
    ; payload-valid = pv
    ; v-is-inr = refl
    }

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
  -- ValidAtWF memory-only dependence
  --
  -- ValidAtWF only depends on memory, not registers. When memory is
  -- preserved, validity transfers to a new state.
  ------------------------------------------------------------------------

  -- ValidAtWF only depends on memory, not registers
  -- When memory is preserved (stackMem and heapMem equal), validity transfers
  -- By structural induction on ValidAtWF
  validityWF-mem-only : ∀ {m alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    stackMem s₂ ≡ stackMem s₁ →
    heapMem s₂ ≡ heapMem s₁ →
    ValidAtWF m alloc v loc s₁ → ValidAtWF m alloc v loc s₂

  validityWF-mem-only {m} {alloc} {Unit} tt loc s₁ s₂ stack-eq heap-eq valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-mem-only {m} {alloc} {A * B} (a , b) loc s₁ s₂ stack-eq heap-eq
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} lmm fp sp fb sb slb fv sv) =
    valid-pair-wf lmm fp' sp' fb sb slb fv' sv'
    where
      fp' : readLoc s₂ loc ≡ just (SV-Ptr fl)
      fp' = trans (readLoc-stack-heap-eq s₂ s₁ loc stack-eq heap-eq) fp

      sp' : readLoc s₂ (sucLoc loc) ≡ just (SV-Ptr sl)
      sp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) sp

      fv' = validityWF-mem-only a fl s₁ s₂ stack-eq heap-eq fv
      sv' = validityWF-mem-only b sl s₁ s₂ stack-eq heap-eq sv

  validityWF-mem-only {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s₁ s₂ stack-eq heap-eq
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} lmm ep cp eb slb ev bc) =
    valid-closure-wf bb lmm ep' cp' eb slb ev' bc
    where
      ep' : readLoc s₂ loc ≡ just (SV-Ptr el)
      ep' = trans (readLoc-stack-heap-eq s₂ s₁ loc stack-eq heap-eq) ep

      cp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) cp

      ev' = validityWF-mem-only env el s₁ s₂ stack-eq heap-eq ev

  -- Kind-coerced closure: recurse on underlying validity, re-coerce.
  validityWF-mem-only {m} {alloc} {A ⇒[ _ ] B} f loc s₁ s₂ stack-eq heap-eq (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-mem-only f loc s₁ s₂ stack-eq heap-eq cv)

  -- Eff (effectful morphism): recurse on underlying closure validity

  -- inl (any mode)
  validityWF-mem-only {m} {alloc} {A + B} .(sem-inl a) loc s₁ s₂ stack-eq heap-eq
    (valid-inl-wf {a = a} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inl-wf lmm pp' pb slb pv'
    where
      pp' : readLoc s₂ (sucLoc loc) ≡ just (SV-Ptr pl)
      pp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) pp

      pv' = validityWF-mem-only a pl s₁ s₂ stack-eq heap-eq pv

  -- inr (any mode)
  validityWF-mem-only {m} {alloc} {A + B} .(sem-inr b) loc s₁ s₂ stack-eq heap-eq
    (valid-inr-wf {b = b} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inr-wf lmm pp' pb slb pv'
    where
      pp' : readLoc s₂ (sucLoc loc) ≡ just (SV-Ptr pl)
      pp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) pp

      pv' = validityWF-mem-only b pl s₁ s₂ stack-eq heap-eq pv

  -- OCP-0003: μ-type and ν-type validity preservation
  -- Uses proven lemmas from MuValidity
  validityWF-mem-only {m} {alloc} {μ-type F} x loc s₁ s₂ stack-eq heap-eq (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-mem-only alloc wf x loc s₁ s₂ stack-eq heap-eq μv)

  validityWF-mem-only {m} {alloc} {ν-type F} x loc s₁ s₂ stack-eq heap-eq (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-mem-only alloc wf x loc s₁ s₂ stack-eq heap-eq νv)

  -- Primitives: memory-independent (BeforeFrontier doesn't depend on state)
  validityWF-mem-only {m} {alloc} {Int} _ loc s₁ s₂ stack-eq heap-eq (valid-int-wf bf) =
    valid-int-wf bf
  validityWF-mem-only {m} {alloc} {Float} _ loc s₁ s₂ stack-eq heap-eq (valid-float-wf bf) =
    valid-float-wf bf
  validityWF-mem-only {m} {alloc} {Str} _ loc s₁ s₂ stack-eq heap-eq (valid-str-wf bf) =
    valid-str-wf bf
  validityWF-mem-only {m} {alloc} {Buffer} _ loc s₁ s₂ stack-eq heap-eq (valid-buffer-wf bf) =
    valid-buffer-wf bf

  ------------------------------------------------------------------------
  -- ValidAtWF preservation under writes to frontier locations
  --
  -- These are ValidAtWF versions of validity-write-at-frontier and
  -- validity-write-at-suc-frontier from ValidityWriteLemma.agda.
  ------------------------------------------------------------------------

  -- Import helpers for frontier inequality
  -- ValidAtWF is preserved when writing to at-frontier location
  validityWF-write-at-frontier : ∀ {m alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAtWF m alloc v loc s →
    ValidAtWF m alloc v loc (write-loc s (AtStack (current-frame alloc) (next-slot alloc)) val)

  validityWF-write-at-frontier {m} {alloc} {Unit} _ loc s val loc-before valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-write-at-frontier {m} {alloc} {A * B} (a , b) loc s val loc-before
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} lmm fp sp fb sb slb fv sv) =
    valid-pair-wf lmm fp' sp' fb sb slb fv' sv'
    where
      fp' = trans (write-at-frontier-preserves-before s alloc loc val loc-before) fp
      sp' = trans (write-at-frontier-preserves-before s alloc (sucLoc loc) val slb) sp
      fv' = validityWF-write-at-frontier a fl s val fb fv
      sv' = validityWF-write-at-frontier b sl s val sb sv

  validityWF-write-at-frontier {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s val loc-before
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} lmm ep cp eb slb ev bc) =
    valid-closure-wf bb lmm ep' cp' eb slb ev' bc
    where
      ep' = trans (write-at-frontier-preserves-before s alloc loc val loc-before) ep
      cp' = trans (write-at-frontier-preserves-before s alloc (sucLoc loc) val slb) cp
      ev' = validityWF-write-at-frontier env el s val eb ev

  -- Kind-coerced closure
  validityWF-write-at-frontier {m} {alloc} {A ⇒[ _ ] B} f loc s val loc-before (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-write-at-frontier f loc s val loc-before cv)

  -- inl (any mode)
  validityWF-write-at-frontier {m} {alloc} {A + B} .(sem-inl a) loc s val loc-before
    (valid-inl-wf {a = a} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inl-wf lmm pp' pb slb pv'
    where
      pp' = trans (write-at-frontier-preserves-before s alloc (sucLoc loc) val slb) pp
      pv' = validityWF-write-at-frontier a pl s val pb pv

  -- inr (any mode)
  validityWF-write-at-frontier {m} {alloc} {A + B} .(sem-inr b) loc s val loc-before
    (valid-inr-wf {b = b} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inr-wf lmm pp' pb slb pv'
    where
      pp' = trans (write-at-frontier-preserves-before s alloc (sucLoc loc) val slb) pp
      pv' = validityWF-write-at-frontier b pl s val pb pv

  -- OCP-0003: μ-type and ν-type cases - using μValid-mem-preserved
  -- Writing at frontier preserves memory at all BeforeFrontier locations
  validityWF-write-at-frontier {m} {alloc} {μ-type F} x loc s val loc-before (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-mem-preserved alloc wf x loc s s' loc-before mem-eq μv)
    where
      s' = write-loc s (AtStack (current-frame alloc) (next-slot alloc)) val
      mem-eq : ∀ loc' → BeforeFrontier alloc loc' → readLoc s' loc' ≡ readLoc s loc'
      mem-eq loc' bf = write-at-frontier-preserves-before s alloc loc' val bf

  validityWF-write-at-frontier {m} {alloc} {ν-type F} x loc s val loc-before (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-mem-preserved alloc wf x loc s s' loc-before mem-eq νv)
    where
      s' = write-loc s (AtStack (current-frame alloc) (next-slot alloc)) val
      mem-eq : ∀ loc' → BeforeFrontier alloc loc' → readLoc s' loc' ≡ readLoc s loc'
      mem-eq loc' bf = write-at-frontier-preserves-before s alloc loc' val bf

  -- Primitives: BeforeFrontier unchanged
  validityWF-write-at-frontier {m} {alloc} {Int} _ loc s val loc-before (valid-int-wf bf) =
    valid-int-wf bf
  validityWF-write-at-frontier {m} {alloc} {Float} _ loc s val loc-before (valid-float-wf bf) =
    valid-float-wf bf
  validityWF-write-at-frontier {m} {alloc} {Str} _ loc s val loc-before (valid-str-wf bf) =
    valid-str-wf bf
  validityWF-write-at-frontier {m} {alloc} {Buffer} _ loc s val loc-before (valid-buffer-wf bf) =
    valid-buffer-wf bf

  -- ValidAtWF is preserved when writing to suc-frontier location
  validityWF-write-at-suc-frontier : ∀ {m alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAtWF m alloc v loc s →
    ValidAtWF m alloc v loc (write-loc s (AtStack (current-frame alloc) (suc (next-slot alloc))) val)

  validityWF-write-at-suc-frontier {m} {alloc} {Unit} _ loc s val loc-before valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-write-at-suc-frontier {m} {alloc} {A * B} (a , b) loc s val loc-before
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} lmm fp sp fb sb slb fv sv) =
    valid-pair-wf lmm fp' sp' fb sb slb fv' sv'
    where
      fp' = trans (write-at-suc-frontier-preserves-before s alloc loc val loc-before) fp
      sp' = trans (write-at-suc-frontier-preserves-before s alloc (sucLoc loc) val slb) sp
      fv' = validityWF-write-at-suc-frontier a fl s val fb fv
      sv' = validityWF-write-at-suc-frontier b sl s val sb sv

  validityWF-write-at-suc-frontier {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s val loc-before
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} lmm ep cp eb slb ev bc) =
    valid-closure-wf bb lmm ep' cp' eb slb ev' bc
    where
      ep' = trans (write-at-suc-frontier-preserves-before s alloc loc val loc-before) ep
      cp' = trans (write-at-suc-frontier-preserves-before s alloc (sucLoc loc) val slb) cp
      ev' = validityWF-write-at-suc-frontier env el s val eb ev

  -- Kind-coerced closure
  validityWF-write-at-suc-frontier {m} {alloc} {A ⇒[ _ ] B} f loc s val loc-before (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-write-at-suc-frontier f loc s val loc-before cv)

  -- inl (any mode)
  validityWF-write-at-suc-frontier {m} {alloc} {A + B} .(sem-inl a) loc s val loc-before
    (valid-inl-wf {a = a} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inl-wf lmm pp' pb slb pv'
    where
      pp' = trans (write-at-suc-frontier-preserves-before s alloc (sucLoc loc) val slb) pp
      pv' = validityWF-write-at-suc-frontier a pl s val pb pv

  -- inr (any mode)
  validityWF-write-at-suc-frontier {m} {alloc} {A + B} .(sem-inr b) loc s val loc-before
    (valid-inr-wf {b = b} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inr-wf lmm pp' pb slb pv'
    where
      pp' = trans (write-at-suc-frontier-preserves-before s alloc (sucLoc loc) val slb) pp
      pv' = validityWF-write-at-suc-frontier b pl s val pb pv

  -- OCP-0003: μ-type and ν-type cases - using μValid-mem-preserved
  -- Writing at suc-frontier preserves memory at all BeforeFrontier locations
  validityWF-write-at-suc-frontier {m} {alloc} {μ-type F} x loc s val loc-before (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-mem-preserved alloc wf x loc s s' loc-before mem-eq μv)
    where
      s' = write-loc s (AtStack (current-frame alloc) (suc (next-slot alloc))) val
      mem-eq : ∀ loc' → BeforeFrontier alloc loc' → readLoc s' loc' ≡ readLoc s loc'
      mem-eq loc' bf = write-at-suc-frontier-preserves-before s alloc loc' val bf

  validityWF-write-at-suc-frontier {m} {alloc} {ν-type F} x loc s val loc-before (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-mem-preserved alloc wf x loc s s' loc-before mem-eq νv)
    where
      s' = write-loc s (AtStack (current-frame alloc) (suc (next-slot alloc))) val
      mem-eq : ∀ loc' → BeforeFrontier alloc loc' → readLoc s' loc' ≡ readLoc s loc'
      mem-eq loc' bf = write-at-suc-frontier-preserves-before s alloc loc' val bf

  -- Primitives: BeforeFrontier unchanged
  validityWF-write-at-suc-frontier {m} {alloc} {Int} _ loc s val loc-before (valid-int-wf bf) =
    valid-int-wf bf
  validityWF-write-at-suc-frontier {m} {alloc} {Float} _ loc s val loc-before (valid-float-wf bf) =
    valid-float-wf bf
  validityWF-write-at-suc-frontier {m} {alloc} {Str} _ loc s val loc-before (valid-str-wf bf) =
    valid-str-wf bf
  validityWF-write-at-suc-frontier {m} {alloc} {Buffer} _ loc s val loc-before (valid-buffer-wf bf) =
    valid-buffer-wf bf

  ------------------------------------------------------------------------
  -- Validity transport across allocation advancement
  --
  -- When the frontier advances (next-slot increases), ValidAtWF can be
  -- transported to the new alloc. This is needed when writing to fresh
  -- slots and then proving existing values are still valid.
  --
  -- Key insight: BeforeFrontier locations stay before the new frontier,
  -- so all constraints in ValidAtWF constructors are preserved.
  ------------------------------------------------------------------------

  validityWF-alloc-advance : ∀ {m alloc A} (v : ⟦ A ⟧) loc s (n : ℕ) →
    ValidAtWF m alloc v loc s →
    let alloc' = record alloc { next-slot = next-slot alloc +ℕ n }
    in ValidAtWF m alloc' v loc s

  validityWF-alloc-advance {m} {alloc} {Unit} tt loc s n valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-alloc-advance {m} {alloc} {A * B} (a , b) loc s n
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} lmm fp sp fb sb slb fv sv) =
    valid-pair-wf lmm fp sp fb' sb' slb' fv' sv'
    where
      fb' = stack-alloc-advances alloc n fl fb
      sb' = stack-alloc-advances alloc n sl sb
      slb' = stack-alloc-advances alloc n (sucLoc loc) slb
      fv' = validityWF-alloc-advance a fl s n fv
      sv' = validityWF-alloc-advance b sl s n sv

  validityWF-alloc-advance {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s n
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} lmm ep cp eb slb ev bc) =
    valid-closure-wf bb lmm ep cp eb' slb' ev' bc
    where
      eb' = stack-alloc-advances alloc n el eb
      slb' = stack-alloc-advances alloc n (sucLoc loc) slb
      ev' = validityWF-alloc-advance env el s n ev

  -- Kind-coerced closure
  validityWF-alloc-advance {m} {alloc} {A ⇒[ _ ] B} f loc s n (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-alloc-advance f loc s n cv)

  -- inl (any mode)
  validityWF-alloc-advance {m} {alloc} {A + B} .(sem-inl a) loc s n
    (valid-inl-wf {a = a} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inl-wf lmm pp pb' slb' pv'
    where
      pb' = stack-alloc-advances alloc n pl pb
      slb' = stack-alloc-advances alloc n (sucLoc loc) slb
      pv' = validityWF-alloc-advance a pl s n pv

  -- inr (any mode)
  validityWF-alloc-advance {m} {alloc} {A + B} .(sem-inr b) loc s n
    (valid-inr-wf {b = b} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inr-wf lmm pp pb' slb' pv'
    where
      pb' = stack-alloc-advances alloc n pl pb
      slb' = stack-alloc-advances alloc n (sucLoc loc) slb
      pv' = validityWF-alloc-advance b pl s n pv

  -- OCP-0003: μ-type and ν-type cases - using μValid-frontier-advance
  validityWF-alloc-advance {m} {alloc} {μ-type F} x loc s n (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-frontier-advance alloc alloc' wf x loc s refl slot-≤ ≤-refl μv)
    where
      open import Data.Nat.Properties using (≤-refl; m≤m+n)
      alloc' = record alloc { next-slot = next-slot alloc +ℕ n }
      slot-≤ : next-slot alloc ≤ next-slot alloc'
      slot-≤ = m≤m+n (next-slot alloc) n

  validityWF-alloc-advance {m} {alloc} {ν-type F} x loc s n (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-frontier-advance alloc alloc' wf x loc s refl slot-≤ ≤-refl νv)
    where
      open import Data.Nat.Properties using (≤-refl; m≤m+n)
      alloc' = record alloc { next-slot = next-slot alloc +ℕ n }
      slot-≤ : next-slot alloc ≤ next-slot alloc'
      slot-≤ = m≤m+n (next-slot alloc) n

  -- Primitives: advance BeforeFrontier
  validityWF-alloc-advance {m} {alloc} {Int} _ loc s n (valid-int-wf bf) =
    valid-int-wf (stack-alloc-advances alloc n loc bf)
  validityWF-alloc-advance {m} {alloc} {Float} _ loc s n (valid-float-wf bf) =
    valid-float-wf (stack-alloc-advances alloc n loc bf)
  validityWF-alloc-advance {m} {alloc} {Str} _ loc s n (valid-str-wf bf) =
    valid-str-wf (stack-alloc-advances alloc n loc bf)
  validityWF-alloc-advance {m} {alloc} {Buffer} _ loc s n (valid-buffer-wf bf) =
    valid-buffer-wf (stack-alloc-advances alloc n loc bf)

  ------------------------------------------------------------------------
  -- Validity transport across arbitrary frontier advancement
  --
  -- More general than validityWF-alloc-advance: works for any alloc'
  -- related by frontier-monotone properties (frame-preserved, slot/heap
  -- monotone). Used when transporting validity through IR execution.
  ------------------------------------------------------------------------

  validityWF-frontier-advance : ∀ {m alloc alloc' A} (v : ⟦ A ⟧) loc (s : LocState FS) →
    current-frame alloc' ≡ current-frame alloc →
    next-slot alloc ≤ next-slot alloc' →
    next-heap-ref alloc ≤ next-heap-ref alloc' →
    ValidAtWF m alloc v loc s →
    ValidAtWF m alloc' v loc s

  validityWF-frontier-advance {m} {alloc} {alloc'} {Unit} tt loc s cf-eq slot-≤ heap-≤ valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-frontier-advance {m} {alloc} {alloc'} {A * B} (a , b) loc s cf-eq slot-≤ heap-≤
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} lmm fp sp fb sb slb fv sv) =
    valid-pair-wf lmm fp sp fb' sb' slb' fv' sv'
    where
      fb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ fl fb
      sb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ sl sb
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      fv' = validityWF-frontier-advance a fl s cf-eq slot-≤ heap-≤ fv
      sv' = validityWF-frontier-advance b sl s cf-eq slot-≤ heap-≤ sv

  validityWF-frontier-advance {.Heap} {alloc} {alloc'} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s cf-eq slot-≤ heap-≤
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} lmm ep cp eb slb ev bc) =
    valid-closure-wf bb lmm ep cp eb' slb' ev' bc
    where
      eb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ el eb
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      ev' = validityWF-frontier-advance env el s cf-eq slot-≤ heap-≤ ev

  -- Kind-coerced closure
  validityWF-frontier-advance {m} {alloc} {alloc'} {A ⇒[ _ ] B} f loc s cf-eq slot-≤ heap-≤ (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-frontier-advance f loc s cf-eq slot-≤ heap-≤ cv)

  -- inl (any mode)
  validityWF-frontier-advance {m} {alloc} {alloc'} {A + B} .(sem-inl a) loc s cf-eq slot-≤ heap-≤
    (valid-inl-wf {a = a} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inl-wf lmm pp pb' slb' pv'
    where
      pb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ pl pb
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      pv' = validityWF-frontier-advance a pl s cf-eq slot-≤ heap-≤ pv

  -- inr (any mode)
  validityWF-frontier-advance {m} {alloc} {alloc'} {A + B} .(sem-inr b) loc s cf-eq slot-≤ heap-≤
    (valid-inr-wf {b = b} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inr-wf lmm pp pb' slb' pv'
    where
      pb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ pl pb
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      pv' = validityWF-frontier-advance b pl s cf-eq slot-≤ heap-≤ pv

  -- OCP-0003: μ-type and ν-type cases - using proven lemmas from MuValidity
  validityWF-frontier-advance {m} {alloc} {alloc'} {μ-type F} x loc s cf-eq slot-≤ heap-≤ (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-frontier-advance alloc alloc' wf x loc s cf-eq slot-≤ heap-≤ μv)

  validityWF-frontier-advance {m} {alloc} {alloc'} {ν-type F} x loc s cf-eq slot-≤ heap-≤ (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-frontier-advance alloc alloc' wf x loc s cf-eq slot-≤ heap-≤ νv)

  -- Primitives: advance BeforeFrontier
  validityWF-frontier-advance {m} {alloc} {alloc'} {Int} _ loc s cf-eq slot-≤ heap-≤ (valid-int-wf bf) =
    valid-int-wf (frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ loc bf)
  validityWF-frontier-advance {m} {alloc} {alloc'} {Float} _ loc s cf-eq slot-≤ heap-≤ (valid-float-wf bf) =
    valid-float-wf (frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ loc bf)
  validityWF-frontier-advance {m} {alloc} {alloc'} {Str} _ loc s cf-eq slot-≤ heap-≤ (valid-str-wf bf) =
    valid-str-wf (frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ loc bf)
  validityWF-frontier-advance {m} {alloc} {alloc'} {Buffer} _ loc s cf-eq slot-≤ heap-≤ (valid-buffer-wf bf) =
    valid-buffer-wf (frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ loc bf)

  ------------------------------------------------------------------------
  -- ValidAtWF transfer between allocation states with BeforeFrontier transfer
  --
  -- Transfer ValidAtWF m a₁ → ValidAtWF m a₂ using a general bf-transfer
  -- function. This is more general than validityWF-frontier-advance.
  --
  -- The proof applies bf-transfer to all sublocation BeforeFrontier proofs
  -- and recursively transfers nested validity.
  ------------------------------------------------------------------------

  validityWF-with-bf-transfer : ∀ {m A} (v : ⟦ A ⟧) loc (s : LocState FS)
    (a₁ a₂ : AllocState {FS})
    (bf-transfer : ∀ loc' → BeforeFrontier a₁ loc' → BeforeFrontier a₂ loc') →
    ValidAtWF m a₁ v loc s →
    ValidAtWF m a₂ v loc s

  validityWF-with-bf-transfer {m} {Unit} tt loc s a₁ a₂ bf valid-unit-wf = valid-unit-wf

  -- Pair (any mode)
  validityWF-with-bf-transfer {m} {A * B} (a , b) loc s a₁ a₂ bf
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} lmm fp sp fb sb slb fv sv) =
    valid-pair-wf lmm fp sp (bf fl fb) (bf sl sb) (bf (sucLoc loc) slb)
      (validityWF-with-bf-transfer a fl s a₁ a₂ bf fv)
      (validityWF-with-bf-transfer b sl s a₁ a₂ bf sv)

  -- Closure
  validityWF-with-bf-transfer {.Heap} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s a₁ a₂ bf
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} lmm ep cp eb slb ev bc) =
    valid-closure-wf bb lmm ep cp (bf el eb) (bf (sucLoc loc) slb)
      (validityWF-with-bf-transfer env el s a₁ a₂ bf ev) bc

  -- Kind-coerced closure
  validityWF-with-bf-transfer {m} {A ⇒[ _ ] B} f loc s a₁ a₂ bf (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-with-bf-transfer f loc s a₁ a₂ bf cv)

  -- inl (any mode)
  validityWF-with-bf-transfer {m} {A + B} .(sem-inl a) loc s a₁ a₂ bf
    (valid-inl-wf {a = a} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inl-wf lmm pp (bf pl pb) (bf (sucLoc loc) slb)
      (validityWF-with-bf-transfer a pl s a₁ a₂ bf pv)

  -- inr (any mode)
  validityWF-with-bf-transfer {m} {A + B} .(sem-inr b) loc s a₁ a₂ bf
    (valid-inr-wf {b = b} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inr-wf lmm pp (bf pl pb) (bf (sucLoc loc) slb)
      (validityWF-with-bf-transfer b pl s a₁ a₂ bf pv)

  -- OCP-0003: μ-type and ν-type cases - using proven lemmas from MuValidity
  validityWF-with-bf-transfer {m} {μ-type F} x loc s a₁ a₂ bf (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-bf-transfer a₁ a₂ wf x loc s bf μv)

  validityWF-with-bf-transfer {m} {ν-type F} x loc s a₁ a₂ bf (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-bf-transfer a₁ a₂ wf x loc s bf νv)

  -- Primitives: transfer BeforeFrontier
  validityWF-with-bf-transfer {m} {Int} _ loc s a₁ a₂ bf (valid-int-wf bfr) =
    valid-int-wf (bf loc bfr)
  validityWF-with-bf-transfer {m} {Float} _ loc s a₁ a₂ bf (valid-float-wf bfr) =
    valid-float-wf (bf loc bfr)
  validityWF-with-bf-transfer {m} {Str} _ loc s a₁ a₂ bf (valid-str-wf bfr) =
    valid-str-wf (bf loc bfr)
  validityWF-with-bf-transfer {m} {Buffer} _ loc s a₁ a₂ bf (valid-buffer-wf bfr) =
    valid-buffer-wf (bf loc bfr)

  ------------------------------------------------------------------------
  -- Validity preservation when memory at BeforeFrontier is preserved
  --
  -- Key lemma for IR execution: if memory at all BeforeFrontier locations
  -- is preserved (same readLoc values), then ValidAtWF is preserved.
  -- This is more precise than validityWF-mem-only (full memory equality).
  --
  -- The proof works because ValidAtWF at a BeforeFrontier location means
  -- all reachable sub-locations are also BeforeFrontier (structural).
  ------------------------------------------------------------------------

  validityWF-mem-preserved : ∀ {m alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    BeforeFrontier alloc loc →
    (∀ loc' → BeforeFrontier alloc loc' → readLoc s₂ loc' ≡ readLoc s₁ loc') →
    ValidAtWF m alloc v loc s₁ →
    ValidAtWF m alloc v loc s₂

  validityWF-mem-preserved {m} {alloc} {Unit} tt loc s₁ s₂ loc-before mem-eq valid-unit-wf =
    valid-unit-wf

  -- Pair (any mode)
  validityWF-mem-preserved {m} {alloc} {A * B} (a , b) loc s₁ s₂ loc-before mem-eq
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} lmm fp sp fb sb slb fv sv) =
    valid-pair-wf lmm fp' sp' fb sb slb fv' sv'
    where
      fp' = trans (mem-eq loc loc-before) fp
      sp' = trans (mem-eq (sucLoc loc) slb) sp
      fv' = validityWF-mem-preserved a fl s₁ s₂ fb mem-eq fv
      sv' = validityWF-mem-preserved b sl s₁ s₂ sb mem-eq sv

  validityWF-mem-preserved {.Heap} {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s₁ s₂ loc-before mem-eq
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} lmm ep cp eb slb ev bc) =
    valid-closure-wf bb lmm ep' cp' eb slb ev' bc
    where
      ep' = trans (mem-eq loc loc-before) ep
      cp' = trans (mem-eq (sucLoc loc) slb) cp
      ev' = validityWF-mem-preserved env el s₁ s₂ eb mem-eq ev

  -- Kind-coerced closure
  validityWF-mem-preserved {m} {alloc} {A ⇒[ _ ] B} f loc s₁ s₂ loc-before mem-eq (valid-coerce-kind-wf cv) =
    valid-coerce-kind-wf (validityWF-mem-preserved f loc s₁ s₂ loc-before mem-eq cv)

  -- inl (any mode)
  validityWF-mem-preserved {m} {alloc} {A + B} .(sem-inl a) loc s₁ s₂ loc-before mem-eq
    (valid-inl-wf {a = a} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inl-wf lmm pp' pb slb pv'
    where
      pp' = trans (mem-eq (sucLoc loc) slb) pp
      pv' = validityWF-mem-preserved a pl s₁ s₂ pb mem-eq pv

  -- inr (any mode)
  validityWF-mem-preserved {m} {alloc} {A + B} .(sem-inr b) loc s₁ s₂ loc-before mem-eq
    (valid-inr-wf {b = b} {payload-loc = pl} lmm pp pb slb pv) =
    valid-inr-wf lmm pp' pb slb pv'
    where
      pp' = trans (mem-eq (sucLoc loc) slb) pp
      pv' = validityWF-mem-preserved b pl s₁ s₂ pb mem-eq pv

  -- OCP-0003: μ-type and ν-type cases - using proven lemmas from MuValidity
  validityWF-mem-preserved {m} {alloc} {μ-type F} x loc s₁ s₂ loc-before mem-eq (valid-μ-wf wf .x μv) =
    valid-μ-wf wf x (μValid-mem-preserved alloc wf x loc s₁ s₂ loc-before mem-eq μv)

  validityWF-mem-preserved {m} {alloc} {ν-type F} x loc s₁ s₂ loc-before mem-eq (valid-ν-wf wf .x νv) =
    valid-ν-wf wf x (νValid-mem-preserved alloc wf x loc s₁ s₂ loc-before mem-eq νv)

  -- Primitives: BeforeFrontier unchanged
  validityWF-mem-preserved {m} {alloc} {Int} _ loc s₁ s₂ loc-before mem-eq (valid-int-wf bf) =
    valid-int-wf bf
  validityWF-mem-preserved {m} {alloc} {Float} _ loc s₁ s₂ loc-before mem-eq (valid-float-wf bf) =
    valid-float-wf bf
  validityWF-mem-preserved {m} {alloc} {Str} _ loc s₁ s₂ loc-before mem-eq (valid-str-wf bf) =
    valid-str-wf bf
  validityWF-mem-preserved {m} {alloc} {Buffer} _ loc s₁ s₂ loc-before mem-eq (valid-buffer-wf bf) =
    valid-buffer-wf bf

  ------------------------------------------------------------------------
  -- Validity preservation with excluded slot
  --
  -- Variant of validityWF-mem-preserved for when memory differs at one
  -- specific slot (the "gap slot"). This is used by pair's validity proof
  -- where backup-slot is modified but no sub-location uses it.
  --
  -- The key insight is that IR results have sub-locations that are either:
  --   1. Input1 locations at slots < start-frontier (inherited from input)
  --   2. Fresh allocations at slots ≥ suc start-frontier (allocated by IR)
  -- So slot = start-frontier is a "gap" never used by sub-locations.
  --
  -- Parameters:
  --   gap-slot : the slot to exclude from memory preservation
  --   gap-unused : proof that no sub-location is at the gap slot
  --   mem-eq : memory preserved for all OTHER BeforeFrontier locations
  ------------------------------------------------------------------------

  -- Helper: extract slot from AtStack location (for documentation, may be used later)
  private
    slot-of-loc : ValueLocation FS → ℕ
    slot-of-loc (AtStack _ k) = k
    slot-of-loc (AtDynamic _) = 0  -- dummy, heap locations don't use slot comparison

  ------------------------------------------------------------------------
  -- Validity preservation with gap slot
  --
  -- Key insight for pair validity: when IR f executes starting at
  -- next-slot = suc backup-slot, its result has sub-locations at:
  --   - Input1 locations: slots < backup-slot (inherited from input)
  --   - Fresh allocations: slots ≥ suc backup-slot (allocated by f)
  -- Therefore NO sub-location is at exactly backup-slot.
  --
  -- This means we can transfer validity even when memory differs at
  -- the gap slot, as long as memory agrees on all other BeforeFrontier
  -- locations.
  ------------------------------------------------------------------------

  -- Validity transfers when memory differs only at gap slot.
  -- The gap slot is NOT accessed because of disjoint slot ranges:
  --   - Input1 data is at slots < gap-slot
  --   - Fresh allocations are at slots ≥ suc gap-slot
  --   - gap-slot falls between these ranges
  validityWF-mem-preserved-excluding :
    ∀ {m A} (alloc : AllocState {FS}) (v : ⟦ A ⟧) (loc : ValueLocation FS)
      (gap-frame : Frame) (gap-slot : ℕ)
      (s₁ s₂ : LocState FS) →
    -- Location is before frontier
    BeforeFrontier alloc loc →
    -- Memory agrees on all BeforeFrontier locations except the gap
    (∀ (loc' : ValueLocation FS) →
       BeforeFrontier alloc loc' →
       loc' ≢ AtStack gap-frame gap-slot →
       readLoc s₁ loc' ≡ readLoc s₂ loc') →
    -- Validity transfers
    ValidAtWF m alloc v loc s₁ →
    ValidAtWF m alloc v loc s₂
  validityWF-mem-preserved-excluding = SMP.!!

  ------------------------------------------------------------------------
  -- Validity preservation with positive region bounds
  --
  -- Positive characterization: instead of excluding a gap slot, we specify
  -- the two disjoint regions where sub-locations can exist:
  --   1. Input1 region: [0, input-bound) - inherited from input value
  --   2. Fresh region: [fresh-start, frontier) - newly allocated by IR
  --
  -- The gap [input-bound, fresh-start) contains no sub-locations, so we
  -- don't need memory agreement there.
  --
  -- This is semantically equivalent to validityWF-mem-preserved-excluding
  -- but uses positive bounds rather than negative (≢) reasoning.
  --
  -- Plan: structural predicate `LocInRegions` + `LocsInRegions` captures
  -- the layout invariant that ValidAtWF alone doesn't encode. Each caller
  -- proves their value's sub-locations land in one of the four regions
  -- (input/fresh/heap/ancestor); the proof then dispatches the four
  -- region predicates per readLoc-transfer site.
  ------------------------------------------------------------------------

  -- Per-location predicate: this loc is in one of the four regions
  -- (input/fresh on current frame, ancestor, or heap).
  data LocInRegions (alloc : AllocState {FS}) (input-bound fresh-start : ℕ) :
       ValueLocation FS → Set where
    loc-in-input : ∀ {k} →
      k < input-bound →
      LocInRegions alloc input-bound fresh-start
        (AtStack (current-frame alloc) k)
    loc-in-fresh : ∀ {k} →
      fresh-start ≤ k → k < next-slot alloc →
      LocInRegions alloc input-bound fresh-start
        (AtStack (current-frame alloc) k)
    loc-in-anc : ∀ {f k} →
      current-frame alloc ≺ f →
      LocInRegions alloc input-bound fresh-start (AtStack f k)
    loc-in-heap : ∀ {hl} →
      LocInRegions alloc input-bound fresh-start (AtDynamic hl)

  -- Structural predicate: keyed by the ValidAtWF derivation so its
  -- existentials (fst-loc, snd-loc, env-loc, ...) are shared. Recurses
  -- structurally; at each pointer-read site we carry a LocInRegions
  -- witness for the loc being read.
  LocsInRegions : ∀ {m A} {v : ⟦ A ⟧} {loc s} {alloc : AllocState {FS}}
                  (input-bound fresh-start : ℕ) →
                  ValidAtWF m alloc v loc s → Set
  LocsInRegions {alloc = alloc} ib fs valid-unit-wf = ⊤
  LocsInRegions {alloc = alloc} ib fs
    (valid-pair-wf {pair-loc = pl} lmm fp sp fb sb slb fv sv) =
    LocInRegions alloc ib fs pl ×
    LocInRegions alloc ib fs (sucLoc pl) ×
    LocsInRegions ib fs fv ×
    LocsInRegions ib fs sv
  LocsInRegions {alloc = alloc} ib fs
    (valid-closure-wf bb {closure-loc = cl} lmm ep cp eb slb ev bc) =
    LocInRegions alloc ib fs cl ×
    LocInRegions alloc ib fs (sucLoc cl) ×
    LocsInRegions ib fs ev
  LocsInRegions ib fs (valid-coerce-kind-wf cv) = LocsInRegions ib fs cv
  LocsInRegions {alloc = alloc} ib fs
    (valid-inl-wf {sum-loc = sl} lmm pp pb slb pv) =
    LocInRegions alloc ib fs (sucLoc sl) ×
    LocsInRegions ib fs pv
  LocsInRegions {alloc = alloc} ib fs
    (valid-inr-wf {sum-loc = sl} lmm pp pb slb pv) =
    LocInRegions alloc ib fs (sucLoc sl) ×
    LocsInRegions ib fs pv
  LocsInRegions ib fs (valid-μ-wf wf x μv) = ⊤    -- handled via μ-stub
  LocsInRegions ib fs (valid-ν-wf wf x νv) = ⊤    -- handled via ν-stub
  LocsInRegions ib fs (valid-int-wf bf)    = ⊤
  LocsInRegions ib fs (valid-float-wf bf)  = ⊤
  LocsInRegions ib fs (valid-str-wf bf)    = ⊤
  LocsInRegions ib fs (valid-buffer-wf bf) = ⊤

  -- Helper: derive a mem-eq at a particular loc from the four region
  -- predicates and a LocInRegions witness.
  loc-mem-eq-from-regions :
    ∀ {alloc : AllocState {FS}} {input-bound fresh-start s₁ s₂ loc} →
    (∀ slot → slot < input-bound →
      readLoc s₂ (AtStack (current-frame alloc) slot) ≡
      readLoc s₁ (AtStack (current-frame alloc) slot)) →
    (∀ slot → fresh-start ≤ slot → slot < next-slot alloc →
      readLoc s₂ (AtStack (current-frame alloc) slot) ≡
      readLoc s₁ (AtStack (current-frame alloc) slot)) →
    (∀ h → readLoc s₂ (AtDynamic h) ≡ readLoc s₁ (AtDynamic h)) →
    (∀ f k → current-frame alloc ≺ f →
      readLoc s₂ (AtStack f k) ≡ readLoc s₁ (AtStack f k)) →
    LocInRegions alloc input-bound fresh-start loc →
    readLoc s₂ loc ≡ readLoc s₁ loc
  loc-mem-eq-from-regions ir fr hr ar (loc-in-input {k} k<ib)         = ir k k<ib
  loc-mem-eq-from-regions ir fr hr ar (loc-in-fresh {k} fs≤k k<next)   = fr k fs≤k k<next
  loc-mem-eq-from-regions ir fr hr ar (loc-in-anc {f} {k} cf≺f)        = ar f k cf≺f
  loc-mem-eq-from-regions ir fr hr ar (loc-in-heap {hl})               = hr hl

  -- TEMP: μ/ν cases deferred. The same regional reasoning applies but
  -- requires defining μValid-mem-preserved-in-regions / νValid-mem-preserved-in-regions
  -- which are sister lemmas in MuValidity. Tracked separately.
  postulate
    μ-validity-in-regions-stub : ∀ {alloc F} {wf : WellFormedF F} {x loc s₁ s₂}
                                   {input-bound fresh-start : ℕ} →
      μValid alloc wf x loc s₁ →
      μValid alloc wf x loc s₂

    ν-validity-in-regions-stub : ∀ {alloc F} {wf : WellFormedF F} {x loc s₁ s₂}
                                   {input-bound fresh-start : ℕ} →
      νValid alloc wf x loc s₁ →
      νValid alloc wf x loc s₂

  -- STRONG version: requires an additional LocsInRegions hypothesis that
  -- witnesses the value's sub-locations all land in input/fresh/heap/anc
  -- (never in the gap [input-bound, fresh-start) on current frame).
  -- This is the version that can be proven without postulates (modulo μ/ν
  -- stubs, which require sister lemmas in MuValidity).
  --
  -- The original `validityWF-mem-preserved-in-regions` (below, still
  -- postulated as SMP.!!) is the unsafe version without this hypothesis.
  -- Callers can migrate to the strong version as needed; until then the
  -- unsafe version remains for backward compatibility.
  validityWF-mem-preserved-in-regions-strong :
    ∀ {m A} (alloc : AllocState {FS}) (v : ⟦ A ⟧) (loc : ValueLocation FS)
      (input-bound fresh-start : ℕ)
      (s₁ s₂ : LocState FS) →
    BeforeFrontier alloc loc →
    input-bound ≤ fresh-start →
    fresh-start ≤ next-slot alloc →
    (∀ slot → slot < input-bound →
      readLoc s₂ (AtStack (current-frame alloc) slot) ≡
      readLoc s₁ (AtStack (current-frame alloc) slot)) →
    (∀ slot → fresh-start ≤ slot → slot < next-slot alloc →
      readLoc s₂ (AtStack (current-frame alloc) slot) ≡
      readLoc s₁ (AtStack (current-frame alloc) slot)) →
    (∀ h → readLoc s₂ (AtDynamic h) ≡ readLoc s₁ (AtDynamic h)) →
    (∀ f k → current-frame alloc ≺ f →
      readLoc s₂ (AtStack f k) ≡ readLoc s₁ (AtStack f k)) →
    (vw : ValidAtWF m alloc v loc s₁) → LocsInRegions input-bound fresh-start vw →
    ValidAtWF m alloc v loc s₂

  validityWF-mem-preserved-in-regions-strong alloc tt loc ib fs s₁ s₂
    loc-before _ _ _ _ _ _ valid-unit-wf _ = valid-unit-wf

  validityWF-mem-preserved-in-regions-strong alloc (a , b) loc ib fs s₁ s₂
    loc-before ib≤fs fs≤next ir fr hr ar
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} lmm fp sp fb sb slb fv sv)
    (pl-ir , spl-ir , flocs , slocs) =
    valid-pair-wf lmm fp' sp' fb sb slb fv' sv'
    where
      pl-eq  = loc-mem-eq-from-regions ir fr hr ar pl-ir
      spl-eq = loc-mem-eq-from-regions ir fr hr ar spl-ir
      fp'    = trans pl-eq fp
      sp'    = trans spl-eq sp
      fv'    = validityWF-mem-preserved-in-regions-strong alloc a fl ib fs s₁ s₂
                 fb ib≤fs fs≤next ir fr hr ar fv flocs
      sv'    = validityWF-mem-preserved-in-regions-strong alloc b sl ib fs s₁ s₂
                 sb ib≤fs fs≤next ir fr hr ar sv slocs

  validityWF-mem-preserved-in-regions-strong alloc
    .(λ arg → eval body (pair env arg)) loc ib fs s₁ s₂
    loc-before ib≤fs fs≤next ir fr hr ar
    (valid-closure-wf {body = body} {env = env} bb
      {closure-loc = clo} {env-loc = el} lmm ep cp eb slb ev bc)
    (cl-ir , scl-ir , elocs) =
    valid-closure-wf bb lmm ep' cp' eb slb ev' bc
    where
      cl-eq  = loc-mem-eq-from-regions ir fr hr ar cl-ir
      scl-eq = loc-mem-eq-from-regions ir fr hr ar scl-ir
      ep'    = trans cl-eq ep
      cp'    = trans scl-eq cp
      ev'    = validityWF-mem-preserved-in-regions-strong alloc env el ib fs s₁ s₂
                 eb ib≤fs fs≤next ir fr hr ar ev elocs

  validityWF-mem-preserved-in-regions-strong alloc f loc ib fs s₁ s₂
    loc-before ib≤fs fs≤next ir fr hr ar (valid-coerce-kind-wf cv) flocs =
    valid-coerce-kind-wf
      (validityWF-mem-preserved-in-regions-strong alloc f loc ib fs s₁ s₂
         loc-before ib≤fs fs≤next ir fr hr ar cv flocs)

  validityWF-mem-preserved-in-regions-strong alloc .(sem-inl a) loc ib fs s₁ s₂
    loc-before ib≤fs fs≤next ir fr hr ar
    (valid-inl-wf {a = a} {payload-loc = pl} lmm pp pb slb pv)
    (sl-ir , plocs) =
    valid-inl-wf lmm pp' pb slb pv'
    where
      sl-eq = loc-mem-eq-from-regions ir fr hr ar sl-ir
      pp'   = trans sl-eq pp
      pv'   = validityWF-mem-preserved-in-regions-strong alloc a pl ib fs s₁ s₂
                pb ib≤fs fs≤next ir fr hr ar pv plocs

  validityWF-mem-preserved-in-regions-strong alloc .(sem-inr b) loc ib fs s₁ s₂
    loc-before ib≤fs fs≤next ir fr hr ar
    (valid-inr-wf {b = b} {payload-loc = pl} lmm pp pb slb pv)
    (sl-ir , plocs) =
    valid-inr-wf lmm pp' pb slb pv'
    where
      sl-eq = loc-mem-eq-from-regions ir fr hr ar sl-ir
      pp'   = trans sl-eq pp
      pv'   = validityWF-mem-preserved-in-regions-strong alloc b pl ib fs s₁ s₂
                pb ib≤fs fs≤next ir fr hr ar pv plocs

  -- μ/ν: defer to the inline stubs above (parallel lemma needed in MuValidity).
  validityWF-mem-preserved-in-regions-strong alloc x loc ib fs s₁ s₂
    loc-before _ _ _ _ _ _ (valid-μ-wf wf .x μv) _ =
    valid-μ-wf wf x (μ-validity-in-regions-stub {input-bound = ib} {fresh-start = fs} μv)
  validityWF-mem-preserved-in-regions-strong alloc x loc ib fs s₁ s₂
    loc-before _ _ _ _ _ _ (valid-ν-wf wf .x νv) _ =
    valid-ν-wf wf x (ν-validity-in-regions-stub {input-bound = ib} {fresh-start = fs} νv)

  -- Primitives: BeforeFrontier alone is sufficient.
  validityWF-mem-preserved-in-regions-strong alloc _ loc ib fs s₁ s₂
    loc-before _ _ _ _ _ _ (valid-int-wf bf) _ = valid-int-wf bf
  validityWF-mem-preserved-in-regions-strong alloc _ loc ib fs s₁ s₂
    loc-before _ _ _ _ _ _ (valid-float-wf bf) _ = valid-float-wf bf
  validityWF-mem-preserved-in-regions-strong alloc _ loc ib fs s₁ s₂
    loc-before _ _ _ _ _ _ (valid-str-wf bf) _ = valid-str-wf bf
  validityWF-mem-preserved-in-regions-strong alloc _ loc ib fs s₁ s₂
    loc-before _ _ _ _ _ _ (valid-buffer-wf bf) _ = valid-buffer-wf bf

  -- UNSAFE version (still postulated): no LocsInRegions hypothesis.
  -- Existing callers (PairWF2's 5 sites) use this. Migrate to the strong
  -- version above (taking a LocsInRegions witness) to discharge this.
  validityWF-mem-preserved-in-regions :
    ∀ {m A} (alloc : AllocState {FS}) (v : ⟦ A ⟧) (loc : ValueLocation FS)
      (input-bound fresh-start : ℕ)
      (s₁ s₂ : LocState FS) →
    BeforeFrontier alloc loc →
    input-bound ≤ fresh-start →
    fresh-start ≤ next-slot alloc →
    (∀ slot → slot < input-bound →
      readLoc s₂ (AtStack (current-frame alloc) slot) ≡
      readLoc s₁ (AtStack (current-frame alloc) slot)) →
    (∀ slot → fresh-start ≤ slot → slot < next-slot alloc →
      readLoc s₂ (AtStack (current-frame alloc) slot) ≡
      readLoc s₁ (AtStack (current-frame alloc) slot)) →
    (∀ h → readLoc s₂ (AtDynamic h) ≡ readLoc s₁ (AtDynamic h)) →
    (∀ f k → current-frame alloc ≺ f →
      readLoc s₂ (AtStack f k) ≡ readLoc s₁ (AtStack f k)) →
    ValidAtWF m alloc v loc s₁ →
    ValidAtWF m alloc v loc s₂
  validityWF-mem-preserved-in-regions = SMP.!!

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
    ValidAtWF m alloc v loc s →
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
    ValidAtWF m alloc v loc s →
    -- Trace only writes at slots ≥ next-slot alloc
    TraceWritesAbove (next-slot alloc) trace →
    TraceNoHeapWrites trace →
    -- Validity preserved after trace
    ValidAtWF m alloc v loc (proj₁ (exec-trace trace s alloc))
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

  -- Plan 0.14: now a trivial accessor — the producer carried the
  -- consequence directly.
  irresult-mem-preserved : ∀ {m A B} {ir : IR A B} {x : ⟦ A ⟧}
    {s : LocState FS} {alloc : AllocState {FS}}
    (result : IRResultAWF m ir x s alloc) →
    (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    readLoc (IRResultAWF.final-state result) loc ≡ readLoc s loc
  irresult-mem-preserved = IRResultAWF.mem-preserved-before

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