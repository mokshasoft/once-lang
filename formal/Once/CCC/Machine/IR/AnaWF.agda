------------------------------------------------------------------------
-- Once.CCC.Machine.IR.AnaWF
--
-- Anamorphism handler for lazy corecursive production.
--
-- OCP-0003: Ana (anamorphism) is fundamentally different from Cata/Para.
-- While those eagerly consume μ-types, Ana lazily produces ν-types.
--
-- Implementation: ν-types are represented as thunks containing:
--   - coalg-ref: reference to the coalgebra IR
--   - seed: the current seed value
--
-- When observed via Out, the thunk is forced by applying coalg to seed,
-- producing an F-layer with new seeds for recursive positions.
--
------------------------------------------------------------------------
-- Star-Based Proof Architecture (per lessons-learned.md)
--
-- See RecCoreWF.agda for full documentation.
-- Semantic correctness uses the same documented postulate approach.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.AnaWF where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; m≤n+m)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.Type using (Functor)
open import Once.Functor.Translate using (WellFormedF)
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import SMPrimitives for trace predicates
import Once.CCC.Machine.SMPrimitives as SMP

-- Import consolidated postulates (shared with RecCoreWF, ParaWF, SumRecWF)
import Once.CCC.Machine.IR.RecSchemePostulates as RSP

------------------------------------------------------------------------
-- ν-Type Representation
--
-- ν-types (final coalgebras) are represented as lazy thunks:
--
-- [thunk-slot] = { coalg-ref, seed }
--      ↑
--   νF pointer
--
-- The thunk contains:
--   - coalg-ref: pointer to the coalgebra closure/code
--   - seed: current seed value of type A
--
-- When Out observes the ν-value:
--   1. Load coalg and seed from thunk
--   2. Apply coalg to seed: A → F(A)
--   3. For each recursive position in F(A):
--      - Create new thunk with same coalg and new sub-seed
--   4. Return F(νF) with thunks at recursive positions
------------------------------------------------------------------------

-- | Thunk slot layout
thunk-coalg-offset : ℕ
thunk-coalg-offset = 0

thunk-seed-offset : ℕ
thunk-seed-offset = 1

------------------------------------------------------------------------
-- AnaWF Implementation
--
-- Ana creates a thunk representing the ν-value.
-- No recursion needed - we just package coalg + seed.
------------------------------------------------------------------------

module AnaWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS
  open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; n≤1+n; n<1+n; +-comm; +-monoʳ-≤)
  open import Relation.Binary.PropositionalEquality using (subst)

  -- Open SMPrimitives modules
  open SMP.TracePrimitives {FS}
  open SMP.RecSchemeSemantics {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc; RecDispatcherWF;
           validityWF-mem-only; validityWF-frontier-advance;
           validityWF-alloc-advance; mem-preserved-from-tnhw;
           mk-IRResultAWF-via-bump)

  ------------------------------------------------------------------------
  -- Semantic Correctness Postulate (from consolidated module)
  --
  -- See RecSchemePostulates.agda for documentation.
  ------------------------------------------------------------------------
  open RSP.RecSchemePostulatesImpl {FS} program-bound public
    using (rec-scheme-semantic)

  ------------------------------------------------------------------------
  -- Arithmetic helpers for stack requirement bounds
  ------------------------------------------------------------------------

  private
    open import Data.Nat.Properties using (m≤n+m)

    -- suc n ≤ n + 2: By +-comm, n + 2 = 2 + n = suc (suc n), and suc n ≤ suc (suc n) by n≤1+n
    suc-≤-plus-2 : ∀ n → suc n ≤ n +ℕ 2
    suc-≤-plus-2 n = subst (suc n ≤_) (+-comm 2 n) (n≤1+n (suc n))

    -- 2 ≤ m + 2: using m≤n+m
    2≤m+2 : ∀ m → 2 ≤ m +ℕ 2
    2≤m+2 m = m≤n+m 2 m

    -- Any stack requirement ≥ pair-slots = 2, so suc n ≤ n + req
    suc-≤-plus-req : ∀ n m → suc n ≤ n +ℕ (m +ℕ pair-slots)
    suc-≤-plus-req n m = ≤-trans (suc-≤-plus-2 n) (+-monoʳ-≤ n (2≤m+2 m))

  -- Memory preservation helper for recursion scheme traces
  rec-scheme-mem-preserved : ∀ {n : ℕ} (s : LocState FS) (alloc : AllocState {FS}) →
    n ≡ next-slot alloc →
    halted s ≡ false →
    ∀ loc → BeforeFrontier alloc loc →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc)) loc ≡
    readLoc s loc
  rec-scheme-mem-preserved {n} s alloc refl not-halted (AtStack f k) (stack-before refl k<n) =
    rec-scheme-preserves-slot-below-3 n k s alloc not-halted k<n
  rec-scheme-mem-preserved {n} s alloc refl not-halted (AtStack f k) (stack-ancestor cf≺f _) =
    rec-scheme-preserves-ancestor-3 n s alloc f k not-halted (λ eq → ≺⇒≢ cf≺f (sym eq))
  rec-scheme-mem-preserved {n} s alloc refl not-halted (AtDynamic hl) (heap-before _) =
    rec-scheme-preserves-heap-3 n s alloc hl not-halted

  -- Plan 0.14: rec-scheme-mem-preserved variant for the 4-instr trace.
  -- Combines the 4-instr building blocks from SMP.RecSchemeSemantics.
  rec-scheme-mem-preserved-4 : ∀ {n : ℕ} (s : LocState FS) (alloc : AllocState {FS}) →
    n ≡ next-slot alloc →
    halted s ≡ false →
    ∀ loc → BeforeFrontier alloc loc →
    readLoc (proj₁ (exec-trace (rec-scheme-trace-4 n) s alloc)) loc ≡
    readLoc s loc
  rec-scheme-mem-preserved-4 {n} s alloc refl not-halted (AtStack f k) (stack-before refl k<n) =
    rec-scheme-preserves-slot-below-4 n k s alloc not-halted k<n
  rec-scheme-mem-preserved-4 {n} s alloc refl not-halted (AtStack f k) (stack-ancestor cf≺f _) =
    rec-scheme-preserves-ancestor-4 n s alloc f k not-halted (λ eq → ≺⇒≢ cf≺f (sym eq))
  rec-scheme-mem-preserved-4 {n} s alloc refl not-halted (AtDynamic hl) (heap-before _) =
    rec-scheme-preserves-heap-4 n s alloc hl not-halted

  ------------------------------------------------------------------------
  -- Ana: Anamorphism (unfold to build ν-type)
  --
  -- Semantically: ana coalg x produces the infinite structure νF
  -- where each observation (Out) reveals one F-layer.
  --
  -- Implementation: Store seed in a thunk slot. The coalgebra is
  -- implicitly associated with the ν-type representation.
  --
  -- The lazy semantics means:
  --   1. Ana just stores the seed
  --   2. Out forces computation by applying coalgebra
  --
  -- Productivity: Guaranteed by IR totality of coalgebra.
  -- Each Out application terminates, producing one F-layer.
  ------------------------------------------------------------------------

  -- | run-ana-core: anamorphism handler (lazy thunk creation)
  run-ana-core : ∀ {F A}
    → (wf : WellFormedF F)
    → (coalg : IR A (⟦ F ⟧T A))
    → (rec-wf : RecDispatcherWF (ir-size (Ana wf coalg)))
    → (mIn : AllocMode)
    → (x : ⟦ A ⟧)
    → (input-loc : ValueLocation FS)
    → (s : LocState FS)
    → (alloc : AllocState {FS})
    → ValidAtWF mIn alloc x input-loc s
    → BeforeFrontier alloc input-loc
    → halted s ≡ false
    → readReg (regs s) Input1 ≡ SV-Ptr input-loc
    → ∃[ mOut ] IRResultAWF mOut (Ana wf coalg) x s alloc
  run-ana-core {F} {A} wf coalg rec-wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    Heap ,
    mk-IRResultAWF-via-bump
      s' alloc' ana-trace (mkBump 1 0) refl
      SMP.!!
      refl
      (let raw = rec-scheme-alloc-correct-4 result-slot s alloc not-halted
           arith : next-slot alloc +ℕ 1 ≡ suc (next-slot alloc)
           arith = +-comm (next-slot alloc) 1
       in trans raw (cong (λ k → record alloc { next-slot = k }) arith))
      (at-loc result-loc result-valid result-bf rax-eq result-valid result-bf)
      not-halted'
      (mem-preserved-from-tnhw alloc ana-trace s s' refl trace-wa tt)
      SMP.!!
      (exec-trace-preserves-halted-WF ana-trace)
      _
      (record
        { max-slot-written = next-slot alloc'
        ; stack-budget = ir-stack-requirement (Ana wf coalg)
        ; bump-fits-stack-budget = ≤-trans (s≤s z≤n) (m≤n+m pair-slots (ir-stack-requirement coalg))
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = reclaim-bound
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = trace-wa
        ; trace-slot-reads-above = tt
        ; trace-writes-below = trace-wb
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (Ana wf coalg)
        ; scratch-bounded = m≤m+n (suc (next-slot alloc)) (ir-scratch-requirement (Ana wf coalg))
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      -- Ana stores seed at frontier slot as thunk representation
      result-slot = next-slot alloc
      result-loc = AtStack (current-frame alloc) result-slot

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = suc (next-slot alloc) }

      -- Trace: alloc-stack the result slot, store input (seed) there,
      -- return slot address. Plan 0.14: instr-alloc-stack 1 at the
      -- start makes runtime alloc match alloc'.
      ana-trace : AbstractTrace
      ana-trace = rec-scheme-trace-4 result-slot

      s' : LocState FS
      s' = proj₁ (exec-trace ana-trace s alloc)

      slot-mono : next-slot alloc ≤ next-slot alloc'
      slot-mono = n≤1+n (next-slot alloc)

      result-bf : BeforeFrontier alloc' result-loc
      result-bf = stack-before refl (n<1+n (next-slot alloc))

      -- Result validity: Ana produces νF from seed (postulated)
      result-valid : ValidAtWF Heap alloc' (eval (Ana wf coalg) x) result-loc s'
      result-valid = rec-scheme-semantic (Ana wf coalg) alloc' x result-loc s'

      -- Stack requirement bound: suc n ≤ n + ir-stack-requirement (Ana wf coalg)
      -- ir-stack-requirement (Ana _ coalg) = ir-stack-requirement coalg + pair-slots
      n = next-slot alloc
      reclaim-bound : suc n ≤ n +ℕ ir-stack-requirement (Ana wf coalg)
      reclaim-bound = suc-≤-plus-req n (ir-stack-requirement coalg)

      rax-eq : readReg (regs s') Output ≡ SV-Ptr result-loc
      rax-eq = rec-scheme-output-is-slot-4 result-slot s alloc not-halted

      not-halted' : halted s' ≡ false
      not-halted' = rec-scheme-preserves-halted-4 result-slot s alloc not-halted

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc bf = rec-scheme-mem-preserved-4 s alloc refl not-halted loc bf

      trace-wa : SMP.TraceWritesAbove (next-slot alloc) ana-trace
      trace-wa = ≤-refl , tt

      trace-wb : SMP.TraceWritesBelow (suc (next-slot alloc)) ana-trace
      trace-wb = n<1+n (next-slot alloc) , tt

      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        _
      frontier-stable s'' input-loc' _ _ _ = inj₂ (inj₂ tt)

------------------------------------------------------------------------
-- Summary
--
-- AnaWF provides:
--   1. Thunk representation for ν-types (coalg-ref + seed)
--   2. run-ana-core: anamorphism handler implementation
--
-- Key difference from Cata/Para:
--   - Cata/Para: eagerly consume μ-types via structural recursion
--   - Ana: lazily produce ν-types by creating thunks
--
-- The thunk representation enables:
--   - Infinite structures (productivity, not termination)
--   - Lazy evaluation (compute on demand via Out)
--   - Sharing (same coalg + different seeds)
--
-- When Out observes a ν-value:
--   1. Extract coalg and seed from thunk
--   2. Execute coalg on seed to get F(A)
--   3. For each recursive A in F(A), create new thunk
--   4. Return F(νF) with thunks at recursive positions
--
-- The implementation provides:
--   - Algorithmic structure (traces, state computation)
--   - Proven properties: trace bounds, halted preservation, memory preservation
--   - Semantic correctness via documented postulate (rec-scheme-semantic)
------------------------------------------------------------------------
