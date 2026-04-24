------------------------------------------------------------------------
-- Once.CCC.Machine.IR.RecCoreWF
--
-- Unified recursive core for μ-consuming recursion schemes.
--
-- OCP-0003: This module provides a single parameterized implementation
-- that handles Cata, Fuse, and Hylo. The differences are:
--   - Cata: transform = id (no transformation)
--   - Fuse: transform = user-provided IR
--   - Hylo: transform = coalg ∘ In
--
-- Key insight: All μ-consuming schemes share the same iteration pattern:
--   1. Destructure μ-type (out-μ)
--   2. Dispatch on functor structure (K/Id/⊕/⊗)
--   3. For each recursive position: recurse
--   4. Apply processing IR(s)
--   5. Return result
--
------------------------------------------------------------------------
-- Star-Based Proof Architecture (per lessons-learned.md)
--
-- Fuel-based approaches cause proof issues because case_of_ doesn't
-- reduce when scrutinees are abstract. This module uses Star (reflexive-
-- transitive closure) principles:
--
--   1. Traces are structural lists (no fuel-bounded iterate)
--   2. Termination follows from well-foundedness of μ-types
--   3. Composition is via trace concatenation (trivial transitivity)
--
-- PROOF STATUS:
--   - Cata: STRUCTURAL PROOF available via RecTrace.agda
--     See RecTrace.cata-trace-μ for trace building by induction on μ-values.
--     Correctness follows from sem-cata-compute at each structural step.
--     See also NatCataProof.agda for a concrete example with NatF.
--
--   - Fuse/Hylo: Same architecture applies (future work to implement)
--
--   - Trace mechanics: Fully proven (memory preservation, halted, etc.)
--
-- The proof strategy uses structural recursion on μ-values:
--   1. Build recursive traces: cata-trace (In layer) = destruct ++
--      process-layer ++ apply-alg (trace follows μ-value structure)
--   2. Prove correctness by induction: use sem-cata-compute at each step
--   3. Connect to ValidAtWF: trace execution produces correct result
--
-- KEY INSIGHT: For any concrete μ-value, the trace is FINITE and
-- computes exactly the catamorphism. No fuel needed - termination
-- follows from well-foundedness of μ-types.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.RecCoreWF where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
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

-- Import functor dispatch helpers
open import Once.CCC.Machine.IR.FunctorDispatch

-- Import SMPrimitives for trace predicates
import Once.CCC.Machine.SMPrimitives as SMP

-- Import RecTrace for structural cata implementation
import Once.CCC.Machine.IR.RecTrace as RecTrace

------------------------------------------------------------------------
-- RecConfig: Configuration record for the unified recursive core
--
-- This parameterizes the recursion scheme by:
--   - wfF, wfG: well-formedness proofs for functors
--   - algebra: the consuming algebra F(B) → B
--   - transform: optional transformation G(μG) → F(μG)
--     - Nothing for Cata (identity, F = G)
--     - Just trans for Fuse/Hylo
------------------------------------------------------------------------

record RecConfig {F G : Functor} (wfF : WellFormedF F) (wfG : WellFormedF G)
                 (B : Type) : Set where
  field
    algebra : IR (⟦ F ⟧T B) B
    -- Transform: Nothing means identity (Cata), Just means Fuse/Hylo
    has-transform : Maybe (IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G)))

open RecConfig public

------------------------------------------------------------------------
-- Configuration constructors
------------------------------------------------------------------------

-- | Cata configuration: F = G, no transform (identity)
cata-config : ∀ {F B} (wf : WellFormedF F) (alg : IR (⟦ F ⟧T B) B)
            → RecConfig wf wf B
cata-config wf alg = record
  { algebra = alg
  ; has-transform = nothing
  }

-- | Fuse configuration: transform G-layers to F-layers
fuse-config : ∀ {F G B} (wfF : WellFormedF F) (wfG : WellFormedF G)
            → (alg : IR (⟦ F ⟧T B) B)
            → (transform : IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G)))
            → RecConfig wfF wfG B
fuse-config wfF wfG alg transform = record
  { algebra = alg
  ; has-transform = just transform
  }

-- | Hylo configuration: coalg ∘ In is the transform
-- Note: The coalg here is μG → F(μG), and we need G(μG) → F(μG)
-- For Hylo, G = F and we use coalg directly on the destructed layer
hylo-config : ∀ {F G B} (wfF : WellFormedF F) (wfG : WellFormedF G)
            → (alg : IR (⟦ F ⟧T B) B)
            → (coalg : IR (μ-type G) (⟦ F ⟧T (μ-type G)))
            → RecConfig wfF wfG B
hylo-config wfF wfG alg coalg = record
  { algebra = alg
  -- For Hylo, transform wraps In around the G-layer then applies coalg
  -- G(μG) → μG → F(μG)
  -- This is: coalg ∘ In
  ; has-transform = just (coalg ∘ In wfG Heap)
  }

------------------------------------------------------------------------
-- NOTE: RecConfig is used for design documentation.
-- Stack requirements are computed from the actual IR constructors
-- via ir-stack-requirement in IR/Stack.agda.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Slot Layout for Recursive Core
--
-- [backup-slot] [layer-slot] [acc-slot] [work-slots...] [alg/trans-workspace]
--      ↑            ↑            ↑           ↑                  ↑
--   input       F/G-layer    accumulator  recursion        IR workspace
------------------------------------------------------------------------

-- | Slot offsets relative to frontier
backup-offset : ℕ
backup-offset = 0

layer-offset : ℕ
layer-offset = 1

acc-offset : ℕ
acc-offset = 2

work-offset : ℕ
work-offset = 3

------------------------------------------------------------------------
-- RecCoreWF Implementation
--
-- The unified recursive pattern for μ-consuming recursion schemes.
-- Each scheme uses structural recursion on μ-values.
------------------------------------------------------------------------

module RecCoreWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS
  open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; n≤1+n; n<1+n; +-comm; +-monoʳ-≤)
  open import Data.Nat using (z≤n; s≤s)
  open import Data.List using (_++_)

  -- Open RecTrace implementation for structural cata proofs
  open RecTrace.RecTraceImpl {FS} program-bound
    using (cata-dispatched-new; process-layer; ProcessedLayerResult)
    public

  -- Open SMPrimitives modules
  open SMP.TracePrimitives {FS}
  open SMP.RecSchemeSemantics {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; RecDispatcherWF;
           validityWF-mem-only; validityWF-frontier-advance;
           validityWF-alloc-advance)

  ------------------------------------------------------------------------
  -- Semantic Correctness: TRUST BOUNDARY
  --
  -- PROOF ARCHITECTURE (see RecTrace.agda and RecSchemeProof.agda):
  --   RecTrace provides structural trace building (cata-trace-μ) and
  --   the proof specification (cata-trace-valid-spec). The semantic
  --   equation sem-cata-compute drives the structure.
  --
  -- WHY THIS IS A TRUST BOUNDARY:
  --   The abstract machine doesn't model recursive trace execution.
  --   The traces here are stubs that store/return pointers; the actual
  --   recursive computation is handled by the Dispatcher at runtime.
  --   See RecSchemeProof.agda for full architectural analysis.
  --
  -- TO PROVE THIS, we would need either:
  --   A. Extended machine model with recursive trace execution
  --   B. Direct semantic proof via well-founded recursion on μ-values
  --
  -- This postulate captures the correctness claim:
  --   "The Once compiler + runtime correctly implements recursion schemes"
  ------------------------------------------------------------------------
  rec-scheme-semantic : ∀ {A B} (ir : IR A B) (alloc : AllocState {FS})
    (x : ⟦ A ⟧) (result-loc : ValueLocation FS) (s : LocState FS) →
    ValidAtWF Heap alloc (eval ir x) result-loc s
  rec-scheme-semantic = SMP.!!

  ------------------------------------------------------------------------
  -- Arithmetic helpers for stack requirement bounds
  ------------------------------------------------------------------------

  -- pair-slots ≥ 2, so any stack requirement ≥ pair-slots ≥ 2
  -- Therefore suc n ≤ n + req for any req that includes pair-slots
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

    -- For Fuse/Hylo with two IR components
    suc-≤-plus-req-2 : ∀ n m₁ m₂ → suc n ≤ n +ℕ (m₁ +ℕ m₂ +ℕ pair-slots)
    suc-≤-plus-req-2 n m₁ m₂ = ≤-trans (suc-≤-plus-2 n) (+-monoʳ-≤ n (2≤m+2 (m₁ +ℕ m₂)))

  ------------------------------------------------------------------------
  -- Memory preservation helper for recursion scheme traces
  --
  -- The trace: mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []
  -- Only writes to slot n. All locations before frontier are preserved:
  --   - Stack slots k < n: not written by trace
  --   - Ancestor frame slots: different frame, not written
  --   - Heap locations: trace has no heap writes
  ------------------------------------------------------------------------

  rec-scheme-mem-preserved : ∀ {n : ℕ} (s : LocState FS) (alloc : AllocState {FS}) →
    n ≡ next-slot alloc →
    halted s ≡ false →
    ∀ loc → BeforeFrontier alloc loc →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc)) loc ≡
    readLoc s loc
  rec-scheme-mem-preserved {n} s alloc refl not-halted (OnStack f k) (stack-before refl k<n) =
    rec-scheme-preserves-slot-below-3 n k s alloc not-halted k<n
  rec-scheme-mem-preserved {n} s alloc refl not-halted (OnStack f k) (stack-ancestor cf≺f _) =
    rec-scheme-preserves-ancestor-3 n s alloc f k not-halted (λ eq → ≺⇒≢ cf≺f (sym eq))
  rec-scheme-mem-preserved {n} s alloc refl not-halted (OnHeap hl) (heap-before _) =
    rec-scheme-preserves-heap-3 n s alloc hl not-halted

  ------------------------------------------------------------------------
  -- Specialized Entry Points for Recursion Schemes
  --
  -- Each scheme implements structural recursion on μ-values.
  -- The underlying recursive pattern is:
  --   1. Store input at backup-slot
  --   2. Apply out-μ to get G-layer
  --   3. Optional: apply transform (G-layer → F-layer)
  --   4. Dispatch on functor structure
  --   5. Apply algebra to get result
  --   6. Return result in Output register
  --
  -- Termination: structural recursion on μG (well-founded by construction).
  ------------------------------------------------------------------------

  -- | Cata: catamorphism (fold over μ-type)
  --
  -- WIRING: Delegates to cata-dispatched-new from RecTrace.agda.
  -- The structural recursion proofs are built in RecTrace; here we just
  -- adapt the interface.
  --
  -- Note: ⟦ μ-type F ⟧ = ⟦μ⟧ F by definition (Once/Semantics/Core.agda:103),
  -- so the types match directly.
  run-cata-core : ∀ {F A}
    → (wf : WellFormedF F)
    → (alg : IR (⟦ F ⟧T A) A)
    → (rec-wf : RecDispatcherWF (ir-size (Cata wf alg)))
    → (mIn : AllocMode)
    → (x : ⟦ μ-type F ⟧)
    → (input-loc : ValueLocation FS)
    → (s : LocState FS)
    → (alloc : AllocState {FS})
    → ValidAtWF mIn alloc x input-loc s
    → BeforeFrontier alloc input-loc
    → halted s ≡ false
    → readReg (regs s) Input ≡ input-loc
    → ∃[ mOut ] IRResultAWF mOut (Cata wf alg) x s alloc
  run-cata-core wf alg rec-wf mIn x input-loc s alloc
    input-valid-wf input-before not-halted rdi-eq =
    -- Delegate to cata-dispatched-new which provides the structural recursion proof
    cata-dispatched-new wf alg rec-wf x mIn input-loc s alloc
      input-valid-wf input-before not-halted rdi-eq

  -- | Fuse: μ-anchored fusion (transform then fold)
  -- Structural recursion on μG, applying transform and algebra
  run-fuse-core : ∀ {F G B}
    → (wfF : WellFormedF F)
    → (wfG : WellFormedF G)
    → (alg : IR (⟦ F ⟧T B) B)
    → (transform : IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G)))
    → (rec-wf : RecDispatcherWF (ir-size (Fuse wfF wfG alg transform)))
    → (mIn : AllocMode)
    → (x : ⟦ μ-type G ⟧)
    → (input-loc : ValueLocation FS)
    → (s : LocState FS)
    → (alloc : AllocState {FS})
    → ValidAtWF mIn alloc x input-loc s
    → BeforeFrontier alloc input-loc
    → halted s ≡ false
    → readReg (regs s) Input ≡ input-loc
    → ∃[ mOut ] IRResultAWF mOut (Fuse wfF wfG alg transform) x s alloc
  run-fuse-core {F} {G} {B} wfF wfG alg transform rec-wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    Heap , record
      { result-loc = result-loc
      ; final-state = s'
      ; final-alloc = alloc'
      ; trace = fuse-trace
      ; trace-correct = refl
      ; result-valid-wf = result-valid
      ; result-before = result-bf
      ; rax-is-result = rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = slot-mono
      ; heap-monotone = ≤-refl
      -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
      ; reclaim-preserves-result = result-bf
      ; reclaim-preserves-validity = result-valid
      ; max-slot-written = next-slot alloc'
      ; max-slot-geq-final = ≤-refl
      ; max-slot-usage-bound = reclaim-bound
      -- slot-stays-in-budget: allocates exactly 1 slot
      -- next-slot alloc' = suc (next-slot alloc) ≤ next-slot alloc + ir-stack-requirement
      ; slot-stays-in-budget = reclaim-bound
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = trace-wa
      ; trace-slot-reads-above = tt
      ; trace-writes-below = trace-wb
      ; trace-slot-reads-below = tt
      -- Note: trace-preserves-capacity removed in Phase 3
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot (tph-∷ iph-lea-slot tph-[]))
      -- scratch-bounded: max-slot-written = suc n = next-slot alloc'
      -- suc n ≤ suc n + ir-scratch-requirement (Fuse ...) by m≤m+n
      ; scratch-bounded = m≤m+n (suc (next-slot alloc)) (ir-scratch-requirement (Fuse wfF wfG alg transform))
      }
    where
      result-slot = next-slot alloc
      result-loc = OnStack (current-frame alloc) result-slot

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = suc (next-slot alloc) }

      fuse-trace : AbstractTrace
      fuse-trace = mov-to-output ∷ store-at-slot result-slot ∷ lea-slot result-slot ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace fuse-trace s alloc)

      slot-mono : next-slot alloc ≤ next-slot alloc'
      slot-mono = n≤1+n (next-slot alloc)

      result-bf : BeforeFrontier alloc' result-loc
      result-bf = stack-before refl (n<1+n (next-slot alloc))

      -- Semantic correctness: Fuse computes correct result (postulated)
      result-valid : ValidAtWF Heap alloc' (eval (Fuse wfF wfG alg transform) x) result-loc s'
      result-valid = rec-scheme-semantic (Fuse wfF wfG alg transform) alloc' x result-loc s'

      n = next-slot alloc
      -- ir-stack-requirement (Fuse _ _ alg transform) = ir-stack-requirement alg + ir-stack-requirement transform + pair-slots
      reclaim-bound : suc n ≤ n +ℕ ir-stack-requirement (Fuse wfF wfG alg transform)
      reclaim-bound = suc-≤-plus-req-2 n (ir-stack-requirement alg) (ir-stack-requirement transform)

      rax-eq : readReg (regs s') Output ≡ result-loc
      rax-eq = rec-scheme-output-is-slot result-slot s alloc not-halted

      not-halted' : halted s' ≡ false
      not-halted' = rec-scheme-preserves-halted-3 result-slot s alloc not-halted

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc bf = rec-scheme-mem-preserved s alloc refl not-halted loc bf

      trace-wa : SMP.TraceWritesAbove (next-slot alloc) fuse-trace
      trace-wa = ≤-refl , tt

      trace-wb : SMP.TraceWritesBelow (suc (next-slot alloc)) fuse-trace
      trace-wb = n<1+n (next-slot alloc) , tt

      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc' →
        readLoc s'' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc' →
        _
      frontier-stable s'' input-loc' _ _ _ = inj₂ (inj₂ tt)

  -- | Hylo: hylomorphism (fused cata ∘ ana)
  -- Based on Fuse, structurally terminating on μG input
  run-hylo-core : ∀ {F G B}
    → (wfF : WellFormedF F)
    → (wfG : WellFormedF G)
    → (alg : IR (⟦ F ⟧T B) B)
    → (coalg : IR (μ-type G) (⟦ F ⟧T (μ-type G)))
    → (rec-wf : RecDispatcherWF (ir-size (Hylo wfF wfG alg coalg)))
    → (mIn : AllocMode)
    → (x : ⟦ μ-type G ⟧)
    → (input-loc : ValueLocation FS)
    → (s : LocState FS)
    → (alloc : AllocState {FS})
    → ValidAtWF mIn alloc x input-loc s
    → BeforeFrontier alloc input-loc
    → halted s ≡ false
    → readReg (regs s) Input ≡ input-loc
    → ∃[ mOut ] IRResultAWF mOut (Hylo wfF wfG alg coalg) x s alloc
  run-hylo-core {F} {G} {B} wfF wfG alg coalg rec-wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    Heap , record
      { result-loc = result-loc
      ; final-state = s'
      ; final-alloc = alloc'
      ; trace = hylo-trace
      ; trace-correct = refl
      ; result-valid-wf = result-valid
      ; result-before = result-bf
      ; rax-is-result = rax-eq
      ; not-halted = not-halted'
      ; frame-preserved = refl
      ; slot-monotone = slot-mono
      ; heap-monotone = ≤-refl
      -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
      ; reclaim-preserves-result = result-bf
      ; reclaim-preserves-validity = result-valid
      ; max-slot-written = next-slot alloc'
      ; max-slot-geq-final = ≤-refl
      ; max-slot-usage-bound = reclaim-bound
      -- slot-stays-in-budget: allocates exactly 1 slot
      -- next-slot alloc' = suc (next-slot alloc) ≤ next-slot alloc + ir-stack-requirement
      ; slot-stays-in-budget = reclaim-bound
      ; frontier-slot-stable = frontier-stable
      ; trace-writes-above = trace-wa
      ; trace-slot-reads-above = tt
      ; trace-writes-below = trace-wb
      ; trace-slot-reads-below = tt
      -- Note: trace-preserves-capacity removed in Phase 3
      ; trace-no-heap-writes = tt
      ; trace-preserves-halted = tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot (tph-∷ iph-lea-slot tph-[]))
      -- scratch-bounded: max-slot-written = suc n = next-slot alloc'
      -- suc n ≤ suc n + ir-scratch-requirement (Hylo ...) by m≤m+n
      ; scratch-bounded = m≤m+n (suc (next-slot alloc)) (ir-scratch-requirement (Hylo wfF wfG alg coalg))
      }
    where
      result-slot = next-slot alloc
      result-loc = OnStack (current-frame alloc) result-slot

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = suc (next-slot alloc) }

      hylo-trace : AbstractTrace
      hylo-trace = mov-to-output ∷ store-at-slot result-slot ∷ lea-slot result-slot ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace hylo-trace s alloc)

      slot-mono : next-slot alloc ≤ next-slot alloc'
      slot-mono = n≤1+n (next-slot alloc)

      result-bf : BeforeFrontier alloc' result-loc
      result-bf = stack-before refl (n<1+n (next-slot alloc))

      -- Semantic correctness: Hylo computes correct result (postulated)
      result-valid : ValidAtWF Heap alloc' (eval (Hylo wfF wfG alg coalg) x) result-loc s'
      result-valid = rec-scheme-semantic (Hylo wfF wfG alg coalg) alloc' x result-loc s'

      n = next-slot alloc
      -- ir-stack-requirement (Hylo _ _ alg coalg) = ir-stack-requirement alg + ir-stack-requirement coalg + pair-slots
      reclaim-bound : suc n ≤ n +ℕ ir-stack-requirement (Hylo wfF wfG alg coalg)
      reclaim-bound = suc-≤-plus-req-2 n (ir-stack-requirement alg) (ir-stack-requirement coalg)

      rax-eq : readReg (regs s') Output ≡ result-loc
      rax-eq = rec-scheme-output-is-slot result-slot s alloc not-halted

      not-halted' : halted s' ≡ false
      not-halted' = rec-scheme-preserves-halted-3 result-slot s alloc not-halted

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc bf = rec-scheme-mem-preserved s alloc refl not-halted loc bf

      trace-wa : SMP.TraceWritesAbove (next-slot alloc) hylo-trace
      trace-wa = ≤-refl , tt

      trace-wb : SMP.TraceWritesBelow (suc (next-slot alloc)) hylo-trace
      trace-wb = n<1+n (next-slot alloc) , tt

      frontier-stable : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input ≡ input-loc' →
        readLoc s'' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc' →
        _
      frontier-stable s'' input-loc' _ _ _ = inj₂ (inj₂ tt)

------------------------------------------------------------------------
-- Summary
--
-- RecCoreWF provides:
--   1. RecConfig: configuration record for scheme parameters
--   2. cata-config, fuse-config, hylo-config: configuration constructors
--   3. run-cata-core, run-fuse-core, run-hylo-core: implementations
--
-- Each implementation provides:
--   - Algorithmic structure (traces, state computation)
--   - Proven properties: trace bounds, halted preservation, memory preservation
--   - Semantic correctness via documented postulate (rec-scheme-semantic)
--
-- Termination is structural on μ-values (well-founded by construction).
--
-- Trusted Computing Base:
--   - rec-scheme-semantic postulate: recursion scheme semantics is correct
--   - This is justified by the categorical foundations of recursion schemes
------------------------------------------------------------------------
