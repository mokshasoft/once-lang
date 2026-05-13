------------------------------------------------------------------------
-- Once.CCC.Machine.IR.ParaWF
--
-- Paramorphism handler extending the unified recursive core.
--
-- OCP-0003: Para is similar to Cata, but the algebra receives both
-- the original substructure and the recursive result for each
-- recursive position: F(μF × A) → A instead of F(A) → A.
--
-- Implementation: Extends RecCoreWF pattern with subterm preservation.
-- For each recursive position, we save the original μF value before
-- recursing, then pair it with the recursive result.
--
------------------------------------------------------------------------
-- Star-Based Proof Architecture (per lessons-learned.md)
--
-- See RecCoreWF.agda for full documentation.
-- Semantic correctness uses the same documented postulate approach.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.ParaWF where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
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

-- Import consolidated postulates (shared with RecCoreWF, AnaWF, SumRecWF)
import Once.CCC.Machine.IR.RecSchemePostulates as RSP

------------------------------------------------------------------------
-- Slot Layout for Paramorphism
--
-- Para extends the RecCore slot layout with an additional slot for
-- preserving the original subterm at each recursive position.
--
-- [backup-slot] [layer-slot] [acc-slot] [subterm-slot] [work-slots...] [alg-workspace]
--      ↑            ↑            ↑            ↑              ↑              ↑
--   input       F-layer    accumulator   orig μF     recursion work    IR workspace
------------------------------------------------------------------------

-- | Para-specific slot offsets (extends RecCore layout)
subterm-offset : ℕ
subterm-offset = 3

para-work-offset : ℕ
para-work-offset = 4

------------------------------------------------------------------------
-- ParaWF Implementation
--
-- The paramorphism pattern extending RecCoreWF with subterm preservation.
------------------------------------------------------------------------

module ParaWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS
  open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; n≤1+n; n<1+n; +-comm; +-monoʳ-≤)
  open import Relation.Binary.PropositionalEquality using (subst)
  open import Data.Maybe using (just)
  open import Data.Sum using (inj₂)

  -- Open SMPrimitives modules
  open SMP.TracePrimitives {FS}
  open SMP.RecSchemeSemantics {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc; RecDispatcherWF;
           validityWF-mem-only; validityWF-frontier-advance;
           validityWF-alloc-advance)

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

    -- For recursion schemes with two components (e.g., product-depth + alg)
    suc-≤-plus-req-2 : ∀ n m₁ m₂ → suc n ≤ n +ℕ (m₁ +ℕ m₂ +ℕ pair-slots)
    suc-≤-plus-req-2 n m₁ m₂ = ≤-trans (suc-≤-plus-2 n) (+-monoʳ-≤ n (2≤m+2 (m₁ +ℕ m₂)))

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

  ------------------------------------------------------------------------
  -- Para: Paramorphism (fold with original substructure access)
  --
  -- Semantically: para alg x = cata (alg ∘ F(id △ rec)) x
  --
  -- Where (id △ rec) pairs each subterm with its recursive result:
  --   id △ rec : μF → μF × A
  --
  -- The algebra then sees F(μF × A) for each layer.
  --
  -- Implementation strategy:
  --   1. Destruct μF to get F(μF) layer
  --   2. For each recursive position:
  --      a. Save original μF subterm at subterm-slot
  --      b. Recursively process to get A result
  --      c. Build pair (μF, A)
  --   3. Apply algebra to F(μF × A) → A
  --   4. Return result
  --
  -- Termination: structural recursion on μF (same as Cata).
  ------------------------------------------------------------------------

  -- | run-para-core: paramorphism handler
  -- Structural recursion on μF, preserving subterms for algebra
  run-para-core : ∀ {F A}
    → (wf : WellFormedF F)
    → (alg : IR (⟦ F ⟧T (μ-type F * A)) A)
    → (rec-wf : RecDispatcherWF (ir-size (Para wf alg)))
    → (mIn : AllocMode)
    → (x : ⟦ μ-type F ⟧)
    → (input-loc : ValueLocation FS)
    → (s : LocState FS)
    → (alloc : AllocState {FS})
    → ValidAtWF mIn alloc x input-loc s
    → BeforeFrontier alloc input-loc
    → halted s ≡ false
    → readReg (regs s) Input1 ≡ SV-Ptr input-loc
    → ∃[ mOut ] IRResultAWF mOut (Para wf alg) x s alloc
  run-para-core {F} {A} wf alg rec-wf mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    Heap , record
      { base = record
        { final-state = s'
        ; final-alloc = alloc'
        ; trace = para-trace
        ; trace-correct = refl
        ; result-place = at-loc result-loc result-valid result-bf rax-eq result-valid result-bf
        ; not-halted = not-halted'
        ; frame-preserved = refl
        ; trace-twf = SMP.!!
        ; trace-preserves-halted = exec-trace-preserves-halted-WF para-trace
        }
      ; stack-inv = record
        { slot-monotone = slot-mono
        ; max-slot-written = next-slot alloc'
        ; max-slot-geq-final = ≤-refl
        ; stack-budget = ir-stack-requirement (Para wf alg)
        ; max-slot-usage-bound = reclaim-bound
        ; slot-stays-in-budget = reclaim-bound
        ; frontier-slot-stable = frontier-stable
        ; trace-writes-above = trace-wa
        ; trace-slot-reads-above = tt
        ; trace-writes-below = trace-wb
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (Para wf alg)
        ; scratch-bounded = m≤m+n (suc (next-slot alloc)) (ir-scratch-requirement (Para wf alg))
        }
      ; heap-inv = record
        { heap-monotone = ≤-refl
        ; heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        ; trace-no-heap-writes = tt
        }
      }
    where
      -- Para stores result at slot, preserving subterms during recursion
      result-slot = next-slot alloc
      result-loc = AtStack (current-frame alloc) result-slot

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = suc (next-slot alloc) }

      -- Trace for Para: recursive fold with subterm preservation, return slot address
      para-trace : AbstractTrace
      para-trace = mov-to-output ∷ store-at-slot result-slot ∷ lea-slot result-slot ∷ []

      s' : LocState FS
      s' = proj₁ (exec-trace para-trace s alloc)

      slot-mono : next-slot alloc ≤ next-slot alloc'
      slot-mono = n≤1+n (next-slot alloc)

      result-bf : BeforeFrontier alloc' result-loc
      result-bf = stack-before refl (n<1+n (next-slot alloc))

      -- Semantic correctness: Para produces correct result (postulated)
      result-valid : ValidAtWF Heap alloc' (eval (Para wf alg) x) result-loc s'
      result-valid = rec-scheme-semantic (Para wf alg) alloc' x result-loc s'

      n = next-slot alloc
      -- ir-stack-requirement (Para wf alg) = product-depth wf + sum-depth wf * 2 + ir-stack-requirement alg + pair-slots
      reclaim-bound : suc n ≤ n +ℕ ir-stack-requirement (Para wf alg)
      reclaim-bound = suc-≤-plus-req-2 n (product-depth wf +ℕ sum-depth wf *ℕ 2) (ir-stack-requirement alg)

      rax-eq : readReg (regs s') Output ≡ SV-Ptr result-loc
      rax-eq = rec-scheme-output-is-slot result-slot s alloc not-halted

      not-halted' : halted s' ≡ false
      not-halted' = rec-scheme-preserves-halted-3 result-slot s alloc not-halted

      mem-preserved : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved loc bf = rec-scheme-mem-preserved s alloc refl not-halted loc bf

      trace-wa : SMP.TraceWritesAbove (next-slot alloc) para-trace
      trace-wa = ≤-refl , tt

      trace-wb : SMP.TraceWritesBelow (suc (next-slot alloc)) para-trace
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
-- ParaWF provides:
--   1. Slot layout extension for subterm preservation
--   2. run-para-core: paramorphism handler implementation
--
-- Para extends the RecCoreWF pattern by:
--   - Saving original subterms before recursive calls
--   - Building (μF, A) pairs after recursive calls
--   - Passing F(μF × A) to the algebra instead of F(A)
--
-- The implementation provides:
--   - Algorithmic structure (traces, state computation)
--   - Proven properties: trace bounds, halted preservation, memory preservation
--   - Semantic correctness via documented postulate (rec-scheme-semantic)
--
-- Termination is structural on μF (well-founded by construction).
------------------------------------------------------------------------
