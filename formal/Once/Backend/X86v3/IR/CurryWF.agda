------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.CurryWF
--
-- Curry IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Takes RecDispatcherWF as parameter to construct BodyCorrect.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.CurryWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m+n≤o⇒m≤o; +-monoʳ-≤; *-monoˡ-≤; m≤m*n; +-assoc)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation hiding (AllocMode)

------------------------------------------------------------------------
-- Curry implementation
------------------------------------------------------------------------

module CurryWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecLemmas {FS}
  open FrameSemantics FS

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; BodyCorrect;
           valid-closure-wf; validityWF-mem-only;
           validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-with-bf-transfer;
           at-frontier-neq-before-wf; suc-frontier-neq-before-wf)

  -- Import ApplyWF for bf-same-frame-slot
  open import Once.Backend.X86v3.IR.ApplyWF
  open ApplyWFImpl {FS} program-bound
    using (bf-same-frame-slot)

  -- Import lemmas
  open import Once.Backend.X86v3.DispatcherArithmeticLemma
    using (suc<+2)
  open import Once.Backend.X86v3.SizeBoundLemma
    using (curry-body-bound)

  -- Import write operations
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import frontier lemmas
  open import Once.Backend.X86v3.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (at-frontier-before-closure; frontier-same-heap)

  ------------------------------------------------------------------------
  -- Curry: creates closure with BodyCorrect stored for Apply to use
  --
  -- Takes RecDispatcherWF as parameter. This is used to construct
  -- BodyCorrect.execute which Apply will later use.
  ------------------------------------------------------------------------

  -- Helper: closure-slots ≤ ir-stack-requirement (curry f m) for any AllocMode
  -- Both Stack and Heap modes give type-slots 2 for closures, and closure-slots = 2
  closure-slots-≤-curry-req : ∀ {A B C} (f : IR (A * B) C) (m : AllocMode) →
    closure-slots ≤ ir-stack-requirement (curry f m)
  closure-slots-≤-curry-req f Stack = ≤-refl
  closure-slots-≤-curry-req f Heap = ≤-refl

  run-curry : ∀ {A B C} (mIn : AllocMode) (f : IR (A * B) C) (m : AllocMode)
    (ir<bound : ir-size (curry f m) < program-bound)
    (rec-wf : RecDispatcherWF (ir-size (curry f m)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- Capacity using ir-stack-requirement
    next-slot alloc +ℕ ir-stack-requirement (curry f m) ≤ frame-capacity alloc →
    IRResultAWF Heap (curry f m) x s alloc  -- Closure is always Heap (boxed)
  run-curry mIn f m ir<bound rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = closure-loc
      ; final-state = s-final
      ; final-alloc = alloc-final
      ; result-valid-wf = curry-result-wf
      ; result-before = closure-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted-final
      ; frame-preserved = frame-preserved-curry
      ; slot-monotone = slot-monotone-curry
      ; heap-monotone = heap-monotone-curry
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-curry
      -- Reclamation: curry allocates closure-slots, result at closure-loc
      ; reclaimable-slot = next-slot alloc +ℕ closure-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) closure-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = curry-reclaim-preserves-result
      ; reclaim-preserves-validity = curry-reclaim-preserves-validity
      ; reclaim-size-bound = reclaim-size-bound-curry
      }
    where
      -- Size bound for body
      body<bound = curry-body-bound f {m} program-bound ir<bound

      closure-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- PROVEN: closure-fits from combined-cap
      -- ir-stack-requirement (curry f m) = type-slots-for-mode m (B ⇒[ Many ] C) = 2 = closure-slots
      -- So: closure-slots ≤ ir-stack-requirement (curry f m) trivially
      -- and: slot + closure-slots ≤ slot + ir-stack-requirement ≤ capacity
      req-curry = ir-stack-requirement (curry f m)

      -- closure-slots ≤ ir-stack-requirement (curry f m)
      -- ir-stack-requirement (curry f m) = type-slots-for-mode m (B ⇒[ Many ] C) = 2 = closure-slots
      closure-bound : closure-slots ≤ req-curry
      closure-bound = closure-slots-≤-curry-req f m

      closure-fits : next-slot alloc +ℕ closure-slots ≤ frame-capacity alloc
      closure-fits = ≤-trans (+-monoʳ-≤ (next-slot alloc) closure-bound) combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ closure-slots
        ; slots-available = closure-fits
        }

      s₁ = write-loc s closure-loc input-loc
      code-loc = sucLoc closure-loc
      s₂ = write-loc s₁ (sucLoc closure-loc) code-loc
      s-final = record s₂ { regs = writeReg (regs s₂) RAX closure-loc }
      alloc-final = alloc₁

      -- PROVEN: mem-preserved-curry via write-preserves-disjoint
      mem-preserved-curry : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-curry loc bf =
        trans (readLoc-stackMem-eq s-final s₂ loc refl refl)
              (trans (write-preserves-disjoint s₁ (sucLoc closure-loc) code-loc loc
                       (λ eq → suc-frontier-neq-before-wf alloc loc bf eq))
                     (write-preserves-disjoint s closure-loc input-loc loc
                       (λ eq → at-frontier-neq-before-wf alloc loc bf eq)))

      closure-before : BeforeFrontier alloc-final closure-loc
      closure-before = at-frontier-before-closure alloc closure-fits

      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc closure-slots closure-fits input-loc input-before

      code-before₁ : BeforeFrontier alloc₁ code-loc
      code-before₁ = stack-before refl (suc<+2 (next-slot alloc))

      env-ptr : readLoc s-final closure-loc ≡ just input-loc
      env-ptr = trans refl (trans
                  (write-preserves-disjoint s₁ (sucLoc closure-loc) code-loc closure-loc
                    (sucLoc-neq closure-loc))
                  (write-read-same s closure-loc input-loc))

      code-ptr : readLoc s-final (sucLoc closure-loc) ≡ just code-loc
      code-ptr = write-read-same s₁ (sucLoc closure-loc) code-loc

      sucLoc-closure-before : BeforeFrontier alloc₁ (sucLoc closure-loc)
      sucLoc-closure-before = code-before₁

      -- PROVEN: input-valid-wf-final via write helpers and alloc-advance
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final closure-slots closure-fits
          (validityWF-mem-only x input-loc s₂ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s₁ code-loc input-before
              (validityWF-write-at-frontier x input-loc s input-loc input-before
                input-valid-wf)))

      -- KEY: Construct BodyCorrect using rec-wf!
      -- rec-wf is RecDispatcherWF (ir-size (curry f m))
      -- Since curry-smaller : ir-size f < ir-size (curry f m), we can dispatch to f
      --
      -- Uses ir-stack-requirement for body-capacity
      --
      -- STACK-ALLOCATED RESULTS: No escape postulate needed!
      -- Body can return stack-allocated values. Apply uses body's reclaimable-slot
      -- for reclamation, so stack slots below that survive. Body's
      -- reclaim-preserves-result proves the result survives reclamation.

      body-correct : BodyCorrect f x input-loc program-bound
      body-correct = record
        { body-capacity = ir-stack-requirement f
        ; body-cap-eq = refl
        ; execute = λ arg arg-loc pair-loc s' alloc' mPair pair-valid-wf pair-before not-halt rdi-eq' combined-cap' →
            rec-wf mPair f (curry-smaller f {m}) (pair x arg) pair-loc s' alloc'
              pair-valid-wf pair-before not-halt rdi-eq' combined-cap'
        }

      rax-eq : readReg (regs s-final) RAX ≡ closure-loc
      rax-eq = writeReg-same (regs s₂) RAX closure-loc

      not-halted-final : halted s-final ≡ false
      not-halted-final = not-halted

      frame-preserved-curry : current-frame alloc-final ≡ current-frame alloc
      frame-preserved-curry = refl

      slot-monotone-curry : next-slot alloc ≤ next-slot alloc-final
      slot-monotone-curry = m≤m+n (next-slot alloc) closure-slots

      heap-monotone-curry : next-heap-ref alloc ≤ next-heap-ref alloc-final
      heap-monotone-curry = ≤-refl

      -- KEY: Output valid-closure-wf with body-correct embedded!
      -- valid-closure-wf returns ValidAtWF Heap (closure is always boxed)
      curry-result-wf : ValidAtWF Heap alloc-final (eval (curry f m) x) closure-loc s-final
      curry-result-wf = valid-closure-wf body<bound
                          env-ptr code-ptr input-before₁ code-before₁ sucLoc-closure-before
                          input-valid-wf-final body-correct

      -- Transfer closure-before from alloc₁ to the reclaimed allocation
      curry-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ closure-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ closure-slots ; slots-available = fits }) closure-loc
      curry-reclaim-preserves-result fits =
        frontier-same-heap alloc₁ (record alloc { next-slot = next-slot alloc +ℕ closure-slots ; slots-available = fits })
          refl refl refl closure-loc closure-before

      -- Validity at reclaimed allocation - PROVEN via bf-same-frame-slot
      -- The two allocations have the same current-frame, next-slot, and next-heap-ref.
      -- Only slots-available differs (proof-irrelevant).
      curry-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ closure-slots ≤ frame-capacity alloc) →
        ValidAtWF Heap (record alloc { next-slot = next-slot alloc +ℕ closure-slots ; slots-available = fits })
                  (eval (curry f m) x) closure-loc s-final
      curry-reclaim-preserves-validity fits = validityWF-with-bf-transfer
        (eval (curry f m) x) closure-loc s-final alloc₁
        (record alloc { next-slot = next-slot alloc +ℕ closure-slots ; slots-available = fits })
        (λ loc bf → bf-same-frame-slot alloc₁
          (record alloc { next-slot = next-slot alloc +ℕ closure-slots ; slots-available = fits })
          refl refl refl loc bf)
        curry-result-wf

      -- Reclaim size bound: reclaimable ≤ slot + ir-stack-requirement
      -- curry: reclaimable = slot + closure-slots
      -- ir-stack-requirement (curry f m) = ir-stack-requirement f + closure-slots
      -- So closure-slots ≤ ir-stack-requirement (curry f m) ✓
      reclaim-size-bound-curry : next-slot alloc +ℕ closure-slots ≤ next-slot alloc +ℕ req-curry
      reclaim-size-bound-curry = +-monoʳ-≤ (next-slot alloc) closure-bound
