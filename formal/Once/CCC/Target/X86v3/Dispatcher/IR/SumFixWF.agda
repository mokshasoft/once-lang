------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR.SumFixWF
--
-- IR handlers for sum types (inl-ir, inr-ir, case-ir, initial) and
-- recursive types (fold-ir, unfold-ir).
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.IR.SumFixWF where

open import Data.Nat using (ℕ; _<_; _≤_; suc; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; n≤1+n; +-monoʳ-≤; m≤m*n; m<m+n; *-monoʳ-≤; ≤-irrelevant)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine
open import Once.CCC.Target.X86v3.Types
open import Once.CCC.IR
open import Once.CCC.Target.X86v3.Dispatcher.Allocation hiding (AllocMode)

------------------------------------------------------------------------
-- Sum and Fix IR implementations
------------------------------------------------------------------------

module SumFixWFImpl {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open FrameSemantics FS

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; valid-unit-wf;
           validityWF-mem-only; validityWF-frontier-advance;
           validityWF-alloc-advance; validityWF-mem-preserved;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           decomposePairWF; PairValidWF;
           valid-inl-wf; valid-inr-wf; valid-fold-wf;
           decomposeInlWF; decomposeInrWF; decomposeFoldWF;
           InlValidWF; InrValidWF; FoldValidWF;
           at-frontier-neq-before-wf; suc-frontier-neq-before-wf)

  -- Import frontier lemmas
  open import Once.CCC.Target.X86v3.Dispatcher.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (frontier-same-heap; at-frontier-becomes-before)

  -- Import write operations
  open import Once.CCC.Target.X86v3.Dispatcher.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import suc<+2 lemma for Heap mode proofs
  open import Once.CCC.Target.X86v3.Dispatcher.DispatcherArithmeticLemma using (suc<+2)

  -- Helper: fold is injective (wrap is injective)
  fold-injective : ∀ {F} {a b : ⟦ F ⟧} → fold a ≡ fold b → a ≡ b
  fold-injective refl = refl

  -- Helper: inl is injective
  inl-injective : ∀ {A B} {a b : ⟦ A ⟧} → inl {A} {B} a ≡ inl {A} {B} b → a ≡ b
  inl-injective refl = refl

  -- Helper: inr is injective
  inr-injective : ∀ {A B} {a b : ⟦ B ⟧} → inr {A} {B} a ≡ inr {A} {B} b → a ≡ b
  inr-injective refl = refl

  ------------------------------------------------------------------------
  -- Initial: absurd elimination (input is Void, so never executed)
  ------------------------------------------------------------------------

  run-initial : ∀ {m A}
    (x : ⟦ Void ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    ∃[ mOut ] IRResultAWF mOut (initial {A}) x s alloc
  run-initial () _ _ _ _ _ _ _  -- x : ⟦ Void ⟧ = ⊥, so pattern match is absurd

  ------------------------------------------------------------------------
  -- Unfold: dereference the fold pointer
  --
  -- fold v is stored as a pointer to location where v is stored.
  -- unfold just extracts the pointer and returns it.
  -- Input: Heap mode (fold is always boxed)
  -- Output: mode mV from the unfolded value
  ------------------------------------------------------------------------

  run-unfold : ∀ {m F}
    (x : ⟦ Fix F ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →  -- Reference-based: any mode works
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    ∃[ mOut ] IRResultAWF mOut (unfold-ir {F}) x s alloc
  -- Pattern match on x = wrap v to expose fold structure
  -- Since ⟦ Fix F ⟧ = Wrapped (⟦ F ⟧) and wrap v = fold v
  -- Reference-based model: Stack and Heap use same pointer representation
  run-unfold {m} {F} (wrap v) input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let fold-decomp = decomposeFoldWF input-valid-wf
        mV = FoldValidWF.mV fold-decomp
        unfolded-val = FoldValidWF.unfolded fold-decomp
        unfolded-loc = FoldValidWF.unfolded-loc fold-decomp
        unfolded-valid-wf = FoldValidWF.unfolded-valid fold-decomp
        unfolded-before = FoldValidWF.unfolded-before fold-decomp
        -- v-is-fold gives us: wrap v ≡ fold unfolded-val, hence v ≡ unfolded-val
        v-eq : v ≡ unfolded-val
        v-eq = fold-injective (FoldValidWF.v-is-fold fold-decomp)
        -- Read the pointer from input-loc
        mem-read : readLoc s (resolveSourceExt (regs s) (IndReg RDI)) ≡ just unfolded-loc
        mem-read = subst (λ loc → readLoc s loc ≡ just unfolded-loc)
                         (sym rdi-eq) (FoldValidWF.unfolded-ptr fold-decomp)
        s' = exec (load RAX (IndReg RDI)) s
        unfolded-valid-wf-s' = validityWF-mem-only unfolded-val unfolded-loc s s'
                                 (load-preserves-stackMem RAX (IndReg RDI) s)
                                 (load-preserves-heapMem RAX (IndReg RDI) s)
                                 unfolded-valid-wf
        -- Transport to get validity for v (which is what eval unfold-ir wants)
        result-valid-wf-v : ValidAtWF mV alloc v unfolded-loc s'
        result-valid-wf-v = subst (λ u → ValidAtWF mV alloc u unfolded-loc s') (sym v-eq) unfolded-valid-wf-s'
        -- Prove that load doesn't halt
        not-halted-s' : halted s' ≡ false
        not-halted-s' = load-no-halt RAX (IndReg RDI) s unfolded-loc mem-read not-halted
    in mV , record
      { result-loc = unfolded-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid-wf = result-valid-wf-v
      ; result-before = unfolded-before
      ; rax-is-result = load-result RAX (IndReg RDI) s unfolded-loc mem-read
      ; not-halted = not-halted-s'
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc _ →
          readLoc-stackMem-eq s' s loc
            (load-preserves-stackMem RAX (IndReg RDI) s)
            (load-preserves-heapMem RAX (IndReg RDI) s)
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = λ fits →
          frontier-same-heap alloc (record alloc { slots-available = fits }) refl refl refl unfolded-loc unfolded-before
      ; reclaim-preserves-validity = λ fits →
          subst (λ u → ValidAtWF mV _ u unfolded-loc s') (sym v-eq)
            (validityWF-frontier-advance unfolded-val unfolded-loc s' refl ≤-refl ≤-refl
              (validityWF-mem-only unfolded-val unfolded-loc s s'
                (load-preserves-stackMem RAX (IndReg RDI) s)
                (load-preserves-heapMem RAX (IndReg RDI) s)
                unfolded-valid-wf))
      ; reclaim-size-bound = m≤m+n (next-slot alloc) (ir-stack-requirement (unfold-ir {F}))
      }

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

  -- Helper: type-slots (A + B) > 0
  sum-slots-pos : ∀ {A B} → 0 < type-slots (A + B)
  sum-slots-pos {A} {B} = s≤s z≤n

  -- Proof irrelevance for allocation state equality
  -- Two AllocState records differing only in ≤ proof are equal (via ≤-irrelevant)
  alloc-slots-eq : ∀ {FS : FrameSemantics} (alloc : AllocState {FS}) (k : ℕ)
    (fits₁ fits₂ : next-slot alloc +ℕ k ≤ frame-capacity alloc) →
    record alloc { next-slot = next-slot alloc +ℕ k ; slots-available = fits₁ } ≡
    record alloc { next-slot = next-slot alloc +ℕ k ; slots-available = fits₂ }
  alloc-slots-eq alloc k fits₁ fits₂ =
    cong (λ p → record alloc { next-slot = next-slot alloc +ℕ k ; slots-available = p })
         (≤-irrelevant fits₁ fits₂)

  run-inl : ∀ {A B} (mIn : AllocMode) (m : AllocMode)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement (inl-ir {A} {B} m) ≤ frame-capacity alloc →
    IRResultAWF m (inl-ir {A} {B} m) x s alloc  -- Output mode is m (the inl-ir's AllocMode)

  -- Stack mode: reference-based (tag + pointer), same as Heap mode
  run-inl {A} {B} mIn Stack x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = sum-loc
      ; final-state = s-final
      ; final-alloc = alloc₁
      ; result-valid-wf = inl-valid-wf-final
      ; result-before = sum-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-inl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-inl
      ; reclaimable-slot = next-slot alloc +ℕ sum-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) sum-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = inl-reclaim-preserves-result
      ; reclaim-preserves-validity = inl-reclaim-preserves-validity
      ; reclaim-size-bound = reclaim-size-bound-inl
      }
    where
      -- Stack mode: sum-slots = stack-type-slots (A + B) = 2 (tag + pointer)
      sum-slots : ℕ
      sum-slots = 2

      sum-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- ir-stack-requirement (inl-ir Stack) = stack-type-slots (A + B) = 2 = sum-slots
      sum-fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc
      sum-fits = combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
        ; slots-available = sum-fits
        }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) RAX sum-loc }

      -- Stack mode: sum-slots = 2 > 0
      sum-slots>0 : 0 < sum-slots
      sum-slots>0 = s≤s z≤n

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots sum-slots>0 sum-fits

      -- sucLoc sum-loc is BeforeFrontier after allocation
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (suc<+2 (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots sum-fits input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc stack-valid)

      -- Input validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots sum-fits
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inl x (Stack mode = reference-based)
      inl-valid-wf-final : ValidAtWF Stack alloc₁ (inl {A} {B} x) sum-loc s-final
      inl-valid-wf-final = valid-inl-wf payload-ptr input-before₁ sucLoc-sum-before input-valid-wf-final

      rax-eq : readReg (regs s-final) RAX ≡ sum-loc
      rax-eq = writeReg-same (regs s₁) RAX sum-loc

      slot-monotone-inl : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-inl = m≤m+n (next-slot alloc) sum-slots

      mem-preserved-inl : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-inl loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-preserves-disjoint s (sucLoc sum-loc) input-loc loc
                (λ eq → suc-frontier-neq-before-wf alloc loc bf eq))

      inl-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits }) sum-loc
      inl-reclaim-preserves-result fits = at-frontier-becomes-before alloc sum-slots sum-slots>0 fits

      inl-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        ValidAtWF Stack (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits })
                  (inl {A} {B} x) sum-loc s-final
      inl-reclaim-preserves-validity fits =
        subst (λ a → ValidAtWF Stack a (inl {A} {B} x) sum-loc s-final)
              (alloc-slots-eq alloc sum-slots sum-fits fits)
              inl-valid-wf-final

      -- reclaim-size-bound: sum-slots = 2 = ir-stack-requirement (inl-ir Stack)
      reclaim-size-bound-inl : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ ir-stack-requirement (inl-ir {A} {B} Stack)
      reclaim-size-bound-inl = ≤-refl

  -- Heap mode: boxed representation (tag + pointer)
  run-inl {A} {B} mIn Heap x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = sum-loc
      ; final-state = s-final
      ; final-alloc = alloc₁
      ; result-valid-wf = inl-valid-wf-final
      ; result-before = sum-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-inl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-inl
      ; reclaimable-slot = next-slot alloc +ℕ sum-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) sum-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = inl-reclaim-preserves-result
      ; reclaim-preserves-validity = inl-reclaim-preserves-validity
      ; reclaim-size-bound = reclaim-size-bound-inl
      }
    where
      -- Heap mode: sum-slots = heap-type-slots (A + B) = 2 (tag + pointer)
      sum-slots : ℕ
      sum-slots = 2

      sum-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- ir-stack-requirement (inl-ir Heap) = heap-type-slots (A + B) = 2 = sum-slots
      -- So sum-fits follows directly from combined-cap
      sum-fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc
      sum-fits = combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
        ; slots-available = sum-fits
        }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) RAX sum-loc }

      -- Heap mode: sum-slots = 2 > 0
      sum-slots>0 : 0 < sum-slots
      sum-slots>0 = s≤s z≤n

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots sum-slots>0 sum-fits

      -- sucLoc sum-loc is BeforeFrontier after allocation
      -- Need: suc (next-slot alloc) < next-slot alloc +ℕ 2
      -- Uses suc<+2 from DispatcherArithmeticLemma
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (suc<+2 (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots sum-fits input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc stack-valid)

      -- Input validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots sum-fits
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inl x (Heap mode = boxed)
      -- valid-inl-wf needs: payload-ptr, payload-before, sucLoc-before, payload-valid
      inl-valid-wf-final : ValidAtWF Heap alloc₁ (inl {A} {B} x) sum-loc s-final
      inl-valid-wf-final = valid-inl-wf payload-ptr input-before₁ sucLoc-sum-before input-valid-wf-final

      rax-eq : readReg (regs s-final) RAX ≡ sum-loc
      rax-eq = writeReg-same (regs s₁) RAX sum-loc

      slot-monotone-inl : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-inl = m≤m+n (next-slot alloc) sum-slots

      mem-preserved-inl : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-inl loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-preserves-disjoint s (sucLoc sum-loc) input-loc loc
                (λ eq → suc-frontier-neq-before-wf alloc loc bf eq))

      inl-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits }) sum-loc
      inl-reclaim-preserves-result fits = at-frontier-becomes-before alloc sum-slots sum-slots>0 fits

      inl-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        ValidAtWF Heap (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits })
                  (inl {A} {B} x) sum-loc s-final
      -- alloc₁ has sum-fits but fits might be different proof object
      -- Use ≤-irrelevant to equate different ≤ proof terms
      inl-reclaim-preserves-validity fits =
        subst (λ a → ValidAtWF Heap a (inl {A} {B} x) sum-loc s-final)
              (alloc-slots-eq alloc sum-slots sum-fits fits)
              inl-valid-wf-final

      -- reclaim-size-bound: sum-slots = 2 = ir-stack-requirement (inl-ir Heap)
      reclaim-size-bound-inl : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ ir-stack-requirement (inl-ir {A} {B} Heap)
      reclaim-size-bound-inl = ≤-refl

  ------------------------------------------------------------------------
  -- Inr: inject right into sum type
  --
  -- Creates a sum value (inr x) by:
  -- 1. Allocating type-slots (A + B) slots at frontier
  -- 2. Writing input-loc (payload pointer) to sucLoc sum-loc
  -- 3. Returning sum-loc
  --
  -- Memory layout: sum-loc stores tag (implicit), sucLoc sum-loc stores payload ptr
  -- Same pattern as run-inl, but produces inr instead of inl
  ------------------------------------------------------------------------

  run-inr : ∀ {A B} (mIn : AllocMode) (m : AllocMode)
    (x : ⟦ B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement (inr-ir {A} {B} m) ≤ frame-capacity alloc →
    IRResultAWF m (inr-ir {A} {B} m) x s alloc  -- Output mode is m (the inr-ir's AllocMode)

  -- Stack mode: reference-based (tag + pointer), same as Heap mode
  run-inr {A} {B} mIn Stack x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = sum-loc
      ; final-state = s-final
      ; final-alloc = alloc₁
      ; result-valid-wf = inr-valid-wf-final
      ; result-before = sum-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-inr
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-inr
      ; reclaimable-slot = next-slot alloc +ℕ sum-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) sum-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = inr-reclaim-preserves-result
      ; reclaim-preserves-validity = inr-reclaim-preserves-validity
      ; reclaim-size-bound = reclaim-size-bound-inr
      }
    where
      -- Stack mode: sum-slots = stack-type-slots (A + B) = 2 (tag + pointer)
      sum-slots : ℕ
      sum-slots = 2

      sum-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- ir-stack-requirement (inr-ir Stack) = stack-type-slots (A + B) = 2 = sum-slots
      sum-fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc
      sum-fits = combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
        ; slots-available = sum-fits
        }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) RAX sum-loc }

      -- Stack mode: sum-slots = 2 > 0
      sum-slots>0 : 0 < sum-slots
      sum-slots>0 = s≤s z≤n

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots sum-slots>0 sum-fits

      -- sucLoc sum-loc is BeforeFrontier after allocation
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (suc<+2 (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots sum-fits input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc stack-valid)

      -- Input validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots sum-fits
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inr x (Stack mode = reference-based)
      inr-valid-wf-final : ValidAtWF Stack alloc₁ (inr {A} {B} x) sum-loc s-final
      inr-valid-wf-final = valid-inr-wf payload-ptr input-before₁ sucLoc-sum-before input-valid-wf-final

      rax-eq : readReg (regs s-final) RAX ≡ sum-loc
      rax-eq = writeReg-same (regs s₁) RAX sum-loc

      slot-monotone-inr : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-inr = m≤m+n (next-slot alloc) sum-slots

      mem-preserved-inr : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-inr loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-preserves-disjoint s (sucLoc sum-loc) input-loc loc
                (λ eq → suc-frontier-neq-before-wf alloc loc bf eq))

      inr-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits }) sum-loc
      inr-reclaim-preserves-result fits = at-frontier-becomes-before alloc sum-slots sum-slots>0 fits

      inr-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        ValidAtWF Stack (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits })
                  (inr {A} {B} x) sum-loc s-final
      inr-reclaim-preserves-validity fits =
        subst (λ a → ValidAtWF Stack a (inr {A} {B} x) sum-loc s-final)
              (alloc-slots-eq alloc sum-slots sum-fits fits)
              inr-valid-wf-final

      -- reclaim-size-bound: sum-slots = 2 = ir-stack-requirement (inr-ir Stack)
      reclaim-size-bound-inr : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ ir-stack-requirement (inr-ir {A} {B} Stack)
      reclaim-size-bound-inr = ≤-refl

  -- Heap mode: boxed representation (tag + pointer)
  run-inr {A} {B} mIn Heap x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = sum-loc
      ; final-state = s-final
      ; final-alloc = alloc₁
      ; result-valid-wf = inr-valid-wf-final
      ; result-before = sum-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-inr
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-inr
      ; reclaimable-slot = next-slot alloc +ℕ sum-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) sum-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = inr-reclaim-preserves-result
      ; reclaim-preserves-validity = inr-reclaim-preserves-validity
      ; reclaim-size-bound = reclaim-size-bound-inr
      }
    where
      -- Heap mode: sum-slots = heap-type-slots (A + B) = 2 (tag + pointer)
      sum-slots : ℕ
      sum-slots = 2

      sum-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- ir-stack-requirement (inr-ir Heap) = heap-type-slots (A + B) = 2 = sum-slots
      -- So sum-fits follows directly from combined-cap
      sum-fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc
      sum-fits = combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
        ; slots-available = sum-fits
        }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) RAX sum-loc }

      -- Heap mode: sum-slots = 2 > 0
      sum-slots>0 : 0 < sum-slots
      sum-slots>0 = s≤s z≤n

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots sum-slots>0 sum-fits

      -- sucLoc sum-loc is BeforeFrontier after allocation
      -- Uses suc<+2 from DispatcherArithmeticLemma
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (suc<+2 (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots sum-fits input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc stack-valid)

      -- Input validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots sum-fits
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inr x (Heap mode = boxed)
      -- valid-inr-wf needs: payload-ptr, payload-before, sucLoc-before, payload-valid
      inr-valid-wf-final : ValidAtWF Heap alloc₁ (inr {A} {B} x) sum-loc s-final
      inr-valid-wf-final = valid-inr-wf payload-ptr input-before₁ sucLoc-sum-before input-valid-wf-final

      rax-eq : readReg (regs s-final) RAX ≡ sum-loc
      rax-eq = writeReg-same (regs s₁) RAX sum-loc

      slot-monotone-inr : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-inr = m≤m+n (next-slot alloc) sum-slots

      mem-preserved-inr : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-inr loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-preserves-disjoint s (sucLoc sum-loc) input-loc loc
                (λ eq → suc-frontier-neq-before-wf alloc loc bf eq))

      inr-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits }) sum-loc
      inr-reclaim-preserves-result fits = at-frontier-becomes-before alloc sum-slots sum-slots>0 fits

      inr-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        ValidAtWF Heap (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits })
                  (inr {A} {B} x) sum-loc s-final
      inr-reclaim-preserves-validity fits =
        subst (λ a → ValidAtWF Heap a (inr {A} {B} x) sum-loc s-final)
              (alloc-slots-eq alloc sum-slots sum-fits fits)
              inr-valid-wf-final

      -- reclaim-size-bound: sum-slots = 2 = ir-stack-requirement (inr-ir Heap)
      reclaim-size-bound-inr : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ ir-stack-requirement (inr-ir {A} {B} Heap)
      reclaim-size-bound-inr = ≤-refl

  ------------------------------------------------------------------------
  -- Fold: wrap value in recursive type
  --
  -- Heap mode (boxed):
  --   1. Allocate 1 slot at frontier for pointer
  --   2. Write input-loc (pointer to unfolded value) to fold-loc
  --   Memory: fold-loc contains pointer to unfolded value
  --
  -- Stack mode (unboxed):
  --   1. Allocate stack-type-slots F slots at frontier
  --   2. Copy unfolded value inline to fold-loc
  --   Memory: fold-loc contains F data inline
  ------------------------------------------------------------------------

  -- Helper: stack/heap-type-slots (Fix F) = 1 > 0 (reference-based model)
  fix-slots-pos : ∀ {F} → 0 < stack-type-slots (Fix F)
  fix-slots-pos {F} = s≤s z≤n

  run-fold : ∀ {F} (mIn : AllocMode) (m : AllocMode)
    (x : ⟦ F ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement (fold-ir {F} m) ≤ frame-capacity alloc →
    IRResultAWF m (fold-ir {F} m) x s alloc

  -- Stack mode: reference-based (pointer to unfolded value)
  -- Allocate 1 slot and write pointer to input-loc
  run-fold {F} mIn Stack x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = fold-loc
      ; final-state = s-final
      ; final-alloc = alloc₁
      ; result-valid-wf = fold-valid-wf-final
      ; result-before = fold-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-fold
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-fold
      ; reclaimable-slot = next-slot alloc +ℕ fix-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) fix-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = fold-reclaim-preserves-result
      ; reclaim-preserves-validity = fold-reclaim-preserves-validity
      ; reclaim-size-bound = reclaim-size-bound-fold
      }
    where
      fix-slots = stack-type-slots (Fix F)  -- Stack mode: 1 slot for pointer
      fold-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- ir-stack-requirement (fold-ir Stack) = stack-type-slots (Fix F) = fix-slots
      fix-fits : next-slot alloc +ℕ fix-slots ≤ frame-capacity alloc
      fix-fits = combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ fix-slots
        ; slots-available = fix-fits
        }

      -- Write pointer to unfolded value at fold-loc
      s₁ = write-loc s fold-loc input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) RAX fold-loc }

      -- fold-loc is BeforeFrontier after allocation (stack-type-slots (Fix F) = 1 > 0)
      fold-before : BeforeFrontier alloc₁ fold-loc
      fold-before = at-frontier-becomes-before alloc fix-slots (fix-slots-pos {F}) fix-fits

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc fix-slots fix-fits input-loc input-before

      -- Unfolded pointer: readLoc s-final fold-loc ≡ just input-loc
      unfolded-ptr : readLoc s-final fold-loc ≡ just input-loc
      unfolded-ptr = trans (readLoc-stackMem-eq s-final s₁ fold-loc refl refl)
                           (write-read-same s fold-loc input-loc stack-valid)

      -- Input validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final fix-slots fix-fits
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for fold x = wrap x
      fold-valid-wf-final : ValidAtWF Stack alloc₁ (wrap x) fold-loc s-final
      fold-valid-wf-final = valid-fold-wf unfolded-ptr input-before₁ input-valid-wf-final

      rax-eq : readReg (regs s-final) RAX ≡ fold-loc
      rax-eq = writeReg-same (regs s₁) RAX fold-loc

      slot-monotone-fold : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-fold = m≤m+n (next-slot alloc) fix-slots

      mem-preserved-fold : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-fold loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-preserves-disjoint s fold-loc input-loc loc
                (λ eq → at-frontier-neq-before-wf alloc loc bf eq))

      fold-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ fix-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ fix-slots ; slots-available = fits }) fold-loc
      fold-reclaim-preserves-result fits = at-frontier-becomes-before alloc fix-slots (fix-slots-pos {F}) fits

      fold-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ fix-slots ≤ frame-capacity alloc) →
        ValidAtWF Stack (record alloc { next-slot = next-slot alloc +ℕ fix-slots ; slots-available = fits }) (wrap x) fold-loc s-final
      fold-reclaim-preserves-validity fits =
        let alloc-reclaim = record alloc { next-slot = next-slot alloc +ℕ fix-slots ; slots-available = fits }
        in subst (λ a → ValidAtWF Stack a (wrap x) fold-loc s-final)
                 (cong (λ p → record alloc { next-slot = next-slot alloc +ℕ fix-slots ; slots-available = p })
                       (≤-irrelevant fix-fits fits))
                 fold-valid-wf-final

      reclaim-size-bound-fold : next-slot alloc +ℕ fix-slots ≤ next-slot alloc +ℕ ir-stack-requirement (fold-ir {F} Stack)
      reclaim-size-bound-fold = ≤-refl

  -- Heap mode: boxed (pointer to unfolded value)
  run-fold {F} mIn Heap x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = fold-loc
      ; final-state = s-final
      ; final-alloc = alloc₁
      ; result-valid-wf = fold-valid-wf-final
      ; result-before = fold-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = slot-monotone-fold
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = mem-preserved-fold
      ; reclaimable-slot = next-slot alloc +ℕ fix-slots
      ; reclaim-monotone = m≤m+n (next-slot alloc) fix-slots
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = fold-reclaim-preserves-result
      ; reclaim-preserves-validity = fold-reclaim-preserves-validity
      ; reclaim-size-bound = reclaim-size-bound-fold
      }
    where
      fix-slots = heap-type-slots (Fix F)  -- Heap mode: 1 slot for pointer
      fold-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- ir-stack-requirement (fold-ir Heap) = heap-type-slots (Fix F) = fix-slots
      fix-fits : next-slot alloc +ℕ fix-slots ≤ frame-capacity alloc
      fix-fits = combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ fix-slots
        ; slots-available = fix-fits
        }

      -- Write pointer to unfolded value at fold-loc
      s₁ = write-loc s fold-loc input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) RAX fold-loc }

      -- fold-loc is BeforeFrontier after allocation (heap-type-slots (Fix F) = 1 > 0)
      fold-before : BeforeFrontier alloc₁ fold-loc
      fold-before = at-frontier-becomes-before alloc fix-slots (fix-slots-pos {F}) fix-fits

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc fix-slots fix-fits input-loc input-before

      -- Unfolded pointer: readLoc s-final fold-loc ≡ just input-loc
      unfolded-ptr : readLoc s-final fold-loc ≡ just input-loc
      unfolded-ptr = trans (readLoc-stackMem-eq s-final s₁ fold-loc refl refl)
                           (write-read-same s fold-loc input-loc stack-valid)

      -- Input validity in final state
      input-valid-wf-final : ValidAtWF mIn alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final fix-slots fix-fits
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for fold x = wrap x
      -- valid-fold-wf produces ValidAtWF Heap (boxed pointer)
      fold-valid-wf-final : ValidAtWF Heap alloc₁ (wrap x) fold-loc s-final
      fold-valid-wf-final = valid-fold-wf unfolded-ptr input-before₁ input-valid-wf-final

      rax-eq : readReg (regs s-final) RAX ≡ fold-loc
      rax-eq = writeReg-same (regs s₁) RAX fold-loc

      slot-monotone-fold : next-slot alloc ≤ next-slot alloc₁
      slot-monotone-fold = m≤m+n (next-slot alloc) fix-slots

      mem-preserved-fold : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-fold loc bf =
        trans (readLoc-stackMem-eq s-final s₁ loc refl refl)
              (write-preserves-disjoint s fold-loc input-loc loc
                (λ eq → at-frontier-neq-before-wf alloc loc bf eq))

      fold-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ fix-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ fix-slots ; slots-available = fits }) fold-loc
      fold-reclaim-preserves-result fits = at-frontier-becomes-before alloc fix-slots (fix-slots-pos {F}) fits

      fold-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ fix-slots ≤ frame-capacity alloc) →
        ValidAtWF Heap (record alloc { next-slot = next-slot alloc +ℕ fix-slots ; slots-available = fits })
                  (wrap x) fold-loc s-final
      fold-reclaim-preserves-validity fits =
        subst (λ a → ValidAtWF Heap a (wrap x) fold-loc s-final)
              (alloc-slots-eq alloc fix-slots fix-fits fits)
              fold-valid-wf-final

      -- reclaim-size-bound: fix-slots = ir-stack-requirement (fold-ir Heap)
      reclaim-size-bound-fold : next-slot alloc +ℕ fix-slots ≤ next-slot alloc +ℕ ir-stack-requirement (fold-ir {F} Heap)
      reclaim-size-bound-fold = ≤-refl

  ------------------------------------------------------------------------
  -- Case: dispatch on sum type
  --
  -- For a sum value x : ⟦ A + B ⟧ (either inl a or inr b):
  -- 1. Read payload pointer from sucLoc input-loc
  -- 2. Load payload into RDI
  -- 3. Dispatch to f (for inl) or g (for inr) via RecDispatcherWF
  --
  -- Branches are mutually exclusive, so capacity is shared.
  -- ir-size (case-ir f g) = suc (ir-size f + ir-size g)
  ------------------------------------------------------------------------

  run-case : ∀ {m A B C} (f : IR A C) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (case-ir f g)))
    (x : ⟦ A + B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF m alloc x input-loc s →  -- Reference-based: any mode works
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement (case-ir f g) ≤ frame-capacity alloc →
    ∃[ mOut ] IRResultAWF mOut (case-ir f g) x s alloc

  -- Case for inl: dispatch to f
  run-case {m} {A} {B} {C} f g rec-wf (inj₁ a) input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    mF , record
      { result-loc = IRResultAWF.result-loc result-f
      ; final-state = IRResultAWF.final-state result-f
      ; final-alloc = IRResultAWF.final-alloc result-f
      ; result-valid-wf = IRResultAWF.result-valid-wf result-f
      ; result-before = IRResultAWF.result-before result-f
      ; rax-is-result = IRResultAWF.rax-is-result result-f
      ; not-halted = IRResultAWF.not-halted result-f
      ; frame-preserved = IRResultAWF.frame-preserved result-f
      ; slot-monotone = IRResultAWF.slot-monotone result-f
      ; heap-monotone = IRResultAWF.heap-monotone result-f
      ; heap-preserved = IRResultAWF.heap-preserved result-f
      ; capacity-preserved = IRResultAWF.capacity-preserved result-f
      ; mem-preserved-before = λ loc bf → trans (IRResultAWF.mem-preserved-before result-f loc bf)
                                                (mem-setup-eq loc)
      ; reclaimable-slot = IRResultAWF.reclaimable-slot result-f
      ; reclaim-monotone = IRResultAWF.reclaim-monotone result-f
      ; reclaim-bounded = IRResultAWF.reclaim-bounded result-f
      ; reclaim-preserves-result = IRResultAWF.reclaim-preserves-result result-f
      ; reclaim-preserves-validity = IRResultAWF.reclaim-preserves-validity result-f
      ; reclaim-size-bound = ≤-trans (IRResultAWF.reclaim-size-bound result-f) cap-f-bound
      }
    where
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-case = ir-stack-requirement (case-ir f g)

      -- Decompose sum validity
      inl-decomp = decomposeInlWF input-valid-wf
      a' = InlValidWF.a inl-decomp
      mA = InlValidWF.mA inl-decomp
      payload-loc = InlValidWF.payload-loc inl-decomp
      payload-before = InlValidWF.payload-before inl-decomp
      payload-valid-wf' = InlValidWF.payload-valid inl-decomp

      -- v-is-inl : inl a ≡ inl a', so a ≡ a' by inl-injective
      a-eq : a' ≡ a
      a-eq = inl-injective (sym (InlValidWF.v-is-inl inl-decomp))

      -- Transport payload validity from a' to a
      payload-valid-wf : ValidAtWF mA alloc a payload-loc s
      payload-valid-wf = subst (λ x → ValidAtWF mA alloc x payload-loc s) a-eq payload-valid-wf'

      -- Capacity for f
      -- case-stack-req: ir-stack-requirement (case-ir f g) = rf + rg
      -- So rf ≤ req-case, hence slot + rf ≤ slot + req-case ≤ cap
      cap-f-bound : next-slot alloc +ℕ rf ≤ next-slot alloc +ℕ req-case
      cap-f-bound = +-monoʳ-≤ (next-slot alloc) (m≤m+n rf rg)

      cap-f : next-slot alloc +ℕ rf ≤ frame-capacity alloc
      cap-f = ≤-trans cap-f-bound combined-cap

      -- Put payload-loc in RDI for dispatch
      s-setup = record s { regs = writeReg (regs s) RDI payload-loc }

      -- s-setup preserves memory from s (only regs changed)
      mem-setup-eq : ∀ loc → readLoc s-setup loc ≡ readLoc s loc
      mem-setup-eq loc = readLoc-stackMem-eq s-setup s loc refl refl

      rdi-payload : readReg (regs s-setup) RDI ≡ payload-loc
      rdi-payload = writeReg-same (regs s) RDI payload-loc

      not-halted-setup : halted s-setup ≡ false
      not-halted-setup = not-halted

      payload-valid-wf-setup : ValidAtWF mA alloc a payload-loc s-setup
      payload-valid-wf-setup = validityWF-mem-only a payload-loc s s-setup refl refl payload-valid-wf

      -- Dispatch to f via recursive dispatch
      f-exec-result : ∃[ mOut ] IRResultAWF mOut f a s-setup alloc
      f-exec-result = rec-wf mA f (case-f-smaller f g) a payload-loc s-setup alloc
                        payload-valid-wf-setup payload-before not-halted-setup rdi-payload cap-f
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result

  -- Case for inr: dispatch to g
  run-case {m} {A} {B} {C} f g rec-wf (inj₂ b) input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    mG , record
      { result-loc = IRResultAWF.result-loc result-g
      ; final-state = IRResultAWF.final-state result-g
      ; final-alloc = IRResultAWF.final-alloc result-g
      ; result-valid-wf = IRResultAWF.result-valid-wf result-g
      ; result-before = IRResultAWF.result-before result-g
      ; rax-is-result = IRResultAWF.rax-is-result result-g
      ; not-halted = IRResultAWF.not-halted result-g
      ; frame-preserved = IRResultAWF.frame-preserved result-g
      ; slot-monotone = IRResultAWF.slot-monotone result-g
      ; heap-monotone = IRResultAWF.heap-monotone result-g
      ; heap-preserved = IRResultAWF.heap-preserved result-g
      ; capacity-preserved = IRResultAWF.capacity-preserved result-g
      ; mem-preserved-before = λ loc bf → trans (IRResultAWF.mem-preserved-before result-g loc bf)
                                                (mem-setup-eq loc)
      ; reclaimable-slot = IRResultAWF.reclaimable-slot result-g
      ; reclaim-monotone = IRResultAWF.reclaim-monotone result-g
      ; reclaim-bounded = IRResultAWF.reclaim-bounded result-g
      ; reclaim-preserves-result = IRResultAWF.reclaim-preserves-result result-g
      ; reclaim-preserves-validity = IRResultAWF.reclaim-preserves-validity result-g
      ; reclaim-size-bound = ≤-trans (IRResultAWF.reclaim-size-bound result-g) cap-g-bound
      }
    where
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-case = ir-stack-requirement (case-ir f g)

      -- Decompose sum validity
      inr-decomp = decomposeInrWF input-valid-wf
      b' = InrValidWF.b inr-decomp
      mB = InrValidWF.mB inr-decomp
      payload-loc = InrValidWF.payload-loc inr-decomp
      payload-before = InrValidWF.payload-before inr-decomp
      payload-valid-wf' = InrValidWF.payload-valid inr-decomp

      -- v-is-inr : inr b ≡ inr b', so b ≡ b' by inr-injective
      b-eq : b' ≡ b
      b-eq = inr-injective (sym (InrValidWF.v-is-inr inr-decomp))

      -- Transport payload validity from b' to b
      payload-valid-wf : ValidAtWF mB alloc b payload-loc s
      payload-valid-wf = subst (λ x → ValidAtWF mB alloc x payload-loc s) b-eq payload-valid-wf'

      -- Capacity for g
      -- case-stack-req: ir-stack-requirement (case-ir f g) = rf + rg
      -- So rg ≤ req-case, hence slot + rg ≤ slot + req-case ≤ cap
      cap-g-bound : next-slot alloc +ℕ rg ≤ next-slot alloc +ℕ req-case
      cap-g-bound = +-monoʳ-≤ (next-slot alloc) (m≤n+m rg rf)

      cap-g : next-slot alloc +ℕ rg ≤ frame-capacity alloc
      cap-g = ≤-trans cap-g-bound combined-cap

      -- Put payload-loc in RDI for dispatch
      s-setup = record s { regs = writeReg (regs s) RDI payload-loc }

      -- s-setup preserves memory from s (only regs changed)
      mem-setup-eq : ∀ loc → readLoc s-setup loc ≡ readLoc s loc
      mem-setup-eq loc = readLoc-stackMem-eq s-setup s loc refl refl

      rdi-payload : readReg (regs s-setup) RDI ≡ payload-loc
      rdi-payload = writeReg-same (regs s) RDI payload-loc

      not-halted-setup : halted s-setup ≡ false
      not-halted-setup = not-halted

      payload-valid-wf-setup : ValidAtWF mB alloc b payload-loc s-setup
      payload-valid-wf-setup = validityWF-mem-only b payload-loc s s-setup refl refl payload-valid-wf

      -- Dispatch to g via recursive dispatch
      g-exec-result : ∃[ mOut ] IRResultAWF mOut g b s-setup alloc
      g-exec-result = rec-wf mB g (case-g-smaller f g) b payload-loc s-setup alloc
                        payload-valid-wf-setup payload-before not-halted-setup rdi-payload cap-g
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result
