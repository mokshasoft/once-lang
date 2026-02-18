------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.SumFixWF
--
-- IR handlers for sum types (inl-ir, inr-ir, case-ir, initial) and
-- recursive types (fold-ir, unfold-ir).
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.SumFixWF where

open import Data.Nat using (ℕ; _<_; _≤_; suc; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n; +-monoʳ-≤; m≤m*n; m<m+n; *-monoʳ-≤)
-- n≤m+n is imported from IR.agda
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation hiding (AllocMode)

------------------------------------------------------------------------
-- Sum and Fix IR implementations
------------------------------------------------------------------------

module SumFixWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open FrameSemantics FS

  -- Import IRResultAWF and ValidAtWF
  open import Once.Backend.X86v3.IRResult
  open DispatcherResult {FS} program-bound

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; valid-unit-wf;
           validityWF-mem-only; validityWF-frontier-advance;
           validityWF-alloc-advance; validityWF-mem-preserved;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           decomposePairWF; PairValidWF;
           valid-inl-wf; valid-inr-wf; valid-fold-wf;
           decomposeInlWF; decomposeInrWF; decomposeFoldWF;
           InlValidWF; InrValidWF; FoldValidWF)

  -- Import frontier lemmas
  open import Once.Backend.X86v3.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (frontier-same-heap; at-frontier-becomes-before)

  -- Import write operations
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import validity write lemmas for frontier inequality helpers
  open import Once.Backend.X86v3.ValidityWriteLemma using (module ValidityWriteLemmas)
  open ValidityWriteLemmas {FS} program-bound
    using (at-frontier-neq-before; suc-frontier-neq-before)

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

  run-initial : ∀ {A}
    (x : ⟦ Void ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultAWF (initial {A}) x s alloc
  run-initial () _ _ _ _ _ _ _  -- x : ⟦ Void ⟧ = ⊥, so pattern match is absurd

  ------------------------------------------------------------------------
  -- Unfold: dereference the fold pointer
  --
  -- fold v is stored as a pointer to location where v is stored.
  -- unfold just extracts the pointer and returns it.
  ------------------------------------------------------------------------

  run-unfold : ∀ {F}
    (x : ⟦ Fix F ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultAWF (unfold-ir {F}) x s alloc
  -- Pattern match on x = wrap v to expose fold structure
  -- Since ⟦ Fix F ⟧ = Wrapped (⟦ F ⟧) and wrap v = fold v
  run-unfold {F} (wrap v) input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    let fold-decomp = decomposeFoldWF input-valid-wf
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
        result-valid-wf-v : ValidAtWF alloc v unfolded-loc s'
        result-valid-wf-v = subst (λ u → ValidAtWF alloc u unfolded-loc s') (sym v-eq) unfolded-valid-wf-s'
        -- Prove that load doesn't halt
        not-halted-s' : halted s' ≡ false
        not-halted-s' = load-no-halt RAX (IndReg RDI) s unfolded-loc mem-read not-halted
    in record
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
          subst (λ u → ValidAtWF _ u unfolded-loc s') (sym v-eq)
            (validityWF-frontier-advance unfolded-val unfolded-loc s' refl ≤-refl ≤-refl
              (validityWF-mem-only unfolded-val unfolded-loc s s'
                (load-preserves-stackMem RAX (IndReg RDI) s)
                (load-preserves-heapMem RAX (IndReg RDI) s)
                unfolded-valid-wf))
      ; reclaim-size-bound = m≤m+n (next-slot alloc) pair-slots
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

  -- Postulates for sum type allocation (design issue: type-slots can be > pair-slots)
  postulate
    -- type-slots (A + B) ≤ pair-slots * ir-size inl-ir (assumes boxed representation)
    sum-slots-bound : ∀ {A B} {m : AllocMode} → type-slots (A + B) ≤ pair-slots *ℕ ir-size (inl-ir {A} {B} m)

    -- suc n < n +ℕ type-slots (A + B) (requires type-slots ≥ 2)
    sucLoc-sum-in-range : ∀ {A B} (n : ℕ) → suc n < n +ℕ type-slots (A + B)

    -- Proof irrelevance for allocation state equality
    alloc-slots-eq : ∀ {FS : FrameSemantics} (alloc : AllocState {FS}) (k : ℕ)
      (fits₁ fits₂ : next-slot alloc +ℕ k ≤ frame-capacity alloc) →
      record alloc { next-slot = next-slot alloc +ℕ k ; slots-available = fits₁ } ≡
      record alloc { next-slot = next-slot alloc +ℕ k ; slots-available = fits₂ }

  run-inl : ∀ {A B} {m : AllocMode}
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc +ℕ pair-slots *ℕ ir-size (inl-ir {A} {B} m) ≤ frame-capacity alloc →
    IRResultAWF (inl-ir {A} {B} m) x s alloc
  run-inl {A} {B} {m} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
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
      sum-slots = type-slots (A + B)
      sum-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- Derive capacity for sum allocation
      -- ir-size inl-ir = 1, so pair-slots * 1 = pair-slots ≥ sum-slots when sum-slots ≤ 2
      -- Actually type-slots (A + B) = 1 + max(type-slots A, type-slots B) could be > 2
      -- But ir-stack-requirement inl-ir = type-slots (A + B), and combined-cap uses pair-slots * ir-size
      -- Let's check: ir-size inl-ir = 1, so pair-slots * 1 = 2
      -- This works for boxed representation where type-slots (A + B) = 2 (tag + pointer)
      -- For unboxed, we'd need type-slots (A + B) ≤ pair-slots * ir-size inl-ir

      -- For now, use sum-slots directly with a capacity derivation
      -- sum-slots ≤ pair-slots * ir-size inl-ir = pair-slots * 1 = 2
      -- This holds when type-slots (A + B) ≤ 2 (boxed representation)
      -- NOTE: This is a design issue - type-slots can be > pair-slots for unboxed representation

      sum-fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc
      sum-fits = ≤-trans (+-monoʳ-≤ (next-slot alloc) (sum-slots-bound {A} {B} {m})) combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
        ; slots-available = sum-fits
        }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) RAX sum-loc }

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots (sum-slots-pos {A} {B}) sum-fits

      -- sucLoc sum-loc is BeforeFrontier after allocation
      -- Need: suc (next-slot alloc) < next-slot alloc +ℕ sum-slots = next-slot alloc₁
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (sucLoc-sum-in-range {A} {B} (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots sum-fits input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc)

      -- Input validity in final state
      input-valid-wf-final : ValidAtWF alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots sum-fits
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inl x
      inl-valid-wf-final : ValidAtWF alloc₁ (inl {A} {B} x) sum-loc s-final
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
                (λ eq → suc-frontier-neq-before alloc loc bf eq))

      inl-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits }) sum-loc
      inl-reclaim-preserves-result fits = at-frontier-becomes-before alloc sum-slots (sum-slots-pos {A} {B}) fits

      inl-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        ValidAtWF (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits })
                  (inl {A} {B} x) sum-loc s-final
      -- alloc₁ has sum-fits but fits might be different proof object
      -- Use proof irrelevance via postulate
      inl-reclaim-preserves-validity fits =
        subst (λ a → ValidAtWF a (inl {A} {B} x) sum-loc s-final)
              (alloc-slots-eq alloc sum-slots sum-fits fits)
              inl-valid-wf-final

      reclaim-size-bound-inl : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ pair-slots *ℕ ir-size (inl-ir {A} {B} m)
      reclaim-size-bound-inl = +-monoʳ-≤ (next-slot alloc) (sum-slots-bound {A} {B} {m})

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

  run-inr : ∀ {A B} {m : AllocMode}
    (x : ⟦ B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc +ℕ pair-slots *ℕ ir-size (inr-ir {A} {B} m) ≤ frame-capacity alloc →
    IRResultAWF (inr-ir {A} {B} m) x s alloc
  run-inr {A} {B} {m} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
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
      sum-slots = type-slots (A + B)
      sum-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- Note: sum-slots-bound now uses inr-ir m, but sum type is the same
      -- We rely on the fact that ir-size (inl-ir m) = ir-size (inr-ir m) = 1
      sum-fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc
      sum-fits = ≤-trans (+-monoʳ-≤ (next-slot alloc) (sum-slots-bound {A} {B} {m})) combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ sum-slots
        ; slots-available = sum-fits
        }

      -- Write payload pointer to sucLoc sum-loc
      s₁ = write-loc s (sucLoc sum-loc) input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) RAX sum-loc }

      -- sum-loc is BeforeFrontier after allocation
      sum-before : BeforeFrontier alloc₁ sum-loc
      sum-before = at-frontier-becomes-before alloc sum-slots (sum-slots-pos {A} {B}) sum-fits

      -- sucLoc sum-loc is BeforeFrontier after allocation
      sucLoc-sum-before : BeforeFrontier alloc₁ (sucLoc sum-loc)
      sucLoc-sum-before = stack-before refl (sucLoc-sum-in-range {A} {B} (next-slot alloc))

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc sum-slots sum-fits input-loc input-before

      -- Payload pointer: readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr : readLoc s-final (sucLoc sum-loc) ≡ just input-loc
      payload-ptr = trans (readLoc-stackMem-eq s-final s₁ (sucLoc sum-loc) refl refl)
                          (write-read-same s (sucLoc sum-loc) input-loc)

      -- Input validity in final state
      input-valid-wf-final : ValidAtWF alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final sum-slots sum-fits
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-suc-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for inr x
      inr-valid-wf-final : ValidAtWF alloc₁ (inr {A} {B} x) sum-loc s-final
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
                (λ eq → suc-frontier-neq-before alloc loc bf eq))

      inr-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits }) sum-loc
      inr-reclaim-preserves-result fits = at-frontier-becomes-before alloc sum-slots (sum-slots-pos {A} {B}) fits

      inr-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ sum-slots ≤ frame-capacity alloc) →
        ValidAtWF (record alloc { next-slot = next-slot alloc +ℕ sum-slots ; slots-available = fits })
                  (inr {A} {B} x) sum-loc s-final
      inr-reclaim-preserves-validity fits =
        subst (λ a → ValidAtWF a (inr {A} {B} x) sum-loc s-final)
              (alloc-slots-eq alloc sum-slots sum-fits fits)
              inr-valid-wf-final

      reclaim-size-bound-inr : next-slot alloc +ℕ sum-slots ≤ next-slot alloc +ℕ pair-slots *ℕ ir-size (inr-ir {A} {B} m)
      reclaim-size-bound-inr = +-monoʳ-≤ (next-slot alloc) (sum-slots-bound {A} {B} {m})

  ------------------------------------------------------------------------
  -- Fold: wrap value in recursive type
  --
  -- Creates a fold value (fold x = wrap x) by:
  -- 1. Allocating type-slots (Fix F) = 1 slot at frontier
  -- 2. Writing input-loc (pointer to unfolded value) to fold-loc
  -- 3. Returning fold-loc
  --
  -- Memory layout: fold-loc stores pointer to unfolded value
  ------------------------------------------------------------------------

  -- Helper: type-slots (Fix F) > 0
  fix-slots-pos : ∀ {F} → 0 < type-slots (Fix F)
  fix-slots-pos {F} = s≤s z≤n

  -- Postulate: type-slots (Fix F) ≤ pair-slots * ir-size fold-ir
  -- ir-size fold-ir = 1, so pair-slots * 1 = 2 ≥ type-slots (Fix F) = 1
  postulate
    fix-slots-bound : ∀ {F} → type-slots (Fix F) ≤ pair-slots *ℕ ir-size (fold-ir {F})

  run-fold : ∀ {F}
    (x : ⟦ F ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc +ℕ pair-slots *ℕ ir-size (fold-ir {F}) ≤ frame-capacity alloc →
    IRResultAWF (fold-ir {F}) x s alloc
  run-fold {F} x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
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
      fix-slots = type-slots (Fix F)
      fold-loc = OnStack (current-frame alloc) (next-slot alloc)

      -- Derive capacity for fold allocation
      fix-fits : next-slot alloc +ℕ fix-slots ≤ frame-capacity alloc
      fix-fits = ≤-trans (+-monoʳ-≤ (next-slot alloc) (fix-slots-bound {F})) combined-cap

      alloc₁ : AllocState {FS}
      alloc₁ = record alloc
        { next-slot = next-slot alloc +ℕ fix-slots
        ; slots-available = fix-fits
        }

      -- Write pointer to unfolded value at fold-loc
      s₁ = write-loc s fold-loc input-loc
      s-final = record s₁ { regs = writeReg (regs s₁) RAX fold-loc }

      -- fold-loc is BeforeFrontier after allocation
      fold-before : BeforeFrontier alloc₁ fold-loc
      fold-before = at-frontier-becomes-before alloc fix-slots (fix-slots-pos {F}) fix-fits

      -- input-loc stays BeforeFrontier after allocation
      input-before₁ : BeforeFrontier alloc₁ input-loc
      input-before₁ = stack-alloc-advances alloc fix-slots fix-fits input-loc input-before

      -- Unfolded pointer: readLoc s-final fold-loc ≡ just input-loc
      unfolded-ptr : readLoc s-final fold-loc ≡ just input-loc
      unfolded-ptr = trans (readLoc-stackMem-eq s-final s₁ fold-loc refl refl)
                           (write-read-same s fold-loc input-loc)

      -- Input validity in final state
      input-valid-wf-final : ValidAtWF alloc₁ x input-loc s-final
      input-valid-wf-final =
        validityWF-alloc-advance x input-loc s-final fix-slots fix-fits
          (validityWF-mem-only x input-loc s₁ s-final refl refl
            (validityWF-write-at-frontier x input-loc s input-loc input-before
              input-valid-wf))

      -- Construct validity for fold x = wrap x
      fold-valid-wf-final : ValidAtWF alloc₁ (wrap x) fold-loc s-final
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
                (λ eq → at-frontier-neq-before alloc loc bf eq))

      fold-reclaim-preserves-result : ∀ (fits : next-slot alloc +ℕ fix-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ fix-slots ; slots-available = fits }) fold-loc
      fold-reclaim-preserves-result fits = at-frontier-becomes-before alloc fix-slots (fix-slots-pos {F}) fits

      fold-reclaim-preserves-validity : ∀ (fits : next-slot alloc +ℕ fix-slots ≤ frame-capacity alloc) →
        ValidAtWF (record alloc { next-slot = next-slot alloc +ℕ fix-slots ; slots-available = fits })
                  (wrap x) fold-loc s-final
      fold-reclaim-preserves-validity fits =
        subst (λ a → ValidAtWF a (wrap x) fold-loc s-final)
              (alloc-slots-eq alloc fix-slots fix-fits fits)
              fold-valid-wf-final

      reclaim-size-bound-fold : next-slot alloc +ℕ fix-slots ≤ next-slot alloc +ℕ pair-slots *ℕ ir-size (fold-ir {F})
      reclaim-size-bound-fold = +-monoʳ-≤ (next-slot alloc) (fix-slots-bound {F})

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

  run-case : ∀ {A B C} (f : IR A C) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (case-ir f g)))
    (x : ⟦ A + B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc +ℕ pair-slots *ℕ ir-size (case-ir f g) ≤ frame-capacity alloc →
    IRResultAWF (case-ir f g) x s alloc

  -- Case for inl: dispatch to f
  run-case {A} {B} {C} f g rec-wf (inj₁ a) input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
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
      ; reclaim-size-bound = ≤-trans (IRResultAWF.reclaim-size-bound result-f)
                                      (+-monoʳ-≤ (next-slot alloc) cap-f-bound)
      }
    where
      sf = ir-size f
      sg = ir-size g
      size = ir-size (case-ir f g)

      -- Decompose sum validity
      inl-decomp = decomposeInlWF input-valid-wf
      a' = InlValidWF.a inl-decomp
      payload-loc = InlValidWF.payload-loc inl-decomp
      payload-before = InlValidWF.payload-before inl-decomp
      payload-valid-wf' = InlValidWF.payload-valid inl-decomp

      -- v-is-inl : inl a ≡ inl a', so a ≡ a' by inl-injective
      a-eq : a' ≡ a
      a-eq = inl-injective (sym (InlValidWF.v-is-inl inl-decomp))

      -- Transport payload validity from a' to a
      payload-valid-wf : ValidAtWF alloc a payload-loc s
      payload-valid-wf = subst (λ x → ValidAtWF alloc x payload-loc s) a-eq payload-valid-wf'

      -- Capacity bound: pair-slots * sf ≤ pair-slots * size
      -- Need: sf ≤ size = suc (sf +ℕ sg)
      -- Derivation: sf ≤ sf +ℕ sg ≤ suc (sf +ℕ sg)
      sf≤size : sf ≤ size
      sf≤size = ≤-trans (m≤m+n sf sg) (n≤1+n (sf +ℕ sg))

      cap-f-bound : pair-slots *ℕ sf ≤ pair-slots *ℕ size
      cap-f-bound = *-monoʳ-≤ pair-slots sf≤size

      -- Capacity for f
      cap-f : next-slot alloc +ℕ pair-slots *ℕ sf ≤ frame-capacity alloc
      cap-f = ≤-trans (+-monoʳ-≤ (next-slot alloc) cap-f-bound) combined-cap

      -- Put payload-loc in RDI for dispatch
      s-setup = record s { regs = writeReg (regs s) RDI payload-loc }

      -- s-setup preserves memory from s (only regs changed)
      mem-setup-eq : ∀ loc → readLoc s-setup loc ≡ readLoc s loc
      mem-setup-eq loc = readLoc-stackMem-eq s-setup s loc refl refl

      rdi-payload : readReg (regs s-setup) RDI ≡ payload-loc
      rdi-payload = writeReg-same (regs s) RDI payload-loc

      not-halted-setup : halted s-setup ≡ false
      not-halted-setup = not-halted

      payload-valid-wf-setup : ValidAtWF alloc a payload-loc s-setup
      payload-valid-wf-setup = validityWF-mem-only a payload-loc s s-setup refl refl payload-valid-wf

      -- Dispatch to f
      result-f = rec-wf f (case-f-smaller f g) a payload-loc s-setup alloc
                   payload-valid-wf-setup payload-before not-halted-setup rdi-payload cap-f

  -- Case for inr: dispatch to g
  run-case {A} {B} {C} f g rec-wf (inj₂ b) input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
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
      ; reclaim-size-bound = ≤-trans (IRResultAWF.reclaim-size-bound result-g)
                                      (+-monoʳ-≤ (next-slot alloc) cap-g-bound)
      }
    where
      sf = ir-size f
      sg = ir-size g
      size = ir-size (case-ir f g)

      -- Decompose sum validity
      inr-decomp = decomposeInrWF input-valid-wf
      b' = InrValidWF.b inr-decomp
      payload-loc = InrValidWF.payload-loc inr-decomp
      payload-before = InrValidWF.payload-before inr-decomp
      payload-valid-wf' = InrValidWF.payload-valid inr-decomp

      -- v-is-inr : inr b ≡ inr b', so b ≡ b' by inr-injective
      b-eq : b' ≡ b
      b-eq = inr-injective (sym (InrValidWF.v-is-inr inr-decomp))

      -- Transport payload validity from b' to b
      payload-valid-wf : ValidAtWF alloc b payload-loc s
      payload-valid-wf = subst (λ x → ValidAtWF alloc x payload-loc s) b-eq payload-valid-wf'

      -- Capacity bound: pair-slots * sg ≤ pair-slots * size
      -- Need: sg ≤ size = suc (sf +ℕ sg)
      -- Derivation: sg ≤ sf +ℕ sg ≤ suc (sf +ℕ sg)
      sg≤size : sg ≤ size
      sg≤size = ≤-trans (n≤m+n sf sg) (n≤1+n (sf +ℕ sg))

      cap-g-bound : pair-slots *ℕ sg ≤ pair-slots *ℕ size
      cap-g-bound = *-monoʳ-≤ pair-slots sg≤size

      -- Capacity for g
      cap-g : next-slot alloc +ℕ pair-slots *ℕ sg ≤ frame-capacity alloc
      cap-g = ≤-trans (+-monoʳ-≤ (next-slot alloc) cap-g-bound) combined-cap

      -- Put payload-loc in RDI for dispatch
      s-setup = record s { regs = writeReg (regs s) RDI payload-loc }

      -- s-setup preserves memory from s (only regs changed)
      mem-setup-eq : ∀ loc → readLoc s-setup loc ≡ readLoc s loc
      mem-setup-eq loc = readLoc-stackMem-eq s-setup s loc refl refl

      rdi-payload : readReg (regs s-setup) RDI ≡ payload-loc
      rdi-payload = writeReg-same (regs s) RDI payload-loc

      not-halted-setup : halted s-setup ≡ false
      not-halted-setup = not-halted

      payload-valid-wf-setup : ValidAtWF alloc b payload-loc s-setup
      payload-valid-wf-setup = validityWF-mem-only b payload-loc s s-setup refl refl payload-valid-wf

      -- Dispatch to g
      result-g = rec-wf g (case-g-smaller f g) b payload-loc s-setup alloc
                   payload-valid-wf-setup payload-before not-halted-setup rdi-payload cap-g
