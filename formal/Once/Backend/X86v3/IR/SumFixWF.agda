------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.SumFixWF
--
-- IR handlers for sum types (inl-ir, inr-ir, case-ir, initial) and
-- recursive types (fold-ir, unfold-ir).
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.SumFixWF where

open import Data.Nat using (ℕ; _<_; _+_; _≤_; suc)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n≤1+n)
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
open import Once.Backend.X86v3.Allocation

------------------------------------------------------------------------
-- Sum and Fix IR implementations
------------------------------------------------------------------------

module SumFixWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open FrameSemantics FS

  -- Import IRResultAWF and ValidAtWF
  open import Once.Backend.X86v3.IRResult
  open DispatcherResult {FS} program-bound

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; valid-unit-wf;
           validityWF-mem-only; validityWF-frontier-advance;
           decomposePairWF; PairValidWF;
           valid-inl-wf; valid-inr-wf; valid-fold-wf;
           decomposeInlWF; decomposeInrWF; decomposeFoldWF;
           InlValidWF; InrValidWF; FoldValidWF)

  -- Import frontier lemmas
  open import Once.Backend.X86v3.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (frontier-same-heap)

  -- Helper: fold is injective (wrap is injective)
  fold-injective : ∀ {F} {a b : ⟦ F ⟧} → fold a ≡ fold b → a ≡ b
  fold-injective refl = refl

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
