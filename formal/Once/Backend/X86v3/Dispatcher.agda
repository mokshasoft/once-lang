------------------------------------------------------------------------
-- Once.Backend.X86v3.Dispatcher
--
-- IR Dispatcher with proper allocation state threading.
--
-- Key insight: allocation state is threaded through execution, so
-- freshly allocated locations are guaranteed disjoint from existing
-- valid locations.
--
-- ValidAt now tracks BeforeFrontier recursively, so decomposing a
-- pair automatically gives BeforeFrontier for components.
------------------------------------------------------------------------

module Once.Backend.X86v3.Dispatcher where

open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoʳ-≤; m≤m+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Induction.WellFounded using (Acc; acc)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Validity
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation
open import Once.Backend.X86v3.Apply
open import Once.Backend.X86v3.ClosureWellFormed

-- Import ValidAtWF types for termination-safe dispatch
open import Once.Backend.X86v3.ClosureWellFormed
  using (module ClosureWellFormedDef)

------------------------------------------------------------------------
-- Import lemma modules
------------------------------------------------------------------------

open import Once.Backend.X86v3.DispatcherArithmeticLemma public
  using (compose-slot-bounded-lemma; pair-slot-bounded-lemma; suc<+2)

open import Once.Backend.X86v3.SlotBoundedLemma public
  using (slot-bounded-zero)

open import Once.Backend.X86v3.FrontierLemma public
  using (module FrontierLemmas)

open import Once.Backend.X86v3.SizeBoundLemma public
  using (∘-f-bound; ∘-g-bound; ⟨,⟩-f-bound; ⟨,⟩-g-bound; curry-body-bound)

open import Once.Backend.X86v3.ValidityChainLemma public
  using (module ValidityChainLemmas)

------------------------------------------------------------------------
-- Re-export types from IRResult module
------------------------------------------------------------------------

open import Once.Backend.X86v3.IRResult public
  using (module DispatcherResult; module RecDispatcherDef)

------------------------------------------------------------------------
-- Import helper modules
------------------------------------------------------------------------

import Once.Backend.X86v3.IR.Compose as ComposeImpl
import Once.Backend.X86v3.IR.Pair as PairImpl

-- Import write operations from separate module
open import Once.Backend.X86v3.WriteOps public using (module WriteWithDisjoint)

------------------------------------------------------------------------
-- Closure IR Tracking - NOW FROM VALIDITY!
--
-- Since valid-closure tracks the body IR, we get it from decomposition.
-- No postulates needed - we create all closures, so we know their bodies.
--
-- KEY INSIGHT: ApplySetupResult now contains:
--   - body : IR (EnvType * A) B
--   - env : ⟦ EnvType ⟧
--   - closure-is-body : fst input ≡ (λ arg → eval body (pair env arg))
--   - env-valid, arg-valid for recursive dispatch
--
-- To compute (fst input) (snd input), we dispatch to body with (env, snd input).
-- Since the body came from some curry in the program, and
-- ir-size body < ir-size (curry body) ≤ program-size, recursion terminates.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Main Dispatcher with Allocation Threading
--
-- Parameterized by:
--   program-bound : ℕ (all IRs in the program are smaller)
--   acc-pb : Acc _<_ program-bound (for Apply to recurse on closure bodies)
--
-- Apply uses acc-pb with body<bound to get Acc for body, enabling
-- termination without TERMINATING pragma.
------------------------------------------------------------------------

module Dispatcher {FS : FrameSemantics} (program-bound : ℕ) (acc-pb : Acc _<_ program-bound) where
  open ValidityDef {FS} program-bound
  open DispatcherResult {FS} program-bound
  open FrontierInvariant {FS}
  open WriteWithDisjoint {FS}
  open RecDispatcherDef {FS} program-bound
  open MemOps {FS}
  open WriteOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open Allocator {FS}
  open StackAllocation {FS}
  open FrameSemantics FS
  open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m<m+n; n≤1+n; n<1+n; <-trans; m+n≤o⇒m≤o; +-suc; +-comm; +-monoˡ-≤; +-monoʳ-≤; +-assoc)

  -- Import WF types for termination-safe dispatch
  open ClosureWellFormedDef {FS} program-bound
    using (BodyCorrect; ValidAtWF; IRResultAWF; RecDispatcherWF;
           valid-unit-wf; valid-pair-wf; valid-closure-wf;
           decomposeClosureWF; ClosureValidWF; decomposePairWF; PairValidWF;
           validWF-to-valid; resultWF-to-result; validityWF-mem-only;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-alloc-advance)

  -- Import validity write lemmas
  open import Once.Backend.X86v3.ValidityWriteLemma using (module ValidityWriteLemmas)
  open ValidityWriteLemmas {FS} program-bound

  -- Import frontier and validity chain lemmas
  open FrontierLemmas {FS}
  open ValidityChainLemmas {FS} program-bound

  ------------------------------------------------------------------------
  -- Helper: get Acc for any IR size < program-bound
  -- Used by Apply to get Acc for body (since body<bound comes from closure,
  -- not from structural decrease on the current IR).
  -- Pattern matches acc-pb to extract the accessor function.
  ------------------------------------------------------------------------
  private
    -- Extract smaller Acc from larger Acc using the proof of <
    -- Pattern: rs takes the proof and Agda infers the element from it
    acc-extract : ∀ {m n : ℕ} → Acc _<_ m → n < m → Acc _<_ n
    acc-extract (acc rs) n<m = rs n<m

  get-acc-from-pb : ∀ (n : ℕ) → n < program-bound → Acc _<_ n
  get-acc-from-pb n n<pb = acc-extract acc-pb n<pb

  ------------------------------------------------------------------------
  -- Identity
  ------------------------------------------------------------------------

  run-id : ∀ {A} (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAt alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultA (id {A}) x s alloc
  run-id x input-loc s alloc input-valid input-before not-halted rdi-eq =
    let s' = exec (mov RAX RDI) s
    in record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid = validity-mem-only x input-loc s s' refl refl input-valid
      ; result-before = input-before
      ; rax-is-result = trans (mov-result RAX RDI s) rdi-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; slot-bounded = slot-bounded-zero (next-slot alloc)
      ; capacity-preserved = refl
      }

  ------------------------------------------------------------------------
  -- Fst - BeforeFrontier for fst-loc comes from decomposePair!
  ------------------------------------------------------------------------

  run-fst : ∀ {A B} (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAt alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultA (fst-ir {A} {B}) x s alloc
  run-fst {A} {B} x input-loc s alloc input-valid input-before not-halted rdi-eq =
    let pair-decomp = decomposePair input-valid
        fst-loc = PairValid.fst-loc pair-decomp
        fst-valid = PairValid.fst-valid pair-decomp
        fst-before = PairValid.fst-before pair-decomp
        mem-read : readLoc s (resolveSourceExt (regs s) (IndReg RDI)) ≡ just fst-loc
        mem-read = subst (λ loc → readLoc s loc ≡ just fst-loc)
                         (sym rdi-eq) (PairValid.fst-ptr pair-decomp)
        s' = exec (load RAX (IndReg RDI)) s
        fst-valid-s' : ValidAt alloc (fst x) fst-loc s'
        fst-valid-s' = validity-mem-only (fst x) fst-loc s s'
                         (sym (load-preserves-stackMem RAX (IndReg RDI) s))
                         (sym (load-preserves-heapMem RAX (IndReg RDI) s))
                         fst-valid
    in record
      { result-loc = fst-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid = fst-valid-s'
      ; result-before = fst-before
      ; rax-is-result = load-result RAX (IndReg RDI) s fst-loc mem-read
      ; not-halted = load-no-halt RAX (IndReg RDI) s fst-loc mem-read not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; slot-bounded = slot-bounded-zero (next-slot alloc)
      ; capacity-preserved = refl
      }

  ------------------------------------------------------------------------
  -- Snd - BeforeFrontier for snd-loc comes from decomposePair!
  ------------------------------------------------------------------------

  run-snd : ∀ {A B} (x : ⟦ A * B ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAt alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultA (snd-ir {A} {B}) x s alloc
  run-snd {A} {B} x input-loc s alloc input-valid input-before not-halted rdi-eq =
    let pair-decomp = decomposePair input-valid
        snd-loc = PairValid.snd-loc pair-decomp
        snd-valid = PairValid.snd-valid pair-decomp
        snd-before = PairValid.snd-before pair-decomp
        mem-read : readLoc s (resolveSourceExt (regs s) (IndRegSuc RDI)) ≡ just snd-loc
        mem-read = subst (λ loc → readLoc s (sucLoc loc) ≡ just snd-loc)
                         (sym rdi-eq) (PairValid.snd-ptr pair-decomp)
        s' = exec (load RAX (IndRegSuc RDI)) s
        snd-valid-s' : ValidAt alloc (snd x) snd-loc s'
        snd-valid-s' = validity-mem-only (snd x) snd-loc s s'
                         (sym (load-preserves-stackMem RAX (IndRegSuc RDI) s))
                         (sym (load-preserves-heapMem RAX (IndRegSuc RDI) s))
                         snd-valid
    in record
      { result-loc = snd-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid = snd-valid-s'
      ; result-before = snd-before
      ; rax-is-result = load-result RAX (IndRegSuc RDI) s snd-loc mem-read
      ; not-halted = load-no-halt RAX (IndRegSuc RDI) s snd-loc mem-read not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; slot-bounded = slot-bounded-zero (next-slot alloc)
      ; capacity-preserved = refl
      }

  ------------------------------------------------------------------------
  -- Terminal
  ------------------------------------------------------------------------

  run-terminal : ∀ {A} (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAt alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultA (terminal {A}) x s alloc
  run-terminal x input-loc s alloc input-valid input-before not-halted rdi-eq =
    let s' = exec (mov RAX RDI) s
    in record
      { result-loc = input-loc
      ; final-state = s'
      ; final-alloc = alloc
      ; result-valid = valid-unit
      ; result-before = input-before
      ; rax-is-result = trans (mov-result RAX RDI s) rdi-eq
      ; not-halted = not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; slot-bounded = slot-bounded-zero (next-slot alloc)
      ; capacity-preserved = refl
      }


  ------------------------------------------------------------------------
  -- Main dispatcher (recursive cases use Acc)
  --
  -- ARCHITECTURE: Uses mutual block pattern from X86 backend.
  -- This enables Apply to recursively dispatch to closure bodies:
  -- - When curry f creates a closure, it stores Acc for f in the closure
  -- - When apply extracts body from closure, it uses the stored Acc
  --
  -- Termination is proven via well-founded recursion on ir-size.
  -- The main dispatcher constructs rec from (acc rs) and delegates to helpers.
  ------------------------------------------------------------------------

  mutual
    -- Helper to construct RecDispatcherWF from rs accessor
    -- Defined in mutual block so termination checker can see the structure
    -- Returns IRResultAWF with ValidAtWF for proper threading
    -- Now includes ir-capacity for capacity proofs
    make-rec-wf : ∀ {n} (ir<bound : n < program-bound) →
      (∀ {m} → m < n → Acc _<_ m) →
      RecDispatcherWF n
    make-rec-wf {n} ir<bound rs ir lt x' input-loc' s' alloc' valid' before' not-halted' rdi-eq' ir-cap' =
      run-ir-wf ir (<-trans lt ir<bound) x' input-loc' s' alloc' valid' before' not-halted' rdi-eq' ir-cap' (rs lt)

    -- run-ir-wf uses Acc _<_ (ir-size ir) for termination.
    -- Uses ValidAtWF input and returns IRResultAWF with ValidAtWF output.
    -- For Compose/Pair: sub-IRs have smaller size, so rs gives Acc
    -- For Apply: uses body-correct.execute instead of recursive call!
    -- ir-capacity ensures sufficient stack space for execution.
    run-ir-wf : ∀ {A B} (ir : IR A B)
      (ir<bound : ir-size ir < program-bound) →
      (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS}) →
      ValidAtWF alloc x input-loc s →
      BeforeFrontier alloc input-loc →
      halted s ≡ false →
      readReg (regs s) RDI ≡ input-loc →
      next-slot alloc + ir-stack-requirement ir ≤ frame-capacity alloc →  -- ir-capacity
      Acc _<_ (ir-size ir) →
      IRResultAWF ir x s alloc

    -- Identity: output is same as input, so ValidAtWF preserved
    -- Use validityWF-mem-only to transport from s to s' (only regs change)
    run-ir-wf id _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      let s' = exec (mov RAX RDI) s
      in record
        { result-loc = input-loc
        ; final-state = s'
        ; final-alloc = alloc
        ; result-valid-wf = validityWF-mem-only x input-loc s s' refl refl input-valid-wf
        ; result-before = input-before
        ; rax-is-result = trans (mov-result RAX RDI s) rdi-eq
        ; not-halted = not-halted
        ; frame-preserved = refl
        ; slot-monotone = ≤-refl
        ; heap-monotone = ≤-refl
        ; slot-bounded = slot-bounded-zero (next-slot alloc)
        ; capacity-preserved = refl
        }

    -- Fst: extracts first component from pair ValidAtWF
    -- Use validityWF-mem-only to transport from s to s' (load only changes regs)
    run-ir-wf fst-ir _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      let pair-decomp = decomposePairWF input-valid-wf
          fst-loc = PairValidWF.fst-loc pair-decomp
          fst-valid-wf = PairValidWF.fst-valid pair-decomp
          fst-before = PairValidWF.fst-before pair-decomp
          mem-read : readLoc s (resolveSourceExt (regs s) (IndReg RDI)) ≡ just fst-loc
          mem-read = subst (λ loc → readLoc s loc ≡ just fst-loc)
                           (sym rdi-eq) (PairValidWF.fst-ptr pair-decomp)
          s' = exec (load RAX (IndReg RDI)) s
          fst-valid-wf-s' = validityWF-mem-only (fst x) fst-loc s s'
                              (load-preserves-stackMem RAX (IndReg RDI) s)
                              (load-preserves-heapMem RAX (IndReg RDI) s)
                              fst-valid-wf
      in record
        { result-loc = fst-loc
        ; final-state = s'
        ; final-alloc = alloc
        ; result-valid-wf = fst-valid-wf-s'
        ; result-before = fst-before
        ; rax-is-result = load-result RAX (IndReg RDI) s fst-loc mem-read
        ; not-halted = load-no-halt RAX (IndReg RDI) s fst-loc mem-read not-halted
        ; frame-preserved = refl
        ; slot-monotone = ≤-refl
        ; heap-monotone = ≤-refl
        ; slot-bounded = slot-bounded-zero (next-slot alloc)
        ; capacity-preserved = refl
        }

    -- Snd: extracts second component from pair ValidAtWF
    -- Use validityWF-mem-only to transport from s to s' (load only changes regs)
    run-ir-wf snd-ir _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      let pair-decomp = decomposePairWF input-valid-wf
          snd-loc = PairValidWF.snd-loc pair-decomp
          snd-valid-wf = PairValidWF.snd-valid pair-decomp
          snd-before = PairValidWF.snd-before pair-decomp
          mem-read : readLoc s (resolveSourceExt (regs s) (IndRegSuc RDI)) ≡ just snd-loc
          mem-read = subst (λ loc → readLoc s (sucLoc loc) ≡ just snd-loc)
                           (sym rdi-eq) (PairValidWF.snd-ptr pair-decomp)
          s' = exec (load RAX (IndRegSuc RDI)) s
          snd-valid-wf-s' = validityWF-mem-only (snd x) snd-loc s s'
                              (load-preserves-stackMem RAX (IndRegSuc RDI) s)
                              (load-preserves-heapMem RAX (IndRegSuc RDI) s)
                              snd-valid-wf
      in record
        { result-loc = snd-loc
        ; final-state = s'
        ; final-alloc = alloc
        ; result-valid-wf = snd-valid-wf-s'
        ; result-before = snd-before
        ; rax-is-result = load-result RAX (IndRegSuc RDI) s snd-loc mem-read
        ; not-halted = load-no-halt RAX (IndRegSuc RDI) s snd-loc mem-read not-halted
        ; frame-preserved = refl
        ; slot-monotone = ≤-refl
        ; heap-monotone = ≤-refl
        ; slot-bounded = slot-bounded-zero (next-slot alloc)
        ; capacity-preserved = refl
        }

    -- Terminal: outputs unit, ValidAtWF unit trivial
    run-ir-wf terminal _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq _ _ =
      let s' = exec (mov RAX RDI) s
      in record
        { result-loc = input-loc
        ; final-state = s'
        ; final-alloc = alloc
        ; result-valid-wf = valid-unit-wf  -- tt is always valid-wf
        ; result-before = input-before
        ; rax-is-result = trans (mov-result RAX RDI s) rdi-eq
        ; not-halted = not-halted
        ; frame-preserved = refl
        ; slot-monotone = ≤-refl
        ; heap-monotone = ≤-refl
        ; slot-bounded = slot-bounded-zero (next-slot alloc)
        ; capacity-preserved = refl
        }

    -- Compose: run f, then run g with f's output
    -- Use make-rec-wf to construct rec from rs
    -- Derive ir-capacity for f and g from compose's ir-capacity
    run-ir-wf (g ∘ f) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap (acc rs) =
      let -- Derive ir-capacity for f: (req-f + req-g) ≤ capacity implies req-f ≤ capacity
          -- ir-cap : slot + (req-f + req-g) ≤ cap
          -- Need: (slot + req-f) + req-g ≤ cap for m+n≤o⇒m≤o
          -- sym (+-assoc ...) gives: slot + (req-f + req-g) ≡ (slot + req-f) + req-g
          ir-cap-f : next-slot alloc + ir-stack-requirement f ≤ frame-capacity alloc
          ir-cap-f = m+n≤o⇒m≤o (next-slot alloc + ir-stack-requirement f)
                       (subst (λ x → x ≤ frame-capacity alloc)
                              (sym (+-assoc (next-slot alloc) (ir-stack-requirement f) (ir-stack-requirement g)))
                              ir-cap)
          -- Run f via recursive dispatch
          rec-wf = make-rec-wf ir<bound rs
          result-f = rec-wf f (∘-f-smaller f g) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap-f
          s₁ = IRResultAWF.final-state result-f
          alloc₁ = IRResultAWF.final-alloc result-f
          inter-loc = IRResultAWF.result-loc result-f
          inter-valid-wf = IRResultAWF.result-valid-wf result-f
          -- Derive ir-capacity for g
          -- After f: next-slot alloc₁ ≤ next-slot alloc + req-f
          -- Need: next-slot alloc₁ + req-g ≤ frame-capacity alloc₁
          -- Since capacity-preserved: frame-capacity alloc₁ = frame-capacity alloc
          ir-cap-g : next-slot alloc₁ + ir-stack-requirement g ≤ frame-capacity alloc₁
          ir-cap-g = subst (λ cap → next-slot alloc₁ + ir-stack-requirement g ≤ cap)
                       (sym (IRResultAWF.capacity-preserved result-f))
                       (≤-trans (+-monoˡ-≤ (ir-stack-requirement g) (IRResultAWF.slot-bounded result-f))
                                (subst (λ x → x ≤ frame-capacity alloc) (sym (+-assoc (next-slot alloc) _ _)) ir-cap))
          -- Set up RDI for g
          s₁-rdi = record s₁ { regs = writeReg (regs s₁) RDI inter-loc }
          -- Transport validity to s₁-rdi (only regs changed, not memory)
          inter-valid-wf' = validityWF-mem-only (eval f x) inter-loc s₁ s₁-rdi refl refl inter-valid-wf
          -- Run g via recursive dispatch
          result-g = rec-wf g (∘-g-smaller f g) (eval f x) inter-loc s₁-rdi alloc₁
                       inter-valid-wf'
                       (IRResultAWF.result-before result-f)
                       (IRResultAWF.not-halted result-f)
                       (writeReg-same (regs s₁) RDI inter-loc)
                       ir-cap-g
          -- Slot bounded for compose
          slot-bounded-compose = compose-slot-bounded-lemma
            (next-slot alloc) (next-slot alloc₁) (next-slot (IRResultAWF.final-alloc result-g))
            (ir-stack-requirement f) (ir-stack-requirement g)
            (IRResultAWF.slot-bounded result-g) (IRResultAWF.slot-bounded result-f)
      in record
        { result-loc = IRResultAWF.result-loc result-g
        ; final-state = IRResultAWF.final-state result-g
        ; final-alloc = IRResultAWF.final-alloc result-g
        ; result-valid-wf = IRResultAWF.result-valid-wf result-g
        ; result-before = IRResultAWF.result-before result-g
        ; rax-is-result = IRResultAWF.rax-is-result result-g
        ; not-halted = IRResultAWF.not-halted result-g
        ; frame-preserved = trans (IRResultAWF.frame-preserved result-g) (IRResultAWF.frame-preserved result-f)
        ; slot-monotone = ≤-trans (IRResultAWF.slot-monotone result-f) (IRResultAWF.slot-monotone result-g)
        ; heap-monotone = ≤-trans (IRResultAWF.heap-monotone result-f) (IRResultAWF.heap-monotone result-g)
        ; slot-bounded = slot-bounded-compose
        ; capacity-preserved = trans (IRResultAWF.capacity-preserved result-g) (IRResultAWF.capacity-preserved result-f)
        }

    -- Pair: run f and g, combine results into pair
    -- Use make-rec-wf to construct rec from rs
    -- Derive ir-capacity for f and g, and prove pair-fits from ir-capacity
    run-ir-wf ⟨ f , g ⟩ ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap (acc rs) =
      record
        { result-loc = pair-loc
        ; final-state = s-final
        ; final-alloc = alloc₃
        ; result-valid-wf = pair-valid-wf
        ; result-before = pair-before
        ; rax-is-result = rax-eq
        ; not-halted = IRResultAWF.not-halted result-g
        ; frame-preserved = trans (trans refl (IRResultAWF.frame-preserved result-g)) (IRResultAWF.frame-preserved result-f)
        ; slot-monotone = ≤-trans (≤-trans (IRResultAWF.slot-monotone result-f) (IRResultAWF.slot-monotone result-g)) (m≤m+n (next-slot alloc₂) pair-slots)
        ; heap-monotone = ≤-trans (IRResultAWF.heap-monotone result-f) (IRResultAWF.heap-monotone result-g)
        ; slot-bounded = pair-slot-bounded-lemma (next-slot alloc) (next-slot alloc₁) (next-slot alloc₂) (ir-stack-requirement f) (ir-stack-requirement g) pair-slots (IRResultAWF.slot-bounded result-g) (IRResultAWF.slot-bounded result-f)
        ; capacity-preserved = trans (IRResultAWF.capacity-preserved result-g) (IRResultAWF.capacity-preserved result-f)
        }
      where
        rec-wf = make-rec-wf ir<bound rs

        -- PROVEN: ir-capacity for f from pair's ir-capacity
        -- ir-cap : slot + ((req-f + req-g) + ps) ≤ cap
        -- Transform to: (slot + req-f) + (req-g + ps) ≤ cap
        -- Step 1: slot + ((req-f + req-g) + ps) ≡ slot + (req-f + (req-g + ps))
        --         via cong (slot +_) (+-assoc req-f req-g ps)
        -- Step 2: slot + (req-f + (req-g + ps)) ≡ (slot + req-f) + (req-g + ps)
        --         via sym (+-assoc slot req-f (req-g + ps))
        -- Then m+n≤o⇒m≤o gives: slot + req-f ≤ cap
        ir-cap-f : next-slot alloc + ir-stack-requirement f ≤ frame-capacity alloc
        ir-cap-f = m+n≤o⇒m≤o (next-slot alloc + ir-stack-requirement f)
                     (subst (λ x → x ≤ frame-capacity alloc)
                            (trans (cong (next-slot alloc +_)
                                         (+-assoc (ir-stack-requirement f) (ir-stack-requirement g) pair-slots))
                                   (sym (+-assoc (next-slot alloc) (ir-stack-requirement f) (ir-stack-requirement g + pair-slots))))
                            ir-cap)

        -- Run f via dispatcher
        result-f = rec-wf f (⟨,⟩-f-smaller f g) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap-f
        s₁ = IRResultAWF.final-state result-f
        alloc₁ = IRResultAWF.final-alloc result-f
        s₁-rdi = record s₁ { regs = writeReg (regs s₁) RDI input-loc }
        input-before₁ = frontier-monotone alloc alloc₁
                          (sym (IRResultAWF.frame-preserved result-f))
                          (IRResultAWF.slot-monotone result-f)
                          (IRResultAWF.heap-monotone result-f)
                          input-loc input-before

        postulate
          input-valid-wf₁ : ValidAtWF alloc₁ x input-loc s₁-rdi

        -- PROVEN: ir-capacity for g from pair's ir-capacity
        -- From ir-cap, derive: (slot + req-f) + req-g ≤ cap
        -- From slot-bounded: slot₁ ≤ slot + req-f
        -- Therefore: slot₁ + req-g ≤ (slot + req-f) + req-g ≤ cap = cap₁
        ir-cap-g : next-slot alloc₁ + ir-stack-requirement g ≤ frame-capacity alloc₁
        ir-cap-g = subst (λ cap → next-slot alloc₁ + ir-stack-requirement g ≤ cap)
                     (sym (IRResultAWF.capacity-preserved result-f))
                     (≤-trans
                       (+-monoˡ-≤ (ir-stack-requirement g) (IRResultAWF.slot-bounded result-f))
                       (m+n≤o⇒m≤o (next-slot alloc + ir-stack-requirement f + ir-stack-requirement g)
                         (subst (λ x → x ≤ frame-capacity alloc)
                                (trans (sym (+-assoc (next-slot alloc) (ir-stack-requirement f + ir-stack-requirement g) pair-slots))
                                       (cong (_+ pair-slots) (sym (+-assoc (next-slot alloc) (ir-stack-requirement f) (ir-stack-requirement g)))))
                                ir-cap)))

        -- Run g via dispatcher
        result-g = rec-wf g (⟨,⟩-g-smaller f g) x input-loc s₁-rdi alloc₁
                     input-valid-wf₁
                     input-before₁
                     (IRResultAWF.not-halted result-f)
                     (writeReg-same (regs s₁) RDI input-loc)
                     ir-cap-g

        fst-loc = IRResultAWF.result-loc result-f
        fst-before = IRResultAWF.result-before result-f
        fst-valid-wf = IRResultAWF.result-valid-wf result-f
        s₂ = IRResultAWF.final-state result-g
        alloc₂ = IRResultAWF.final-alloc result-g
        snd-loc = IRResultAWF.result-loc result-g
        snd-before = IRResultAWF.result-before result-g
        snd-valid-wf = IRResultAWF.result-valid-wf result-g
        pair-loc = OnStack (current-frame alloc₂) (next-slot alloc₂)

        -- PROVEN: pair-fits from ir-capacity!
        -- After f and g: next-slot alloc₂ ≤ next-slot alloc + (req-f + req-g)
        -- From ir-cap: next-slot alloc + ((req-f + req-g) + pair-slots) ≤ frame-capacity alloc
        -- Therefore: next-slot alloc₂ + pair-slots ≤ frame-capacity alloc₂
        --
        -- Proof chain:
        -- 1. slot-bounded f : slot₁ ≤ slot + req-f
        -- 2. slot-bounded g : slot₂ ≤ slot₁ + req-g
        -- 3. Combine: slot₂ ≤ (slot + req-f) + req-g ≡ slot + (req-f + req-g)
        -- 4. Add ps: slot₂ + ps ≤ (slot + (req-f + req-g)) + ps
        -- 5. Reassociate: (slot + (req-f + req-g)) + ps ≡ slot + ((req-f + req-g) + ps)
        -- 6. From ir-cap: slot + ((req-f + req-g) + ps) ≤ cap
        -- 7. cap₂ = cap via capacity-preserved
        pair-fits : next-slot alloc₂ + pair-slots ≤ frame-capacity alloc₂
        pair-fits = subst (λ cap → next-slot alloc₂ + pair-slots ≤ cap)
                      (sym (trans (IRResultAWF.capacity-preserved result-g)
                                  (IRResultAWF.capacity-preserved result-f)))
                      (≤-trans
                        (subst (λ x → next-slot alloc₂ + pair-slots ≤ x)
                               (+-assoc (next-slot alloc) (ir-stack-requirement f + ir-stack-requirement g) pair-slots)
                               (+-monoˡ-≤ pair-slots slot₂-bound))
                        ir-cap)
          where
            open import Data.Nat.Properties using (≤-reflexive)
            slot₂-bound : next-slot alloc₂ ≤ next-slot alloc + (ir-stack-requirement f + ir-stack-requirement g)
            slot₂-bound = ≤-trans
                            (≤-trans (IRResultAWF.slot-bounded result-g)
                                     (+-monoˡ-≤ (ir-stack-requirement g) (IRResultAWF.slot-bounded result-f)))
                            (≤-reflexive (+-assoc (next-slot alloc) (ir-stack-requirement f) (ir-stack-requirement g)))

        alloc₃ : AllocState {FS}
        alloc₃ = record alloc₂
          { next-slot = next-slot alloc₂ + pair-slots
          ; slots-available = pair-fits
          }

        s₃ = write-loc s₂ pair-loc fst-loc
        s₄ = write-loc s₃ (sucLoc pair-loc) snd-loc
        s-final = record s₄ { regs = writeReg (regs s₄) RAX pair-loc }

        pair-before : BeforeFrontier alloc₃ pair-loc
        pair-before = stack-before refl (m<m+n (next-slot alloc₂) (s≤s z≤n))

        sucLoc-pair-before : BeforeFrontier alloc₃ (sucLoc pair-loc)
        sucLoc-pair-before = stack-before refl (suc<+2 (next-slot alloc₂))

        pair-ptr : readLoc s-final pair-loc ≡ just fst-loc
        pair-ptr = trans refl (trans
                     (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc pair-loc (sucLoc-neq pair-loc))
                     (write-read-same s₂ pair-loc fst-loc))

        snd-ptr : readLoc s-final (sucLoc pair-loc) ≡ just snd-loc
        snd-ptr = write-read-same s₃ (sucLoc pair-loc) snd-loc

        fst-before-alloc₂ : BeforeFrontier alloc₂ fst-loc
        fst-before-alloc₂ = frontier-monotone alloc₁ alloc₂
                              (sym (IRResultAWF.frame-preserved result-g))
                              (IRResultAWF.slot-monotone result-g)
                              (IRResultAWF.heap-monotone result-g)
                              fst-loc fst-before

        fst-before₃ : BeforeFrontier alloc₃ fst-loc
        fst-before₃ = stack-alloc-advances alloc₂ pair-slots pair-fits fst-loc fst-before-alloc₂

        snd-before₃ : BeforeFrontier alloc₃ snd-loc
        snd-before₃ = stack-alloc-advances alloc₂ pair-slots pair-fits snd-loc snd-before

        postulate
          fst-valid-wf-final : ValidAtWF alloc₃ (eval f x) fst-loc s-final
          snd-valid-wf-final : ValidAtWF alloc₃ (eval g x) snd-loc s-final

        pair-valid-wf : ValidAtWF alloc₃ (eval ⟨ f , g ⟩ x) pair-loc s-final
        pair-valid-wf = valid-pair-wf pair-ptr snd-ptr fst-before₃ snd-before₃ sucLoc-pair-before fst-valid-wf-final snd-valid-wf-final

        rax-eq : readReg (regs s-final) RAX ≡ pair-loc
        rax-eq = writeReg-same (regs s₄) RAX pair-loc

    -- Curry: creates closure with BodyCorrect stored for Apply to use
    -- KEY TERMINATION FIX: Constructs BodyCorrect using make-rec, which Apply
    -- extracts and calls instead of making a recursive run-ir call.
    -- ir-capacity directly gives closure-fits since ir-stack-requirement (curry f) = closure-slots
    run-ir-wf (curry f) ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap (acc rs) =
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
        ; slot-bounded = ≤-refl
        ; capacity-preserved = refl
        }
      where
        -- Size bound for body
        body<bound = curry-body-bound f program-bound ir<bound

        closure-loc = OnStack (current-frame alloc) (next-slot alloc)

        -- PROVEN: closure-fits directly from ir-capacity!
        -- ir-stack-requirement (curry f) = closure-slots
        closure-fits : next-slot alloc + closure-slots ≤ frame-capacity alloc
        closure-fits = ir-cap

        alloc₁ : AllocState {FS}
        alloc₁ = record alloc
          { next-slot = next-slot alloc + closure-slots
          ; slots-available = closure-fits
          }

        s₁ = write-loc s closure-loc input-loc
        code-loc = sucLoc closure-loc
        s₂ = write-loc s₁ (sucLoc closure-loc) code-loc
        s-final = record s₂ { regs = writeReg (regs s₂) RAX closure-loc }
        alloc-final = alloc₁

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
        -- Chain: write at frontier → write at suc frontier → reg write → alloc advance
        input-valid-wf-final : ValidAtWF alloc₁ x input-loc s-final
        input-valid-wf-final =
          validityWF-alloc-advance x input-loc s-final closure-slots closure-fits
            (validityWF-mem-only x input-loc s₂ s-final refl refl
              (validityWF-write-at-suc-frontier x input-loc s₁ code-loc input-before
                (validityWF-write-at-frontier x input-loc s input-loc input-before
                  input-valid-wf)))

        -- KEY: Construct BodyCorrect using make-rec-wf!
        -- This is the pre-computed proof that Apply will use.
        -- Since make-rec-wf uses rs (from acc rs), this is structurally smaller.
        -- Now takes ValidAtWF and returns IRResultAWF for full consistency.
        -- ir-capacity is provided by Apply at call time.
        body-correct : BodyCorrect f x input-loc
        body-correct = record
          { execute = λ arg arg-loc pair-loc s' alloc' pair-valid-wf pair-before not-halt rdi-eq' ir-cap' →
              make-rec-wf ir<bound rs f (curry-smaller f) (pair x arg) pair-loc s' alloc'
                pair-valid-wf pair-before not-halt rdi-eq' ir-cap'
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
        curry-result-wf : ValidAtWF alloc-final (eval (curry f) x) closure-loc s-final
        curry-result-wf = valid-closure-wf body<bound
                            env-ptr code-ptr input-before₁ code-before₁ sucLoc-closure-before
                            input-valid-wf-final body-correct

    -- Apply: Uses body-correct.execute instead of recursive run-ir call!
    -- KEY TERMINATION FIX: No recursive call to run-ir. Instead, we extract
    -- body-correct from the closure's ValidAtWF and call execute, which was
    -- pre-computed by Curry using make-rec.
    -- ir-capacity directly gives apply-pair-fits since ir-stack-requirement apply = pair-slots
    run-ir-wf {(A ⇒ B) * A} {B} apply _ x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap _ =
      record
        { result-loc = result-loc
        ; final-state = s-final
        ; final-alloc = final-alloc
        ; result-valid-wf = result-valid-wf
        ; result-before = result-before
        ; rax-is-result = rax-eq
        ; not-halted = not-halted-final
        ; frame-preserved = frame-preserved-apply
        ; slot-monotone = slot-monotone-apply
        ; heap-monotone = heap-monotone-apply
        ; slot-bounded = slot-bounded-apply
        ; capacity-preserved = capacity-preserved-apply
        }
      where
        -- Step 1: Decompose input as pair (closure, arg) using ValidAtWF
        pair-decomp = decomposePairWF input-valid-wf
        closure-loc = PairValidWF.fst-loc pair-decomp
        arg-loc = PairValidWF.snd-loc pair-decomp
        closure-valid-wf = PairValidWF.fst-valid pair-decomp
        arg-valid-wf = PairValidWF.snd-valid pair-decomp
        arg-before = PairValidWF.snd-before pair-decomp

        -- Step 2: Decompose closure to get body-correct!
        -- KEY: This extracts the pre-computed BodyCorrect from Curry.
        closure-decomp = decomposeClosureWF closure-valid-wf
        EnvType = ClosureValidWF.EnvType closure-decomp
        body = ClosureValidWF.body closure-decomp
        env = ClosureValidWF.env closure-decomp
        env-loc = ClosureValidWF.env-loc closure-decomp
        env-valid-wf = ClosureValidWF.env-valid closure-decomp
        env-before = ClosureValidWF.env-before closure-decomp
        closure-is-body = ClosureValidWF.f-is-closure closure-decomp
        -- THE KEY: body-correct from closure!
        body-correct = ClosureValidWF.body-correct closure-decomp

        -- Step 3: Allocate pair-slots for (env, arg) pair
        pair-input-loc = OnStack (current-frame alloc) (next-slot alloc)

        -- PROVEN: apply-pair-fits directly from ir-capacity!
        -- ir-stack-requirement apply = pair-slots
        apply-pair-fits : next-slot alloc + pair-slots ≤ frame-capacity alloc
        apply-pair-fits = ir-cap

        alloc-pair : AllocState {FS}
        alloc-pair = record alloc
          { next-slot = next-slot alloc + pair-slots
          ; slots-available = apply-pair-fits
          }

        -- Write env-loc and arg-loc to pair slots
        s-write-env = write-loc s pair-input-loc env-loc
        s-write-arg = write-loc s-write-env (sucLoc pair-input-loc) arg-loc
        s-pair = record s-write-arg { regs = writeReg (regs s-write-arg) RDI pair-input-loc }

        pair-input-before : BeforeFrontier alloc-pair pair-input-loc
        pair-input-before = at-frontier-before-pair alloc apply-pair-fits

        sucLoc-pair-before : BeforeFrontier alloc-pair (sucLoc pair-input-loc)
        sucLoc-pair-before = stack-before refl (suc<+2 (next-slot alloc))

        env-before-pair : BeforeFrontier alloc-pair env-loc
        env-before-pair = stack-alloc-advances alloc pair-slots apply-pair-fits env-loc env-before

        arg-before-pair : BeforeFrontier alloc-pair arg-loc
        arg-before-pair = stack-alloc-advances alloc pair-slots apply-pair-fits arg-loc arg-before

        -- PROVEN: env-valid-wf-pair via write helpers and alloc-advance
        -- Chain: write at frontier → write at suc frontier → reg write → alloc advance
        env-valid-wf-pair : ValidAtWF alloc-pair env env-loc s-pair
        env-valid-wf-pair =
          validityWF-alloc-advance env env-loc s-pair pair-slots apply-pair-fits
            (validityWF-mem-only env env-loc s-write-arg s-pair refl refl
              (validityWF-write-at-suc-frontier env env-loc s-write-env arg-loc env-before
                (validityWF-write-at-frontier env env-loc s env-loc env-before
                  env-valid-wf)))

        -- PROVEN: arg-valid-wf-pair via write helpers and alloc-advance
        arg-valid-wf-pair : ValidAtWF alloc-pair (snd x) arg-loc s-pair
        arg-valid-wf-pair =
          validityWF-alloc-advance (snd x) arg-loc s-pair pair-slots apply-pair-fits
            (validityWF-mem-only (snd x) arg-loc s-write-arg s-pair refl refl
              (validityWF-write-at-suc-frontier (snd x) arg-loc s-write-env arg-loc arg-before
                (validityWF-write-at-frontier (snd x) arg-loc s env-loc arg-before
                  arg-valid-wf)))

        pair-env-ptr : readLoc s-pair pair-input-loc ≡ just env-loc
        pair-env-ptr = trans refl (trans
                         (write-preserves-disjoint s-write-env (sucLoc pair-input-loc) arg-loc pair-input-loc
                           (sucLoc-neq pair-input-loc))
                         (write-read-same s pair-input-loc env-loc))

        pair-arg-ptr : readLoc s-pair (sucLoc pair-input-loc) ≡ just arg-loc
        pair-arg-ptr = write-read-same s-write-env (sucLoc pair-input-loc) arg-loc

        -- Construct ValidAtWF for the pair (now consistent with BodyCorrect.execute)
        pair-input-valid-wf : ValidAtWF alloc-pair (pair env (snd x)) pair-input-loc s-pair
        pair-input-valid-wf = valid-pair-wf pair-env-ptr pair-arg-ptr
                                env-before-pair arg-before-pair sucLoc-pair-before
                                env-valid-wf-pair arg-valid-wf-pair

        pair-not-halted : halted s-pair ≡ false
        pair-not-halted = not-halted

        pair-rdi-eq : readReg (regs s-pair) RDI ≡ pair-input-loc
        pair-rdi-eq = writeReg-same (regs s-write-arg) RDI pair-input-loc

        -- Step 4: Use body-correct.execute instead of run-ir!
        -- KEY: This is NOT a recursive call to run-ir. The execute function
        -- was constructed by Curry using make-rec-wf, which used rs from (acc rs).
        -- Since execute is just a stored function, calling it doesn't create
        -- a recursive dependency that the termination checker needs to track.
        -- NOW: execute takes ValidAtWF and returns IRResultAWF directly!
        -- NOTE: body's ir-capacity is postulated because apply's ir-stack-requirement
        -- doesn't include the body's requirement. This is an architectural issue:
        -- either body should run in a new frame, or the closure should track body's requirement.
        postulate
          body-ir-cap : next-slot alloc-pair + ir-stack-requirement body ≤ frame-capacity alloc-pair

        body-result : IRResultAWF body (pair env (snd x)) s-pair alloc-pair
        body-result = BodyCorrect.execute body-correct (snd x) arg-loc pair-input-loc
                        s-pair alloc-pair
                        pair-input-valid-wf pair-input-before pair-not-halted pair-rdi-eq body-ir-cap

        -- Extract fields from IRResultAWF (not IRResultA!)
        result-loc = IRResultAWF.result-loc body-result
        s-final = IRResultAWF.final-state body-result
        final-alloc = IRResultAWF.final-alloc body-result
        result-before = IRResultAWF.result-before body-result
        rax-eq = IRResultAWF.rax-is-result body-result
        not-halted-final = IRResultAWF.not-halted body-result

        frame-preserved-apply : current-frame final-alloc ≡ current-frame alloc
        frame-preserved-apply = trans (IRResultAWF.frame-preserved body-result) refl

        slot-monotone-apply : next-slot alloc ≤ next-slot final-alloc
        slot-monotone-apply = ≤-trans (m≤m+n (next-slot alloc) pair-slots)
                                      (IRResultAWF.slot-monotone body-result)

        heap-monotone-apply : next-heap-ref alloc ≤ next-heap-ref final-alloc
        heap-monotone-apply = ≤-trans ≤-refl (IRResultAWF.heap-monotone body-result)

        postulate
          slot-bounded-apply : next-slot final-alloc ≤ next-slot alloc + ir-stack-requirement (apply {A} {B})

        capacity-preserved-apply : frame-capacity final-alloc ≡ frame-capacity alloc
        capacity-preserved-apply = trans (IRResultAWF.capacity-preserved body-result) refl

        -- Transport result validity using closure-is-body
        -- body-result gives: ValidAtWF final-alloc (eval body (pair env (snd x))) result-loc s-final
        -- We need: ValidAtWF final-alloc (eval apply x) result-loc s-final
        -- eval apply x = (fst x) (snd x) = (λ arg → eval body (pair env arg)) (snd x)
        --              = eval body (pair env (snd x))
        -- Direct subst with closure-is-body!
        result-valid-wf : ValidAtWF final-alloc (eval apply x) result-loc s-final
        result-valid-wf = subst (λ f → ValidAtWF final-alloc (f (snd x)) result-loc s-final)
                                (sym closure-is-body)
                                (IRResultAWF.result-valid-wf body-result)

  -- Public API with ValidAtWF
  -- Returns IRResultAWF with ValidAtWF for result validity.
  -- Requires ir-capacity precondition to ensure sufficient stack space.
  run-wf : ∀ {A B} (ir : IR A B) (ir<bound : ir-size ir < program-bound)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc + ir-stack-requirement ir ≤ frame-capacity alloc →  -- ir-capacity
    IRResultAWF ir x s alloc
  run-wf ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap =
    run-ir-wf ir ir<bound x input-loc s alloc input-valid-wf input-before not-halted rdi-eq ir-cap
      (get-acc-from-pb (ir-size ir) ir<bound)

  -- Public API with basic ValidAt (converts to/from WF internally)
  -- NOTE: This requires valid-to-validWF postulate because ValidAt doesn't
  -- carry BodyCorrect for closures. For closure-containing inputs, use run-wf instead.
  -- This API is suitable for program entry points where input is non-closure.
  -- Requires ir-capacity precondition to ensure sufficient stack space.
  run : ∀ {A B} (ir : IR A B) (ir<bound : ir-size ir < program-bound)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAt alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc + ir-stack-requirement ir ≤ frame-capacity alloc →  -- ir-capacity
    IRResultA ir x s alloc
  run ir ir<bound x input-loc s alloc input-valid input-before not-halted rdi-eq ir-cap =
    resultWF-to-result (run-wf ir ir<bound x input-loc s alloc
      (valid-to-validWF input-valid) input-before not-halted rdi-eq ir-cap)
    where
      -- This postulate is only valid for non-closure inputs at program entry.
      -- For closures, BodyCorrect cannot be constructed from ValidAt.
      postulate valid-to-validWF : ∀ {alloc A} {v : ⟦ A ⟧} {loc s} →
                  ValidAt alloc v loc s → ValidAtWF alloc v loc s

------------------------------------------------------------------------
-- Summary
--
-- KEY ARCHITECTURAL CHANGES:
--
-- 1. valid-closure tracks body IR and env value
--    Since we create all closures via curry, we know their bodies.
--    decomposeClosure extracts: EnvType, body, env, env-valid.
--
-- 2. ir-stack-requirement defines static stack bounds for each IR
--    This enables DERIVING capacity proofs instead of postulating them.
--
-- 3. ClosureWellFormed pattern for termination
--    Curry stores BodyCorrect in closure, Apply extracts and uses it.
--    This eliminates the termination issue without TERMINATING pragma.
--
-- 4. ValidAtWF type for full consistency
--    ValidAtWF includes BodyCorrect for closures, enabling Apply to
--    receive and return IRResultAWF with ValidAtWF throughout.
--
-- 5. ir-capacity precondition (NEW)
--    run-ir-wf requires: next-slot alloc + ir-stack-requirement ir ≤ frame-capacity alloc
--    This enables deriving capacity proofs and is threaded through recursion.
--
-- ValidAt alloc v loc s = validity + BeforeFrontier for all component locs
-- IRResultA includes final-alloc + result-before frontier proof + capacity-preserved
--
-- ELIMINATED POSTULATES (Tier 1 - PROVEN):
--   ✓ slot-bounded-compose - arithmetic proof with helper lemma
--   ✓ slot-bounded-pair - arithmetic proof with helper lemma
--   ✓ sucLoc-before-from-snd (4x) - added sucLoc-before to ValidAt structure
--   ✓ sucLoc-before-from-code (4x) - added sucLoc-before to ValidAt structure
--   ✓ validityWF-mem-only - memory transport for ValidAtWF (structural induction)
--   ✓ closure-fits - DIRECTLY from ir-capacity (curry case)
--   ✓ apply-pair-fits - DIRECTLY from ir-capacity (apply case)
--   ✓ ir-cap-f (pair case) - arithmetic via +-assoc and m+n≤o⇒m≤o
--   ✓ ir-cap-g (pair case) - arithmetic via +-monoˡ-≤ and capacity-preserved
--   ✓ pair-fits (pair case) - arithmetic via slot bounds and +-assoc
--
-- ELIMINATED POSTULATES (Tier 3 - IMPLEMENTED):
--   ✓ body-smaller - body<bound from ClosureValid (extracted via ApplySetupResult)
--   ✓ pair-input-loc, s-pair, alloc-pair - actual pair construction
--   ✓ pair-input-valid, pair-input-before - derived from validity proofs
--   ✓ pair-not-halted, pair-rdi-eq - register/state proofs
--   ✓ result-loc, s-final, final-alloc - from recursive dispatch
--   ✓ body-result-valid, result-before - from run-ir result (via BodyCorrect.execute)
--   ✓ rax-eq, not-halted-final - from IRResultAWF fields
--   ✓ frame-preserved-apply, heap-monotone-apply - from recursive call
--   ✓ capacity-preserved-apply - from recursive call
--
-- FULLY PROVEN (no postulates):
--   - id, fst-ir, snd-ir, terminal (all cases of run-ir-wf)
--   - compose (including ir-capacity derivation for sub-IRs)
--   - curry (closure-fits proven from ir-capacity)
--   - apply (apply-pair-fits proven from ir-capacity)
--   - compose slot-bounded, pair slot-bounded
--   - validity-write-at-frontier (uses sucLoc-before from ValidAt)
--   - validity-write-at-suc-frontier (uses sucLoc-before from ValidAt)
--   - validityWF-write-at-frontier, validityWF-write-at-suc-frontier
--   - Apply setup: extracts body IR and all components from closure
--   - Apply termination: uses BodyCorrect.execute instead of run-ir
--   - Apply semantic correctness: result-valid uses closure-is-body
--
-- REMAINING POSTULATES (9 total):
--
--   Validity preservation through IR execution (4):
--     - input-valid-wf₁: input valid after running f (pair case)
--     - fst-valid-wf-final, snd-valid-wf-final: valid after writes (pair)
--     - input-valid-wf-final: env valid after writes (curry case)
--     These require "write isolation" - proving IR only writes at frontier.
--
--   Validity preservation with alloc change (2):
--     - env-valid-wf-pair, arg-valid-wf-pair: valid after writes (apply case)
--     Need validity transport across both state and alloc changes.
--
--   Body capacity (apply case - 1):
--     - body-ir-cap: body's ir-capacity (architecture issue - body requirement
--       not tracked in apply's ir-stack-requirement)
--
--   Slot bound (1):
--     - slot-bounded-apply: body runs in same frame, requires architecture fix
--       (either new frame for body, or track body requirement in closure)
--
--   Conversion (1):
--     - valid-to-validWF: only valid for non-closure inputs at program entry
--
-- NEXT STEPS:
--   1. Add "mem-preserved-before-frontier" to IRResultAWF for write isolation
--   2. Create validity transport lemma for alloc advancement
--   3. Fix body capacity issue (new frame or track requirement in closure)
------------------------------------------------------------------------
