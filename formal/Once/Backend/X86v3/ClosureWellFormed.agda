------------------------------------------------------------------------
-- Once.Backend.X86v3.ClosureWellFormed
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

module Once.Backend.X86v3.ClosureWellFormed where

open import Data.Nat using (ℕ; _<_; _≤_; _≥_; _+_) renaming (_*_ to _*ℕ_)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

------------------------------------------------------------------------
-- BodyResult: Result type for body execution
--
-- When a closure body executes with (env, arg), it produces this result.
-- This is essentially IRResultA specialized to the body.
------------------------------------------------------------------------

module ClosureWellFormedDef {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open FrameSemantics FS

  -- Import IRResultA
  open import Once.Backend.X86v3.IRResult
  open DispatcherResult {FS} program-bound

  -- Import write operations for validity preservation proofs
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import capacity lemmas (needed for BodyCorrect.execute signature)
  open import Once.Backend.X86v3.Postulates
  open CapacityLemmas {FS} program-bound
    using (CapacityInvariant; SlotInWorking; program-bound-cap-from-invariant;
           invariant-preserved; slot-in-working-preserved; sub-ir-in-working;
           apply-pair-preserves-program-bound-cap)

  ------------------------------------------------------------------------
  -- Mutual block for BodyCorrect, ValidAtWF, IRResultAWF
  --
  -- These types are mutually dependent:
  -- - BodyCorrect.execute returns IRResultAWF
  -- - IRResultAWF.result-valid-wf uses ValidAtWF
  -- - ValidAtWF.valid-closure-wf uses BodyCorrect
  --
  -- Option A implementation: BodyCorrect.execute takes ValidAtWF input
  -- and returns IRResultAWF, making the whole system use ValidAtWF
  -- consistently. This eliminates the need for valid-to-validWF.
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- IRResultAWF: IR execution result with ValidAtWF
  --
  -- Defined first since BodyCorrect needs it.
  -- Uses forward declaration pattern for ValidAtWF.
  ------------------------------------------------------------------------

  -- Forward declare ValidAtWF type for IRResultAWF
  data ValidAtWF (alloc : AllocState {FS}) : {A : Type} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set

  record IRResultAWF {A B : Type}
                     (ir : IR A B)
                     (x : ⟦ A ⟧)
                     (s : LocState FS)
                     (alloc : AllocState {FS}) : Set where
    inductive
    field
      result-loc : ValueLocation FS
      final-state : LocState FS
      final-alloc : AllocState {FS}
      result-valid-wf : ValidAtWF final-alloc (eval ir x) result-loc final-state
      result-before : BeforeFrontier final-alloc result-loc
      rax-is-result : readReg (regs final-state) RAX ≡ result-loc
      not-halted : halted final-state ≡ false
      frame-preserved : current-frame final-alloc ≡ current-frame alloc
      slot-monotone : next-slot alloc ≤ next-slot final-alloc
      heap-monotone : next-heap-ref alloc ≤ next-heap-ref final-alloc
      -- Heap preservation: no heap allocation during stack-only IR operations
      heap-preserved : next-heap-ref final-alloc ≡ next-heap-ref alloc
      -- slot-bounded REMOVED: Using dynamic capacity threading instead (X86 pattern)
      -- Capacity is threaded via BodyCorrect.body-capacity for apply
      capacity-preserved : frame-capacity final-alloc ≡ frame-capacity alloc
      -- Write isolation: IR execution only writes at/after frontier
      -- Memory at BeforeFrontier locations is preserved
      mem-preserved-before : ∀ loc → BeforeFrontier alloc loc →
        readLoc final-state loc ≡ readLoc s loc

      -- Stack reclamation: After IR completes, only the result needs to persist.
      -- Intermediate allocations can be reclaimed to free stack space.
      reclaimable-slot : ℕ
      reclaim-monotone : next-slot alloc ≤ reclaimable-slot
      reclaim-bounded : reclaimable-slot ≤ next-slot final-alloc
      reclaim-preserves-result : ∀ (fits : reclaimable-slot ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = reclaimable-slot ; slots-available = fits }) result-loc
      -- Reclaim preserves validity: ValidAtWF at the reclaimed allocation
      -- This is the key lemma for compose/pair to transfer validity through reclamation
      -- Unlike frontier-advance, this handles the "backwards" direction of reclamation
      reclaim-preserves-validity : ∀ (fits : reclaimable-slot ≤ frame-capacity alloc) →
        ValidAtWF (record alloc { next-slot = reclaimable-slot ; slots-available = fits })
                  (eval ir x) result-loc final-state
      -- Reclaim size bound: reclaimable-slot is within the IR's size budget
      -- This replaces slot-bounded and IS provable for apply (reclaimable = slot + pair-slots)
      -- Used by compose/pair to derive capacity for subsequent operations
      reclaim-size-bound : reclaimable-slot ≤ next-slot alloc + pair-slots *ℕ ir-size ir

  open IRResultAWF public

  ------------------------------------------------------------------------
  -- BodyCorrect: Pre-computed proof that body execution works
  --
  -- Takes ValidAtWF input and returns IRResultAWF.
  -- Uses NO_POSITIVITY_CHECK because the mutual dependency with ValidAtWF
  -- is safe - BodyCorrect is only constructed in Curry using make-rec-wf,
  -- which is structurally smaller.
  --
  -- STACK-ALLOCATED RESULTS:
  -- Body CAN return stack-allocated values! Apply uses body's
  -- reclaimable-slot for reclamation, so stack slots below that survive.
  -- Body's reclaim-preserves-result proves result survives reclamation.
  -- No escape analysis postulate needed.
  ------------------------------------------------------------------------

  {-# NO_POSITIVITY_CHECK #-}
  record BodyCorrect {EnvType A B : Type}
                     (body : IR (EnvType * A) B)
                     (env : ⟦ EnvType ⟧)
                     (env-loc : ValueLocation FS)
                     (bound : ℕ) : Set where
    inductive
    field
      -- Body's capacity requirement, stored by Curry for Apply to use
      -- Set to: pair-slots * ir-size body
      -- This is the X86 backend pattern: closure carries its own capacity
      body-capacity : ℕ

      -- Equation proving body-capacity = pair-slots * ir-size body
      -- This lets Apply use arithmetic lemmas on body-capacity
      body-cap-eq : body-capacity ≡ pair-slots *ℕ ir-size body

      -- Given proper setup, body execution succeeds
      -- Returns IRResultAWF directly - no escape constraint needed!
      -- Apply uses body's reclaimable-slot for reclamation, so
      -- stack-allocated results below reclaimable-slot survive.
      execute : ∀ (arg : ⟦ A ⟧) (arg-loc pair-loc : ValueLocation FS)
        (s : LocState FS) (alloc : AllocState {FS}) →
        -- Preconditions (ValidAtWF for full consistency)
        ValidAtWF alloc (pair env arg) pair-loc s →
        BeforeFrontier alloc pair-loc →
        halted s ≡ false →
        readReg (regs s) RDI ≡ pair-loc →
        -- LINEAR capacity: body-capacity = pair-slots * ir-size body
        -- This is the ONLY capacity constraint needed
        next-slot alloc + body-capacity ≤ frame-capacity alloc →
        -- Result: IRResultAWF (stack-allocated results allowed!)
        IRResultAWF body (pair env arg) s alloc

  open BodyCorrect public

  ------------------------------------------------------------------------
  -- ValidAtWF: Validity with well-formedness for closures
  --
  -- Now defined after BodyCorrect (no cycle in definition).
  ------------------------------------------------------------------------

  data ValidAtWF alloc where

    valid-unit-wf : ∀ {loc s} →
      ValidAtWF alloc {Unit} tt loc s

    valid-pair-wf : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
      {pair-loc fst-loc snd-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s pair-loc ≡ just fst-loc →
      readLoc s (sucLoc pair-loc) ≡ just snd-loc →
      BeforeFrontier alloc fst-loc →
      BeforeFrontier alloc snd-loc →
      BeforeFrontier alloc (sucLoc pair-loc) →
      ValidAtWF alloc a fst-loc s →
      ValidAtWF alloc b snd-loc s →
      ValidAtWF alloc {A * B} (a , b) pair-loc s

    -- Closure with well-formedness: includes body-correct!
    -- body-correct is parameterized by program-bound for nested apply calls
    valid-closure-wf : ∀ {EnvType q A B}
      {body : IR (EnvType * A) B}
      {env : ⟦ EnvType ⟧}
      (body<bound : ir-size body < program-bound) →
      {closure-loc env-loc code-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s closure-loc ≡ just env-loc →
      readLoc s (sucLoc closure-loc) ≡ just code-loc →
      BeforeFrontier alloc env-loc →
      BeforeFrontier alloc code-loc →
      BeforeFrontier alloc (sucLoc closure-loc) →
      ValidAtWF alloc env env-loc s →
      -- THE KEY ADDITION: body-correct proof with program-bound
      BodyCorrect body env env-loc program-bound →
      ValidAtWF alloc {A ⇒[ q ] B} (λ arg → eval body (pair env arg)) closure-loc s

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
      env-ptr : readLoc s closure-loc ≡ just env-loc
      code-ptr : readLoc s (sucLoc closure-loc) ≡ just code-loc
      -- Frontier tracking
      env-before : BeforeFrontier alloc env-loc
      code-before : BeforeFrontier alloc code-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc closure-loc)
      -- Env validity (now using ValidAtWF)
      env-valid : ValidAtWF alloc env env-loc s
      -- PRE-COMPUTED body execution proof with program-bound
      body-correct : BodyCorrect body env env-loc program-bound

  open ClosureWellFormed public

  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF closures
  ------------------------------------------------------------------------

  record ClosureValidWF (alloc : AllocState {FS}) {q : Quantity} {A B : Type}
                        (f : ⟦ A ⇒[ q ] B ⟧)
                        (closure-loc : ValueLocation FS)
                        (s : LocState FS) : Set where
    field
      EnvType : Type
      body : IR (EnvType * A) B
      env : ⟦ EnvType ⟧
      body<bound : ir-size body < program-bound
      env-loc : ValueLocation FS
      code-loc : ValueLocation FS
      env-ptr : readLoc s closure-loc ≡ just env-loc
      code-ptr : readLoc s (sucLoc closure-loc) ≡ just code-loc
      env-before : BeforeFrontier alloc env-loc
      code-before : BeforeFrontier alloc code-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc closure-loc)
      env-valid : ValidAtWF alloc env env-loc s
      -- THE KEY: body-correct is extracted with program-bound!
      body-correct : BodyCorrect body env env-loc program-bound
      f-is-closure : f ≡ (λ arg → eval body (pair env arg))

  decomposeClosureWF : ∀ {alloc q A B} {f : ⟦ A ⇒[ q ] B ⟧} {loc s} →
    ValidAtWF alloc {A ⇒[ q ] B} f loc s → ClosureValidWF alloc {q} f loc s
  decomposeClosureWF (valid-closure-wf {EnvType} {_} {_} {_} {body} {env}
                       bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) = record
    { EnvType = EnvType
    ; body = body
    ; env = env
    ; body<bound = bb
    ; env-loc = el
    ; code-loc = cl
    ; env-ptr = ep
    ; code-ptr = cp
    ; env-before = eb
    ; code-before = cb
    ; sucLoc-before = slb
    ; env-valid = ev
    ; body-correct = bc
    ; f-is-closure = refl
    }

  ------------------------------------------------------------------------
  -- Conversion: ValidAtWF to ValidAt (drops body-correct)
  ------------------------------------------------------------------------

  validWF-to-valid : ∀ {alloc A} {v : ⟦ A ⟧} {loc s} →
    ValidAtWF alloc v loc s → ValidAt alloc v loc s

  validWF-to-valid valid-unit-wf = valid-unit

  validWF-to-valid (valid-pair-wf fp sp fb sb slb fv sv) =
    valid-pair fp sp fb sb slb (validWF-to-valid fv) (validWF-to-valid sv)

  validWF-to-valid (valid-closure-wf {body = body} {env = env} bb ep cp eb cb slb ev _) =
    valid-closure {body = body} {env = env} bb ep cp eb cb slb (validWF-to-valid ev)

  -- Convert IRResultAWF to IRResultA (drops body-correct info)
  resultWF-to-result : ∀ {A B} {ir : IR A B} {x s alloc} →
    IRResultAWF ir x s alloc → IRResultA ir x s alloc
  resultWF-to-result r = record
    { result-loc = IRResultAWF.result-loc r
    ; final-state = IRResultAWF.final-state r
    ; final-alloc = IRResultAWF.final-alloc r
    ; result-valid = validWF-to-valid (IRResultAWF.result-valid-wf r)
    ; result-before = IRResultAWF.result-before r
    ; rax-is-result = IRResultAWF.rax-is-result r
    ; not-halted = IRResultAWF.not-halted r
    ; frame-preserved = IRResultAWF.frame-preserved r
    ; slot-monotone = IRResultAWF.slot-monotone r
    ; heap-monotone = IRResultAWF.heap-monotone r
    ; capacity-preserved = IRResultAWF.capacity-preserved r
    ; reclaimable-slot = IRResultAWF.reclaimable-slot r
    ; reclaim-monotone = IRResultAWF.reclaim-monotone r
    ; reclaim-bounded = IRResultAWF.reclaim-bounded r
    ; reclaim-preserves-result = IRResultAWF.reclaim-preserves-result r
    ; reclaim-size-bound = IRResultAWF.reclaim-size-bound r
    }

  ------------------------------------------------------------------------
  -- RecDispatcherWF: Recursive dispatcher interface with ValidAtWF
  --
  -- Used by Curry to construct BodyCorrect.
  -- Takes ValidAtWF input and returns IRResultAWF with ValidAtWF output.
  --
  -- SIMPLIFIED: Only needs linear capacity (pair-slots * ir-size).
  -- No global invariants needed - capacity is threaded dynamically per closure.
  ------------------------------------------------------------------------

  RecDispatcherWF : ℕ → Set
  RecDispatcherWF bound = ∀ {A B} (ir : IR A B) →
    ir-size ir < bound →
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS) (s : LocState FS)
    (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- LINEAR capacity: pair-slots * ir-size covers ir-req + recursion
    next-slot alloc + pair-slots *ℕ ir-size ir ≤ frame-capacity alloc →
    IRResultAWF ir x s alloc

  ------------------------------------------------------------------------
  -- Decomposition for ValidAtWF pairs
  ------------------------------------------------------------------------

  record PairValidWF (alloc : AllocState {FS}) {A B : Type}
                     (p : ⟦ A * B ⟧)
                     (pair-loc : ValueLocation FS)
                     (s : LocState FS) : Set where
    field
      fst-loc : ValueLocation FS
      snd-loc : ValueLocation FS
      fst-ptr : readLoc s pair-loc ≡ just fst-loc
      snd-ptr : readLoc s (sucLoc pair-loc) ≡ just snd-loc
      fst-before : BeforeFrontier alloc fst-loc
      snd-before : BeforeFrontier alloc snd-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc pair-loc)
      fst-valid : ValidAtWF alloc (fst p) fst-loc s
      snd-valid : ValidAtWF alloc (snd p) snd-loc s

  decomposePairWF : ∀ {alloc A B} {p : ⟦ A * B ⟧} {loc s} →
    ValidAtWF alloc p loc s → PairValidWF alloc p loc s
  decomposePairWF (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) = record
    { fst-loc = fl
    ; snd-loc = sl
    ; fst-ptr = fp
    ; snd-ptr = sp
    ; fst-before = fb
    ; snd-before = sb
    ; sucLoc-before = slb
    ; fst-valid = fv
    ; snd-valid = sv
    }

  ------------------------------------------------------------------------
  -- Lift ValidAt to ValidAtWF for non-closure types
  --
  -- For Unit and pairs of non-closures, we can convert ValidAt to ValidAtWF.
  -- This is used when we don't have body-correct info but need ValidAtWF.
  ------------------------------------------------------------------------

  valid-to-validWF-unit : ∀ {alloc loc s} →
    ValidAtWF alloc {Unit} tt loc s
  valid-to-validWF-unit = valid-unit-wf

  ------------------------------------------------------------------------
  -- ValidAtWF memory-only dependence
  --
  -- ValidAtWF only depends on memory, not registers. When memory is
  -- preserved, validity transfers to a new state.
  ------------------------------------------------------------------------

  -- ValidAtWF only depends on memory, not registers
  -- When memory is preserved (stackMem and heapMem equal), validity transfers
  -- PROVEN by structural induction on ValidAtWF
  validityWF-mem-only : ∀ {alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    stackMem s₂ ≡ stackMem s₁ →
    heapMem s₂ ≡ heapMem s₁ →
    ValidAtWF alloc v loc s₁ → ValidAtWF alloc v loc s₂

  validityWF-mem-only {alloc} {Unit} tt loc s₁ s₂ stack-eq heap-eq valid-unit-wf =
    valid-unit-wf

  validityWF-mem-only {alloc} {A * B} (a , b) loc s₁ s₂ stack-eq heap-eq
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp' sp' fb sb slb fv' sv'
    where
      fp' : readLoc s₂ loc ≡ just fl
      fp' = trans (readLoc-stack-heap-eq s₂ s₁ loc stack-eq heap-eq) fp

      sp' : readLoc s₂ (sucLoc loc) ≡ just sl
      sp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) sp

      fv' : ValidAtWF alloc a fl s₂
      fv' = validityWF-mem-only a fl s₁ s₂ stack-eq heap-eq fv

      sv' : ValidAtWF alloc b sl s₂
      sv' = validityWF-mem-only b sl s₁ s₂ stack-eq heap-eq sv

  validityWF-mem-only {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s₁ s₂ stack-eq heap-eq
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep' cp' eb cb slb ev' bc
    where
      ep' : readLoc s₂ loc ≡ just el
      ep' = trans (readLoc-stack-heap-eq s₂ s₁ loc stack-eq heap-eq) ep

      cp' : readLoc s₂ (sucLoc loc) ≡ just cl
      cp' = trans (readLoc-stack-heap-eq s₂ s₁ (sucLoc loc) stack-eq heap-eq) cp

      ev' : ValidAtWF alloc env el s₂
      ev' = validityWF-mem-only env el s₁ s₂ stack-eq heap-eq ev

  ------------------------------------------------------------------------
  -- ValidAtWF preservation under writes to frontier locations
  --
  -- These are ValidAtWF versions of validity-write-at-frontier and
  -- validity-write-at-suc-frontier from ValidityWriteLemma.agda.
  ------------------------------------------------------------------------

  -- Import helpers for frontier inequality
  open import Data.Empty using (⊥-elim)
  open import Data.Nat.Properties using (1+n≰n; <⇒≤)
  open import Data.Nat using (suc)

  -- Helper: slot at next-slot is different from any slot before frontier
  at-frontier-neq-before-wf : ∀ (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    OnStack (current-frame alloc) (next-slot alloc) ≢ loc
  at-frontier-neq-before-wf alloc loc bf eq = fresh-stack-after alloc loc bf (sym eq)

  -- Helper: slot at suc next-slot is different from any slot before frontier
  suc-frontier-neq-before-wf : ∀ (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    OnStack (current-frame alloc) (suc (next-slot alloc)) ≢ loc
  suc-frontier-neq-before-wf alloc (OnStack .(current-frame alloc) .(suc (next-slot alloc)))
    (stack-before refl k<next) refl =
    ⊥-elim (1+n≰n (<⇒≤ k<next))
  suc-frontier-neq-before-wf alloc (OnStack f k) (stack-ancestor cf≺f _) eq
    with eq
  ... | refl = ≺⇒≢ cf≺f refl
  suc-frontier-neq-before-wf alloc (OnHeap r o) _ ()

  -- ValidAtWF is preserved when writing to at-frontier location
  validityWF-write-at-frontier : ∀ {alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAtWF alloc v loc s →
    ValidAtWF alloc v loc (write-loc s (OnStack (current-frame alloc) (next-slot alloc)) val)

  validityWF-write-at-frontier {alloc} {Unit} _ loc s val loc-before valid-unit-wf =
    valid-unit-wf

  validityWF-write-at-frontier {alloc} {A * B} (a , b) loc s val loc-before
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp' sp' fb sb slb fv' sv'
    where
      fresh = OnStack (current-frame alloc) (next-slot alloc)

      fp' : readLoc (write-loc s fresh val) loc ≡ just fl
      fp' = trans (write-preserves-disjoint s fresh val loc
                    (at-frontier-neq-before-wf alloc loc loc-before)) fp

      sp' : readLoc (write-loc s fresh val) (sucLoc loc) ≡ just sl
      sp' = trans (write-preserves-disjoint s fresh val (sucLoc loc)
                    (at-frontier-neq-before-wf alloc (sucLoc loc) slb)) sp

      fv' = validityWF-write-at-frontier a fl s val fb fv
      sv' = validityWF-write-at-frontier b sl s val sb sv

  validityWF-write-at-frontier {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s val loc-before
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep' cp' eb cb slb ev' bc
    where
      fresh = OnStack (current-frame alloc) (next-slot alloc)

      ep' : readLoc (write-loc s fresh val) loc ≡ just el
      ep' = trans (write-preserves-disjoint s fresh val loc
                    (at-frontier-neq-before-wf alloc loc loc-before)) ep

      cp' : readLoc (write-loc s fresh val) (sucLoc loc) ≡ just cl
      cp' = trans (write-preserves-disjoint s fresh val (sucLoc loc)
                    (at-frontier-neq-before-wf alloc (sucLoc loc) slb)) cp

      ev' = validityWF-write-at-frontier env el s val eb ev

  -- ValidAtWF is preserved when writing to suc-frontier location
  validityWF-write-at-suc-frontier : ∀ {alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAtWF alloc v loc s →
    ValidAtWF alloc v loc (write-loc s (OnStack (current-frame alloc) (suc (next-slot alloc))) val)

  validityWF-write-at-suc-frontier {alloc} {Unit} _ loc s val loc-before valid-unit-wf =
    valid-unit-wf

  validityWF-write-at-suc-frontier {alloc} {A * B} (a , b) loc s val loc-before
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp' sp' fb sb slb fv' sv'
    where
      fresh = OnStack (current-frame alloc) (suc (next-slot alloc))

      fp' : readLoc (write-loc s fresh val) loc ≡ just fl
      fp' = trans (write-preserves-disjoint s fresh val loc
                    (suc-frontier-neq-before-wf alloc loc loc-before)) fp

      sp' : readLoc (write-loc s fresh val) (sucLoc loc) ≡ just sl
      sp' = trans (write-preserves-disjoint s fresh val (sucLoc loc)
                    (suc-frontier-neq-before-wf alloc (sucLoc loc) slb)) sp

      fv' = validityWF-write-at-suc-frontier a fl s val fb fv
      sv' = validityWF-write-at-suc-frontier b sl s val sb sv

  validityWF-write-at-suc-frontier {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s val loc-before
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep' cp' eb cb slb ev' bc
    where
      fresh = OnStack (current-frame alloc) (suc (next-slot alloc))

      ep' : readLoc (write-loc s fresh val) loc ≡ just el
      ep' = trans (write-preserves-disjoint s fresh val loc
                    (suc-frontier-neq-before-wf alloc loc loc-before)) ep

      cp' : readLoc (write-loc s fresh val) (sucLoc loc) ≡ just cl
      cp' = trans (write-preserves-disjoint s fresh val (sucLoc loc)
                    (suc-frontier-neq-before-wf alloc (sucLoc loc) slb)) cp

      ev' = validityWF-write-at-suc-frontier env el s val eb ev

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

  validityWF-alloc-advance : ∀ {alloc A} (v : ⟦ A ⟧) loc s (n : ℕ)
    (fits : next-slot alloc + n ≤ frame-capacity alloc) →
    ValidAtWF alloc v loc s →
    let alloc' = record alloc { next-slot = next-slot alloc + n ; slots-available = fits }
    in ValidAtWF alloc' v loc s

  validityWF-alloc-advance {alloc} {Unit} tt loc s n fits valid-unit-wf =
    valid-unit-wf

  validityWF-alloc-advance {alloc} {A * B} (a , b) loc s n fits
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp sp fb' sb' slb' fv' sv'
    where
      alloc' = record alloc { next-slot = next-slot alloc + n ; slots-available = fits }
      fb' : BeforeFrontier alloc' fl
      fb' = stack-alloc-advances alloc n fits fl fb
      sb' : BeforeFrontier alloc' sl
      sb' = stack-alloc-advances alloc n fits sl sb
      slb' : BeforeFrontier alloc' (sucLoc loc)
      slb' = stack-alloc-advances alloc n fits (sucLoc loc) slb
      fv' = validityWF-alloc-advance a fl s n fits fv
      sv' = validityWF-alloc-advance b sl s n fits sv

  validityWF-alloc-advance {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s n fits
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep cp eb' cb' slb' ev' bc
    where
      alloc' = record alloc { next-slot = next-slot alloc + n ; slots-available = fits }
      eb' : BeforeFrontier alloc' el
      eb' = stack-alloc-advances alloc n fits el eb
      cb' : BeforeFrontier alloc' cl
      cb' = stack-alloc-advances alloc n fits cl cb
      slb' : BeforeFrontier alloc' (sucLoc loc)
      slb' = stack-alloc-advances alloc n fits (sucLoc loc) slb
      ev' = validityWF-alloc-advance env el s n fits ev

  ------------------------------------------------------------------------
  -- Validity transport across arbitrary frontier advancement
  --
  -- More general than validityWF-alloc-advance: works for any alloc'
  -- related by frontier-monotone properties (frame-preserved, slot/heap
  -- monotone). Used when transporting validity through IR execution.
  ------------------------------------------------------------------------

  validityWF-frontier-advance : ∀ {alloc alloc' A} (v : ⟦ A ⟧) loc (s : LocState FS) →
    current-frame alloc' ≡ current-frame alloc →
    next-slot alloc ≤ next-slot alloc' →
    next-heap-ref alloc ≤ next-heap-ref alloc' →
    ValidAtWF alloc v loc s →
    ValidAtWF alloc' v loc s

  validityWF-frontier-advance {alloc} {alloc'} {Unit} tt loc s cf-eq slot-≤ heap-≤ valid-unit-wf =
    valid-unit-wf

  validityWF-frontier-advance {alloc} {alloc'} {A * B} (a , b) loc s cf-eq slot-≤ heap-≤
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp sp fb' sb' slb' fv' sv'
    where
      fb' : BeforeFrontier alloc' fl
      fb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ fl fb
      sb' : BeforeFrontier alloc' sl
      sb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ sl sb
      slb' : BeforeFrontier alloc' (sucLoc loc)
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      fv' = validityWF-frontier-advance a fl s cf-eq slot-≤ heap-≤ fv
      sv' = validityWF-frontier-advance b sl s cf-eq slot-≤ heap-≤ sv

  validityWF-frontier-advance {alloc} {alloc'} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s cf-eq slot-≤ heap-≤
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep cp eb' cb' slb' ev' bc
    where
      eb' : BeforeFrontier alloc' el
      eb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ el eb
      cb' : BeforeFrontier alloc' cl
      cb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ cl cb
      slb' : BeforeFrontier alloc' (sucLoc loc)
      slb' = frontier-monotone alloc alloc' (sym cf-eq) slot-≤ heap-≤ (sucLoc loc) slb
      ev' = validityWF-frontier-advance env el s cf-eq slot-≤ heap-≤ ev

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

  validityWF-mem-preserved : ∀ {alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    BeforeFrontier alloc loc →
    (∀ loc' → BeforeFrontier alloc loc' → readLoc s₂ loc' ≡ readLoc s₁ loc') →
    ValidAtWF alloc v loc s₁ →
    ValidAtWF alloc v loc s₂

  validityWF-mem-preserved {alloc} {Unit} tt loc s₁ s₂ loc-before mem-eq valid-unit-wf =
    valid-unit-wf

  validityWF-mem-preserved {alloc} {A * B} (a , b) loc s₁ s₂ loc-before mem-eq
    (valid-pair-wf {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair-wf fp' sp' fb sb slb fv' sv'
    where
      -- loc is BeforeFrontier, so readLoc s₂ loc = readLoc s₁ loc
      -- But we can't directly derive BeforeFrontier loc from the structure...
      -- Actually we CAN'T use mem-eq loc loc-before because we need loc-before
      -- Wait - we have loc-before as a parameter! So we can use mem-eq loc loc-before.
      fp' : readLoc s₂ loc ≡ just fl
      fp' = trans (mem-eq loc loc-before) fp

      sp' : readLoc s₂ (sucLoc loc) ≡ just sl
      sp' = trans (mem-eq (sucLoc loc) slb) sp

      fv' = validityWF-mem-preserved a fl s₁ s₂ fb mem-eq fv
      sv' = validityWF-mem-preserved b sl s₁ s₂ sb mem-eq sv

  validityWF-mem-preserved {alloc} {A ⇒[ _ ] B} .(λ arg → eval body (pair env arg)) loc s₁ s₂ loc-before mem-eq
    (valid-closure-wf {body = body} {env = env} bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev bc) =
    valid-closure-wf bb ep' cp' eb cb slb ev' bc
    where
      ep' : readLoc s₂ loc ≡ just el
      ep' = trans (mem-eq loc loc-before) ep

      cp' : readLoc s₂ (sucLoc loc) ≡ just cl
      cp' = trans (mem-eq (sucLoc loc) slb) cp

      ev' = validityWF-mem-preserved env el s₁ s₂ eb mem-eq ev

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
  reclaim-alloc : (alloc : AllocState {FS}) (reclaim-slot : ℕ)
    (monotone : next-slot alloc ≤ reclaim-slot)
    (fits : reclaim-slot ≤ frame-capacity alloc) →
    AllocState {FS}
  reclaim-alloc alloc rs _ fits = record alloc
    { next-slot = rs
    ; slots-available = fits
    }

  -- BeforeFrontier is preserved after reclamation (frontier only advances)
  reclaim-preserves-frontier : ∀ (alloc : AllocState {FS}) reclaim-slot
    (monotone : next-slot alloc ≤ reclaim-slot)
    (fits : reclaim-slot ≤ frame-capacity alloc)
    (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    BeforeFrontier (reclaim-alloc alloc reclaim-slot monotone fits) loc
  reclaim-preserves-frontier alloc rs monotone fits loc bf =
    stack-alloc-advances' alloc rs monotone fits loc bf
    where
      -- Helper using existing stack-alloc-advances pattern
      stack-alloc-advances' : ∀ (alloc : AllocState {FS}) (rs : ℕ)
        (monotone : next-slot alloc ≤ rs)
        (fits : rs ≤ frame-capacity alloc)
        (loc : ValueLocation FS) →
        BeforeFrontier alloc loc →
        BeforeFrontier (record alloc { next-slot = rs ; slots-available = fits }) loc
      stack-alloc-advances' alloc rs monotone fits (OnStack f k) (stack-before refl k<next) =
        stack-before refl (<-≤-trans k<next monotone)
        where open import Data.Nat.Properties using (<-≤-trans)
      stack-alloc-advances' alloc rs monotone fits (OnStack f k) (stack-ancestor cf≺f src) =
        stack-ancestor cf≺f src  -- Frame ordering and provenance unchanged (same current-frame)
      stack-alloc-advances' alloc rs monotone fits (OnHeap r o) (heap-before r<next) =
        heap-before r<next

  -- ValidAtWF is preserved after reclamation
  validityWF-reclaim : ∀ {alloc A} (v : ⟦ A ⟧) loc s reclaim-slot
    (monotone : next-slot alloc ≤ reclaim-slot)
    (fits : reclaim-slot ≤ frame-capacity alloc)
    (loc-before : BeforeFrontier alloc loc) →
    ValidAtWF alloc v loc s →
    ValidAtWF (reclaim-alloc alloc reclaim-slot monotone fits) v loc s
  validityWF-reclaim {alloc} v loc s rs mono fits loc-bf valid =
    validityWF-frontier-advance v loc s refl mono ≤-refl valid
    where
      open import Data.Nat.Properties using (≤-refl)


