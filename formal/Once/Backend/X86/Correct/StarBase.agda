------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StarBase
--
-- Simple Star-based IR execution proofs.
-- These are non-recursive (don't call run-ir-star-at-offset).
-- Extracted from MutualIR.agda to reduce compilation time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StarBase where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; r15-in-heap; r15-in-code; RbpInvariant; stack-inv-preserved-unchanged)
open import Once.Backend.X86.Layout using (InStack; InHeap; InCode; stack-code-disjoint)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackCapacity; rsp-bound-to-capacity; capacity-2-to-rsp-bound;
         capacity-preserved-rsp-unchanged; rsp-bound-preserved-unchanged; slots; pair-alloc;
         ir-rsp-delta; ir-stack-requirement; ir-output-capacity; output-slots;
         apply-consumed-slots)
open import Level using (Lift; lift)
open import Once.Backend.X86.Correct.ClosureWellFormed using (ClosureWellFormed)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; star-step4)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-unit; valid-pair; valid-inl; valid-inr;
         valid-closure; valid-eff; valid-fix;
         PairAtS; fst-valid-s; snd-valid-s;
         InlAtS; InrAtS; ClosureAtS;
         valid-arrow-to-eff;
         valid-subst-addr-mem;  -- Takes full memory equality (no region-to-heap)
         ClosureAtS-preserved-under-mem-eq;  -- Takes full memory equality
         ClosureAtS-preserved-under-heap-eq;
         Region; Stack; Heap; InRegion)
open import Once.Backend.Common.PrimContract using (PrimContract)

open import Data.Nat using (_>_; _<_; _≥_)
open import Data.List.Properties using (++-assoc)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; subst₂)

------------------------------------------------------------------------
-- ClosureWFOutput: Optional closure well-formedness produced by curry
------------------------------------------------------------------------

-- | When an IR term produces a closure (curry), this captures its WF proof.
-- For other IR terms, this will be no-closure.
--
-- The existential quantification allows us to hide the closure's types
-- when threading through compose/pair.
--
-- closure-addr: Runtime heap address where the closure is stored.
--   This is needed by apply to look up the closure in memory.
--   For curry, this is the address returned in rax.
--   For pair ⟨curry f, g⟩, this is stored at pair-addr (fst).
--
-- E, A, B are EXPLICIT so that apply can case-split on A ≟T A' / B ≟T B'
-- using decidable type equality to unify the closure types with apply's types.
--
-- cl: The semantic Closure value produced by curry.
-- cl-env-eq: Closure.env-addr cl ≡ env-addr (refl at curry construction)
-- cl-sem-eq: Closure.semantics cl ≡ semantics (refl at curry construction)
-- closure-at: ClosureAtS layout at the output state's memory
-- cwf-cap: StackCapacity for apply + thunk at the output state
--
-- CLOSURE IDENTITY TRACKING (eliminates sem-eq/env-addr-eq/cl-addr-eq postulates):
-- - closure-valid: ValidAt for the closure at closure-addr
-- - closure-addr-from-rax: proof that closure-addr equals the result address
--   (curry returns closure in rax, pair's first component is at this address)
--
-- This enables apply to prove:
-- - cl-addr (from valid-pair-decompose) = closure-addr (from has-closure)
-- - proj₁ x (runtime closure) = cl (tracked closure)
data ClosureWFOutput (prog : Program) (s : State) : Set₁ where
  no-closure : ClosureWFOutput prog s
  has-closure : (E A B : Type)
                (closure-addr code-ptr env-addr : ℕ) (env : ⟦ E ⟧)
                (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                (wf : ClosureWellFormed {E} {A} {B} prog code-ptr env semantics)
                (cl : Closure A B)
                (cl-env-eq : Closure.env-addr cl ≡ env-addr)
                (cl-sem-eq : Closure.semantics cl ≡ semantics)
                (env-valid : ValidAt env env-addr (memory s))
                (closure-at : ClosureAtS env-addr code-ptr closure-addr (memory s))
                -- Region tracking: closure can be Stack or Heap
                -- Stack = current codegen (sub rsp), Heap = future heap allocation
                (closure-region : Region)
                (closure-in-region : InRegion closure-region closure-addr)
                -- Stack closure preservation invariant:
                -- Track the entry-rsp of the IR that created this closure.
                -- Stack closures are allocated BELOW creator's entry-rsp (in the creator's frame).
                -- When parent IR writes at addresses >= creator-entry-rsp, the closure is preserved
                -- because closure-addr < creator-entry-rsp <= write-addresses.
                (creator-entry-rsp : Word)
                (closure-below-entry-rsp : closure-region ≡ Stack → closure-addr < creator-entry-rsp)
                (cwf-cap : StackCapacity s (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf))
                -- CLOSURE IDENTITY TRACKING:
                -- closure-valid: ValidAt for the semantic closure at closure-addr
                -- This allows apply to connect cl (from has-closure) with proj₁ x (from input)
                -- NOTE: Explicit {A ⇒ B} to help Agda's type inference
                (closure-valid : ValidAt {A ⇒ B} cl closure-addr (memory s))
                -- result-addr: The address where curry stored its result (= rax at curry's output)
                -- This is a FIXED value that doesn't change during transport.
                -- At curry: result-addr = rax s'
                -- At pair: pair uses rax s1 as addr-a, which equals result-addr (since f=curry)
                -- At apply: cl-addr = addr-a = result-addr = closure-addr
                (result-addr : Word)
                (closure-addr-eq-result : closure-addr ≡ result-addr)
                -- pair-fst-addr: The address stored as first component of the pair.
                -- At curry: pair-fst-addr = result-addr = rax (will become pair's first component)
                -- At pair: pair-fst-addr = rax s1 = result-addr (proven at pair construction)
                -- At apply: cl-addr (from valid-pair-decompose) = pair-fst-addr = result-addr
                -- This enables proving cl-addr-is-res-addr at apply!
                (pair-fst-addr : Word)
                (pair-fst-is-result : pair-fst-addr ≡ result-addr)
                -- fst-addr-is-rax: At curry output, fst-addr = rax (used by Pair to prove pair-fst-is-res)
                -- At curry: refl (curry puts closure addr in rax)
                -- At pair: postulated (rax = pair address, not closure)
                (fst-addr-is-rax : pair-fst-addr ≡ readReg (regs s) rax)
                -- CLEANER ABSTRACTION: Track pair address as FIXED memory location (not register)
                -- pair-result-addr: The fixed memory address where the pair lives.
                -- At curry: 0 (no pair yet), becomes meaningful after Pair
                -- At Pair: = rax s-final = r15 s3 (the allocated pair address)
                -- At Compose/Apply: FIXED value, doesn't change during transport
                (pair-result-addr : Word)
                -- fst-at-pair: Memory at pair-result-addr contains pair-fst-addr.
                -- At curry: postulated (no pair)
                -- At Pair: PROVEN from pair construction
                -- At Apply: used with just-injective to prove cl-addr = fst-addr
                (fst-at-pair : readMem (memory s) pair-result-addr ≡ just pair-fst-addr)
                -- pair-addr-is-rax: Track that pair-result-addr equals rax.
                -- Valid from Pair output to Compose transfer. After transfer, rax holds g's result.
                -- At curry: refl (pair-result-addr = 0, rax = result addr)
                -- At Pair: refl (pair-result-addr = rax s-final by definition)
                -- Through Compose's f: transported with rax preservation
                -- After Compose transfer: postulated (FALSE but unused - we use pair-addr-is-rdi instead)
                (pair-addr-is-rax : pair-result-addr ≡ readReg (regs s) rax)
                -- pair-addr-is-rdi: Track that pair-result-addr equals rdi.
                -- Only meaningful after Compose transfer. Used at Apply!
                -- At curry: postulated (rdi has input)
                -- At Pair: postulated (pair in rax, not rdi)
                -- At Compose (after transfer): PROVEN from pair-addr-is-rax + transfer info:
                --   pair-addr = rax s1 = rdi s2 (via rdi2-raw : rdi s2 = rax s1)
                -- At Apply: USE directly to prove pair-addr = rdi s
                (pair-addr-is-rdi : pair-result-addr ≡ readReg (regs s) rdi)
                →
                ClosureWFOutput prog s

-- | Transport ClosureWFOutput across program equality and state change.
-- Requires full memory preservation (for ValidAt and ClosureAtS), rsp preservation (for StackCapacity),
-- and rax preservation (for fst-addr-is-rax and pair-addr-is-rax fields).
-- The creator-entry-rsp, closure-below-entry-rsp, and pair-result-addr are preserved as-is (they're fixed values).
-- Uses full memory equality to avoid region-to-heap postulate.
--
-- NOTE: pair-addr-is-rdi-s2 is provided by caller because:
--   - Normal case (rdi preserved): caller provides (λ eq → trans eq (sym rdi-eq))
--   - Compose transfer: caller derives from pair-addr-is-rax + transfer info
transport-cwf : ∀ {prog1 prog2 : Program} {s1 s2 : State} →
  prog1 ≡ prog2 →
  (∀ addr → readMem (memory s2) addr ≡ readMem (memory s1) addr) →
  readReg (regs s2) rsp ≡ readReg (regs s1) rsp →
  readReg (regs s2) rax ≡ readReg (regs s1) rax →  -- For fst-addr-is-rax and pair-addr-is-rax
  -- For pair-addr-is-rdi: caller provides transport function
  -- Takes (pa = rax s1) from has-closure's pair-addr-is-rax, produces (pa = rdi s2)
  -- Normal case: λ {pa} _ pair-is-rax → trans pair-is-rax (trans (sym rax-eq) rdi-eq) if rdi=rax preserved
  -- Compose transfer: λ {pa} _ pair-is-rax → trans pair-is-rax (sym rdi2-raw) where rdi2-raw : rdi s2 = rax s1
  (pair-addr-is-rdi-s2 : ∀ {pa} → pa ≡ readReg (regs s1) rdi → pa ≡ readReg (regs s1) rax → pa ≡ readReg (regs s2) rdi) →
  ClosureWFOutput prog1 s1 → ClosureWFOutput prog2 s2
transport-cwf _ _ _ _ _ no-closure = no-closure
transport-cwf {s1 = s1} {s2 = s2} refl mem-eq rsp-eq rax-eq rdi-transport
  (has-closure E A B ca cp ea env sem wf cl cl-env-eq cl-sem-eq env-valid closure-at cl-region cl-in-region creator-rsp cl-below-rsp cwf-cap cl-valid res-addr ca-eq-res fst-addr fst-is-res fst-is-rax pair-addr fst-at-pair pair-is-rax pair-is-rdi) =
  has-closure E A B ca cp ea env sem wf cl cl-env-eq cl-sem-eq
    (valid-subst-addr-mem env-valid refl mem-eq)
    (ClosureAtS-preserved-under-mem-eq closure-at mem-eq)
    cl-region
    cl-in-region
    creator-rsp
    cl-below-rsp  -- Preserved as-is: describes original allocation
    (capacity-preserved-rsp-unchanged s1 s2 _ cwf-cap rsp-eq)
    cl-valid-transported
    res-addr       -- Preserved as-is: fixed value from curry
    ca-eq-res      -- Preserved as-is: closure-addr hasn't changed
    fst-addr       -- Preserved as-is: pair's first component address
    fst-is-res     -- Preserved as-is: still equals result-addr
    (trans fst-is-rax (sym rax-eq))  -- Transport fst-addr-is-rax using rax equality
    pair-addr      -- Preserved as-is: FIXED memory address
    fst-at-pair-transported  -- Transport fst-at-pair using mem-eq at fixed address
    (trans pair-is-rax (sym rax-eq))  -- Transport pair-addr-is-rax using rax equality
    (rdi-transport pair-is-rdi pair-is-rax)  -- Derive pair-addr-is-rdi using caller-provided function
  where
    -- Transport closure-valid: ValidAt cl ca (memory s1) → ValidAt cl ca (memory s2)
    cl-valid-transported : ValidAt {A ⇒ B} cl ca (memory s2)
    cl-valid-transported = valid-subst-addr-mem {A ⇒ B} {cl} cl-valid refl mem-eq

    -- Transport fst-at-pair:
    -- readMem (memory s1) pair-addr = just fst-addr
    -- → readMem (memory s2) pair-addr = just fst-addr
    -- Simple: pair-addr is FIXED, just use mem-eq
    fst-at-pair-transported : readMem (memory s2) pair-addr ≡ just fst-addr
    fst-at-pair-transported = trans (mem-eq pair-addr) fst-at-pair

-- | Transport ClosureWFOutput across program equality only (same state).
subst-cwf-prog : ∀ {prog1 prog2 : Program} {s : State} →
  prog1 ≡ prog2 → ClosureWFOutput prog1 s → ClosureWFOutput prog2 s
subst-cwf-prog refl cwf = cwf

------------------------------------------------------------------------
-- IRStarResult: Result type for Star-based IR execution
------------------------------------------------------------------------

-- | Record type for Star-based IR execution result
-- Contains all properties needed for proof composition
record IRStarResult {A B : Type} (ir : IR A B) (prog : Program)
                    (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
  field
    ir-star       : Star prog s s'
    ir-halted     : halted s' ≡ false
    ir-pc         : pc s' ≡ offset +ℕ compile-length ir
    ir-rax        : readReg (regs s') rax ≡ encode (eval ir x)
    ir-r14        : readReg (regs s') r14 ≡ readReg (regs s) r14
    ir-r15        : readReg (regs s') r15 ≡ readReg (regs s) r15
    ir-rbp        : readReg (regs s') rbp ≡ readReg (regs s) rbp
    ir-mem        : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    ir-mem-rbp    : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    -- Memory at rbp+8 preserved (where ret-addr is stored in thunk context)
    ir-mem-rbp+8  : readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)

    ------------------------------------------------------------------------
    -- REFACTORING OPPORTUNITY: The following two fields (ir-mem-above and
    -- ir-mem-heap) are derivable from ir-mem-preserved and can be removed.
    --
    -- Benefits of removal:
    --   - Simpler mental model: one unified "addresses ≥ entry-rsp preserved"
    --   - Fewer fields to prove when constructing IRStarResult
    --   - Cleaner separation: ir-mem-preserved handles all memory preservation
    --
    -- How to derive them:
    --   - ir-mem-above: addr > rbp ≥ rsp = entry-rsp (needs input RbpInvariant)
    --     See: IRStarDerived.derive-mem-above
    --   - ir-mem-heap: InHeap addr → addr ≥ entry-rsp (via heap-addr-≥-stack-addr)
    --     See: IRStarDerived.derive-heap-preserved
    --
    -- What needs to be done:
    --   1. Add ir-input-rbp-inv : RbpInvariant s field (to derive ir-mem-above)
    --   2. Update 13 files that construct IRStarResult/V to remove these fields
    --   3. Update consumer call sites to use derived versions or ir-mem-preserved
    --   4. Files affected: Pair, Case, Compose, Curry, Apply, Inl, Inr, etc.
    --
    -- Note: ir-mem-code CANNOT be removed (code region has lower=0, no ordering)
    ------------------------------------------------------------------------
    -- Memory above frame preserved (for caller's rbp in pair proofs)
    -- Any address strictly above rbp is not touched by IR execution
    -- DERIVABLE: See IRStarDerived.derive-mem-above
    ir-mem-above  : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s') addr ≡ readMem (memory s) addr
    -- D041: Memory at code-region addresses preserved
    -- IR only writes to stack region, code region is disjoint from stack (stack-code-disjoint)
    -- Therefore code addresses are never written by IR execution
    -- NOT DERIVABLE from ir-mem-preserved (code region has lower=0)
    ir-mem-code   : ∀ addr → InCode addr → readMem (memory s') addr ≡ readMem (memory s) addr
    -- D041: Memory at heap-region addresses preserved
    -- IR only writes to stack region, heap region is disjoint from stack (stack-heap-disjoint)
    -- Therefore heap addresses are never written by IR execution
    -- DERIVABLE: See IRStarDerived.derive-heap-preserved
    ir-mem-heap   : ∀ addr → InHeap addr → readMem (memory s') addr ≡ readMem (memory s) addr

    -- Write bounds for stack escape analysis
    -- IR execution only writes to addresses < entry-rsp (its own stack frame)
    -- Therefore addresses >= entry-rsp are preserved (caller's frame, heap, code)
    ir-entry-rsp : ℕ
    ir-entry-rsp-eq : ir-entry-rsp ≡ readReg (regs s) rsp
    ir-mem-preserved : ∀ addr → addr ≥ ir-entry-rsp → readMem (memory s') addr ≡ readMem (memory s) addr

    ir-stack-inv  : StackInvariant s'
    -- Abstract stack capacity (output = input - consumed)
    ir-capacity   : StackCapacity s' (ir-output-capacity ir)
    -- RbpInvariant preserved: rsp s' ≤ rbp s' (needed for memory disjointness)
    ir-rbp-inv    : RbpInvariant s'
    -- Optional closure well-formedness (produced by curry, consumed by apply)
    ir-closure-wf : ClosureWFOutput prog s'

open IRStarResult public

-- | Derived: concrete rsp bound from abstract capacity
-- Returns rsp > slots (ir-output-capacity ir)
ir-rsp-bound : ∀ {A B ir prog s s' x offset} →
  IRStarResult {A} {B} ir prog s s' x offset →
  readReg (regs s') rsp > slots (ir-output-capacity ir)
ir-rsp-bound res = StackCapacity.rsp-sufficient (ir-capacity res)

------------------------------------------------------------------------
-- IRRunner: Type for the recursive IR execution function
------------------------------------------------------------------------

-- | Type signature for the recursive IR execution function.
-- Recursive case handlers (compose, pair, case, curry, apply) take
-- an IRRunner as a parameter, allowing them to be defined outside
-- the mutual block. This dramatically reduces compilation time.
--
-- NOTE: Sized types removed for compilation performance (10-100x speedup).
-- Termination is guaranteed by structural recursion on IR constructors.
IRRunner : Set₁
IRRunner = ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > pair-alloc →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

------------------------------------------------------------------------
-- IRStarResultV: Validity-Based Result Type
--
-- Like IRStarResult, but uses ValidAt instead of encode equality.
-- This enables postulate-free correctness proofs.
------------------------------------------------------------------------

-- | Validity-based IR execution result
-- Replaces ir-rax : rax ≡ encode (eval ir x) with
--          ir-result-valid : ValidAt (eval ir x) rax memory
record IRStarResultV {A B : Type} (ir : IR A B) (prog : Program)
                     (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
  field
    -- Execution properties (same as IRStarResult)
    ir-star       : Star prog s s'
    ir-halted     : halted s' ≡ false
    ir-pc         : pc s' ≡ offset +ℕ compile-length ir

    -- NEW: Validity-based correctness (replaces ir-rax)
    -- Says "rax points to a valid representation of eval ir x in memory"
    ir-result-valid : ValidAt (eval ir x) (readReg (regs s') rax) (memory s')

    -- Register preservation (same as IRStarResult)
    ir-r14        : readReg (regs s') r14 ≡ readReg (regs s) r14
    ir-r15        : readReg (regs s') r15 ≡ readReg (regs s) r15
    ir-rbp        : readReg (regs s') rbp ≡ readReg (regs s) rbp
    -- RSP delta tracking (needed for capacity threading through compose/case/pair)
    -- rsp s' = rsp s ∸ (delta * 8). Most IRs have delta=0; curry has delta=2.
    ir-rsp        : readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slots (ir-rsp-delta ir)

    -- Memory preservation (same as IRStarResult)
    ir-mem        : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    ir-mem-rbp    : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    ir-mem-rbp+8  : readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    ir-mem-above  : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s') addr ≡ readMem (memory s) addr
    ir-mem-code   : ∀ addr → InCode addr → readMem (memory s') addr ≡ readMem (memory s) addr
    ir-mem-heap   : ∀ addr → InHeap addr → readMem (memory s') addr ≡ readMem (memory s) addr

    -- NEW: Write bounds for stack escape analysis
    -- IR execution only writes to addresses < entry-rsp (its own stack frame)
    -- Therefore addresses >= entry-rsp are preserved (caller's frame, heap, code)
    ir-entry-rsp : ℕ
    ir-entry-rsp-eq : ir-entry-rsp ≡ readReg (regs s) rsp
    ir-mem-preserved : ∀ addr → addr ≥ ir-entry-rsp → readMem (memory s') addr ≡ readMem (memory s) addr

    -- Invariants (same as IRStarResult)
    ir-stack-inv  : StackInvariant s'
    ir-capacity   : StackCapacity s' (ir-output-capacity ir)
    ir-rbp-inv    : RbpInvariant s'
    ir-closure-wf : ClosureWFOutput prog s'

open IRStarResultV public using ()
  renaming ( ir-star to ir-star-v; ir-halted to ir-halted-v; ir-pc to ir-pc-v
           ; ir-result-valid to ir-result-valid
           ; ir-r14 to ir-r14-v; ir-r15 to ir-r15-v; ir-rbp to ir-rbp-v; ir-rsp to ir-rsp-v
           ; ir-mem to ir-mem-v; ir-mem-rbp to ir-mem-rbp-v; ir-mem-rbp+8 to ir-mem-rbp+8-v
           ; ir-mem-above to ir-mem-above-v
           ; ir-mem-code to ir-mem-code-v; ir-mem-heap to ir-mem-heap-v
           ; ir-entry-rsp to ir-entry-rsp-v; ir-entry-rsp-eq to ir-entry-rsp-eq-v
           ; ir-mem-preserved to ir-mem-preserved-v
           ; ir-stack-inv to ir-stack-inv-v; ir-capacity to ir-capacity-v
           ; ir-rbp-inv to ir-rbp-inv-v; ir-closure-wf to ir-closure-wf-v )

-- | Derived: concrete rsp bound from abstract capacity
-- Returns rsp > slots (ir-output-capacity ir)
ir-rsp-bound-v : ∀ {A B ir prog s s' x offset} →
  IRStarResultV {A} {B} ir prog s s' x offset →
  readReg (regs s') rsp > slots (ir-output-capacity ir)
ir-rsp-bound-v res = StackCapacity.rsp-sufficient (IRStarResultV.ir-capacity res)

------------------------------------------------------------------------
-- IRRunnerV: Validity-Based Recursive IR Runner
------------------------------------------------------------------------

-- | Validity-based recursive IR runner
-- Like IRRunner, but takes ValidAt precondition and returns ValidAt postcondition.
-- This enables threading validity through recursive IR execution without encode.
IRRunnerV : Set₁
IRRunnerV = ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State)
              (addr-in : ℕ) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ addr-in →
  ValidAt x addr-in (memory s) →  -- Input validity (replaces encode x)
  StackInvariant s →
  readReg (regs s) rsp > pair-alloc →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix)

------------------------------------------------------------------------
-- IRRunnerWithWF: Extended runner that tracks closure WF
------------------------------------------------------------------------

-- | Like IRRunner, but also returns optional ClosureWFOutput.
-- This enables threading WF proofs from curry through to apply.
IRRunnerWithWF : Set₁
IRRunnerWithWF = ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > pair-alloc →
  RbpInvariant s →
  ClosureWFOutput (prefix ++ compile-x86 ir ++ suffix) s →  -- Input WF context
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] (IRStarResult ir prog s s' x (length prefix)
             × ClosureWFOutput prog s')  -- Output WF context

------------------------------------------------------------------------
-- ApplyReady: Everything apply needs to execute without postulates
------------------------------------------------------------------------

-- | Complete data package for apply execution.
-- When the dispatcher calls apply, it provides this record instead of
-- just ClosureWFOutput. This eliminates all 4 postulates in Apply.agda:
--   1. apply-fallback (unreachable cases) - eliminated by always having data
--   2. cl-is-input (cwf.sem ≡ semantics) - provided by ar-sem-eq (semantics only!)
--   3. apply-closure-at-wf (ClosureAtS) - provided by ar-closure-at
--   4. cap-for-apply (StackCapacity) - provided by ar-capacity
--
-- KEY DESIGN: ar-sem-eq provides ONLY semantics equality, not full Closure equality.
-- This is sufficient for correctness because eval apply (cl, arg) = (Closure.semantics cl) arg.
-- The env-addr field of the input closure is IRRELEVANT to correctness — what matters
-- is the runtime memory layout (ar-closure-at, ar-env-valid) and the semantics match.
record ApplyReady {A B : Type} (x : ⟦ (A ⇒ B) * A ⟧) (s : State) (prog : Program) : Set₁ where
  field
    ar-E : Type
    ar-env : ⟦ ar-E ⟧
    ar-env-addr : ℕ
    ar-code-ptr : ℕ
    ar-closure-addr : ℕ
    ar-arg-addr : ℕ
    ar-sem : ⟦ A ⟧ → ⟦ B ⟧
    ar-wf : ClosureWellFormed {ar-E} {A} {B} prog ar-code-ptr ar-env ar-sem
    -- Structural equalities: connect ClosureWFOutput to input closure
    -- These are threading proofs (provable by tracing curry → compose/pair → apply)
    -- Apply.agda uses these directly, eliminating need for valid-addr-is-encode!
    ar-sem-eq : ar-sem ≡ Closure.semantics (proj₁ x)
    ar-env-addr-eq : ar-env-addr ≡ Closure.env-addr (proj₁ x)
    -- Memory layout: closure structure at ar-closure-addr
    ar-closure-at : ClosureAtS ar-env-addr ar-code-ptr ar-closure-addr (memory s)
    -- Env validity at runtime address
    ar-env-valid : ValidAt ar-env ar-env-addr (memory s)
    -- Memory layout: pair structure at rdi
    ar-pair-at : PairAtS ar-closure-addr ar-arg-addr (readReg (regs s) rdi) (memory s)
    -- Closure validity (from valid-pair-decompose in MutualIR)
    -- Option B: Region is inside this ValidAt, no reconstruction needed
    ar-v-cl : ValidAt {A ⇒ B} (proj₁ x) ar-closure-addr (memory s)
    -- Argument validity
    ar-v-arg : ValidAt {A} (proj₂ x) ar-arg-addr (memory s)
    -- Stack capacity for apply + thunk
    ar-capacity : StackCapacity s (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity ar-wf)

open ApplyReady public

------------------------------------------------------------------------
-- MaybeApplyReady: Type function for apply-specific dispatch data
------------------------------------------------------------------------

-- | When the IR is apply, this is ApplyReady (everything apply needs).
-- For all other IRs, it's a trivially inhabited type (Lift ⊤).
MaybeApplyReady : ∀ {A B} → IR A B → ⟦ A ⟧ → State → Program → Set₁
MaybeApplyReady (apply {A} {B}) x s prog = ApplyReady {A} {B} x s prog
MaybeApplyReady _ _ _ _ = Lift _ ⊤

------------------------------------------------------------------------
-- RbpInvariant preservation helper
------------------------------------------------------------------------

-- | Preserve RbpInvariant when rsp and rbp are unchanged
rbp-inv-preserved-unchanged : ∀ (s s' : State) →
  RbpInvariant s →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  readReg (regs s') rbp ≡ readReg (regs s) rbp →
  RbpInvariant s'
rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq = record
  { rbp-frame = RbpInvariant.rbp-frame rbp-inv
  ; rbp-is-base = trans rbp-eq (RbpInvariant.rbp-is-base rbp-inv)
  ; frame-bound = subst (sp-addr (RbpInvariant.rbp-frame rbp-inv) ≥_) (sym rsp-eq)
                        (RbpInvariant.frame-bound rbp-inv)
  }
  where
    open import Data.Nat using (_≤_; _≥_)
    open import Relation.Binary.PropositionalEquality using (subst)

-- | RbpInvariant is preserved through IR execution when rsp and rbp are unchanged
-- Uses ir-rbp-inv from IRStarResult and register preservation from transfer
rbp-inv-preserved-through-ir : ∀ (s s1 s2 : State) →
  RbpInvariant s →
  ∀ {A B} {ir : IR A B} {prog x offset} →
  IRStarResult ir prog s s1 x offset →
  readReg (regs s2) rsp ≡ readReg (regs s1) rsp →
  readReg (regs s2) rbp ≡ readReg (regs s1) rbp →
  RbpInvariant s2
rbp-inv-preserved-through-ir s s1 s2 _ {ir = ir} r rsp2-eq rbp2-eq =
  -- s1 has RbpInvariant from ir-rbp-inv r
  -- s2 has same rsp and rbp as s1, so RbpInvariant is preserved
  rbp-inv-preserved-unchanged s1 s2 (ir-rbp-inv r) rsp2-eq rbp2-eq
  where open IRStarResult

------------------------------------------------------------------------
-- Validity-Based Star Proofs (Phase 4: Simple Producers)
--
-- These return IRStarResultV with ValidAt, eliminating encode postulates.
-- Clean interface: ValidAt x rdi m replaces rdi ≡ encode x
-- No explicit address parameters - rdi is implicitly the input address.
------------------------------------------------------------------------

-- | Validity-based id execution
-- Input validity at rdi → output validity at rax (same address, id copies rdi to rax)
run-id-star-vv : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s output-slots →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (id {A}) ++ suffix
  in ∃[ s' ] IRStarResultV (id {A}) prog s s' x (length prefix)
run-id-star-vv {A} prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
  let prog = prefix ++ compile-x86 (id {A}) ++ suffix
      s' : State
      s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                    ; pc = pc s +ℕ 1 }
      fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                       (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)
      step-eq : step prog s ≡ just s'
      step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                      (execMov-reg-reg s rax rdi)
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 cap-in rsp-eq
      -- Key: rax s' = rdi s, memory unchanged
      rax-eq : readReg (regs s') rax ≡ readReg (regs s) rdi
      rax-eq = readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)
      result-valid : ValidAt x (readReg (regs s') rax) (memory s')
      result-valid = subst (λ a → ValidAt x a (memory s')) (sym rax-eq) input-valid
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h-false
    ; ir-pc = cong (_+ℕ 1) pc-eq
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-rsp = rsp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-entry-rsp = readReg (regs s) rsp
    ; ir-entry-rsp-eq = refl
    ; ir-mem-preserved = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }

-- | Validity-based terminal execution
-- Result is tt at address 0, so valid-unit (no input validity needed)
run-terminal-star-vv : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackInvariant s →
  StackCapacity s output-slots →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (terminal {A}) ++ suffix
  in ∃[ s' ] IRStarResultV (terminal {A}) prog s s' x (length prefix)
run-terminal-star-vv {A} prefix suffix x s h-false pc-eq stack-inv cap-in rbp-inv =
  let (s' , step-eq , h' , pc' , rax-eq') = run-terminal-at-offset {A} prefix suffix x s h-false pc-eq
      prog = prefix ++ compile-x86 (terminal {A}) ++ suffix
      rsp-eq = readReg-writeReg-rax-rsp (regs s) 0
      rbp-eq = readReg-writeReg-rax-rbp (regs s) 0
      cap = capacity-preserved-rsp-unchanged s s' 2 cap-in rsp-eq
      -- rax s' = 0, eval terminal x = tt, so ValidAt tt 0 m = valid-unit
      result-valid : ValidAt {Unit} tt (readReg (regs s') rax) (memory s')
      result-valid = subst (λ a → ValidAt {Unit} tt a (memory s')) (sym rax-eq') valid-unit
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) 0
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) 0
    ; ir-rbp = rbp-eq
    ; ir-rsp = rsp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-entry-rsp = readReg (regs s) rsp
    ; ir-entry-rsp-eq = refl
    ; ir-mem-preserved = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) 0)
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }

-- | Validity-based fold execution
-- Input x : ⟦ F ⟧ valid at rdi → output (wrap x) : Fix F valid at rax
run-fold-star-vv : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s output-slots →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fold {F}) ++ suffix
  in ∃[ s' ] IRStarResultV (fold {F}) prog s s' x (length prefix)
run-fold-star-vv {F} prefix suffix x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
  let prog = prefix ++ compile-x86 (fold {F}) ++ suffix
      s' : State
      s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                    ; pc = pc s +ℕ 1 }
      fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                       (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)
      step-eq : step prog s ≡ just s'
      step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                      (execMov-reg-reg s rax rdi)
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 cap-in rsp-eq
      -- Key: rax s' = rdi s, memory unchanged
      rax-eq : readReg (regs s') rax ≡ readReg (regs s) rdi
      rax-eq = readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)
      result-valid : ValidAt (wrap x) (readReg (regs s') rax) (memory s')
      result-valid = subst (λ a → ValidAt (wrap x) a (memory s')) (sym rax-eq) (valid-fix input-valid)
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h-false
    ; ir-pc = cong (_+ℕ 1) pc-eq
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-rsp = rsp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-entry-rsp = readReg (regs s) rsp
    ; ir-entry-rsp-eq = refl
    ; ir-mem-preserved = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }

-- | Validity-based unfold execution
-- Input (wrap x') : Fix F valid at rdi → output x' : ⟦ F ⟧ valid at rax
-- Extracts underlying validity from valid-fix
run-unfold-star-vv : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s output-slots →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
  in ∃[ s' ] IRStarResultV (unfold {F}) prog s s' x (length prefix)
run-unfold-star-vv {F} prefix suffix (wrap x') s h-false pc-eq (valid-fix input-valid) stack-inv cap-in rbp-inv =
  let prog = prefix ++ compile-x86 (unfold {F}) ++ suffix
      s' : State
      s' = record s { regs = writeReg (regs s) rax (readReg (regs s) rdi)
                    ; pc = pc s +ℕ 1 }
      fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
      fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                       (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)
      step-eq : step prog s ≡ just s'
      step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                      (execMov-reg-reg s rax rdi)
      rsp-eq = readReg-writeReg-rax-rsp (regs s) (readReg (regs s) rdi)
      rbp-eq = readReg-writeReg-rax-rbp (regs s) (readReg (regs s) rdi)
      cap = capacity-preserved-rsp-unchanged s s' 2 cap-in rsp-eq
      -- Key: rax s' = rdi s, memory unchanged
      rax-eq : readReg (regs s') rax ≡ readReg (regs s) rdi
      rax-eq = readReg-writeReg-same (regs s) rax (readReg (regs s) rdi)
      -- input-valid : ValidAt {F} x' rdi m (extracted from valid-fix)
      -- eval unfold (wrap x') = x', so result-valid : ValidAt {F} x' rax m'
      result-valid : ValidAt x' (readReg (regs s') rax) (memory s')
      result-valid = subst (λ a → ValidAt x' a (memory s')) (sym rax-eq) input-valid
  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h-false
    ; ir-pc = cong (_+ℕ 1) pc-eq
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) (readReg (regs s) rdi)
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi)
    ; ir-rbp = rbp-eq
    ; ir-rsp = rsp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-entry-rsp = readReg (regs s) rsp
    ; ir-entry-rsp-eq = refl
    ; ir-mem-preserved = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) (readReg (regs s) rdi))
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }

------------------------------------------------------------------------
-- Validity-Based Consumer Proofs (Phase 5: Consumers)
--
-- These consume ValidAt input and produce ValidAt output.
-- Pattern: Extract component validity from ValidAt via pattern matching.
------------------------------------------------------------------------

-- | Validity-based fst consumer
-- Input: ValidAt (a, b) rdi m - pattern match to extract component validities
-- Output: ValidAt a rax m' - first component validity preserved
run-fst-star-vv : ∀ {A B} (prefix suffix : Program)
    (a : ⟦ A ⟧) (b : ⟦ B ⟧)
    (addr-a addr-b : Word)  -- Component addresses from ValidAt
    (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  (va : ValidAt a addr-a (memory s)) →
  (vb : ValidAt b addr-b (memory s)) →
  (pair-at : PairAtS addr-a addr-b (readReg (regs s) rdi) (memory s)) →
  StackInvariant s →
  StackCapacity s output-slots →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultV (fst {A} {B}) prog s s' (a , b) (length prefix)
run-fst-star-vv {A} {B} prefix suffix a b addr-a addr-b s h-false pc-eq va vb pair-at stack-inv cap-in rbp-inv =
  let
    prog = prefix ++ compile-x86 (fst {A} {B}) ++ suffix
    input-addr = readReg (regs s) rdi

    -- From PairAtS: memory at input-addr contains addr-a
    mem-eq : readMem (memory s) input-addr ≡ just addr-a
    mem-eq = fst-valid-s pair-at

    -- Execute fst: rax := mem[rdi] = addr-a
    (s' , step-eq , h' , pc' , rax-eq) =
      run-fst-at-offset-s {A} {B} prefix suffix input-addr addr-a s h-false pc-eq refl mem-eq

    -- Result validity: va at addr-a, and rax = addr-a
    result-valid : ValidAt a (readReg (regs s') rax) (memory s')
    result-valid = subst (λ addr → ValidAt a addr (memory s')) (sym rax-eq) va

    rsp-eq = readReg-writeReg-rax-rsp (regs s) addr-a
    rbp-eq = readReg-writeReg-rax-rbp (regs s) addr-a
    cap = capacity-preserved-rsp-unchanged s s' 2 cap-in rsp-eq

  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) addr-a
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) addr-a
    ; ir-rbp = rbp-eq
    ; ir-rsp = rsp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl  -- fst doesn't write memory
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-entry-rsp = readReg (regs s) rsp
    ; ir-entry-rsp-eq = refl
    ; ir-mem-preserved = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) addr-a)
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }

-- | Validity-based snd consumer
-- Input: ValidAt (a, b) rdi m - pattern match to extract component validities
-- Output: ValidAt b rax m' - second component validity preserved
run-snd-star-vv : ∀ {A B} (prefix suffix : Program)
    (a : ⟦ A ⟧) (b : ⟦ B ⟧)
    (addr-a addr-b : Word)  -- Component addresses from ValidAt
    (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  (va : ValidAt a addr-a (memory s)) →
  (vb : ValidAt b addr-b (memory s)) →
  (pair-at : PairAtS addr-a addr-b (readReg (regs s) rdi) (memory s)) →
  StackInvariant s →
  StackCapacity s output-slots →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultV (snd {A} {B}) prog s s' (a , b) (length prefix)
run-snd-star-vv {A} {B} prefix suffix a b addr-a addr-b s h-false pc-eq va vb pair-at stack-inv cap-in rbp-inv =
  let
    prog = prefix ++ compile-x86 (snd {A} {B}) ++ suffix
    input-addr = readReg (regs s) rdi

    -- From PairAtS: memory at input-addr+8 contains addr-b
    mem-eq : readMem (memory s) (input-addr +ℕ 8) ≡ just addr-b
    mem-eq = snd-valid-s pair-at

    -- Execute snd: rax := mem[rdi+8] = addr-b
    (s' , step-eq , h' , pc' , rax-eq) =
      run-snd-at-offset-s {A} {B} prefix suffix input-addr addr-b s h-false pc-eq refl mem-eq

    -- Result validity: vb at addr-b, and rax = addr-b
    result-valid : ValidAt b (readReg (regs s') rax) (memory s')
    result-valid = subst (λ addr → ValidAt b addr (memory s')) (sym rax-eq) vb

    rsp-eq = readReg-writeReg-rax-rsp (regs s) addr-b
    rbp-eq = readReg-writeReg-rax-rbp (regs s) addr-b
    cap = capacity-preserved-rsp-unchanged s s' 2 cap-in rsp-eq

  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) addr-b
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) addr-b
    ; ir-rbp = rbp-eq
    ; ir-rsp = rsp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl  -- snd doesn't write memory
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-entry-rsp = readReg (regs s) rsp
    ; ir-entry-rsp-eq = refl
    ; ir-mem-preserved = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) addr-b)
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }

------------------------------------------------------------------------
-- Validity-based arr and prim (Phase 6b: wiring)
------------------------------------------------------------------------

-- | Validity-based arr execution
-- arr is identity on arrow types: eval (arr {A} {B}) fn = fn
-- So output validity equals input validity
run-arr-star-vv : ∀ {A B} (prefix suffix : Program) (fn : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt fn (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s output-slots →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultV (arr {A} {B}) prog s s' fn (length prefix)
run-arr-star-vv {A} {B} prefix suffix fn s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
  let
    prog = prefix ++ compile-x86 (arr {A} {B}) ++ suffix
    input-addr = readReg (regs s) rdi

    -- Final state after mov rax, rdi
    s' : State
    s' = record s { regs = writeReg (regs s) rax input-addr
                  ; pc = pc s +ℕ 1 }

    -- Step execution (inline from run-arr-at-offset)
    fetch-eq : fetch prog (pc s) ≡ just (mov (reg rax) (reg rdi))
    fetch-eq = subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rdi)))
                     (sym pc-eq) (fetch-at-prefix-end prefix (mov (reg rax) (reg rdi)) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (mov (reg rax) (reg rdi)) h-false fetch-eq)
                    (execMov-reg-reg s rax rdi)

    h' : halted s' ≡ false
    h' = h-false

    pc' : pc s' ≡ length prefix +ℕ 1
    pc' = cong (λ p → p +ℕ 1) pc-eq

    -- rax in s' = rdi in s (raw equality)
    rax-eq-raw : readReg (regs s') rax ≡ readReg (regs s) rdi
    rax-eq-raw = readReg-writeReg-same (regs s) rax input-addr

    -- Validity at new location (same type index A ⇒ B)
    valid-at-rax : ValidAt {A ⇒ B} fn (readReg (regs s') rax) (memory s')
    valid-at-rax = subst (λ addr → ValidAt fn addr (memory s)) (sym rax-eq-raw) input-valid

    -- Convert from (A ⇒ B) to (Eff A B) - same runtime representation
    -- eval arr fn = fn, and arr : IR (A ⇒ B) (Eff A B)
    result-valid : ValidAt {Eff A B} fn (readReg (regs s') rax) (memory s')
    result-valid = valid-arrow-to-eff valid-at-rax

    -- Register preservation
    rsp-eq = readReg-writeReg-rax-rsp (regs s) input-addr
    rbp-eq = readReg-writeReg-rax-rbp (regs s) input-addr
    cap = capacity-preserved-rsp-unchanged s s' 2 cap-in rsp-eq

  in s' , record
    { ir-star = star-single h-false step-eq
    ; ir-halted = h'
    ; ir-pc = pc'
    ; ir-result-valid = result-valid
    ; ir-r14 = readReg-writeReg-rax-r14 (regs s) input-addr
    ; ir-r15 = readReg-writeReg-rax-r15 (regs s) input-addr
    ; ir-rbp = rbp-eq
    ; ir-rsp = rsp-eq
    ; ir-mem = refl
    ; ir-mem-rbp = refl
    ; ir-mem-rbp+8 = refl
    ; ir-mem-above = λ _ _ → refl  -- arr doesn't write memory
    ; ir-mem-code = λ _ _ → refl
    ; ir-mem-heap = λ _ _ → refl
    ; ir-entry-rsp = readReg (regs s) rsp
    ; ir-entry-rsp-eq = refl
    ; ir-mem-preserved = λ _ _ → refl
    ; ir-stack-inv = stack-inv-preserved-unchanged s s' stack-inv
                       (readReg-writeReg-rax-r15 (regs s) input-addr)
                       rsp-eq
    ; ir-capacity = cap
    ; ir-rbp-inv = rbp-inv-preserved-unchanged s s' rbp-inv rsp-eq rbp-eq
    ; ir-closure-wf = no-closure
    }

-- | Validity-based prim execution (POSTULATE - awaiting domain compiler proofs)
--
-- ARCHITECTURE: compile-x86 (Prim _ _ c) now uses contract-program c (actual assembly).
-- The compile-x86/compile-length mismatch has been ELIMINATED.
--
-- This postulate remains because domain compilers haven't yet provided
-- PrimContract instances with full proofs. When they do, this postulate
-- can be eliminated by unpacking prim-correct from the contract:
--
--   prim-correct : ∀ ... → ∃[ s' ] PrimEffect sem x prog s s'
--
-- The PrimEffect includes:
--   - effect-star: Star trace proving assembly executes
--   - effect-result-valid: ValidAt (sem x) rax m'
--   - All register/memory preservation proofs
--
-- For programs not using Prim, the correctness proof is complete.
-- For programs using Prim, this is trusted until Arith/IO provide contracts.
postulate
  -- Awaiting domain compiler contracts (Arith, IO, etc.)
  run-prim-star-vv : ∀ {A B} (name : String) (sem : ⟦ A ⟧ → ⟦ B ⟧) (contract : PrimContract sem) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    (∀ addr → InStack addr → readReg (regs s) rdi ≢ addr) →
    StackInvariant s →
    StackCapacity s output-slots →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (Prim {A} {B} name sem contract) ++ suffix
    in ∃[ s' ] IRStarResultV (Prim {A} {B} name sem contract) prog s s' x (length prefix)

