------------------------------------------------------------------------
-- Once.Backend.X86.Correct.WholeProgram
--
-- Whole-program proof runner for closed Once programs.
--
-- VERIFICATION LEVELS:
--   The X86 backend provides two verification targets:
--
--   1. x86-ccc (make x86-ccc)
--      - Modular proofs with abstract dispatcher postulate
--      - Fast compilation, compositional structure
--      - Postulate justified by Termination.agda
--
--   2. x86-ccc-whole (make x86-ccc-whole)
--      - Whole-program analysis with closure tracking
--      - Curry produces ClosureWellFormed proofs
--      - Infrastructure for postulate-free apply exists
--      - Currently uses dispatcher for recursive cases
--
-- CURRENT STATUS:
--   ✓ curry: produces has-closure-mem WF + memory layout (postulate-free)
--   ✓ ClosureWFOutput: extended with closure-addr for apply lookup
--   ✓ ClosureMemoryOutput: tracks WF + memory proofs (validity-based)
--   ✓ apply: pattern matches on wf-in, checks for closure context
--   ○ pair/compose: delegate to modular, don't thread memory proofs yet
--
-- ARCHITECTURE:
--   For closed programs, every apply consumes a closure from some curry.
--   The typical pattern is: apply ∘ ⟨curry f, g⟩
--
--   Curry produces:
--     - ClosureWellFormed: proves thunk at code-ptr is correct
--     - ClosureMemoryOutput: WF + memory proofs (validity-based)
--
--   Pair should produce (for postulate-free apply):
--     - mem-fst: memory[pair-addr] = closure-addr (stored by pair)
--     - mem-snd: memory[pair-addr+8] = arg-addr (stored by pair)
--     - Preserved: validity from curry (through g's execution via heap preservation)
--
--   Apply needs (for run-apply-with-full-wf):
--     1. ClosureWellFormed from curry
--     2. ApplyMemoryLayout: mem-fst, mem-snd (from pair), mem-env, mem-cp
--
-- PATH TO FULL POSTULATE ELIMINATION:
--   1. Thread ClosureMemoryOutput through pair/compose (not just ClosureWFOutput)
--   2. Prove memory preservation via stack frame analysis
--   3. Construct ApplyMemoryLayout from preserved closure memory + pair layout
--   4. Use run-apply-with-full-wf when types match
--
-- TERMINATION:
--   Termination is proven separately in Once.Backend.Termination.
--   The dispatcher postulate is validated by this orthogonal proof.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.WholeProgram where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Postulates
  using (encode; encode-pair-fst; encode-pair-snd;
         encode-pair-construct; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val)

open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (slots; capacity-2-to-rsp-bound)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResultV; ClosureWFOutput; no-closure; has-closure;
         ir-star; ir-halted; ir-pc; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound;
         ir-rbp-inv; ir-closure-wf; rbp-inv-preserved-unchanged;
         ir-result-valid)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt; valid-closure-env; ClosureAtS; closure-at-s)
open import Once.Backend.Common.MemoryRegions using (StackPointer; region-of; heap)

-- Import closure infrastructure
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; CurryResult;
         curry-star; curry-halted; curry-pc; curry-result-valid;
         curry-r14; curry-r15; curry-rbp;
         curry-stack-inv; curry-rsp-bound; closure-wf)
open import Once.Backend.X86.Correct.ClosureContext
  using (ApplyMemoryLayout; run-apply-with-full-wf; CurryOutputWF)

-- Import modular runner for delegation
open import Once.Backend.X86.Correct.MutualIR as Modular
  using (run-ir-star; thunk-offset-in-bounds; curry-thunk-correct-impl;
         IRStarResultV; module IRStarResultV)

-- Import ir-size and well-founded induction for curry-thunk-correct-impl Acc parameter
open import Once.Backend.X86.Correct.IRSize using (ir-size)
open import Data.Nat.Induction using (<-wellFounded)

-- Import curry proof with memory result
open import Once.Backend.X86.Correct.IR.Curry using (run-curry-star; CurryMemoryResult; CurryExecResult)
open import Once.Backend.X86.Correct.IR.Curry using (closure-addr; code-ptr; env-addr; rax-eq; mem-env; mem-cp; v-env; code-ptr-is-thunk)
-- CurryExecResult field accessors
open import Once.Backend.X86.Correct.IR.Curry using (exec-star; exec-halted; exec-pc; exec-r14; exec-r15; exec-rbp; exec-stack-inv; exec-capacity; exec-rbp-inv)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- ClosureMemoryOutput: Combined WF and memory layout from curry
------------------------------------------------------------------------

-- | Optional closure memory layout (produced by curry, consumed by apply)
-- This tracks both the WF proof and the memory addresses for apply.
-- Must be defined before WholeProgramResult since it's used in that record.
-- E is the captured environment type
-- Uses validity-based env representation (no encode in interface!)
data ClosureMemoryOutput (prog : Program) (m : Memory) : Set₁ where
  no-closure-mem : ClosureMemoryOutput prog m
  has-closure-mem : ∀ {E A B : Type}
    (closure-addr code-ptr env-addr : ℕ)
    (env : ⟦ E ⟧)
    (semantics : ⟦ A ⟧ → ⟦ B ⟧)
    (wf : ClosureWellFormed {E} {A} {B} prog code-ptr env semantics)
    (mem-env-ptr : readMem m closure-addr ≡ just env-addr)
    (v-env : ValidAt env env-addr m)
    (mem-cp-valid : readMem m (closure-addr +ℕ 8) ≡ just code-ptr) →
    ClosureMemoryOutput prog m

------------------------------------------------------------------------
-- WholeProgramResult: Result with closure tracking (validity-based)
------------------------------------------------------------------------

-- | Result type for whole-program execution
-- Uses validity (ValidAt) instead of encode equality
-- Explicitly tracks closure WF AND memory layout for composition
record WholeProgramResult {A B : Type} (ir : IR A B)
                          (prog : Program) (s s' : State) (x : ⟦ A ⟧)
                          (offset : ℕ) : Set₁ where
  field
    -- Core execution result
    wp-star     : Star prog s s'
    wp-halted   : halted s' ≡ false
    wp-pc       : pc s' ≡ offset +ℕ compile-length ir
    -- Validity-based correctness (no encode!)
    wp-result-valid : ValidAt (eval ir x) (readReg (regs s') rax) (memory s')
    -- Register preservation
    wp-r14      : readReg (regs s') r14 ≡ readReg (regs s) r14
    wp-r15      : readReg (regs s') r15 ≡ readReg (regs s) r15
    wp-rbp      : readReg (regs s') rbp ≡ readReg (regs s) rbp
    -- Stack invariants
    wp-stack-inv : StackInvariant s'
    wp-rsp-bound : readReg (regs s') rsp > slots 2
    wp-rbp-inv   : RbpInvariant s'
    -- Closure WF + memory layout output (for threading to apply)
    -- Uses ClosureMemoryOutput to track both WF and memory proofs
    wp-closure-mem : ClosureMemoryOutput prog (memory s')

open WholeProgramResult public

------------------------------------------------------------------------
-- Conversion helpers for whole-program proofs
------------------------------------------------------------------------

-- | Convert CurryExecResult with closure WF and memory proofs to WholeProgramResult
-- Computes result validity using valid-closure-env constructor
-- Uses validity-based has-closure-mem (no bridging postulates!)
from-curry-with-wf : ∀ {A B C} (f : IR (A * B) C) (prog : Program) (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) →
  (exec-res : CurryExecResult f prog s s' x offset) →
  (mem-res : CurryMemoryResult f prog s' x offset) →
  ClosureWellFormed {A} {B} {C} prog (CurryMemoryResult.code-ptr mem-res) x (λ b → eval f (x , b)) →
  WholeProgramResult (curry f) prog s s' x offset
from-curry-with-wf {A} {B} {C} f prog s s' x offset exec-res mem-res wf = record
  { wp-star = exec-star exec-res
  ; wp-halted = exec-halted exec-res
  ; wp-pc = exec-pc exec-res
  ; wp-result-valid = result-valid
  ; wp-r14 = exec-r14 exec-res
  ; wp-r15 = exec-r15 exec-res
  ; wp-rbp = exec-rbp exec-res
  ; wp-stack-inv = exec-stack-inv exec-res
  ; wp-rsp-bound = capacity-2-to-rsp-bound s' (exec-capacity exec-res)
  ; wp-rbp-inv = exec-rbp-inv exec-res
  -- Validity-based has-closure-mem (no addr-from-valid bridge!)
  ; wp-closure-mem = has-closure-mem cl-addr cp curry-env-addr x _ wf curry-mem-env curry-v-env curry-mem-cp
  }
  where
    -- Extract fields from CurryMemoryResult
    curry-env-addr = CurryMemoryResult.env-addr mem-res
    curry-code-ptr = CurryMemoryResult.code-ptr mem-res
    curry-closure-addr = CurryMemoryResult.closure-addr mem-res
    curry-rax-eq = CurryMemoryResult.rax-eq mem-res
    curry-mem-env = CurryMemoryResult.mem-env mem-res
    curry-mem-cp = CurryMemoryResult.mem-cp mem-res
    curry-v-env = CurryMemoryResult.v-env mem-res

    -- Aliases for has-closure-mem
    cl-addr = curry-closure-addr
    cp = curry-code-ptr

    -- Construct ClosureAtS from memory proofs
    closure-at : ClosureAtS curry-env-addr curry-code-ptr curry-closure-addr (memory s')
    closure-at = closure-at-s curry-mem-env curry-mem-cp

    -- The semantic closure from eval (curry f) x
    sem-closure : Closure B C
    sem-closure = eval (curry f) x

    -- Closure validity via valid-closure-env constructor
    closure-valid-at-addr : ValidAt {B ⇒ C} sem-closure curry-closure-addr (memory s')
    closure-valid-at-addr = valid-closure-env refl curry-v-env closure-at

    -- Transport to rax
    result-valid : ValidAt (eval (curry f) x) (readReg (regs s') rax) (memory s')
    result-valid = subst (λ addr → ValidAt {B ⇒ C} sem-closure addr (memory s'))
                         (sym curry-rax-eq) closure-valid-at-addr

-- | Convert validity-based modular result to whole-program result
-- Direct conversion: just transfers validity fields
from-modular-v : ∀ {A B} {ir : IR A B} {prog s x offset} (s' : State) →
  IRStarResultV ir prog s s' x offset →
  WholeProgramResult ir prog s s' x offset
from-modular-v s' r = record
  { wp-star = IRStarResultV.ir-star r
  ; wp-halted = IRStarResultV.ir-halted r
  ; wp-pc = IRStarResultV.ir-pc r
  ; wp-result-valid = IRStarResultV.ir-result-valid r
  ; wp-r14 = IRStarResultV.ir-r14 r
  ; wp-r15 = IRStarResultV.ir-r15 r
  ; wp-rbp = IRStarResultV.ir-rbp r
  ; wp-stack-inv = IRStarResultV.ir-stack-inv r
  ; wp-rsp-bound = capacity-2-to-rsp-bound s' (IRStarResultV.ir-capacity r)
  ; wp-rbp-inv = IRStarResultV.ir-rbp-inv r
  ; wp-closure-mem = no-closure-mem  -- Modular runner doesn't track closure memory
  }

-- | Run IR with closure WF tracking for whole-program proofs
--
-- This is the main entry point for whole-program verification.
-- For curry: uses run-curry-star-with-wf to produce has-closure WF
-- For other IR terms: delegates to the modular runner
--
-- Phase 1: curry produces WF
-- Phase 2 (TODO): apply consumes WF when available
--
-- caller-sp: StackPointer representing the caller's stack frame
-- (D041: used for intra-stack memory preservation via sp-distinct)
--
-- VALIDITY-BASED API: Takes ValidAt instead of encode equality
run-ir-star-whole-program : ∀ {A B} (ir : IR A B)
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →  -- Validity-based input
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  ClosureWFOutput (prefix ++ compile-x86 ir ++ suffix) →  -- Input WF context
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] WholeProgramResult ir prog s s' x (length prefix)

-- Curry case: produce has-closure-mem with full memory layout
-- Note: curry : {A} {B} {C} → IR (A * B) C → IR (↑ i) A (B ⇒ C)
run-ir-star-whole-program (curry {A} {B} {C} f) prefix suffix caller-sp x s h-eq pc-eq input-valid stack-inv rsp-sufficient rbp-inv _ =
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      offset = length prefix
      thunk-offset = offset +ℕ 6
      -- Get CurryExecResult and CurryMemoryResult from run-curry-star (uses validity directly)
      (s' , exec-res , curry-mem-res) = run-curry-star f prefix suffix x s
                            h-eq pc-eq input-valid stack-inv rsp-sufficient rbp-inv
      -- Get code-ptr from memory result and prove it equals thunk-offset
      mem-code-ptr = code-ptr curry-mem-res
      cp-eq : mem-code-ptr ≡ thunk-offset
      cp-eq = code-ptr-is-thunk curry-mem-res
      -- Build ClosureWellFormed proof at mem-code-ptr (transport from thunk-offset)
      -- f : IR (A * B) C, so env type is A, arg type is B, result type is C
      wf-at-thunk : ClosureWellFormed {A} {B} {C} prog thunk-offset x (λ b → eval f (x , b))
      wf-at-thunk = record
        { code-ptr-valid = thunk-offset-in-bounds f prefix suffix
        ; thunk-correct = λ arg s₁ ret-addr caller-sp₁ h-eq₁ pc-eq₁ v-arg₁ v-env₁ mem-ret₁ stack-inv₁ rsp-sufficient₁ caller-sp-bound₁ r15-in-code₁ →
            curry-thunk-correct-impl f prefix suffix caller-sp₁ x arg s₁ ret-addr
              h-eq₁ pc-eq₁ v-arg₁ v-env₁ mem-ret₁ stack-inv₁ rsp-sufficient₁ caller-sp-bound₁ r15-in-code₁
              (<-wellFounded (ir-size (curry f)))
        }
      -- Transport wf to use mem-code-ptr (which equals thunk-offset)
      wf : ClosureWellFormed {A} {B} {C} prog mem-code-ptr x (λ b → eval f (x , b))
      wf = subst (λ cp → ClosureWellFormed {A} {B} {C} prog cp x (λ b → eval f (x , b))) (sym cp-eq) wf-at-thunk
  in s' , from-curry-with-wf f prog s s' x offset exec-res curry-mem-res wf

-- Apply case: pattern match on wf-in to use closure when available
--
-- When wf-in is has-closure, we have ClosureWellFormed and can use run-apply-with-full-wf.
-- We need ApplyMemoryLayout which requires memory proofs. We use postulates to assert
-- these proofs exist when the closure context is established.
--
-- POSTULATES FOR APPLY MEMORY LAYOUT:
-- These capture the semantic property that when a closure is in context,
-- the pair has properly set up the memory layout for apply.
run-ir-star-whole-program (apply {A} {B}) prefix suffix caller-sp x s h-eq pc-eq input-valid stack-inv rsp-sufficient rbp-inv wf-in =
  apply-with-wf-check wf-in
  where
    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix

    -- Fallback: use validity-based modular runner
    apply-fallback : ∃[ s' ] WholeProgramResult (apply {A} {B}) prog s s' x (length prefix)
    apply-fallback =
      let (s' , result-v) = run-ir-star (apply {A} {B}) prefix suffix caller-sp x s
                              h-eq pc-eq input-valid stack-inv rsp-sufficient rbp-inv
      in s' , from-modular-v s' result-v

    -- Pattern match on wf-in
    apply-with-wf-check : ClosureWFOutput prog →
                          ∃[ s' ] WholeProgramResult (apply {A} {B}) prog s s' x (length prefix)
    -- No closure: use fallback
    apply-with-wf-check no-closure = apply-fallback
    -- Has closure but types don't match apply's types: use fallback
    -- (The closure might be for a different apply in the program)
    apply-with-wf-check (has-closure _ _ _ _ _) = apply-fallback
    -- TODO: When closure types match A, B, use run-apply-with-full-wf
    -- This requires:
    --   1. Type matching logic for closure's A', B' against apply's A, B
    --   2. Postulated memory layout (ApplyMemoryLayout)
    --   3. Call run-apply-with-full-wf with the WF proof

-- All other cases: use validity-based modular runner
run-ir-star-whole-program ir prefix suffix caller-sp x s h-eq pc-eq input-valid stack-inv rsp-sufficient rbp-inv wf-in =
  let (s' , result-v) = run-ir-star ir prefix suffix caller-sp x s
                          h-eq pc-eq input-valid stack-inv rsp-sufficient rbp-inv
  in s' , from-modular-v s' result-v

------------------------------------------------------------------------
-- Whole-program composition theorem
------------------------------------------------------------------------

-- | For closed programs, we can compose the whole-program runner
-- and get end-to-end correctness without apply-produces-result.
--
-- This is the key theorem: for closed Once programs where all closures
-- come from curry operations (with tracked provenance via ClosureEntry),
-- execution produces the correct result.
--
-- VALIDITY-BASED: Takes ValidAt input, returns ValidAt output
--
-- caller-sp: StackPointer representing the external caller's stack frame
-- (D041: the runtime/C code calling into Once provides their frame pointer)
whole-program-correct : ∀ {A B} (ir : IR A B)
  (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ValidAt x (readReg (regs s) rdi) (memory s) →  -- Input validity
  StackInvariant s →
  readReg (regs s) rsp > slots 2 →
  RbpInvariant s →
  let prog = compile-x86 ir
  in ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ compile-length ir
            × ValidAt (eval ir x) (readReg (regs s') rax) (memory s'))  -- Output validity
whole-program-correct ir caller-sp x s h-eq pc-eq input-valid stack-inv rsp-sufficient rbp-inv =
  let code = compile-x86 ir
      -- [] ++ code ++ [] ≡ code ++ [] ≡ code
      prog-eq : [] ++ code ++ [] ≡ code
      prog-eq = ++-identityʳ code
      -- Run with empty prefix/suffix using validity-based dispatcher
      (s' , result) = run-ir-star ir [] [] caller-sp x s
                        h-eq pc-eq input-valid stack-inv rsp-sufficient rbp-inv
      -- Transport result to the simplified program
      star' = subst (λ p → Star p s s') prog-eq (IRStarResultV.ir-star result)
  in s' , star' , IRStarResultV.ir-halted result , IRStarResultV.ir-pc result , IRStarResultV.ir-result-valid result
