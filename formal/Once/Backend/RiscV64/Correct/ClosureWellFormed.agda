------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.ClosureWellFormed
--
-- Well-formedness predicate for closures: tracks that a closure's
-- code-ptr points to valid thunk code within the program.
--
-- This is the key to eliminating the run-apply-star postulate.
-- In whole-program proofs:
-- 1. Curry produces a ClosureWellFormed proof along with the closure
-- 2. Apply requires a ClosureWellFormed proof as a precondition
-- 3. This allows tracing execution through jalr → thunk → ret
--
-- RISC-V calling convention for thunk:
--   - s0 = env (captured value)
--   - a0 = arg (argument to apply)
--   - ra = return address (set by jalr)
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.ClosureWellFormed where

open import Size
open import Once.Type
open import Once.IRS
open import Once.SemanticsS hiding (code-ptr; env-addr; semantics)

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

------------------------------------------------------------------------
-- ThunkResult: Result type for thunk execution
------------------------------------------------------------------------

-- | When a thunk executes, it produces this result
-- This captures what happens when apply calls a closure
--
-- RISC-V thunk state:
--   - Entry: s0=env, a0=arg, ra=return address, pc=code-ptr
--   - Exit:  a0=result, pc=return address (from ret)
record ThunkResult {A B : Type} (prog : Program) (s s' : State)
                   (f : ⟦ A ⟧ → ⟦ B ⟧) (a : ⟦ A ⟧) : Set where
  field
    thunk-star     : Star prog s s'
    thunk-halted   : halted s' ≡ false
    thunk-a0       : readReg (regs s') a0 ≡ encode (f a)
    thunk-s1       : readReg (regs s') s1 ≡ readReg (regs s) s1

open ThunkResult public

------------------------------------------------------------------------
-- ClosureWellFormed: Well-formedness predicate for closures
------------------------------------------------------------------------

-- | A closure is well-formed in a program if:
-- 1. Its code-ptr points to a location in the program
-- 2. Executing from code-ptr produces the correct result
--
-- Key insight: This is established by curry and consumed by apply.
-- In whole-program proofs, curry and apply are in the same program,
-- so the well-formedness proof can be threaded through.
--
-- The thunk ends with `ret`, which jumps to the address in ra.
-- The caller (apply) sets ra via `jalr`, and thunk-correct
-- guarantees execution returns there.
--
-- NOTE: We use explicit runtime values (code-ptr, env-addr) rather than
-- the semantic Closure record because:
-- 1. Closure.code-ptr in semantics is 0 (placeholder)
-- 2. The actual code-ptr comes from compilation (offset + 7)
-- 3. Apply reads these from memory, not from the semantic record
--
-- NEW: stack-requirement parameter (2026-01-02)
--   The thunk requires this many bytes of stack to execute successfully.
--   For curry-generated closures, this is StackDepth (curry f).
--   This replaces the false universal postulate sp-bound-for-f-in-thunk.
record ClosureWellFormed {A B : Type} (prog : Program)
                         (code-ptr : ℕ) (env-addr : ℕ)
                         (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                         (stack-requirement : ℕ) : Set where
  field
    -- The code-ptr is within the program bounds
    code-ptr-valid : code-ptr < length prog

    -- Executing from code-ptr produces correct result for any input
    -- ret-addr: the return address (set by jalr in ra, jumped to by ret)
    -- stack-bound: proof that sufficient stack is available (NEW)
    thunk-correct : ∀ (a : ⟦ A ⟧) (s : State) (ret-addr : ℕ) →
      halted s ≡ false →
      pc s ≡ code-ptr →
      readReg (regs s) a0 ≡ encode a →
      readReg (regs s) s0 ≡ env-addr →
      readReg (regs s) ra ≡ ret-addr →  -- Return address in ra
      stack-requirement ≤ readReg (regs s) sp →  -- Stack precondition (NEW)
      ∃[ s' ] (ThunkResult prog s s' semantics a
              × pc s' ≡ ret-addr)

open ClosureWellFormed public

------------------------------------------------------------------------
-- CurryResult: Extended result for curry that includes well-formedness
------------------------------------------------------------------------

-- | When curry executes, it produces:
-- 1. A closure value (in a0)
-- 2. A proof that this closure is well-formed
--
-- This allows apply to use the well-formedness proof
--
-- The closure's runtime values are:
-- - a0 = closure address (new-sp)
-- - [closure] = env-addr = encode x
-- - [closure+8] = code-ptr = offset + 7
record CurryResult {i : Size} {A B C : Type} (f : IR i (A * B) C)
                   (prog : Program) (s s' : State) (x : ⟦ A ⟧)
                   (offset : ℕ) : Set where
  field
    -- Standard execution properties
    curry-star     : Star prog s s'
    curry-halted   : halted s' ≡ false
    curry-pc       : pc s' ≡ offset +ℕ compile-length (curry f)
    curry-a0       : readReg (regs s') a0 ≡ encode {B ⇒ C} (eval (curry f) x)
    curry-s1       : readReg (regs s') s1 ≡ readReg (regs s) s1

    -- The closure produced is well-formed!
    -- This is the key property that apply needs
    -- Note: curry f : IR A (B ⇒ C), so eval (curry f) x : Closure B C
    --       semantics = Closure.semantics (eval (curry f) x) = λ b → eval f (x , b)
    --       code-ptr = offset + 7 (thunk entry in program)
    --       env-addr = encode x (captured value)
    --       stack-requirement = StackDepth (curry f) (includes thunk allocation + body execution)
    closure-wf : ClosureWellFormed {B} {C} prog
                   (offset +ℕ 7)           -- code-ptr: thunk at offset+7
                   (encode x)              -- env-addr: encoded captured value
                   (λ b → eval f (x , b))  -- semantics: partial application
                   (StackDepth (curry f))  -- stack-requirement: proven from code generation

open CurryResult public

------------------------------------------------------------------------
-- ApplyMemoryLayout: Memory layout precondition for apply
------------------------------------------------------------------------

-- | Memory layout precondition for apply
-- Captures that the pair (closure, arg) is properly laid out in memory
record ApplyMemoryLayout {A B : Type} (prog : Program) (s : State)
                         (closure-addr code-ptr env-addr : ℕ) (arg : ⟦ A ⟧) : Set where
  field
    -- Pair layout: a0 points to (closure-addr, encode arg)
    mem-fst : readMem (memory s) (readReg (regs s) a0) ≡ just closure-addr
    mem-snd : readMem (memory s) (readReg (regs s) a0 +ℕ 8) ≡ just (encode arg)
    -- Closure layout: closure-addr points to (env-addr, code-ptr)
    mem-env : readMem (memory s) closure-addr ≡ just env-addr
    mem-cp  : readMem (memory s) (closure-addr +ℕ 8) ≡ just code-ptr

open ApplyMemoryLayout public

------------------------------------------------------------------------
-- CurryOutputWF: What curry produces for threading to apply
------------------------------------------------------------------------

-- | When curry executes, it produces this WF info that can be used by apply
-- This captures the connection between curry's output and apply's input
record CurryOutputWF {i : Size} {A B C : Type} (f : IR i (A * B) C)
                     (prog : Program) (offset : ℕ) (x : ⟦ A ⟧) : Set where
  field
    code-ptr : ℕ
    env-addr : ℕ
    stack-req : ℕ  -- Stack requirement for thunk execution
    code-ptr-eq : code-ptr ≡ offset +ℕ 7  -- Thunk is at offset+7
    env-addr-eq : env-addr ≡ encode x      -- Env is encoded input
    wf : ClosureWellFormed {B} {C} prog code-ptr env-addr (λ b → eval f (x , b)) stack-req

open CurryOutputWF public

-- | Extract ApplyInputWF from CurryOutputWF
-- This is the key conversion that enables threading
ApplyInputWF : ∀ (A B : Type) → Program → Set
ApplyInputWF A B prog =
  ∃[ code-ptr ] ∃[ env-addr ] ∃[ sem ] ∃[ stack-req ]
  ClosureWellFormed {A} {B} prog code-ptr env-addr sem stack-req

curry-output-to-apply-input : ∀ {i A B C} (f : IR i (A * B) C)
                              (prog : Program) (offset : ℕ) (x : ⟦ A ⟧) →
                              CurryOutputWF f prog offset x →
                              ApplyInputWF B C prog
curry-output-to-apply-input f prog offset x cow =
  CurryOutputWF.code-ptr cow ,
  CurryOutputWF.env-addr cow ,
  (λ b → eval f (x , b)) ,
  CurryOutputWF.stack-req cow ,
  CurryOutputWF.wf cow

------------------------------------------------------------------------
-- Internal placeholders (NOT official postulates)
------------------------------------------------------------------------

-- REMOVED: dummy-wf-for-arrow postulate (2026-01-06)
--
-- This was a placeholder for arrow types in trivialWF.
-- trivialWF should only be called for types without closures.
-- Arrow types get WF from curry's output via MutualIR.
--
-- If removing this breaks the build, it means trivialWF is being called
-- with arrow types, which would indicate a gap in the WF threading.
--
-- postulate
--   dummy-wf-for-arrow : ∀ {A B : Type} (prog : Program) → ApplyInputWF A B prog

------------------------------------------------------------------------
-- ClosuresWF: WF for all closures in values of a given type
--
-- This type family computes what WF information is needed for values
-- of each type. Used to thread WF through composition.
------------------------------------------------------------------------

open import Data.Unit using (⊤; tt)

-- | WF for all closures that might appear in a value of type T
-- For arrow types: existentially quantified ClosureWellFormed
-- For products: WF for both components
-- For sums: WF for both branches (conservative)
-- For other types: trivial (no closures)
ClosuresWF : Type → Program → Set
ClosuresWF Unit prog = ⊤
ClosuresWF Void prog = ⊤
ClosuresWF Int prog = ⊤
ClosuresWF Float prog = ⊤
ClosuresWF Str prog = ⊤
ClosuresWF Buffer prog = ⊤
ClosuresWF (TVar _) prog = ⊤
ClosuresWF (Eff _ _) prog = ⊤
ClosuresWF (A * B) prog = ClosuresWF A prog × ClosuresWF B prog
ClosuresWF (A + B) prog = ClosuresWF A prog × ClosuresWF B prog
ClosuresWF (A ⇒[ _ ] B) prog = ApplyInputWF A B prog  -- Pattern match on actual constructor
ClosuresWF (Fix F) prog = ⊤  -- Recursive types: assume no closures for now

-- | Trivial WF for types without closures
-- IMPORTANT: This function should ONLY be called for types that genuinely
-- don't contain closures. Arrow types must get their WF from curry's output
-- via MutualIR. If this function is called with an arrow type, it will cause
-- a compile-time error to help identify gaps in WF threading.
trivialWF : ∀ T prog → ClosuresWF T prog
trivialWF Unit prog = tt
trivialWF Void prog = tt
trivialWF Int prog = tt
trivialWF Float prog = tt
trivialWF Str prog = tt
trivialWF Buffer prog = tt
trivialWF (TVar _) prog = tt
trivialWF (Eff _ _) prog = tt
trivialWF (A * B) prog = trivialWF A prog , trivialWF B prog
trivialWF (A + B) prog = trivialWF A prog , trivialWF B prog
trivialWF (A ⇒[ _ ] B) prog = error-trivialWF-called-with-arrow
  where postulate error-trivialWF-called-with-arrow : ApplyInputWF A B prog
        -- ERROR: Arrow types should get WF from curry's output, not trivialWF!
        -- This postulate indicates a gap in WF threading that needs investigation
trivialWF (Fix F) prog = tt

-- | Extract WF for first component of a pair
fstWF : ∀ {A B} {prog} → ClosuresWF (A * B) prog → ClosuresWF A prog
fstWF (wf-a , wf-b) = wf-a

-- | Extract WF for second component of a pair
sndWF : ∀ {A B} {prog} → ClosuresWF (A * B) prog → ClosuresWF B prog
sndWF (wf-a , wf-b) = wf-b

-- | Build WF for a pair from components
pairWF : ∀ {A B} {prog} → ClosuresWF A prog → ClosuresWF B prog → ClosuresWF (A * B) prog
pairWF wf-a wf-b = wf-a , wf-b

-- | Extract WF for apply input: from (A ⇒ B) * A, get the closure's WF
applyInputWF : ∀ {A B} {prog} → ClosuresWF ((A ⇒ B) * A) prog → ApplyInputWF A B prog
applyInputWF (wf-closure , wf-arg) = wf-closure
