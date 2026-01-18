------------------------------------------------------------------------
-- Once.Backend.X86.Correct.ClosureWellFormed
--
-- Well-formedness predicate for closures: tracks that a closure's
-- code-ptr points to valid thunk code within the program.
--
-- This is the key to eliminating the apply-produces-result postulate.
-- In whole-program proofs:
-- 1. Curry produces a ClosureWellFormed proof along with the closure
-- 2. Apply requires a ClosureWellFormed proof as a precondition
-- 3. This allows tracing execution through call → thunk → ret
------------------------------------------------------------------------

module Once.Backend.X86.Correct.ClosureWellFormed where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (slots; StackCapacity; ir-output-capacity)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.Common.MemoryRegions
  using (InCode; InHeap; StackPointer; frameSlot)

open import Once.Postulates using (encode)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_; _<_; _≥_) renaming (_+_ to _+ℕ_)
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
-- D041: caller-sp identifies the caller's stack frame.
-- Memory preservation for caller's frame uses sp-distinct (region-based).
record ThunkResult {A B : Type} (prog : Program) (s s' : State)
                   (caller-sp : StackPointer)
                   (f : ⟦ A ⟧ → ⟦ B ⟧) (a : ⟦ A ⟧) : Set where
  field
    thunk-star     : Star prog s s'
    thunk-halted   : halted s' ≡ false
    -- Validity-based result (no encode!)
    thunk-result-valid : ValidAt (f a) (readReg (regs s') rax) (memory s')
    thunk-r14      : readReg (regs s') r14 ≡ readReg (regs s) r14
    thunk-r15      : readReg (regs s') r15 ≡ readReg (regs s) r15
    thunk-rbp      : readReg (regs s') rbp ≡ readReg (regs s) rbp
    thunk-stack-inv : StackInvariant s'
    thunk-capacity : StackCapacity s' 2

    -- RSP after thunk = entry RSP + 8 (thunk's ret pops return address)
    -- Thunk internally: push r15, push rbp, sub 16, <run f>, add 16, pop rbp, pop r15, ret
    -- Net effect on rsp: -8 -8 -16 +16 +8 +8 +8 = +8
    thunk-rsp-plus-8 : readReg (regs s') rsp ≡ readReg (regs s) rsp +ℕ 8

    -- D041: Memory in caller's stack frame is preserved
    -- Thunk writes only to its own frame, caller's frame is disjoint
    -- Uses abstract frameSlot - no addresses in interface!
    -- k is a slot INDEX (0, 1, 2, ...), not an address
    thunk-preserves-frame : ∀ k → frameSlot (memory s') caller-sp k ≡
                                  frameSlot (memory s) caller-sp k

    -- Memory at address 0 is preserved (null page protection)
    -- Thunk only writes to stack region, and 0 is not in stack region
    thunk-preserves-zero : readMem (memory s') 0 ≡ readMem (memory s) 0

    -- Memory at code-region addresses is preserved
    -- Thunk only writes to stack region, which is disjoint from code region
    thunk-preserves-code : ∀ addr → InCode addr →
                           readMem (memory s') addr ≡ readMem (memory s) addr

    -- Memory at heap-region addresses is preserved
    -- Thunk only writes to stack region, which is disjoint from heap region
    thunk-preserves-heap : ∀ addr → InHeap addr →
                           readMem (memory s') addr ≡ readMem (memory s) addr

    -- D041: Memory above thunk's entry rsp is preserved
    -- Thunk writes only at addresses ≤ entry-rsp - 8 (its own frame)
    -- So addresses > entry-rsp are safe (caller's caller frame and higher)
    thunk-preserves-above-entry-rsp : ∀ addr → addr > readReg (regs s) rsp →
                                      readMem (memory s') addr ≡ readMem (memory s) addr

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
-- The thunk ends with `ret`, which pops a return address from the stack.
-- The caller (apply) pushes this address via `call`, and thunk-correct
-- guarantees execution returns there.
--
-- NOTE: We use explicit runtime values (code-ptr, env) rather than
-- the semantic Closure record because:
-- 1. Closure.code-ptr in semantics is 0 (placeholder)
-- 2. The actual code-ptr comes from compilation (offset + 6)
-- 3. Apply reads these from memory, not from the semantic record
--
-- E is the env type, env is the captured environment value.
-- thunk-correct takes validity for both arg AND env (fully validity-based!)
record ClosureWellFormed {E A B : Type} (prog : Program)
                         (code-ptr : ℕ) (env : ⟦ E ⟧)
                         (semantics : ⟦ A ⟧ → ⟦ B ⟧) : Set where
  field
    -- The code-ptr is within the program bounds
    code-ptr-valid : code-ptr < length prog

    -- Executing from code-ptr produces correct result for any input
    -- ret-addr: the return address (pushed by call, popped by ret)
    -- caller-sp: identifies the caller's stack frame (D041)
    -- caller-sp-bound: caller's frame starts 8 bytes above current rsp (call convention)
    -- r15-in-code-evidence: r15 is in code region (set by Apply before call)
    -- v-arg: validity proof for argument (eliminates encode bridging!)
    -- v-env: validity proof for environment (eliminates encode bridging!)
    thunk-correct : ∀ (a : ⟦ A ⟧) (s : State) (ret-addr : ℕ) (caller-sp : StackPointer) →
      halted s ≡ false →
      pc s ≡ code-ptr →
      ValidAt a (readReg (regs s) rdi) (memory s) →    -- validity for arg!
      ValidAt env (readReg (regs s) r12) (memory s) →  -- validity for env!
      readMem (memory s) (readReg (regs s) rsp) ≡ just ret-addr →  -- Return address on stack
      StackInvariant s →
      readReg (regs s) rsp > slots 2 →
      StackPointer.addr caller-sp ≡ readReg (regs s) rsp +ℕ 8 →  -- D041: caller-sp bound
      InCode (readReg (regs s) r15) →  -- r15 in code region (from Apply)
      ∃[ s' ] (ThunkResult prog s s' caller-sp semantics a
              × pc s' ≡ ret-addr)

open ClosureWellFormed public

------------------------------------------------------------------------
-- CurryResult: Extended result for curry that includes well-formedness
------------------------------------------------------------------------

-- | When curry executes, it produces:
-- 1. A closure value (in rax)
-- 2. A proof that this closure is well-formed
--
-- This allows apply to use the well-formedness proof
--
-- The closure's runtime values are:
-- - rax = closure address (new-rsp)
-- - [closure] = env-addr = encode x
-- - [closure+8] = code-ptr = offset + 6
record CurryResult {A B C : Type} (f : IR (A * B) C)
                   (prog : Program) (s s' : State) (x : ⟦ A ⟧)
                   (offset : ℕ) : Set₁ where
  field
    -- Standard execution properties
    curry-star     : Star prog s s'
    curry-halted   : halted s' ≡ false
    curry-pc       : pc s' ≡ offset +ℕ compile-length (curry f)
    -- Validity-based result (replaces curry-rax : rax ≡ encode result)
    curry-result-valid : ValidAt {B ⇒ C} (eval (curry f) x) (readReg (regs s') rax) (memory s')
    curry-r14      : readReg (regs s') r14 ≡ readReg (regs s) r14
    curry-r15      : readReg (regs s') r15 ≡ readReg (regs s) r15
    curry-rbp      : readReg (regs s') rbp ≡ readReg (regs s) rbp
    curry-mem      : readMem (memory s') (readReg (regs s) r15) ≡
                     readMem (memory s) (readReg (regs s) r15)
    curry-stack-inv : StackInvariant s'
    curry-capacity : StackCapacity s' (ir-output-capacity (curry f))

    -- The closure produced is well-formed!
    -- This is the key property that apply needs
    -- Note: curry f : IR A (B ⇒ C), so eval (curry f) x : Closure B C
    --       semantics = Closure.semantics (eval (curry f) x) = λ b → eval f (x , b)
    --       code-ptr = offset + 6 (thunk entry in program)
    --       env = x (the captured value of type A)
    closure-wf : ClosureWellFormed {A} {B} {C} prog
                   (offset +ℕ 6)           -- code-ptr: thunk at offset+6
                   x                       -- env: the captured value
                   (λ b → eval f (x , b))  -- semantics: partial application

open CurryResult public

------------------------------------------------------------------------
-- ApplyWithWF: Apply execution that uses well-formedness
------------------------------------------------------------------------

-- | Apply a closure, given a well-formedness proof
-- This eliminates the need for apply-produces-result postulate!
--
-- Sketch of proof:
-- 1. Load (cl, a) from rdi
-- 2. Extract env-addr, code-ptr, a
-- 3. Set up call: push ret addr, set r12 = env-addr, set rdi = a
-- 4. Jump to code-ptr (call r15)
-- 5. By ClosureWellFormed.thunk-correct, execution produces correct result
-- 6. Return lands at ret addr
-- 7. Result is in rax
record ApplyWithWFResult {A B : Type} (prog : Program) (s s' : State)
                         (cl : Closure A B) (a : ⟦ A ⟧)
                         (offset : ℕ) : Set where
  field
    apply-star     : Star prog s s'
    apply-halted   : halted s' ≡ false
    apply-pc       : pc s' ≡ offset +ℕ compile-length (apply {A} {B})
    apply-rax      : readReg (regs s') rax ≡ encode (Closure.semantics cl a)
    apply-r14      : readReg (regs s') r14 ≡ readReg (regs s) r14
    apply-r15      : readReg (regs s') r15 ≡ readReg (regs s) r15
    apply-rbp      : readReg (regs s') rbp ≡ readReg (regs s) rbp
    apply-mem      : readMem (memory s') (readReg (regs s) r15) ≡
                     readMem (memory s) (readReg (regs s) r15)
    apply-stack-inv : StackInvariant s'
    apply-capacity : StackCapacity s' 2

open ApplyWithWFResult public

------------------------------------------------------------------------
-- run-apply-with-wf: Apply using well-formedness (TODO: implement)
------------------------------------------------------------------------

-- | Execute apply with a well-formedness proof
-- This is the key function that eliminates the postulate
--
-- TODO: Implement this by:
-- 1. Trace the 6 apply instructions up to the call
-- 2. Use ClosureWellFormed.thunk-correct to trace through the thunk
-- 3. Trace the ret instruction back
-- 4. Compose all Star proofs
--
-- run-apply-with-wf : ∀ {A B} (prefix suffix : Program)
--                     (cl : Closure A B) (a : ⟦ A ⟧) (s : State) →
--   ClosureWellFormed (prefix ++ compile-x86 (apply {A} {B}) ++ suffix) cl →
--   halted s ≡ false →
--   pc s ≡ length prefix →
--   readReg (regs s) rdi ≡ encode (cl , a) →
--   StackInvariant s →
--   readReg (regs s) rsp > slots 2 →
--   ∃[ s' ] ApplyWithWFResult (prefix ++ compile-x86 (apply {A} {B}) ++ suffix)
--                              s s' cl a (length prefix)
-- run-apply-with-wf = ?
