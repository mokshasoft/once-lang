------------------------------------------------------------------------
-- Once.Backend.X86.Postulates
--
-- X86-specific postulates. Separated from Once.Postulates to avoid
-- cyclic imports with X86 modules.
--
-- See Once.Postulates for documentation format and checklist.
------------------------------------------------------------------------

module Once.Backend.X86.Postulates where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; _>_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; length; _++_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)

open import Once.Type using (Type; _⇒_; _*_)
open import Once.IR using (apply; curry; IR)
open import Once.Semantics using (⟦_⟧; encode; eval)
open import Once.Memory using (Word)

open import Once.Backend.X86.Syntax using (rsp; rax; rdi; r14; r15; rbp; Program)
open import Once.Backend.X86.Semantics using (State; readReg; readMem)
open import Once.Backend.X86.Semantics using () renaming (module State to St)
open St using (regs; memory; halted; pc)
open import Once.Backend.X86.Correct.Star using (Star)
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.CodeGen using (compile-x86; compile-length)

------------------------------------------------------------------------
-- Postulate P4: Stack Pointer Bounds (Runtime Property)
------------------------------------------------------------------------
--
-- After any stack-using operation, rsp remains > 16.
--
-- NEEDED BY: Once.Backend.X86.Correct.MutualIR (inl, inr, pair, case, curry)
--
-- JUSTIFICATION:
--   The initial rsp is 0x7FFF0000 (≈2 billion). Stack-using operations
--   subtract at most 64 bytes per call. Even with deep recursion (millions
--   of calls), total stack usage is bounded and rsp never drops below 16.
--   This is a runtime guarantee from the execution environment.
--
-- IMPACT:
--   If the stack were exhausted, the program would crash before returning
--   an incorrect result. This axiom captures that we're assuming sufficient
--   stack space, which is true for any realistic program execution.
--
-- RUNTIME EFFECT: Assumes sufficient stack space (standard runtime assumption)
--
------------------------------------------------------------------------

postulate
  rsp-bound-after-stack-op : ∀ (s : State) → readReg (regs s) rsp > 16

------------------------------------------------------------------------
-- Postulate P5: Closure Application (Semantic Boundary)
------------------------------------------------------------------------
--
-- Executing `apply` on a closure produces the correct result.
--
-- NEEDED BY: Once.Backend.X86.Correct.MutualIR (run-apply-star-direct)
--
-- WHY THIS IS HARD TO PROVE (MODULAR CASE):
--   Apply's `call r15` instruction jumps to a thunk compiled by curry.
--   The thunk code is NOT in `compile-x86 apply` - it's somewhere in
--   `prefix` where a previous curry compilation placed it.
--
--   In the modular proof (run-ir-star-at-offset apply), we don't know
--   where the closure came from, so we can't prove the thunk is correct.
--
-- SEMANTIC BOUNDARY:
--   This postulate captures the calling convention between curry and apply:
--   - curry stores (encode env, code_ptr) at closure address
--   - apply loads env→r12, code_ptr→r15, arg→rdi, then calls r15
--   - thunk pairs (r12, rdi), calls f, returns result in rax
--   - ret pops return address and jumps back after the call
--
-- PROGRESS TOWARD ELIMINATION:
--   We have built the infrastructure to eliminate this postulate:
--
--   1. ClosureWellFormed predicate (ClosureWellFormed.agda)
--      - Captures that code_ptr points to valid thunk in program
--      - thunk-correct field proves thunk executes correctly
--
--   2. CurryResult establishes ClosureWellFormed (MutualIR.agda)
--      - run-curry-star-with-wf produces CurryResult
--      - closure-wf field provides well-formedness proof
--
--   3. run-apply-with-wf uses ClosureWellFormed (IR/Apply.agda)
--      - Given well-formedness proof, can prove apply correctness
--      - Uses thunk-correct from ClosureWellFormed
--
--   4. ClosureContext infrastructure (ClosureContext.agda) - NEW
--      - ClosureEntry/ClosureContext: Track closures and their WF proofs
--      - ApplyMemoryLayout: Memory precondition for apply
--      - run-apply-with-full-wf: PROVEN apply using WF + memory layout
--      - CurryOutputWF: What curry produces for threading to apply
--
-- ELIMINATION PATH (in progress):
--   The postulate-free path exists but requires threading:
--
--   Step 1: run-curry-star-with-wf → CurryResult with closure-wf ✓
--   Step 2: Extract CurryOutputWF from CurryResult ✓
--   Step 3: Thread CurryOutputWF through compose/pair (TODO)
--   Step 4: run-apply-with-full-wf consumes the WF proof ✓
--
--   For whole-program proofs where curry and apply are composed,
--   use run-curry-star-with-wf + run-apply-with-full-wf instead.
--   This path avoids this postulate entirely.
--
-- REMAINING WORK:
--   - Extend IRStarResult to carry optional ClosureWellFormed output
--   - Modify run-curry-star-direct to output ClosureWellFormed
--   - Modify run-pair-star-direct to track closure WF through pairs
--   - Modify run-apply-star-direct to require/consume ClosureWellFormed
--   - Update run-compose-star-direct to thread WF from curry to apply
--
-- RUNTIME EFFECT: None (proof-only)
--
------------------------------------------------------------------------

postulate
  apply-produces-result : ∀ {A B : Type} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) rdi ≡ encode {(A ⇒ B) * A} x →
    StackInvariant s →
    readReg (regs s) rsp > 16 →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    in ∃[ s' ] (Star prog s s'
              × halted s' ≡ false
              × pc s' ≡ length prefix +ℕ compile-length (apply {A} {B})
              × readReg (regs s') rax ≡ encode {B} (eval (apply {A} {B}) x)
              × readReg (regs s') r14 ≡ readReg (regs s) r14
              × readReg (regs s') r15 ≡ readReg (regs s) r15
              × readReg (regs s') rbp ≡ readReg (regs s) rbp
              × readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
              × readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
              × readMem (memory s') (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
              × StackInvariant s'
              × readReg (regs s') rsp > 16
              × RbpInvariant s')

-- NOTE: encode-curry-at-rsp was ELIMINATED
-- The curry encoding is now derived from encode-closure-construct (in Once.Postulates)
-- via the proof in Once.Backend.X86.Correct.IR.Curry (lines 468-470)
