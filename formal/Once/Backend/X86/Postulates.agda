------------------------------------------------------------------------
-- Once.Backend.X86.Postulates
--
-- X86-specific postulates. Separated from Once.Postulates to avoid
-- cyclic imports with X86 modules.
--
-- See Once.Postulates for documentation format and checklist.
------------------------------------------------------------------------

module Once.Backend.X86.Postulates where

open import Data.Nat using (ℕ; _>_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Backend.X86.Syntax using (rsp; slot-size)
open import Once.Backend.X86.Semantics using (State; readReg)
open import Once.Backend.X86.Semantics using () renaming (module State to St)
open St using (regs)

open import Once.Backend.Common.MemoryRegions using (InStack)

------------------------------------------------------------------------
-- Postulate P4: Stack Pointer Bounds (Runtime Property)
------------------------------------------------------------------------
--
-- After any stack-using operation, rsp remains > slots 5 (40 bytes).
--
-- NEEDED BY: Once.Backend.X86.Correct.MutualIR (inl, inr, pair, case, curry)
--
-- JUSTIFICATION:
--   The initial rsp is 0x7FFF0000 (≈2 billion). Stack-using operations
--   subtract at most 64 bytes per call. Even with deep recursion (millions
--   of calls), total stack usage is bounded and rsp never drops below slots 5.
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

------------------------------------------------------------------------
-- NOTE: rsp-bound-after-stack-op ELIMINATED
------------------------------------------------------------------------
--
-- The rsp-bound-after-stack-op postulate has been eliminated!
--
-- Instead of assuming blanket stack bounds, capacity is now:
--   1. Taken as a precondition (StackPointer with sufficient addr)
--   2. Threaded through via StackCapacity and capacity-from-larger
--   3. The entry point (compile-correct-x86) takes sp-addr sp > slots n
--
------------------------------------------------------------------------

postulate
  -- RSP is always in stack region (runtime invariant)
  -- Used by curry to construct thunk-capacity from rsp-sufficient proof.
  -- TODO: Eliminate by threading InStack evidence through StackCapacity
  rsp-in-stack-after-stack-op : ∀ (s : State) → InStack (readReg (regs s) rsp)

------------------------------------------------------------------------
-- NOTE: rsp-bound-for-ir ELIMINATED
------------------------------------------------------------------------
--
-- The rsp-bound-for-ir postulate has been eliminated!
--
-- Instead of assuming dynamic capacity bounds, capacity is now threaded
-- through the proofs:
--   1. curry produces ClosureWellFormed with thunk-capacity field
--   2. apply provides capacity to thunk-correct via this field
--   3. pair/compose/case thread capacity via capacity-from-larger
--
-- This ensures capacity is properly accounted for through closure calls.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NOTE: apply-produces-result ELIMINATED
------------------------------------------------------------------------
--
-- The apply-produces-result postulate has been eliminated!
--
-- Instead of a monolithic postulate, apply correctness is now proven using:
--   1. ClosureWellFormed - ensures closure has valid code-ptr and thunk
--   2. run-apply-to-ir-result (Apply.agda) - uses ClosureWellFormed
--   3. Local postulates for stack/heap disjointness and memory preservation
--
-- The local postulates in run-apply-to-ir-result are more fine-grained and
-- can be individually verified, unlike the monolithic apply-produces-result.
--
-- Key improvements:
--   - curry now produces has-closure with ClosureWellFormed proof
--   - apply uses run-apply-to-ir-result which consumes ClosureWellFormed
--   - r15 preservation proven via push/pop sequence in apply
--
------------------------------------------------------------------------

-- NOTE: encode-curry-at-rsp was ELIMINATED
-- The curry encoding is now derived from encode-closure-construct (in Once.Postulates)
-- via the proof in Once.Backend.X86.Correct.IR.Curry (lines 468-470)
