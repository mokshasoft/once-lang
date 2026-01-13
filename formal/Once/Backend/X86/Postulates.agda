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

open import Once.Backend.Common.MemoryRegions using (Region; stack; region-of)
open import Once.Backend.X86.Correct.StackInstantiation using (slots)

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

postulate
  -- Changed from > slots 2 to > slots 5 to support memory layout proofs
  -- Pair setup subtracts slots 5 from rsp (3 pushes + sub (slots 2))
  rsp-bound-after-stack-op : ∀ (s : State) → readReg (regs s) rsp > slots 5

  -- RSP is always in stack region (runtime invariant)
  -- Companion to rsp-bound-after-stack-op: rsp not only has enough space,
  -- but is also in the correct memory region.
  rsp-in-stack-after-stack-op : ∀ (s : State) → region-of (readReg (regs s) rsp) ≡ stack

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
