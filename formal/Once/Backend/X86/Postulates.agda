------------------------------------------------------------------------
-- Once.Backend.X86.Postulates
--
-- X86-specific postulates.
--
-- STATUS: ALL POSTULATES ELIMINATED!
-- This module is kept for documentation of eliminated postulates.
------------------------------------------------------------------------

module Once.Backend.X86.Postulates where

------------------------------------------------------------------------
-- NOTE: rsp-bound-after-stack-op ELIMINATED
------------------------------------------------------------------------
--
-- Instead of assuming blanket stack bounds, capacity is now:
--   1. Taken as a precondition (StackPointer with sufficient addr)
--   2. Threaded through via StackCapacity and capacity-from-larger
--   3. The entry point (compile-correct-x86) takes sp-addr sp > slots n
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NOTE: rsp-in-stack-after-stack-op ELIMINATED
------------------------------------------------------------------------
--
-- Instead of assuming RSP is always in stack region, InStack evidence
-- is now derived from the caller's StackPointer:
--   1. caller-sp : StackPointer has in-stack : InStack (addr caller-sp)
--   2. After ret, s-final.rsp = caller-sp.addr (call convention)
--   3. InStack (s-final.rsp) follows by substitution
--
-- This is region-based reasoning, not numeric - just threading existing
-- StackPointer evidence through the proof chain.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NOTE: rsp-bound-for-ir ELIMINATED
------------------------------------------------------------------------
--
-- Instead of assuming dynamic capacity bounds, capacity is now threaded
-- through the proofs:
--   1. curry produces ClosureWellFormed with thunk-capacity field
--   2. apply provides capacity to thunk-correct via this field
--   3. pair/compose/case thread capacity via capacity-from-larger
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NOTE: curry-rsp-preserved ELIMINATED
------------------------------------------------------------------------
--
-- This postulate was declared but never actually used in any proofs.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NOTE: apply-produces-result ELIMINATED
------------------------------------------------------------------------
--
-- Instead of a monolithic postulate, apply correctness is now proven using:
--   1. ClosureWellFormed - ensures closure has valid code-ptr and thunk
--   2. run-apply-to-ir-result (Apply.agda) - uses ClosureWellFormed
--   3. Local postulates for stack/heap disjointness and memory preservation
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- NOTE: encode-curry-at-rsp ELIMINATED
------------------------------------------------------------------------
--
-- The curry encoding is now derived from encode-closure-construct
-- (in Once.Postulates) via the proof in Once.Backend.X86.Correct.IR.Curry
--
------------------------------------------------------------------------
