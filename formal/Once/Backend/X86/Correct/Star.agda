------------------------------------------------------------------------
-- Once.Backend.X86.Correct.Star
--
-- Star (reflexive-transitive closure) relation for x86-64 execution.
-- This module instantiates Common.Star with x86-specific types.
--
-- Key benefit: composition is just transitivity (trivial chaining).
------------------------------------------------------------------------

module Once.Backend.X86.Correct.Star where

open import Once.Backend.X86.Syntax using (Program)
open import Once.Backend.X86.Semantics using (State; step)
open import Once.Backend.X86.Semantics using (module State)
open State using (halted)

-- Instantiate Common.Star with x86 types and re-export everything
open import Once.Backend.Common.Star Program State halted step public
