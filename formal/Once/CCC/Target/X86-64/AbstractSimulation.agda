------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.AbstractSimulation
--
-- DEPRECATED: This module is now a thin re-export from DirectSimulation.
--
-- The old complex StateCorresponds from Refinement/SlotToX86 has been
-- replaced by the simpler X86Corresponds in DirectSimulation.
--
-- The key insight: AbstractInstr maps 1-to-1 to x86 instructions,
-- so simulation is straightforward by construction.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.AbstractSimulation where

-- Re-export everything from DirectSimulation
open import Once.CCC.Target.X86-64.DirectSimulation public
  using (X86State; X86Corresponds; X86Corresponds)

-- Re-export simulation modules
open import Once.CCC.Target.X86-64.DirectSimulation
  using (module X86Corresponds; module InstrSimulation; module TraceSimulation)
  public

------------------------------------------------------------------------
-- Migration note:
--
-- Old API (Refinement/SlotToX86):
--   StateCorresponds σ s - complex record with 13+ fields
--   Per-instruction lemmas for each AbstractInstr
--
-- New API (DirectSimulation):
--   X86Corresponds ls xs - simple record with 4 fields
--   instr-simulation - general lemma for all instructions
--   trace-simulation - proven by induction using instr-simulation
--
-- The old Refinement proofs have been removed as they are superseded
-- by the direct simulation approach.
------------------------------------------------------------------------
