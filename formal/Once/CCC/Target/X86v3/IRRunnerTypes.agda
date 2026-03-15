------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IRRunnerTypes
--
-- DEPRECATED: This module used the old StateCorresponds from Refinement.
--
-- The new approach uses DirectSimulation with X86Corresponds which is
-- much simpler. The trace-based proof in PairWF/Dispatcher produces
-- IRResultAWF with traces that directly simulate to x86.
--
-- This file is kept as a stub for backward compatibility.
-- New code should use DirectSimulation instead.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.IRRunnerTypes where

-- This module is deprecated.
-- See DirectSimulation.agda for the new approach.

open import Data.Unit using (⊤)

-- Stub exports for any code that still imports this module
deprecated-stub : ⊤
deprecated-stub = _
