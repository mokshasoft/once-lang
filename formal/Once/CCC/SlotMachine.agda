------------------------------------------------------------------------
-- Once.CCC.SlotMachine
--
-- Re-exports SMCore and SMPrimitives for backward compatibility.
--
-- SMCore is the SOURCE OF TRUTH for types and core operations.
-- SMPrimitives provides all lemmas and proofs.
-- This module exists only to maintain import compatibility
-- with existing code.
------------------------------------------------------------------------

module Once.CCC.SlotMachine where

-- Re-export everything from SMCore (types and core operations)
open import Once.CCC.SMCore public

-- Re-export everything from SMPrimitives (lemmas and proofs)
open import Once.CCC.SMPrimitives public
