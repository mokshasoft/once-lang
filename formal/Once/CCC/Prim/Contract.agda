------------------------------------------------------------------------
-- Once.CCC.Prim.Contract
--
-- Minimal contract for primitive operations.
--
-- Design: The contract specifies only the interface.
-- The proof obligation is abstract: "preserves CCC state".
------------------------------------------------------------------------

module Once.CCC.Prim.Contract where

open import Once.Type using (Type)
open import Once.CCC.IR using (AllocMode)

------------------------------------------------------------------------
-- PrimContract: Minimal interface specification
--
-- Just says where the result goes. Everything else (frame preservation,
-- memory safety, etc.) is captured by the abstract PreservesCCC predicate
-- that the backend defines.
------------------------------------------------------------------------

record PrimContract (A B : Type) : Set where
  field
    output-mode : AllocMode

open PrimContract public
