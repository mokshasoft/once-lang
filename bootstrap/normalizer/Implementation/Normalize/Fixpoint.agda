------------------------------------------------------------------------
-- Normalize.Fixpoint: Fixpoint property proofs for NoRedex terms
--
-- For NoRedex t: normalize ∘ encode t ⟶* encode t
--
-- This module is a facade that re-exports from split submodules to
-- reduce memory pressure during type-checking.
------------------------------------------------------------------------

module normalizer.Implementation.Normalize.Fixpoint where

-- Re-export everything from the split modules
open import normalizer.Implementation.Normalize.Fixpoint.MainTheorem public
