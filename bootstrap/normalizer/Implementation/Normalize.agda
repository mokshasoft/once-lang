------------------------------------------------------------------------
-- Normalize: The Actual Normalizer
--
-- This module defines a normalizer that applies CCC reduction rules
-- to encoded terms. Unlike `cata TermF In` (which is just identity),
-- this actually reduces redexes.
--
-- Structure:
--   normalize = cata TermF normalize-step
--   normalize-step checks for redexes and applies reductions
--
-- This is a facade module that re-exports from submodules:
--   Normalize.Rebuild       - rebuild helpers
--   Normalize.Dispatch      - is-X dispatch functions
--   Normalize.Handlers      - handler functions and normalize-step
--   Normalize.NoRedexRebuild - NoRedex proofs for rebuilds
--   Normalize.NoRedexHandlers - NoRedex proofs for handlers
--   Normalize.NstepDispatch - tail dispatchers and dispatch lemmas
--   Normalize.Fixpoint      - fixpoint proofs for NoRedex terms
------------------------------------------------------------------------

module normalizer.Implementation.Normalize where

-- Re-export everything from the submodule chain
-- Fixpoint is the top of the chain and re-exports everything below it
open import normalizer.Implementation.Normalize.Fixpoint public

-- Note: distrib, caseWithCtx, _>>_, ⟶1, etc. are all exported via Normalize.Chain

------------------------------------------------------------------------
-- Additional definitions not in submodules
------------------------------------------------------------------------

-- NoRedex proof for normalize (uses nr-cata from NoRedex)
-- nr-cata is re-exported through the Fixpoint chain
normalize-noredex : NoRedex normalize
normalize-noredex = nr-cata nr-normalize-step

------------------------------------------------------------------------
-- The Encoding of the Normalizer
------------------------------------------------------------------------

-- The normalizer encoded as data
-- Abstract prevents Agda from unfolding during MainTheorem type-checking
abstract
  normalize-encoded : Term Unit TermCode'
  normalize-encoded = encode normalize

  -- Definitional equality (for export)
  normalize-encoded-def : normalize-encoded ≡ encode normalize
  normalize-encoded-def = refl
