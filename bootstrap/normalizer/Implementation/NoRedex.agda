------------------------------------------------------------------------
-- NoRedex: Re-export from Foundations
--
-- This module re-exports the NoRedex definitions from Foundations.
-- The core definitions (NoRedex, NotIdStruct, views) are foundational
-- concepts independent of any normalizer implementation.
--
-- Any implementation-specific lemmas about NoRedex would go here,
-- but currently all NoRedex-related content is foundational.
------------------------------------------------------------------------

module normalizer.Implementation.NoRedex where

-- Re-export everything from Foundations.NoRedex
open import normalizer.Foundations.NoRedex public
