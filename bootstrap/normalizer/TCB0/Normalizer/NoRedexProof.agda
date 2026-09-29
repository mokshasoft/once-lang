-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

{-# OPTIONS --safe #-}
module normalizer.TCB0.Normalizer.NoRedexProof where

-- Re-export everything from Syntax.NoRedex
open import normalizer.Syntax.NoRedex public
