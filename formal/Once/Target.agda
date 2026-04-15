-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Target
--
-- Target interface for code generation.
-- Each target (x86-64, x86-32, RISC-V, etc.) implements this interface.
------------------------------------------------------------------------

module Once.Target where

open import Data.String using (String)
open import Once.CCC.IR using (IR)

------------------------------------------------------------------------
-- Target Record
------------------------------------------------------------------------

-- | A target provides architecture-specific code generation
record Target : Set where
  field
    -- | Compile IR to assembly text (function body only)
    irToAsm : ∀ {A B} → IR A B → String
    -- | Assembly file header (e.g., ".section .text")
    asmHeader : String
    -- | Generate function prologue (label, .globl directive)
    functionPrologue : String → String
    -- | Generate function epilogue (ret instruction)
    functionEpilogue : String

open Target public
