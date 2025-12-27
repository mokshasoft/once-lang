{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.Emit
--
-- Unified entry point for verified code generation.
-- Combines all three backends (AArch64, x86-64, RISC-V 64) and provides
-- end-to-end compilation from IR to assembly text.
--
-- This module is extracted via MAlonzo to provide verified pretty-printing
-- for all supported architectures.
------------------------------------------------------------------------

module Once.Backend.Emit where

open import Once.IR using (IR)

-- Import code generation from each backend
open import Once.Backend.AArch64.CodeGen
  using (compile-aarch64)

open import Once.Backend.X86.CodeGen
  using (compile-x86)

open import Once.Backend.RiscV64.CodeGen
  using (compile-riscv)

-- Import assembly text emission from each backend
open import Once.Backend.AArch64.Emit
  using ()
  renaming (programToText to aarch64ProgramToText)

open import Once.Backend.X86.Emit
  using ()
  renaming (programToText to x86ProgramToText)

open import Once.Backend.RiscV64.Emit
  using ()
  renaming (programToText to riscvProgramToText)

open import Data.String using (String)

------------------------------------------------------------------------
-- End-to-end compilation: IR → assembly text
------------------------------------------------------------------------

-- | Compile IR to AArch64 assembly text (verified)
-- Input: IR morphism
-- Output: GAS-compatible assembly text for AArch64
compileAArch64ToText : ∀ {A B} → IR A B → String
compileAArch64ToText ir = aarch64ProgramToText (compile-aarch64 ir)

-- | Compile IR to x86-64 assembly text (verified)
-- Input: IR morphism
-- Output: GAS-compatible assembly text (AT&T syntax) for x86-64
compileX86ToText : ∀ {A B} → IR A B → String
compileX86ToText ir = x86ProgramToText (compile-x86 ir)

-- | Compile IR to RISC-V 64-bit assembly text (verified)
-- Input: IR morphism
-- Output: GAS-compatible assembly text for RISC-V 64
compileRiscVToText : ∀ {A B} → IR A B → String
compileRiscVToText ir = riscvProgramToText (compile-riscv ir)
