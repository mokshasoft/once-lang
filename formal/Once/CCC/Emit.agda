{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.CCC.Emit
--
-- Unified entry point for verified code generation.
-- Combines all three backends (AArch64, x86-64, RISC-V 64) and provides
-- end-to-end compilation from IR to assembly text.
--
-- This module is extracted via MAlonzo to provide verified pretty-printing
-- for all supported architectures.
------------------------------------------------------------------------

module Once.CCC.Emit where

open import Once.CCC.IR using (IR)

-- Import code generation from each backend
open import Once.CCC.Target.AArch64.CodeGen
  using (compile-aarch64)

open import Once.CCC.Target.X86.CodeGen
  using (compile-x86)

-- NOTE: RiscV64.CodeGen uses sized IR (Once.IRS) which is incompatible with
-- unsized IR (Once.IR) used here. Commenting out until types are unified.
-- open import Once.CCC.Target.RiscV64.CodeGen
--   using (compile-riscv)

-- Import assembly text emission from each backend
open import Once.Target.AArch64.Emit
  using ()
  renaming (programToText to aarch64ProgramToText)

open import Once.Target.X86.Emit
  using ()
  renaming (programToText to x86ProgramToText)

-- NOTE: RiscV64.Emit disabled until IR/IRS types are unified
-- open import Once.Target.RiscV64.Emit
--   using ()
--   renaming (programToText to riscvProgramToText)

-- Import C backend code generation
open import Once.CCC.Target.C.CodeGen
  using (compile-c-expr; compile-c-function)

open import Data.String using (String)
open import Once.Type using (Type)

------------------------------------------------------------------------
-- End-to-end compilation: IR → C / assembly text
------------------------------------------------------------------------

-- | Compile IR to C function text (verified)
-- Input: Declared function type, function name, IR morphism
-- Output: C function definition text
compileCToText : Type → String → ∀ {A B} → IR A B → String
compileCToText = compile-c-function

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
-- NOTE: Disabled until IR/IRS types are unified
-- Input: IR morphism
-- Output: GAS-compatible assembly text for RISC-V 64
-- compileRiscVToText : ∀ {A B} → IR A B → String
-- compileRiscVToText ir = riscvProgramToText (compile-riscv ir)
