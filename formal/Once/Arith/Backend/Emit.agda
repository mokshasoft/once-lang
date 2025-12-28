------------------------------------------------------------------------
-- Once.Arith.Backend.Emit
--
-- Aggregate module for all arithmetic backend emitters.
-- Used as the entry point for MAlonzo compilation.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Backend.Emit where

open import Data.String using (String)

-- Import backend modules
import Once.Arith.Backend.X86.Emit as X86
import Once.Arith.Backend.X86.Syntax as X86S
import Once.Arith.Backend.AArch64.Emit as AArch64
import Once.Arith.Backend.AArch64.Syntax as AArch64S
import Once.Arith.Backend.RiscV.Emit as RiscV
import Once.Arith.Backend.RiscV.Syntax as RiscVS

-- Export emit functions with qualified names
emitX86 : X86S.ArithProgram → String
emitX86 = X86.emitProgram

emitAArch64 : AArch64S.ArithProgram → String
emitAArch64 = AArch64.emitProgram

emitRiscV : RiscVS.ArithProgram → String
emitRiscV = RiscV.emitProgram
