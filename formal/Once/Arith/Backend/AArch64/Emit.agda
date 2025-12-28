------------------------------------------------------------------------
-- Once.Arith.Backend.AArch64.Emit
--
-- Assembly text emission for AArch64 arithmetic instructions.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Backend.AArch64.Emit where

open import Once.Arith.Backend.AArch64.Syntax

open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer using (ℤ)
open import Data.Integer.Show renaming (show to showℤ)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; map)

------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------

unlines : List String → String
unlines [] = ""
unlines (x ∷ []) = x
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

------------------------------------------------------------------------
-- GPR emission
------------------------------------------------------------------------

gprToText : GPReg → String
gprToText x0  = "x0"
gprToText x1  = "x1"
gprToText x2  = "x2"
gprToText x3  = "x3"
gprToText x4  = "x4"
gprToText x5  = "x5"
gprToText x6  = "x6"
gprToText x7  = "x7"
gprToText x8  = "x8"
gprToText x9  = "x9"
gprToText x10 = "x10"
gprToText x11 = "x11"
gprToText x12 = "x12"
gprToText x13 = "x13"
gprToText x14 = "x14"
gprToText x15 = "x15"
gprToText x16 = "x16"
gprToText x17 = "x17"
gprToText x18 = "x18"
gprToText x19 = "x19"
gprToText x20 = "x20"
gprToText x21 = "x21"
gprToText x22 = "x22"
gprToText x23 = "x23"
gprToText x24 = "x24"
gprToText x25 = "x25"
gprToText x26 = "x26"
gprToText x27 = "x27"
gprToText x28 = "x28"
gprToText x29 = "x29"
gprToText x30 = "x30"

------------------------------------------------------------------------
-- FP register emission
------------------------------------------------------------------------

fpToText : FPReg → String
fpToText d0  = "d0"
fpToText d1  = "d1"
fpToText d2  = "d2"
fpToText d3  = "d3"
fpToText d4  = "d4"
fpToText d5  = "d5"
fpToText d6  = "d6"
fpToText d7  = "d7"
fpToText d8  = "d8"
fpToText d9  = "d9"
fpToText d10 = "d10"
fpToText d11 = "d11"
fpToText d12 = "d12"
fpToText d13 = "d13"
fpToText d14 = "d14"
fpToText d15 = "d15"
fpToText d16 = "d16"
fpToText d17 = "d17"
fpToText d18 = "d18"
fpToText d19 = "d19"
fpToText d20 = "d20"
fpToText d21 = "d21"
fpToText d22 = "d22"
fpToText d23 = "d23"
fpToText d24 = "d24"
fpToText d25 = "d25"
fpToText d26 = "d26"
fpToText d27 = "d27"
fpToText d28 = "d28"
fpToText d29 = "d29"
fpToText d30 = "d30"
fpToText d31 = "d31"

-- | Single-precision register name (s instead of d)
fpToTextS : FPReg → String
fpToTextS d0  = "s0"
fpToTextS d1  = "s1"
fpToTextS d2  = "s2"
fpToTextS d3  = "s3"
fpToTextS d4  = "s4"
fpToTextS d5  = "s5"
fpToTextS d6  = "s6"
fpToTextS d7  = "s7"
fpToTextS d8  = "s8"
fpToTextS d9  = "s9"
fpToTextS d10 = "s10"
fpToTextS d11 = "s11"
fpToTextS d12 = "s12"
fpToTextS d13 = "s13"
fpToTextS d14 = "s14"
fpToTextS d15 = "s15"
fpToTextS d16 = "s16"
fpToTextS d17 = "s17"
fpToTextS d18 = "s18"
fpToTextS d19 = "s19"
fpToTextS d20 = "s20"
fpToTextS d21 = "s21"
fpToTextS d22 = "s22"
fpToTextS d23 = "s23"
fpToTextS d24 = "s24"
fpToTextS d25 = "s25"
fpToTextS d26 = "s26"
fpToTextS d27 = "s27"
fpToTextS d28 = "s28"
fpToTextS d29 = "s29"
fpToTextS d30 = "s30"
fpToTextS d31 = "s31"

------------------------------------------------------------------------
-- Operand emission
------------------------------------------------------------------------

opToText : Operand → String
opToText (regOp r) = gprToText r
opToText (immOp n) = "#" ++ showℤ n

fpOpToText : FPOperand → String
fpOpToText (fpRegOp r) = fpToText r

------------------------------------------------------------------------
-- Condition code emission
------------------------------------------------------------------------

condToText : Cond → String
condToText cond-eq = "eq"
condToText cond-ne = "ne"
condToText cond-lt = "lt"
condToText cond-le = "le"
condToText cond-gt = "gt"
condToText cond-ge = "ge"

------------------------------------------------------------------------
-- Integer instruction emission
------------------------------------------------------------------------

intInstrToText : IntInstr → String
intInstrToText (mov dst src) =
  "    mov " ++ gprToText dst ++ ", " ++ opToText src
intInstrToText (movz dst imm shift) =
  "    movz " ++ gprToText dst ++ ", #" ++ showℤ imm ++ ", lsl #" ++ showℕ shift
intInstrToText (movk dst imm shift) =
  "    movk " ++ gprToText dst ++ ", #" ++ showℤ imm ++ ", lsl #" ++ showℕ shift
intInstrToText (add dst src1 src2) =
  "    add " ++ gprToText dst ++ ", " ++ gprToText src1 ++ ", " ++ opToText src2
intInstrToText (sub dst src1 src2) =
  "    sub " ++ gprToText dst ++ ", " ++ gprToText src1 ++ ", " ++ opToText src2
intInstrToText (mul dst src1 src2) =
  "    mul " ++ gprToText dst ++ ", " ++ gprToText src1 ++ ", " ++ gprToText src2
intInstrToText (sdiv dst src1 src2) =
  "    sdiv " ++ gprToText dst ++ ", " ++ gprToText src1 ++ ", " ++ gprToText src2
intInstrToText (msub dst mul1 mul2 acc) =
  "    msub " ++ gprToText dst ++ ", " ++ gprToText mul1 ++ ", " ++ gprToText mul2 ++ ", " ++ gprToText acc
intInstrToText (neg dst src) =
  "    neg " ++ gprToText dst ++ ", " ++ gprToText src
intInstrToText (strPre src imm) =
  "    str " ++ gprToText src ++ ", [sp, #-" ++ showℕ imm ++ "]!"
intInstrToText (ldrPost dst imm) =
  "    ldr " ++ gprToText dst ++ ", [sp], #" ++ showℕ imm
intInstrToText (cmp rn op) =
  "    cmp " ++ gprToText rn ++ ", " ++ opToText op
intInstrToText (cset rd cc) =
  "    cset " ++ gprToText rd ++ ", " ++ condToText cc

------------------------------------------------------------------------
-- FP instruction emission
------------------------------------------------------------------------

fpInstrToText : FPInstr → String
fpInstrToText (fmov dst src) =
  "    fmov " ++ fpToText dst ++ ", " ++ fpOpToText src
fpInstrToText (fadd dst src1 src2) =
  "    fadd " ++ fpToText dst ++ ", " ++ fpToText src1 ++ ", " ++ fpToText src2
fpInstrToText (fsub dst src1 src2) =
  "    fsub " ++ fpToText dst ++ ", " ++ fpToText src1 ++ ", " ++ fpToText src2
fpInstrToText (fmul dst src1 src2) =
  "    fmul " ++ fpToText dst ++ ", " ++ fpToText src1 ++ ", " ++ fpToText src2
fpInstrToText (fdiv dst src1 src2) =
  "    fdiv " ++ fpToText dst ++ ", " ++ fpToText src1 ++ ", " ++ fpToText src2
fpInstrToText (fneg dst src) =
  "    fneg " ++ fpToText dst ++ ", " ++ fpToText src
-- Single-precision variants
fpInstrToText (faddS dst src1 src2) =
  "    fadd " ++ fpToTextS dst ++ ", " ++ fpToTextS src1 ++ ", " ++ fpToTextS src2
fpInstrToText (fsubS dst src1 src2) =
  "    fsub " ++ fpToTextS dst ++ ", " ++ fpToTextS src1 ++ ", " ++ fpToTextS src2
fpInstrToText (fmulS dst src1 src2) =
  "    fmul " ++ fpToTextS dst ++ ", " ++ fpToTextS src1 ++ ", " ++ fpToTextS src2
fpInstrToText (fdivS dst src1 src2) =
  "    fdiv " ++ fpToTextS dst ++ ", " ++ fpToTextS src1 ++ ", " ++ fpToTextS src2
fpInstrToText (fnegS dst src) =
  "    fneg " ++ fpToTextS dst ++ ", " ++ fpToTextS src

------------------------------------------------------------------------
-- Unified instruction emission
------------------------------------------------------------------------

instrToText : ArithInstr → String
instrToText (intI i) = intInstrToText i
instrToText (fpI f)  = fpInstrToText f

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

emitProgram : ArithProgram → String
emitProgram instrs = unlines (map instrToText instrs)
