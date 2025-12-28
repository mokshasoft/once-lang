------------------------------------------------------------------------
-- Once.Arith.Backend.AArch64.Syntax
--
-- AArch64 instruction subset for arithmetic operations.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Backend.AArch64.Syntax where

open import Once.Arith.Type using (NumType; RegClass)
open import Once.Arith.Type as T using ()

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Integer using (ℤ)

------------------------------------------------------------------------
-- General-purpose registers (64-bit X registers)
------------------------------------------------------------------------

data GPReg : Set where
  x0  : GPReg
  x1  : GPReg
  x2  : GPReg
  x3  : GPReg
  x4  : GPReg
  x5  : GPReg
  x6  : GPReg
  x7  : GPReg
  x8  : GPReg
  x9  : GPReg
  x10 : GPReg
  x11 : GPReg
  x12 : GPReg
  x13 : GPReg
  x14 : GPReg
  x15 : GPReg
  x16 : GPReg
  x17 : GPReg
  x18 : GPReg
  x19 : GPReg
  x20 : GPReg
  x21 : GPReg
  x22 : GPReg
  x23 : GPReg
  x24 : GPReg
  x25 : GPReg
  x26 : GPReg
  x27 : GPReg
  x28 : GPReg
  x29 : GPReg
  x30 : GPReg

------------------------------------------------------------------------
-- Floating-point / SIMD registers
------------------------------------------------------------------------

data FPReg : Set where
  d0  : FPReg
  d1  : FPReg
  d2  : FPReg
  d3  : FPReg
  d4  : FPReg
  d5  : FPReg
  d6  : FPReg
  d7  : FPReg
  d8  : FPReg
  d9  : FPReg
  d10 : FPReg
  d11 : FPReg
  d12 : FPReg
  d13 : FPReg
  d14 : FPReg
  d15 : FPReg
  d16 : FPReg
  d17 : FPReg
  d18 : FPReg
  d19 : FPReg
  d20 : FPReg
  d21 : FPReg
  d22 : FPReg
  d23 : FPReg
  d24 : FPReg
  d25 : FPReg
  d26 : FPReg
  d27 : FPReg
  d28 : FPReg
  d29 : FPReg
  d30 : FPReg
  d31 : FPReg

------------------------------------------------------------------------
-- Unified register type
------------------------------------------------------------------------

data Reg : RegClass → Set where
  gpr : GPReg → Reg T.GPR
  fp  : FPReg → Reg T.XMM

------------------------------------------------------------------------
-- Operands
------------------------------------------------------------------------

data Operand : Set where
  regOp : GPReg → Operand
  immOp : ℤ → Operand

data FPOperand : Set where
  fpRegOp : FPReg → FPOperand

------------------------------------------------------------------------
-- Condition codes (for comparisons)
------------------------------------------------------------------------

-- | AArch64 condition codes for cset/csel/b.cc instructions
data Cond : Set where
  cond-eq : Cond    -- Equal (Z=1)
  cond-ne : Cond    -- Not equal (Z=0)
  cond-lt : Cond    -- Signed less than (N≠V)
  cond-le : Cond    -- Signed less or equal (Z=1 or N≠V)
  cond-gt : Cond    -- Signed greater than (Z=0 and N=V)
  cond-ge : Cond    -- Signed greater or equal (N=V)

------------------------------------------------------------------------
-- Integer arithmetic instructions
------------------------------------------------------------------------

data IntInstr : Set where
  mov   : GPReg → Operand → IntInstr
  movz  : GPReg → ℤ → ℕ → IntInstr
  movk  : GPReg → ℤ → ℕ → IntInstr
  add   : GPReg → GPReg → Operand → IntInstr
  sub   : GPReg → GPReg → Operand → IntInstr
  mul   : GPReg → GPReg → GPReg → IntInstr
  sdiv  : GPReg → GPReg → GPReg → IntInstr
  msub  : GPReg → GPReg → GPReg → GPReg → IntInstr
  neg   : GPReg → GPReg → IntInstr
  -- Stack operations (for register spilling)
  strPre  : GPReg → ℕ → IntInstr     -- str xn, [sp, #-imm]! (pre-decrement)
  ldrPost : GPReg → ℕ → IntInstr     -- ldr xn, [sp], #imm (post-increment)
  -- Comparison
  cmp     : GPReg → Operand → IntInstr  -- cmp rn, op (sets flags)
  cset    : GPReg → Cond → IntInstr     -- cset rd, cc (rd = cc ? 1 : 0)

------------------------------------------------------------------------
-- Floating-point arithmetic instructions
------------------------------------------------------------------------

data FPInstr : Set where
  fmov  : FPReg → FPOperand → FPInstr
  fadd  : FPReg → FPReg → FPReg → FPInstr
  fsub  : FPReg → FPReg → FPReg → FPInstr
  fmul  : FPReg → FPReg → FPReg → FPInstr
  fdiv  : FPReg → FPReg → FPReg → FPInstr
  fneg  : FPReg → FPReg → FPInstr
  faddS : FPReg → FPReg → FPReg → FPInstr
  fsubS : FPReg → FPReg → FPReg → FPInstr
  fmulS : FPReg → FPReg → FPReg → FPInstr
  fdivS : FPReg → FPReg → FPReg → FPInstr
  fnegS : FPReg → FPReg → FPInstr
  -- Type conversion (OCP-0002)
  fcvtSD : FPReg → FPReg → FPInstr     -- fcvt Dd, Sn (F32 → F64)

------------------------------------------------------------------------
-- Unified arithmetic instruction
------------------------------------------------------------------------

data ArithInstr : Set where
  intI : IntInstr → ArithInstr
  fpI  : FPInstr → ArithInstr

------------------------------------------------------------------------
-- Program
------------------------------------------------------------------------

ArithProgram : Set
ArithProgram = List ArithInstr
