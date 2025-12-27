-- | AArch64 instruction syntax for arithmetic operations
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- This module defines the AArch64 instruction subset used for
-- arithmetic code generation, mirroring the Agda formal specification.
module Once.Arith.Backend.AArch64.Syntax
  ( -- * General-purpose registers
    GPReg (..)
  , gprName
  , gprName32
    -- * Floating-point/SIMD registers
  , FPReg (..)
  , fpRegName
  , fpRegNameS
    -- * Operands
  , Operand (..)
  , FPOperand (..)
    -- * Instructions
  , IntInstr (..)
  , FPInstr (..)
  , ArithInstr (..)
    -- * Programs
  , ArithProgram
  ) where

import Data.Int (Int64)

------------------------------------------------------------------------
-- General-purpose registers (64-bit)
------------------------------------------------------------------------

-- | AArch64 general-purpose registers (64-bit X registers)
data GPReg
  = X0  | X1  | X2  | X3  | X4  | X5  | X6  | X7
  | X8  | X9  | X10 | X11 | X12 | X13 | X14 | X15
  | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23
  | X24 | X25 | X26 | X27 | X28 | X29 | X30
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | 64-bit register name
gprName :: GPReg -> String
gprName X0  = "x0"
gprName X1  = "x1"
gprName X2  = "x2"
gprName X3  = "x3"
gprName X4  = "x4"
gprName X5  = "x5"
gprName X6  = "x6"
gprName X7  = "x7"
gprName X8  = "x8"
gprName X9  = "x9"
gprName X10 = "x10"
gprName X11 = "x11"
gprName X12 = "x12"
gprName X13 = "x13"
gprName X14 = "x14"
gprName X15 = "x15"
gprName X16 = "x16"
gprName X17 = "x17"
gprName X18 = "x18"
gprName X19 = "x19"
gprName X20 = "x20"
gprName X21 = "x21"
gprName X22 = "x22"
gprName X23 = "x23"
gprName X24 = "x24"
gprName X25 = "x25"
gprName X26 = "x26"
gprName X27 = "x27"
gprName X28 = "x28"
gprName X29 = "x29"
gprName X30 = "x30"

-- | 32-bit register name (W registers)
gprName32 :: GPReg -> String
gprName32 X0  = "w0"
gprName32 X1  = "w1"
gprName32 X2  = "w2"
gprName32 X3  = "w3"
gprName32 X4  = "w4"
gprName32 X5  = "w5"
gprName32 X6  = "w6"
gprName32 X7  = "w7"
gprName32 X8  = "w8"
gprName32 X9  = "w9"
gprName32 X10 = "w10"
gprName32 X11 = "w11"
gprName32 X12 = "w12"
gprName32 X13 = "w13"
gprName32 X14 = "w14"
gprName32 X15 = "w15"
gprName32 X16 = "w16"
gprName32 X17 = "w17"
gprName32 X18 = "w18"
gprName32 X19 = "w19"
gprName32 X20 = "w20"
gprName32 X21 = "w21"
gprName32 X22 = "w22"
gprName32 X23 = "w23"
gprName32 X24 = "w24"
gprName32 X25 = "w25"
gprName32 X26 = "w26"
gprName32 X27 = "w27"
gprName32 X28 = "w28"
gprName32 X29 = "w29"
gprName32 X30 = "w30"

------------------------------------------------------------------------
-- Floating-point/SIMD registers
------------------------------------------------------------------------

-- | AArch64 floating-point registers (D = 64-bit double, S = 32-bit single)
data FPReg
  = D0  | D1  | D2  | D3  | D4  | D5  | D6  | D7
  | D8  | D9  | D10 | D11 | D12 | D13 | D14 | D15
  | D16 | D17 | D18 | D19 | D20 | D21 | D22 | D23
  | D24 | D25 | D26 | D27 | D28 | D29 | D30 | D31
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | 64-bit (double) register name
fpRegName :: FPReg -> String
fpRegName D0  = "d0"
fpRegName D1  = "d1"
fpRegName D2  = "d2"
fpRegName D3  = "d3"
fpRegName D4  = "d4"
fpRegName D5  = "d5"
fpRegName D6  = "d6"
fpRegName D7  = "d7"
fpRegName D8  = "d8"
fpRegName D9  = "d9"
fpRegName D10 = "d10"
fpRegName D11 = "d11"
fpRegName D12 = "d12"
fpRegName D13 = "d13"
fpRegName D14 = "d14"
fpRegName D15 = "d15"
fpRegName D16 = "d16"
fpRegName D17 = "d17"
fpRegName D18 = "d18"
fpRegName D19 = "d19"
fpRegName D20 = "d20"
fpRegName D21 = "d21"
fpRegName D22 = "d22"
fpRegName D23 = "d23"
fpRegName D24 = "d24"
fpRegName D25 = "d25"
fpRegName D26 = "d26"
fpRegName D27 = "d27"
fpRegName D28 = "d28"
fpRegName D29 = "d29"
fpRegName D30 = "d30"
fpRegName D31 = "d31"

-- | 32-bit (single) register name
fpRegNameS :: FPReg -> String
fpRegNameS D0  = "s0"
fpRegNameS D1  = "s1"
fpRegNameS D2  = "s2"
fpRegNameS D3  = "s3"
fpRegNameS D4  = "s4"
fpRegNameS D5  = "s5"
fpRegNameS D6  = "s6"
fpRegNameS D7  = "s7"
fpRegNameS D8  = "s8"
fpRegNameS D9  = "s9"
fpRegNameS D10 = "s10"
fpRegNameS D11 = "s11"
fpRegNameS D12 = "s12"
fpRegNameS D13 = "s13"
fpRegNameS D14 = "s14"
fpRegNameS D15 = "s15"
fpRegNameS D16 = "s16"
fpRegNameS D17 = "s17"
fpRegNameS D18 = "s18"
fpRegNameS D19 = "s19"
fpRegNameS D20 = "s20"
fpRegNameS D21 = "s21"
fpRegNameS D22 = "s22"
fpRegNameS D23 = "s23"
fpRegNameS D24 = "s24"
fpRegNameS D25 = "s25"
fpRegNameS D26 = "s26"
fpRegNameS D27 = "s27"
fpRegNameS D28 = "s28"
fpRegNameS D29 = "s29"
fpRegNameS D30 = "s30"
fpRegNameS D31 = "s31"

------------------------------------------------------------------------
-- Operands
------------------------------------------------------------------------

-- | Operand for integer instructions
data Operand
  = RegOp GPReg           -- ^ Register operand
  | ImmOp Int64           -- ^ Immediate value (12-bit for add/sub)
  deriving (Eq, Show)

-- | Operand for floating-point instructions
data FPOperand
  = FPRegOp FPReg         -- ^ FP register operand
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Integer arithmetic instructions
------------------------------------------------------------------------

-- | AArch64 integer arithmetic instructions
data IntInstr
  -- Data movement
  = Mov GPReg Operand              -- ^ mov dst, src
  | Movz GPReg Int64 Int           -- ^ movz dst, #imm, lsl #shift (16-bit chunks)
  | Movk GPReg Int64 Int           -- ^ movk dst, #imm, lsl #shift (keep other bits)

  -- Arithmetic
  | Add GPReg GPReg Operand        -- ^ add dst, src1, src2
  | Sub GPReg GPReg Operand        -- ^ sub dst, src1, src2
  | Mul GPReg GPReg GPReg          -- ^ mul dst, src1, src2
  | Sdiv GPReg GPReg GPReg         -- ^ sdiv dst, src1, src2 (signed divide)
  | Msub GPReg GPReg GPReg GPReg   -- ^ msub dst, mul1, mul2, acc (dst = acc - mul1*mul2)
  | Neg GPReg GPReg                -- ^ neg dst, src
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Floating-point arithmetic instructions
------------------------------------------------------------------------

-- | AArch64 floating-point arithmetic instructions
data FPInstr
  -- Data movement
  = Fmov FPReg FPOperand           -- ^ fmov dst, src

  -- Double-precision (64-bit)
  | Fadd FPReg FPReg FPReg         -- ^ fadd dst, src1, src2
  | Fsub FPReg FPReg FPReg         -- ^ fsub dst, src1, src2
  | Fmul FPReg FPReg FPReg         -- ^ fmul dst, src1, src2
  | Fdiv FPReg FPReg FPReg         -- ^ fdiv dst, src1, src2
  | Fneg FPReg FPReg               -- ^ fneg dst, src

  -- Single-precision (32-bit) - same instructions, different register view
  | FaddS FPReg FPReg FPReg        -- ^ fadd (single)
  | FsubS FPReg FPReg FPReg        -- ^ fsub (single)
  | FmulS FPReg FPReg FPReg        -- ^ fmul (single)
  | FdivS FPReg FPReg FPReg        -- ^ fdiv (single)
  | FnegS FPReg FPReg              -- ^ fneg (single)
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Unified arithmetic instruction
------------------------------------------------------------------------

-- | A single arithmetic instruction (integer or float)
data ArithInstr
  = IntI IntInstr
  | FPI FPInstr
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Program
------------------------------------------------------------------------

-- | An arithmetic program is a list of instructions
type ArithProgram = [ArithInstr]
