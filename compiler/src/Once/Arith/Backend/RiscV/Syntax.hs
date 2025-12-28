{-# LANGUAGE DeriveGeneric #-}
-- | RISC-V instruction syntax for arithmetic operations.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
module Once.Arith.Backend.RiscV.Syntax
  ( -- * Registers
    GPReg(..)
  , FPReg(..)
    -- * Operands
  , Operand(..)
  , FPOperand(..)
    -- * Instructions
  , IntInstr(..)
  , FPInstr(..)
  , ArithInstr(..)
  , ArithProgram
    -- * Register names
  , gprName
  , fpRegName
  ) where

import Data.Int (Int64)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)

------------------------------------------------------------------------
-- General-purpose registers (x0-x31)
------------------------------------------------------------------------

-- | RISC-V general-purpose registers
-- x0 = zero (hardwired to 0)
-- x1 = ra (return address)
-- x2 = sp (stack pointer)
-- x3 = gp (global pointer)
-- x4 = tp (thread pointer)
-- x5-x7 = t0-t2 (temporaries)
-- x8 = s0/fp (saved register / frame pointer)
-- x9 = s1 (saved register)
-- x10-x11 = a0-a1 (function arguments / return values)
-- x12-x17 = a2-a7 (function arguments)
-- x18-x27 = s2-s11 (saved registers)
-- x28-x31 = t3-t6 (temporaries)
data GPReg
  = X0  | X1  | X2  | X3  | X4  | X5  | X6  | X7
  | X8  | X9  | X10 | X11 | X12 | X13 | X14 | X15
  | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23
  | X24 | X25 | X26 | X27 | X28 | X29 | X30 | X31
  deriving (Eq, Show, Ord, Enum, Bounded, Generic)

------------------------------------------------------------------------
-- Floating-point registers (f0-f31)
------------------------------------------------------------------------

-- | RISC-V floating-point registers
-- f0-f7 = ft0-ft7 (FP temporaries)
-- f8-f9 = fs0-fs1 (FP saved registers)
-- f10-f11 = fa0-fa1 (FP arguments / return values)
-- f12-f17 = fa2-fa7 (FP arguments)
-- f18-f27 = fs2-fs11 (FP saved registers)
-- f28-f31 = ft8-ft11 (FP temporaries)
data FPReg
  = F0  | F1  | F2  | F3  | F4  | F5  | F6  | F7
  | F8  | F9  | F10 | F11 | F12 | F13 | F14 | F15
  | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23
  | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31
  deriving (Eq, Show, Ord, Enum, Bounded, Generic)

------------------------------------------------------------------------
-- Operands
------------------------------------------------------------------------

data Operand
  = RegOp GPReg
  | ImmOp Int64
  deriving (Eq, Show)

data FPOperand
  = FPRegOp FPReg
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Integer arithmetic instructions
------------------------------------------------------------------------

data IntInstr
  = Li GPReg Int64                    -- ^ Load immediate (pseudo-instruction)
  | Mv GPReg GPReg                    -- ^ Move register (pseudo: addi rd, rs, 0)
  | Add GPReg GPReg GPReg             -- ^ add rd, rs1, rs2
  | Addi GPReg GPReg Int64            -- ^ addi rd, rs1, imm
  | Sub GPReg GPReg GPReg             -- ^ sub rd, rs1, rs2
  | Mul GPReg GPReg GPReg             -- ^ mul rd, rs1, rs2 (M extension)
  | Div GPReg GPReg GPReg             -- ^ div rd, rs1, rs2 (M extension)
  | Rem GPReg GPReg GPReg             -- ^ rem rd, rs1, rs2 (M extension)
  | Neg GPReg GPReg                   -- ^ neg rd, rs (pseudo: sub rd, x0, rs)
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Floating-point arithmetic instructions
------------------------------------------------------------------------

data FPInstr
  = FmvD FPReg FPReg                  -- ^ fmv.d rd, rs (pseudo: fsgnj.d rd, rs, rs)
  | FmvDX FPReg GPReg                 -- ^ fmv.d.x rd, rs (move int64 to fp reg)
  | FaddD FPReg FPReg FPReg           -- ^ fadd.d rd, rs1, rs2
  | FsubD FPReg FPReg FPReg           -- ^ fsub.d rd, rs1, rs2
  | FmulD FPReg FPReg FPReg           -- ^ fmul.d rd, rs1, rs2
  | FdivD FPReg FPReg FPReg           -- ^ fdiv.d rd, rs1, rs2
  | FnegD FPReg FPReg                 -- ^ fneg.d rd, rs (pseudo: fsgnjn.d rd, rs, rs)
  | FaddS FPReg FPReg FPReg           -- ^ fadd.s rd, rs1, rs2
  | FsubS FPReg FPReg FPReg           -- ^ fsub.s rd, rs1, rs2
  | FmulS FPReg FPReg FPReg           -- ^ fmul.s rd, rs1, rs2
  | FdivS FPReg FPReg FPReg           -- ^ fdiv.s rd, rs1, rs2
  | FnegS FPReg FPReg                 -- ^ fneg.s rd, rs
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Unified arithmetic instruction
------------------------------------------------------------------------

data ArithInstr
  = IntI IntInstr
  | FPI FPInstr
  deriving (Eq, Show)

type ArithProgram = [ArithInstr]

------------------------------------------------------------------------
-- Register names for assembly emission
------------------------------------------------------------------------

-- | Get the ABI name for a GPR
gprName :: GPReg -> Text
gprName X0  = "zero"
gprName X1  = "ra"
gprName X2  = "sp"
gprName X3  = "gp"
gprName X4  = "tp"
gprName X5  = "t0"
gprName X6  = "t1"
gprName X7  = "t2"
gprName X8  = "s0"
gprName X9  = "s1"
gprName X10 = "a0"
gprName X11 = "a1"
gprName X12 = "a2"
gprName X13 = "a3"
gprName X14 = "a4"
gprName X15 = "a5"
gprName X16 = "a6"
gprName X17 = "a7"
gprName X18 = "s2"
gprName X19 = "s3"
gprName X20 = "s4"
gprName X21 = "s5"
gprName X22 = "s6"
gprName X23 = "s7"
gprName X24 = "s8"
gprName X25 = "s9"
gprName X26 = "s10"
gprName X27 = "s11"
gprName X28 = "t3"
gprName X29 = "t4"
gprName X30 = "t5"
gprName X31 = "t6"

-- | Get the ABI name for an FP register
fpRegName :: FPReg -> Text
fpRegName F0  = "ft0"
fpRegName F1  = "ft1"
fpRegName F2  = "ft2"
fpRegName F3  = "ft3"
fpRegName F4  = "ft4"
fpRegName F5  = "ft5"
fpRegName F6  = "ft6"
fpRegName F7  = "ft7"
fpRegName F8  = "fs0"
fpRegName F9  = "fs1"
fpRegName F10 = "fa0"
fpRegName F11 = "fa1"
fpRegName F12 = "fa2"
fpRegName F13 = "fa3"
fpRegName F14 = "fa4"
fpRegName F15 = "fa5"
fpRegName F16 = "fa6"
fpRegName F17 = "fa7"
fpRegName F18 = "fs2"
fpRegName F19 = "fs3"
fpRegName F20 = "fs4"
fpRegName F21 = "fs5"
fpRegName F22 = "fs6"
fpRegName F23 = "fs7"
fpRegName F24 = "fs8"
fpRegName F25 = "fs9"
fpRegName F26 = "fs10"
fpRegName F27 = "fs11"
fpRegName F28 = "ft8"
fpRegName F29 = "ft9"
fpRegName F30 = "ft10"
fpRegName F31 = "ft11"
