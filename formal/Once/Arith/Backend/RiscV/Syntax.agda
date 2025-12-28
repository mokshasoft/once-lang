------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV.Syntax
--
-- RISC-V instruction subset for arithmetic operations.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV.Syntax where

open import Once.Arith.Type using (NumType; RegClass)
open import Once.Arith.Type as T using ()

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Integer using (ℤ)

------------------------------------------------------------------------
-- General-purpose registers (x0-x31)
------------------------------------------------------------------------

data GPReg : Set where
  x0  : GPReg  -- zero (hardwired to 0)
  x1  : GPReg  -- ra (return address)
  x2  : GPReg  -- sp (stack pointer)
  x3  : GPReg  -- gp (global pointer)
  x4  : GPReg  -- tp (thread pointer)
  x5  : GPReg  -- t0 (temporary)
  x6  : GPReg  -- t1 (temporary)
  x7  : GPReg  -- t2 (temporary)
  x8  : GPReg  -- s0/fp (saved register / frame pointer)
  x9  : GPReg  -- s1 (saved register)
  x10 : GPReg  -- a0 (argument / return value)
  x11 : GPReg  -- a1 (argument / return value)
  x12 : GPReg  -- a2 (argument)
  x13 : GPReg  -- a3 (argument)
  x14 : GPReg  -- a4 (argument)
  x15 : GPReg  -- a5 (argument)
  x16 : GPReg  -- a6 (argument)
  x17 : GPReg  -- a7 (argument)
  x18 : GPReg  -- s2 (saved register)
  x19 : GPReg  -- s3 (saved register)
  x20 : GPReg  -- s4 (saved register)
  x21 : GPReg  -- s5 (saved register)
  x22 : GPReg  -- s6 (saved register)
  x23 : GPReg  -- s7 (saved register)
  x24 : GPReg  -- s8 (saved register)
  x25 : GPReg  -- s9 (saved register)
  x26 : GPReg  -- s10 (saved register)
  x27 : GPReg  -- s11 (saved register)
  x28 : GPReg  -- t3 (temporary)
  x29 : GPReg  -- t4 (temporary)
  x30 : GPReg  -- t5 (temporary)
  x31 : GPReg  -- t6 (temporary)

------------------------------------------------------------------------
-- Floating-point registers (f0-f31)
------------------------------------------------------------------------

data FPReg : Set where
  f0  : FPReg  -- ft0 (FP temporary)
  f1  : FPReg  -- ft1 (FP temporary)
  f2  : FPReg  -- ft2 (FP temporary)
  f3  : FPReg  -- ft3 (FP temporary)
  f4  : FPReg  -- ft4 (FP temporary)
  f5  : FPReg  -- ft5 (FP temporary)
  f6  : FPReg  -- ft6 (FP temporary)
  f7  : FPReg  -- ft7 (FP temporary)
  f8  : FPReg  -- fs0 (FP saved register)
  f9  : FPReg  -- fs1 (FP saved register)
  f10 : FPReg  -- fa0 (FP argument / return value)
  f11 : FPReg  -- fa1 (FP argument / return value)
  f12 : FPReg  -- fa2 (FP argument)
  f13 : FPReg  -- fa3 (FP argument)
  f14 : FPReg  -- fa4 (FP argument)
  f15 : FPReg  -- fa5 (FP argument)
  f16 : FPReg  -- fa6 (FP argument)
  f17 : FPReg  -- fa7 (FP argument)
  f18 : FPReg  -- fs2 (FP saved register)
  f19 : FPReg  -- fs3 (FP saved register)
  f20 : FPReg  -- fs4 (FP saved register)
  f21 : FPReg  -- fs5 (FP saved register)
  f22 : FPReg  -- fs6 (FP saved register)
  f23 : FPReg  -- fs7 (FP saved register)
  f24 : FPReg  -- fs8 (FP saved register)
  f25 : FPReg  -- fs9 (FP saved register)
  f26 : FPReg  -- fs10 (FP saved register)
  f27 : FPReg  -- fs11 (FP saved register)
  f28 : FPReg  -- ft8 (FP temporary)
  f29 : FPReg  -- ft9 (FP temporary)
  f30 : FPReg  -- ft10 (FP temporary)
  f31 : FPReg  -- ft11 (FP temporary)

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
-- Integer arithmetic instructions
------------------------------------------------------------------------

data IntInstr : Set where
  li   : GPReg → ℤ → IntInstr                    -- Load immediate (pseudo)
  mv   : GPReg → GPReg → IntInstr                -- Move register (pseudo)
  add  : GPReg → GPReg → GPReg → IntInstr        -- add rd, rs1, rs2
  addi : GPReg → GPReg → ℤ → IntInstr            -- addi rd, rs1, imm
  sub  : GPReg → GPReg → GPReg → IntInstr        -- sub rd, rs1, rs2
  mul  : GPReg → GPReg → GPReg → IntInstr        -- mul rd, rs1, rs2
  div  : GPReg → GPReg → GPReg → IntInstr        -- div rd, rs1, rs2
  rem  : GPReg → GPReg → GPReg → IntInstr        -- rem rd, rs1, rs2
  neg  : GPReg → GPReg → IntInstr                -- neg rd, rs (pseudo)
  -- Stack operations (for register spilling)
  sd   : GPReg → ℤ → IntInstr                    -- sd rs, offset(sp)
  ld   : GPReg → ℤ → IntInstr                    -- ld rd, offset(sp)

------------------------------------------------------------------------
-- Floating-point arithmetic instructions
------------------------------------------------------------------------

data FPInstr : Set where
  fmvD  : FPReg → FPReg → FPInstr                -- fmv.d rd, rs
  faddD : FPReg → FPReg → FPReg → FPInstr        -- fadd.d rd, rs1, rs2
  fsubD : FPReg → FPReg → FPReg → FPInstr        -- fsub.d rd, rs1, rs2
  fmulD : FPReg → FPReg → FPReg → FPInstr        -- fmul.d rd, rs1, rs2
  fdivD : FPReg → FPReg → FPReg → FPInstr        -- fdiv.d rd, rs1, rs2
  fnegD : FPReg → FPReg → FPInstr                -- fneg.d rd, rs
  faddS : FPReg → FPReg → FPReg → FPInstr        -- fadd.s rd, rs1, rs2
  fsubS : FPReg → FPReg → FPReg → FPInstr        -- fsub.s rd, rs1, rs2
  fmulS : FPReg → FPReg → FPReg → FPInstr        -- fmul.s rd, rs1, rs2
  fdivS : FPReg → FPReg → FPReg → FPInstr        -- fdiv.s rd, rs1, rs2
  fnegS : FPReg → FPReg → FPInstr                -- fneg.s rd, rs

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
