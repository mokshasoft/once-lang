-- | x86-64 instruction syntax for arithmetic operations
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- This module defines the x86-64 instruction subset used for
-- arithmetic code generation, mirroring the Agda formal specification.
module Once.Arith.Backend.X86.Syntax
  ( -- * General-purpose registers
    GPReg (..)
  , gprName
  , gprName32
  , gprName16
  , gprName8
    -- * XMM registers
  , XMMReg (..)
  , xmmName
    -- * Memory operands
  , ArithMem (..)
    -- * Operands
  , IntOperand (..)
  , FloatOperand (..)
    -- * Instructions
  , IntInstr (..)
  , FloatInstr (..)
  , ArithInstr (..)
    -- * Programs
  , ArithProgram
  ) where

import Data.Int (Int64)

------------------------------------------------------------------------
-- General-purpose registers (for integers)
------------------------------------------------------------------------

-- | x86-64 general-purpose registers (64-bit)
data GPReg
  = RAX    -- ^ Accumulator / return value
  | RBX    -- ^ Callee-saved
  | RCX    -- ^ Counter (for shifts, mul/div)
  | RDX    -- ^ Data (high bits of mul, div)
  | RSI    -- ^ Source index
  | RDI    -- ^ Destination index / first argument
  | R8     -- ^ Temporary
  | R9     -- ^ Temporary
  | R10    -- ^ Temporary
  | R11    -- ^ Temporary
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | 64-bit register name
gprName :: GPReg -> String
gprName RAX = "rax"
gprName RBX = "rbx"
gprName RCX = "rcx"
gprName RDX = "rdx"
gprName RSI = "rsi"
gprName RDI = "rdi"
gprName R8  = "r8"
gprName R9  = "r9"
gprName R10 = "r10"
gprName R11 = "r11"

-- | 32-bit register name (lower 32 bits)
gprName32 :: GPReg -> String
gprName32 RAX = "eax"
gprName32 RBX = "ebx"
gprName32 RCX = "ecx"
gprName32 RDX = "edx"
gprName32 RSI = "esi"
gprName32 RDI = "edi"
gprName32 R8  = "r8d"
gprName32 R9  = "r9d"
gprName32 R10 = "r10d"
gprName32 R11 = "r11d"

-- | 16-bit register name (lower 16 bits)
gprName16 :: GPReg -> String
gprName16 RAX = "ax"
gprName16 RBX = "bx"
gprName16 RCX = "cx"
gprName16 RDX = "dx"
gprName16 RSI = "si"
gprName16 RDI = "di"
gprName16 R8  = "r8w"
gprName16 R9  = "r9w"
gprName16 R10 = "r10w"
gprName16 R11 = "r11w"

-- | 8-bit register name (lower 8 bits)
gprName8 :: GPReg -> String
gprName8 RAX = "al"
gprName8 RBX = "bl"
gprName8 RCX = "cl"
gprName8 RDX = "dl"
gprName8 RSI = "sil"
gprName8 RDI = "dil"
gprName8 R8  = "r8b"
gprName8 R9  = "r9b"
gprName8 R10 = "r10b"
gprName8 R11 = "r11b"

------------------------------------------------------------------------
-- SSE/AVX registers (for floats)
------------------------------------------------------------------------

-- | XMM registers for SSE/AVX floating-point operations
data XMMReg
  = XMM0 | XMM1 | XMM2  | XMM3  | XMM4  | XMM5  | XMM6  | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11 | XMM12 | XMM13 | XMM14 | XMM15
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | XMM register name
xmmName :: XMMReg -> String
xmmName XMM0  = "xmm0"
xmmName XMM1  = "xmm1"
xmmName XMM2  = "xmm2"
xmmName XMM3  = "xmm3"
xmmName XMM4  = "xmm4"
xmmName XMM5  = "xmm5"
xmmName XMM6  = "xmm6"
xmmName XMM7  = "xmm7"
xmmName XMM8  = "xmm8"
xmmName XMM9  = "xmm9"
xmmName XMM10 = "xmm10"
xmmName XMM11 = "xmm11"
xmmName XMM12 = "xmm12"
xmmName XMM13 = "xmm13"
xmmName XMM14 = "xmm14"
xmmName XMM15 = "xmm15"

------------------------------------------------------------------------
-- Memory operands
------------------------------------------------------------------------

-- | Memory addressing modes for arithmetic
data ArithMem
  = Base GPReg              -- ^ [reg]
  | BaseDisp GPReg Int      -- ^ [reg + disp]
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Operands
------------------------------------------------------------------------

-- | Operand for integer arithmetic
data IntOperand
  = RegI GPReg              -- ^ Register operand
  | MemI ArithMem           -- ^ Memory operand
  | ImmI Int64              -- ^ Immediate value
  deriving (Eq, Show)

-- | Operand for floating-point arithmetic
data FloatOperand
  = RegF XMMReg             -- ^ XMM register operand
  | MemF ArithMem           -- ^ Memory operand
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Integer arithmetic instructions
------------------------------------------------------------------------

-- | Integer arithmetic instructions
data IntInstr
  -- Data movement
  = MovI GPReg IntOperand         -- ^ mov dst, src

  -- Arithmetic
  | AddI GPReg IntOperand         -- ^ add dst, src (dst += src)
  | SubI GPReg IntOperand         -- ^ sub dst, src (dst -= src)
  | IMulI GPReg IntOperand        -- ^ imul dst, src (signed mul)
  | NegI GPReg                    -- ^ neg dst (dst = -dst)

  -- Division: idiv uses rdx:rax / src
  | Cqo                           -- ^ sign-extend rax to rdx:rax
  | IDivI IntOperand              -- ^ idiv src (rdx:rax / src)

  -- Stack operations (for register spilling)
  | PushI GPReg                   -- ^ push src (rsp -= 8; [rsp] = src)
  | PopI GPReg                    -- ^ pop dst (dst = [rsp]; rsp += 8)
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Floating-point arithmetic instructions (SSE)
------------------------------------------------------------------------

-- | Floating-point arithmetic instructions (SSE scalar)
data FloatInstr
  -- Data movement
  = Movss XMMReg FloatOperand     -- ^ movss dst, src (32-bit)
  | Movsd XMMReg FloatOperand     -- ^ movsd dst, src (64-bit)
  | MovqToXMM XMMReg GPReg        -- ^ movq xmm, r64 (load 64-bit int to xmm)

  -- Single-precision (32-bit float)
  | Addss XMMReg FloatOperand     -- ^ addss dst, src
  | Subss XMMReg FloatOperand     -- ^ subss dst, src
  | Mulss XMMReg FloatOperand     -- ^ mulss dst, src
  | Divss XMMReg FloatOperand     -- ^ divss dst, src

  -- Double-precision (64-bit float)
  | Addsd XMMReg FloatOperand     -- ^ addsd dst, src
  | Subsd XMMReg FloatOperand     -- ^ subsd dst, src
  | Mulsd XMMReg FloatOperand     -- ^ mulsd dst, src
  | Divsd XMMReg FloatOperand     -- ^ divsd dst, src

  -- Negation (xor with sign bit)
  | Xorps XMMReg XMMReg           -- ^ xorps dst, src (32-bit)
  | Xorpd XMMReg XMMReg           -- ^ xorpd dst, src (64-bit)

  -- Type conversion (OCP-0002)
  | Cvtss2sd XMMReg XMMReg        -- ^ cvtss2sd dst, src (F32 -> F64)
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Unified arithmetic instruction
------------------------------------------------------------------------

-- | A single arithmetic instruction (integer or float)
data ArithInstr
  = IntI IntInstr
  | FloatI FloatInstr
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Program
------------------------------------------------------------------------

-- | An arithmetic program is a list of instructions
type ArithProgram = [ArithInstr]
