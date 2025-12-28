------------------------------------------------------------------------
-- Once.Arith.Backend.X86.Syntax
--
-- x86-64 instruction subset for arithmetic operations.
-- Extends the main X86.Syntax with arithmetic-specific instructions.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Backend.X86.Syntax where

open import Once.Arith.Type using (NumType)
open import Once.Arith.Type as T using (RegClass)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Integer using (ℤ)

------------------------------------------------------------------------
-- General-purpose registers (for integers)
------------------------------------------------------------------------

-- | x86-64 general-purpose registers (64-bit)
-- These are used for integer arithmetic.
--
data GPReg : Set where
  rax : GPReg    -- Accumulator / return value
  rbx : GPReg    -- Callee-saved
  rcx : GPReg    -- Counter (for shifts, mul/div)
  rdx : GPReg    -- Data (high bits of mul, div)
  rsi : GPReg    -- Source index
  rdi : GPReg    -- Destination index / first argument
  r8  : GPReg    -- Temporary
  r9  : GPReg    -- Temporary
  r10 : GPReg    -- Temporary
  r11 : GPReg    -- Temporary

-- | 32-bit register names (lower 32 bits of 64-bit)
data GPR32 : Set where
  eax ebx ecx edx esi edi r8d r9d r10d r11d : GPR32

-- | 16-bit register names (lower 16 bits)
data GPR16 : Set where
  ax bx cx dx si di : GPR16

-- | 8-bit register names (lower 8 bits)
data GPR8 : Set where
  al bl cl dl sil dil r8b r9b r10b r11b : GPR8

------------------------------------------------------------------------
-- SSE/AVX registers (for floats)
------------------------------------------------------------------------

-- | XMM registers for SSE/AVX floating-point operations
data XMMReg : Set where
  xmm0  : XMMReg
  xmm1  : XMMReg
  xmm2  : XMMReg
  xmm3  : XMMReg
  xmm4  : XMMReg
  xmm5  : XMMReg
  xmm6  : XMMReg
  xmm7  : XMMReg
  xmm8  : XMMReg
  xmm9  : XMMReg
  xmm10 : XMMReg
  xmm11 : XMMReg
  xmm12 : XMMReg
  xmm13 : XMMReg
  xmm14 : XMMReg
  xmm15 : XMMReg

------------------------------------------------------------------------
-- Unified register type
------------------------------------------------------------------------

-- | A register is either GPReg or XMMReg, depending on the numeric type
data Reg : RegClass → Set where
  gpr : GPReg  → Reg T.GPR
  xmm : XMMReg → Reg T.XMM

------------------------------------------------------------------------
-- Operands
------------------------------------------------------------------------

-- | Memory addressing modes for arithmetic
data ArithMem : Set where
  base      : GPReg → ArithMem             -- [reg]
  base+disp : GPReg → ℕ → ArithMem         -- [reg + disp]

-- | Operand for integer arithmetic
data IntOperand : Set where
  regI : GPReg → IntOperand
  memI : ArithMem → IntOperand
  immI : ℤ → IntOperand

-- | Operand for floating-point arithmetic
data FloatOperand : Set where
  regF : XMMReg → FloatOperand
  memF : ArithMem → FloatOperand

------------------------------------------------------------------------
-- Condition codes (for comparisons)
------------------------------------------------------------------------

-- | x86-64 condition codes for setcc/jcc instructions
data CondCode : Set where
  cc-e  : CondCode    -- Equal (ZF=1)
  cc-ne : CondCode    -- Not equal (ZF=0)
  cc-l  : CondCode    -- Less than (signed: SF≠OF)
  cc-le : CondCode    -- Less or equal (signed: ZF=1 or SF≠OF)
  cc-g  : CondCode    -- Greater than (signed: ZF=0 and SF=OF)
  cc-ge : CondCode    -- Greater or equal (signed: SF=OF)

------------------------------------------------------------------------
-- Integer arithmetic instructions
------------------------------------------------------------------------

-- | Integer arithmetic instructions
--
-- These operate on GPR registers with appropriate widths.
-- The NumType parameter determines the instruction variant.
--
data IntInstr : Set where
  -- Data movement
  movI   : GPReg → IntOperand → IntInstr         -- mov dst, src

  -- Arithmetic
  addI   : GPReg → IntOperand → IntInstr         -- add dst, src (dst += src)
  subI   : GPReg → IntOperand → IntInstr         -- sub dst, src (dst -= src)
  imulI  : GPReg → IntOperand → IntInstr         -- imul dst, src (signed mul)
  negI   : GPReg → IntInstr                      -- neg dst (dst = -dst)

  -- Division: idiv uses rdx:rax / src, quotient in rax, remainder in rdx
  -- Caller must set up rdx:rax and handle quotient/remainder
  cqo    : IntInstr                              -- sign-extend rax to rdx:rax
  idivI  : IntOperand → IntInstr                 -- idiv src (rdx:rax / src)

  -- Stack operations (for register spilling)
  pushI  : GPReg → IntInstr                      -- push src (rsp -= 8; [rsp] = src)
  popI   : GPReg → IntInstr                      -- pop dst (dst = [rsp]; rsp += 8)

  -- Comparison
  cmpI   : GPReg → IntOperand → IntInstr         -- cmp dst, src (sets flags)
  setccI : CondCode → GPReg → IntInstr           -- setcc dst (set low byte to 0/1)
  movzxI : GPReg → GPReg → IntInstr              -- movzx dst, src (zero-extend byte)

------------------------------------------------------------------------
-- Floating-point arithmetic instructions (SSE)
------------------------------------------------------------------------

-- | Floating-point arithmetic instructions (SSE scalar)
--
-- addss/addsd: add scalar single/double
-- subss/subsd: subtract scalar single/double
-- mulss/mulsd: multiply scalar single/double
-- divss/divsd: divide scalar single/double
--
data FloatInstr : Set where
  -- Data movement
  movss  : XMMReg → FloatOperand → FloatInstr     -- movss dst, src (32-bit)
  movsd  : XMMReg → FloatOperand → FloatInstr     -- movsd dst, src (64-bit)

  -- Single-precision (32-bit float)
  addss  : XMMReg → FloatOperand → FloatInstr     -- addss dst, src
  subss  : XMMReg → FloatOperand → FloatInstr     -- subss dst, src
  mulss  : XMMReg → FloatOperand → FloatInstr     -- mulss dst, src
  divss  : XMMReg → FloatOperand → FloatInstr     -- divss dst, src

  -- Double-precision (64-bit float)
  addsd  : XMMReg → FloatOperand → FloatInstr     -- addsd dst, src
  subsd  : XMMReg → FloatOperand → FloatInstr     -- subsd dst, src
  mulsd  : XMMReg → FloatOperand → FloatInstr     -- mulsd dst, src
  divsd  : XMMReg → FloatOperand → FloatInstr     -- divsd dst, src

  -- Negation (xor with sign bit)
  xorps  : XMMReg → XMMReg → FloatInstr           -- xorps dst, src (32-bit)
  xorpd  : XMMReg → XMMReg → FloatInstr           -- xorpd dst, src (64-bit)

------------------------------------------------------------------------
-- Unified arithmetic instruction
------------------------------------------------------------------------

-- | A single arithmetic instruction (integer or float)
data ArithInstr : Set where
  intI   : IntInstr → ArithInstr
  floatI : FloatInstr → ArithInstr

------------------------------------------------------------------------
-- Program
------------------------------------------------------------------------

-- | An arithmetic program is a list of instructions
ArithProgram : Set
ArithProgram = List ArithInstr
