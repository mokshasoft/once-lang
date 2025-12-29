------------------------------------------------------------------------
-- Once.Backend.AArch64.Syntax
--
-- AArch64 (ARM64) instruction subset used by Once.
-- This is a minimal subset sufficient for the 14 categorical generators.
--
-- Based on the ARM Architecture Reference Manual (ARMv8-A).
-- Aligns with seL4's verified AArch64 target.
------------------------------------------------------------------------

module Once.Backend.AArch64.Syntax where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)

------------------------------------------------------------------------
-- Registers
------------------------------------------------------------------------

-- | AArch64 general-purpose registers (64-bit)
--
-- We use a subset relevant to Once's calling convention (AAPCS64):
--   x0: first argument AND return value
--   x0-x7: argument registers
--   x19-x28: callee-saved registers
--   x29: frame pointer (fp)
--   x30: link register (lr)
--
-- Note: x31 is either SP (stack pointer) or ZR (zero register)
-- depending on context. We model these separately.
--
data Reg : Set where
  x0  : Reg    -- Argument/return value
  x1  : Reg    -- Argument
  x2  : Reg    -- Argument
  x3  : Reg    -- Argument
  x4  : Reg    -- Argument
  x5  : Reg    -- Argument
  x6  : Reg    -- Argument
  x7  : Reg    -- Argument
  x8  : Reg    -- Indirect result location (caller-saved)
  x9  : Reg    -- Temporary (caller-saved)
  x10 : Reg    -- Temporary (caller-saved)
  x11 : Reg    -- Temporary (caller-saved)
  x12 : Reg    -- Temporary (caller-saved)
  x13 : Reg    -- Temporary (caller-saved)
  x14 : Reg    -- Temporary (caller-saved)
  x15 : Reg    -- Temporary (caller-saved)
  x16 : Reg    -- IP0 - intra-procedure-call scratch
  x17 : Reg    -- IP1 - intra-procedure-call scratch
  x18 : Reg    -- Platform register (reserved)
  x19 : Reg    -- Callee-saved (environment pointer for closures)
  x20 : Reg    -- Callee-saved
  x21 : Reg    -- Callee-saved
  x22 : Reg    -- Callee-saved
  x23 : Reg    -- Callee-saved
  x24 : Reg    -- Callee-saved
  x25 : Reg    -- Callee-saved
  x26 : Reg    -- Callee-saved
  x27 : Reg    -- Callee-saved
  x28 : Reg    -- Callee-saved
  x29 : Reg    -- Frame pointer (fp, callee-saved)
  x30 : Reg    -- Link register (lr)

------------------------------------------------------------------------
-- Memory operands
------------------------------------------------------------------------

-- | Memory addressing modes
--
-- AArch64 supports various addressing modes. For Once, we primarily use:
--   [Xn]          - base register
--   [Xn, #imm]    - base plus immediate offset
--   [SP, #imm]    - stack-relative
--
data Mem : Set where
  -- [reg]: dereference register
  base : Reg → Mem
  -- [reg, #offset]: base plus immediate displacement (must be 8-byte aligned for 64-bit)
  base+imm : Reg → ℕ → Mem
  -- [SP, #offset]: stack-relative addressing
  sp+imm : ℕ → Mem

------------------------------------------------------------------------
-- Operands
------------------------------------------------------------------------

-- | Instruction operands
data Operand : Set where
  reg : Reg → Operand           -- Register operand
  mem : Mem → Operand           -- Memory operand
  imm : ℕ → Operand             -- Immediate value

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

-- | AArch64 instruction subset for Once
--
-- This is the minimal subset needed to implement the 14 categorical generators:
--
-- | Generator | Instructions Used |
-- |-----------|-------------------|
-- | id        | (none/nop)        |
-- | compose   | sequencing        |
-- | fst       | ldr x0, [x0]      |
-- | snd       | ldr x0, [x0, #8]  |
-- | pair      | stp, str, sub sp  |
-- | inl       | str xzr, str x0   |
-- | inr       | mov + str (tag=1) |
-- | case      | ldr + cmp + b.ne  |
-- | terminal  | mov x0, #0        |
-- | initial   | brk #0 (trap)     |
-- | curry     | stp + str + b     |
-- | apply     | ldr + blr         |
-- | fold      | (none/nop)        |
-- | unfold    | (none/nop)        |
-- | arr       | (none/nop)        |
--
data Instr : Set where
  -- Data movement
  mov    : Reg → Operand → Instr          -- mov xD, xS / mov xD, #imm
  ldr    : Reg → Mem → Instr              -- ldr xD, [xN, #imm]
  str    : Reg → Mem → Instr              -- str xS, [xN, #imm]

  -- Pair load/store (for efficient stack operations)
  ldp    : Reg → Reg → Mem → Instr        -- ldp x1, x2, [xN, #imm]
  stp    : Reg → Reg → Mem → Instr        -- stp x1, x2, [xN, #imm]

  -- Arithmetic
  add    : Reg → Reg → Operand → Instr    -- add xD, xN, xM/#imm
  sub    : Reg → Reg → Operand → Instr    -- sub xD, xN, xM/#imm

  -- Comparison (sets PSTATE.NZCV flags)
  cmp    : Reg → Operand → Instr          -- cmp xN, xM/#imm

  -- Branches (PC-relative offsets for position-independent code)
  -- Semantics: PC' = PC + offset (offset is forward distance in instructions)
  b      : ℕ → Instr                      -- b +offset (unconditional branch)
  b-eq   : ℕ → Instr                      -- b.eq +offset (branch if equal, Z=1)
  b-ne   : ℕ → Instr                      -- b.ne +offset (branch if not equal, Z=0)

  -- Subroutine calls (PC-relative)
  bl     : ℕ → Instr                      -- bl +offset (branch with link, sets x30)
  blr    : Reg → Instr                    -- blr xN (branch to register with link)
  ret    : Instr                          -- ret (return via x30)

  -- Stack operations (using SP)
  -- Note: SP must remain 16-byte aligned
  sub-sp : ℕ → Instr                      -- sub sp, sp, #imm
  add-sp : ℕ → Instr                      -- add sp, sp, #imm
  mov-from-sp : Reg → Instr               -- mov xD, sp (get SP value into register)

  -- Special
  nop    : Instr                          -- no operation
  brk    : ℕ → Instr                      -- brk #imm (breakpoint - trap for unreachable)
  adr    : Reg → ℕ → Instr                -- adr xD, #offset (PC-relative address: xD = PC + offset)

  -- Zero register store (for tag=0)
  str-zr : Mem → Instr                    -- str xzr, [mem] (store zero)

  -- Label (pseudo-instruction for assembly)
  label  : ℕ → Instr                      -- label n:

------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------

-- | A program is a list of instructions
Program : Set
Program = List Instr

-- | A function consists of a name and its body
record Function : Set where
  constructor mkfun
  field
    name : ℕ        -- Function identifier
    body : Program  -- Function body

------------------------------------------------------------------------
-- Once-specific conventions (AAPCS64)
------------------------------------------------------------------------

-- | Calling convention for Once (based on AAPCS64)
--
-- Arguments:
--   x0: first argument (input value)
--   x1-x7: additional arguments if needed
--
-- Return:
--   x0: return value
--
-- Callee-saved (preserved across calls):
--   x19-x28, x29 (fp), x30 (lr)
--
-- For closures:
--   x19: environment pointer (callee-saved)
--   The closure structure is: [env_ptr (8 bytes), code_ptr (8 bytes)]
--
-- For products (pairs):
--   Memory layout: [fst (8 bytes), snd (8 bytes)]
--   Access: fst at offset 0, snd at offset 8
--
-- For sums (tagged unions):
--   Memory layout: [tag (8 bytes), value (8 bytes)]
--   tag = 0 for inl, tag = 1 for inr
--   Access: tag at offset 0, value at offset 8
--
-- Stack alignment:
--   SP must be 16-byte aligned at all times

-- | Offsets for product fields
fstOffset : ℕ
fstOffset = 0

sndOffset : ℕ
sndOffset = 8

-- | Offsets for sum fields
tagOffset : ℕ
tagOffset = 0

valueOffset : ℕ
valueOffset = 8

-- | Tag values for sums
inlTag : ℕ
inlTag = 0

inrTag : ℕ
inrTag = 1

-- | Stack frame size (16-byte aligned)
pairFrameSize : ℕ
pairFrameSize = 16

sumFrameSize : ℕ
sumFrameSize = 16

closureFrameSize : ℕ
closureFrameSize = 16
