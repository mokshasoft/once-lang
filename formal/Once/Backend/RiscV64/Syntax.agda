------------------------------------------------------------------------
-- Once.Backend.RiscV64.Syntax
--
-- RISC-V 64-bit (RV64I) instruction subset used by Once.
-- This is a minimal subset sufficient for the 13 categorical generators.
--
-- Based on the RISC-V Unprivileged ISA Specification (ratified).
-- Reference: https://riscv.org/specifications/
------------------------------------------------------------------------

module Once.Backend.RiscV64.Syntax where

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List)

------------------------------------------------------------------------
-- Registers
------------------------------------------------------------------------

-- | RISC-V 64-bit general-purpose registers
--
-- RISC-V has 32 registers (x0-x31) with conventional ABI names.
-- We define them with their ABI names for readability.
--
-- Calling convention (RISC-V LP64):
--   a0-a7: arguments and return values
--   t0-t6: temporaries (caller-saved)
--   s0-s11: saved registers (callee-saved)
--   ra: return address
--   sp: stack pointer
--
-- For Once:
--   a0: first argument AND return value (simpler than x86!)
--   sp: stack pointer
--   s0-s3: callee-saved temporaries for complex operations
--   t0-t2: scratch registers
--
data Reg : Set where
  -- x0: Hardwired zero (reads always return 0, writes are ignored)
  zero : Reg

  -- x1: Return address (caller-saved)
  ra   : Reg

  -- x2: Stack pointer (callee-saved)
  sp   : Reg

  -- x3: Global pointer (reserved, not used by Once)
  gp   : Reg

  -- x4: Thread pointer (reserved, not used by Once)
  tp   : Reg

  -- x5-x7: Temporaries (caller-saved)
  t0   : Reg
  t1   : Reg
  t2   : Reg

  -- x8: Frame pointer / saved register (callee-saved)
  s0   : Reg  -- Also known as fp (frame pointer)

  -- x9: Saved register (callee-saved)
  s1   : Reg

  -- x10-x17: Function arguments / return values (caller-saved)
  -- a0 and a1 are also used for return values
  a0   : Reg  -- First argument / first return value
  a1   : Reg  -- Second argument / second return value
  a2   : Reg  -- Third argument
  a3   : Reg  -- Fourth argument
  a4   : Reg  -- Fifth argument
  a5   : Reg  -- Sixth argument
  a6   : Reg  -- Seventh argument
  a7   : Reg  -- Eighth argument

  -- x18-x27: Saved registers (callee-saved)
  s2   : Reg
  s3   : Reg
  s4   : Reg
  s5   : Reg
  s6   : Reg
  s7   : Reg
  s8   : Reg
  s9   : Reg
  s10  : Reg
  s11  : Reg

  -- x28-x31: Temporaries (caller-saved)
  t3   : Reg
  t4   : Reg
  t5   : Reg
  t6   : Reg

------------------------------------------------------------------------
-- Memory operands
------------------------------------------------------------------------

-- | Memory addressing mode
--
-- RISC-V uses a simple base+offset addressing model.
-- Unlike x86, there are no complex addressing modes (no scale, no index).
-- Memory operands are only valid for load/store instructions.
--
-- Format: offset(base) where offset is a 12-bit signed immediate
--
record Mem : Set where
  constructor _[_]
  field
    base   : Reg   -- Base register
    offset : ℤ     -- Signed 12-bit offset (-2048 to 2047)

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

-- | RISC-V 64-bit instruction subset for Once
--
-- RISC-V instructions are organized by format:
--   R-type: register-register operations
--   I-type: register-immediate and loads
--   S-type: stores
--   B-type: conditional branches
--   U-type: upper immediate
--   J-type: unconditional jumps
--
-- This is the minimal subset needed to implement the 13 categorical generators:
--
-- | Generator | Instructions Used |
-- |-----------|-------------------|
-- | id        | (nop or mv)       |
-- | compose   | sequencing + mv   |
-- | fst       | ld rd, 0(rs)      |
-- | snd       | ld rd, 8(rs)      |
-- | pair      | sd rs, 0(rd); sd rs, 8(rd) + stack alloc |
-- | inl       | sd zero, 0(sp); sd rs, 8(sp) (tag=0) |
-- | inr       | li t0, 1; sd t0, 0(sp); sd rs, 8(sp) (tag=1) |
-- | case      | ld t0, 0(rs); bne t0, zero, label |
-- | terminal  | li a0, 0          |
-- | initial   | ebreak (trap)     |
-- | fold      | mv (identity)     |
-- | unfold    | mv (identity)     |
-- | arr       | mv (identity)     |
-- | curry     | closure creation  |
-- | apply     | jalr (indirect)   |
--
data Instr : Set where
  ------------------------------------------------------------------------
  -- R-type: Register-Register Operations
  -- Format: op rd, rs1, rs2
  ------------------------------------------------------------------------

  -- Arithmetic
  add    : Reg → Reg → Reg → Instr    -- rd = rs1 + rs2
  sub    : Reg → Reg → Reg → Instr    -- rd = rs1 - rs2

  -- Logical
  and    : Reg → Reg → Reg → Instr    -- rd = rs1 & rs2
  or     : Reg → Reg → Reg → Instr    -- rd = rs1 | rs2
  xor    : Reg → Reg → Reg → Instr    -- rd = rs1 ^ rs2

  -- Shifts
  sll    : Reg → Reg → Reg → Instr    -- rd = rs1 << rs2 (logical left)
  srl    : Reg → Reg → Reg → Instr    -- rd = rs1 >> rs2 (logical right)
  sra    : Reg → Reg → Reg → Instr    -- rd = rs1 >> rs2 (arithmetic right)

  -- Comparisons (set if less than)
  slt    : Reg → Reg → Reg → Instr    -- rd = (rs1 < rs2) ? 1 : 0 (signed)
  sltu   : Reg → Reg → Reg → Instr    -- rd = (rs1 < rs2) ? 1 : 0 (unsigned)

  ------------------------------------------------------------------------
  -- I-type: Immediate Operations
  -- Format: op rd, rs1, imm12
  ------------------------------------------------------------------------

  -- Arithmetic immediate
  addi   : Reg → Reg → ℤ → Instr      -- rd = rs1 + imm

  -- Logical immediate
  andi   : Reg → Reg → ℤ → Instr      -- rd = rs1 & imm
  ori    : Reg → Reg → ℤ → Instr      -- rd = rs1 | imm
  xori   : Reg → Reg → ℤ → Instr      -- rd = rs1 ^ imm

  -- Comparison immediate
  slti   : Reg → Reg → ℤ → Instr      -- rd = (rs1 < imm) ? 1 : 0 (signed)
  sltiu  : Reg → Reg → ℤ → Instr      -- rd = (rs1 < imm) ? 1 : 0 (unsigned)

  -- Shift immediate (uses lower 6 bits of immediate for RV64)
  slli   : Reg → Reg → ℕ → Instr      -- rd = rs1 << shamt
  srli   : Reg → Reg → ℕ → Instr      -- rd = rs1 >> shamt (logical)
  srai   : Reg → Reg → ℕ → Instr      -- rd = rs1 >> shamt (arithmetic)

  ------------------------------------------------------------------------
  -- Load Instructions (I-type)
  -- Format: op rd, offset(rs1)
  -- rd = memory[rs1 + offset]
  ------------------------------------------------------------------------

  -- 64-bit load (doubleword)
  ld     : Reg → ℤ → Reg → Instr      -- rd = M[rs1 + offset] (64-bit)

  -- 32-bit loads
  lw     : Reg → ℤ → Reg → Instr      -- rd = signext(M[rs1 + offset]) (32-bit)
  lwu    : Reg → ℤ → Reg → Instr      -- rd = zeroext(M[rs1 + offset]) (32-bit unsigned)

  -- 16-bit loads
  lh     : Reg → ℤ → Reg → Instr      -- rd = signext(M[rs1 + offset]) (16-bit)
  lhu    : Reg → ℤ → Reg → Instr      -- rd = zeroext(M[rs1 + offset]) (16-bit unsigned)

  -- 8-bit loads
  lb     : Reg → ℤ → Reg → Instr      -- rd = signext(M[rs1 + offset]) (8-bit)
  lbu    : Reg → ℤ → Reg → Instr      -- rd = zeroext(M[rs1 + offset]) (8-bit unsigned)

  ------------------------------------------------------------------------
  -- S-type: Store Instructions
  -- Format: op rs2, offset(rs1)
  -- memory[rs1 + offset] = rs2
  ------------------------------------------------------------------------

  sd     : Reg → ℤ → Reg → Instr      -- M[rs1 + offset] = rs2 (64-bit)
  sw     : Reg → ℤ → Reg → Instr      -- M[rs1 + offset] = rs2[31:0] (32-bit)
  sh     : Reg → ℤ → Reg → Instr      -- M[rs1 + offset] = rs2[15:0] (16-bit)
  sb     : Reg → ℤ → Reg → Instr      -- M[rs1 + offset] = rs2[7:0] (8-bit)

  ------------------------------------------------------------------------
  -- B-type: Conditional Branches (PC-relative)
  -- Format: op rs1, rs2, offset
  -- Note: Unlike x86, RISC-V branches compare two registers directly
  --       (no flags register!)
  -- Note: Offsets are PC-relative: pc = pc + offset (if branch taken)
  ------------------------------------------------------------------------

  beq    : Reg → Reg → ℤ → Instr      -- if (rs1 == rs2) pc = pc + offset
  bne    : Reg → Reg → ℤ → Instr      -- if (rs1 != rs2) pc = pc + offset
  blt    : Reg → Reg → ℤ → Instr      -- if (rs1 < rs2) pc = pc + offset (signed)
  bge    : Reg → Reg → ℤ → Instr      -- if (rs1 >= rs2) pc = pc + offset (signed)
  bltu   : Reg → Reg → ℤ → Instr      -- if (rs1 < rs2) pc = pc + offset (unsigned)
  bgeu   : Reg → Reg → ℤ → Instr      -- if (rs1 >= rs2) pc = pc + offset (unsigned)

  ------------------------------------------------------------------------
  -- U-type: Upper Immediate
  -- Format: op rd, imm20
  ------------------------------------------------------------------------

  lui    : Reg → ℤ → Instr            -- rd = imm << 12 (load upper immediate)
  auipc  : Reg → ℤ → Instr            -- rd = pc + (imm << 12) (add upper to PC)

  ------------------------------------------------------------------------
  -- J-type: Unconditional Jumps (PC-relative)
  ------------------------------------------------------------------------

  -- Jump and link (direct, PC-relative)
  jal    : Reg → ℤ → Instr            -- rd = pc + 1; pc = pc + offset

  -- Jump and link register (indirect, absolute)
  jalr   : Reg → Reg → ℤ → Instr      -- rd = pc + 1; pc = (rs1 + offset) & ~1

  ------------------------------------------------------------------------
  -- Pseudo-instructions
  -- These are assembler conveniences that expand to real instructions.
  -- We include them for readability in code generation.
  ------------------------------------------------------------------------

  -- Load immediate (expands to lui + addi or just addi for small values)
  li     : Reg → ℤ → Instr            -- rd = imm

  -- Move register (expands to addi rd, rs, 0)
  mv     : Reg → Reg → Instr          -- rd = rs

  -- Jump (expands to jal zero, offset) - PC-relative
  j      : ℤ → Instr                  -- pc = pc + offset (no link)

  -- Call (expands to jal ra, offset) - PC-relative
  call   : ℤ → Instr                  -- ra = pc + 1; pc = pc + offset

  -- Return (expands to jalr zero, ra, 0)
  ret    : Instr                      -- pc = ra

  -- No operation (expands to addi zero, zero, 0)
  nop    : Instr

  -- Environment break (trap for debugging / unreachable code)
  ebreak : Instr                      -- Raise breakpoint exception

  ------------------------------------------------------------------------
  -- Pseudo-instruction for assembly
  ------------------------------------------------------------------------

  -- Label marker (not a real instruction, used for branch targets)
  label  : ℕ → Instr                  -- label n:

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
-- Once-specific conventions
------------------------------------------------------------------------

-- | Calling convention for Once (RISC-V LP64)
--
-- Arguments:
--   a0: first argument (input value) AND return value
--   a1-a7: additional arguments if needed
--
-- Return:
--   a0: return value (same register as first argument!)
--
-- Note: Unlike x86 (rdi for input, rax for output), RISC-V uses
--       the same register a0 for both. This simplifies id, fold,
--       unfold, and arr which become true no-ops.
--
-- Callee-saved (preserved across calls):
--   s0-s11, sp
--
-- Caller-saved (may be clobbered):
--   ra, t0-t6, a0-a7
--
-- For closures:
--   s0: environment pointer (callee-saved)
--   The closure structure is: [env_ptr, code_ptr]
--
-- For products (pairs):
--   Memory layout: [fst (8 bytes), snd (8 bytes)]
--   Access: fst at offset 0, snd at offset 8
--
-- For sums (tagged unions):
--   Memory layout: [tag (8 bytes), value (8 bytes)]
--   tag = 0 for inl, tag = 1 for inr
--   Access: tag at offset 0, value at offset 8

-- | Offsets for product fields (same as x86 - architecture independent)
fstOffset : ℤ
fstOffset = + 0

sndOffset : ℤ
sndOffset = + 8

-- | Offsets for sum fields (same as x86 - architecture independent)
tagOffset : ℤ
tagOffset = + 0

valueOffset : ℤ
valueOffset = + 8

-- | Tag values for sums (same as x86 - architecture independent)
inlTag : ℤ
inlTag = + 0

inrTag : ℤ
inrTag = + 1

-- | Stack frame size for pair/sum allocation
pairSize : ℤ
pairSize = + 16  -- Two 64-bit words

sumSize : ℤ
sumSize = + 16   -- Tag + value

closureSize : ℤ
closureSize = + 16  -- env_ptr + code_ptr
