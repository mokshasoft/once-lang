-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.RiscV64.Syntax
--
-- RISC-V 64-bit (RV64I) instruction subset used by Once.
-- This is a minimal subset sufficient for the 12 categorical generators.
--
-- RISC-V is a load-store architecture with:
--   - 32 general-purpose registers (x0-x31)
--   - Fixed 32-bit instruction encoding (RV64I base)
--   - Simple addressing: base + 12-bit signed offset
------------------------------------------------------------------------

module Once.CCC.Target.RiscV64.Syntax where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; foldr)

------------------------------------------------------------------------
-- Registers
------------------------------------------------------------------------

-- | RISC-V general-purpose registers
--
-- RISC-V has 32 registers x0-x31 with ABI names:
--   x0  (zero): hardwired zero
--   x1  (ra):   return address
--   x2  (sp):   stack pointer
--   x3  (gp):   global pointer
--   x4  (tp):   thread pointer
--   x5-x7 (t0-t2): temporaries
--   x8  (s0/fp): saved register / frame pointer
--   x9  (s1):   saved register
--   x10-x11 (a0-a1): function arguments / return values
--   x12-x17 (a2-a7): function arguments
--   x18-x27 (s2-s11): saved registers
--   x28-x31 (t3-t6): temporaries
--
data Reg : Set where
  -- Hardwired zero
  zero : Reg   -- x0: always reads as 0

  -- Return address
  ra   : Reg   -- x1: return address

  -- Stack/frame pointers
  sp   : Reg   -- x2: stack pointer
  fp   : Reg   -- x8/s0: frame pointer (callee-saved)

  -- Function arguments and return values
  a0   : Reg   -- x10: first argument / return value
  a1   : Reg   -- x11: second argument / second return value
  a2   : Reg   -- x12: third argument
  a3   : Reg   -- x13: fourth argument
  a4   : Reg   -- x14: fifth argument
  a5   : Reg   -- x15: sixth argument
  a6   : Reg   -- x16: seventh argument
  a7   : Reg   -- x17: eighth argument

  -- Saved registers (callee-saved)
  s1   : Reg   -- x9: saved register
  s2   : Reg   -- x18: saved register (environment pointer for closures)
  s3   : Reg   -- x19: saved register
  s4   : Reg   -- x20: saved register

  -- Temporaries (caller-saved)
  t0   : Reg   -- x5: temporary
  t1   : Reg   -- x6: temporary
  t2   : Reg   -- x7: temporary
  t3   : Reg   -- x28: temporary
  t4   : Reg   -- x29: temporary

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

-- | RISC-V 64-bit instruction subset for Once
--
-- RISC-V is a load-store architecture:
--   - Arithmetic operates on registers only
--   - Memory access via load/store instructions
--
-- | Generator | Instructions Used |
-- |-----------|-------------------|
-- | id        | (none/nop)        |
-- | compose   | sequencing        |
-- | fst       | ld rd, 0(rs)      |
-- | snd       | ld rd, 8(rs)      |
-- | pair      | sd rs, 0(rd); sd rs, 8(rd) |
-- | inl       | sd zero, 0(rd); sd rs, 8(rd) |
-- | inr       | li t0, 1; sd t0, 0(rd); sd rs, 8(rd) |
-- | case      | ld t0, 0(rs); beq/bne |
-- | terminal  | (none/nop)        |
-- | initial   | unimp (trap)      |
-- | curry     | auipc + addi (address computation) |
-- | apply     | jalr (indirect call) |
--
data Instr : Set where
  -- Load/Store (RV64I)
  ld     : Reg → Reg → ℕ → Instr      -- ld rd, offset(rs) : load 64-bit
  sd     : Reg → Reg → ℕ → Instr      -- sd rs, offset(rd) : store 64-bit

  -- Arithmetic (register-register)
  add    : Reg → Reg → Reg → Instr    -- add rd, rs1, rs2
  sub    : Reg → Reg → Reg → Instr    -- sub rd, rs1, rs2

  -- Arithmetic (register-immediate)
  addi   : Reg → Reg → ℤ → Instr      -- addi rd, rs, imm

  -- Load immediate (pseudo-instruction)
  li     : Reg → ℤ → Instr            -- li rd, imm (load immediate)

  -- Address computation
  auipc  : Reg → ℕ → Instr            -- auipc rd, imm : rd = PC + (imm << 12)

  -- Move (pseudo-instruction: addi rd, rs, 0)
  mv     : Reg → Reg → Instr          -- mv rd, rs

  -- Branches
  beq    : Reg → Reg → ℕ → Instr      -- beq rs1, rs2, offset
  bne    : Reg → Reg → ℕ → Instr      -- bne rs1, rs2, offset

  -- Jumps
  jal    : Reg → ℕ → Instr            -- jal rd, offset (rd = PC+4, jump)
  jalr   : Reg → Reg → ℕ → Instr      -- jalr rd, rs, offset (indirect)

  -- Pseudo-instructions
  j      : ℕ → Instr                  -- j offset (jal zero, offset)
  ret    : Instr                      -- ret (jalr zero, ra, 0)
  call   : ℕ → Instr                  -- call offset (auipc + jalr)

  -- Special
  nop    : Instr                      -- nop (addi zero, zero, 0)
  unimp  : Instr                      -- unimp (trap for unreachable)

  -- Label (pseudo-instruction for assembly)
  label  : ℕ → Instr

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
-- Once-specific conventions (RISC-V LP64 ABI)
------------------------------------------------------------------------

-- | Calling convention for Once on RISC-V
--
-- Arguments:
--   a0: first argument (input value)
--   a1: second argument (if needed)
--   a2-a7: additional arguments
--
-- Return:
--   a0: return value
--   a1: second return value (if needed)
--
-- Callee-saved (preserved across calls):
--   s0-s11 (x8-x9, x18-x27), sp
--
-- For closures:
--   s2 (x18): environment pointer
--   The closure structure is: [env_ptr (8 bytes), code_ptr (8 bytes)]
--
-- For products (pairs):
--   Memory layout: [fst (8 bytes), snd (8 bytes)]
--   Access: fst at offset 0, snd at offset 8
--
-- For sums (tagged unions):
--   Memory layout: [tag (8 bytes), value (8 bytes)]
--   tag = 0 for inl, tag = 1 for inr

-- | Word/slot size for RV64 (8 bytes)
slot-size : ℕ
slot-size = 8

-- | Convert slots to bytes: n slots = n * 8 bytes
slots : ℕ → ℕ
slots n = n *ℕ slot-size

------------------------------------------------------------------------
-- Stack consumption analysis
------------------------------------------------------------------------

-- | Stack slots consumed by a single instruction.
-- Catch-all-free per Plan 0.9: adding a new Instr constructor that
-- allocates stack would force this function to be updated (compile
-- error). All RV64 instructions in the current model are pure-bookkeeping
-- with respect to the abstract stack slot count — the addi sp sp ±N
-- form that adjusts %sp is tracked elsewhere via AbstractInstr.
instr-consumed-slots : Instr → ℕ
instr-consumed-slots (ld _ _ _)      = 0
instr-consumed-slots (sd _ _ _)      = 0
instr-consumed-slots (add _ _ _)     = 0
instr-consumed-slots (sub _ _ _)     = 0
instr-consumed-slots (addi _ _ _)    = 0   -- sp adjustment handled separately
instr-consumed-slots (li _ _)        = 0
instr-consumed-slots (auipc _ _)     = 0
instr-consumed-slots (mv _ _)        = 0
instr-consumed-slots (beq _ _ _)     = 0
instr-consumed-slots (bne _ _ _)     = 0
instr-consumed-slots (jal _ _)       = 0   -- call: return addr saved by callee
instr-consumed-slots (jalr _ _ _)    = 0
instr-consumed-slots (j _)           = 0
instr-consumed-slots ret             = 0
instr-consumed-slots (call _)        = 0
instr-consumed-slots nop             = 0
instr-consumed-slots unimp           = 0
instr-consumed-slots (label _)       = 0

-- | Total stack slots consumed by a program
program-consumed-slots : Program → ℕ
program-consumed-slots prog = foldr _+ℕ_ 0 (Data.List.map instr-consumed-slots prog)
  where open import Data.List using (map)