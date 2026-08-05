-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.Syntax
--
-- x86-64 instruction subset used by Once.
-- This is a minimal subset sufficient for the 12 categorical generators.
--
-- Based on the Sail x86-64 formal specification from REMS project.
------------------------------------------------------------------------

module Once.CCC.Target.X86-64.Syntax where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; foldr)
open import Data.String using (String)
open import Once.CCC.Label using (LabelId; Label)

------------------------------------------------------------------------
-- Registers
------------------------------------------------------------------------

-- | x86-64 general-purpose registers (64-bit)
--
-- We use a subset relevant to Once's calling convention:
--   rax: return value
--   rdi: first argument (System V ABI)
--   rsi: second argument
--   rdx: third argument
--   r12: environment pointer (callee-saved, used for closures)
--   rsp: stack pointer
--   rbp: frame pointer
--
-- The physical register file is now the single shared declaration
-- `Once.Target.X86-64.PhysReg` (Plan 0.55), re-exported here so every CCC
-- importer of this module keeps seeing `Reg` unchanged.
open import Once.Target.X86-64.PhysReg public using
  (Reg; rax; rbx; rcx; rdx; rsi; rdi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15)

------------------------------------------------------------------------
-- Memory operands
------------------------------------------------------------------------

-- | Memory addressing modes
--
-- x86-64 supports complex addressing: [base + index*scale + displacement]
-- For Once, we primarily use simple base+displacement addressing.
--
data Mem : Set where
  -- [reg]: dereference register
  base : Reg → Mem
  -- [reg + offset]: base plus displacement (8-byte aligned for 64-bit)
  base+disp : Reg → ℕ → Mem
  -- [rip + offset]: RIP-relative addressing for position-independent code
  -- Used by curry to compute absolute address of thunk code
  rip+disp : ℕ → Mem
  -- [rip + .L_thunk_<n>]: RIP-relative addressing of a closure-body
  -- label. Plan 0.2.4.2 D7. Emitted as `.L_thunk_<n>(%rip)`.
  rip+label : LabelId → Mem

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

-- | x86-64 instruction subset for Once
--
-- This is the minimal subset needed to implement the 12 categorical generators:
--
-- | Generator | Instructions Used |
-- |-----------|-------------------|
-- | id        | (none/nop)        |
-- | compose   | sequencing        |
-- | fst       | mov reg, [reg+0]  |
-- | snd       | mov reg, [reg+8]  |
-- | pair      | mov [reg+0], val; mov [reg+8], val |
-- | inl       | mov [reg+0], 0; mov [reg+8], val (tag=0 + value) |
-- | inr       | mov [reg+0], 1; mov [reg+8], val (tag=1 + value) |
-- | case      | cmp + je/jne      |
-- | terminal  | (none/nop)        |
-- | initial   | ud2 (unreachable) |
-- | curry     | lea + mov (closure creation) |
-- | apply     | call indirect     |
--
data Instr : Set where
  -- Data movement
  mov    : Operand → Operand → Instr    -- mov dst, src
  lea    : Reg → Mem → Instr            -- lea reg, [mem] (load effective address)

  -- Arithmetic (for pointer arithmetic, tag operations)
  add    : Operand → Operand → Instr    -- add dst, src
  sub    : Operand → Operand → Instr    -- sub dst, src

  -- Comparison
  cmp    : Operand → Operand → Instr    -- cmp op1, op2 (sets flags)
  test   : Operand → Operand → Instr    -- test op1, op2 (AND, sets flags)

  -- Control flow
  jmp    : Label → Instr                -- jmp label (unconditional)
  je     : Label → Instr                -- je label (jump if equal/zero)
  jne    : Label → Instr                -- jne label (jump if not equal/not zero)
  call   : Operand → Instr              -- call target (direct or indirect)
  -- Plan 0.11: SigOp call by symbolic name. The argument is a
  -- relocation symbol resolved by the linker — typically the SigOpInfo's
  -- `name` (e.g. an exit-syscall name, "arith.add.int"). CCC does not inspect
  -- the string; emit treats it as a label, simulation treats it as an
  -- opaque calling-convention transition (see `exec-x86 (call-sym _)`
  -- in DirectSimulation).
  call-sym : String → Instr
  ret    : Instr                        -- ret (return from function)

  -- Stack operations
  push   : Operand → Instr              -- push src
  pop    : Reg → Instr                  -- pop dst

  -- Special
  nop    : Instr                        -- no operation
  ud2    : Instr                        -- undefined instruction (trap for unreachable)
  syscall : Instr                       -- syscall instruction (syscall number in rax,
                                        -- args in rdi, rsi, rdx, r10, r8, r9)

  -- Label (pseudo-instruction for assembly)
  label  : Label → Instr                -- label n:

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

-- | Calling convention for Once
--
-- Arguments:
--   rdi: first argument (input value)
--   rsi: second argument (if needed)
--
-- Return:
--   rax: return value
--
-- Callee-saved (preserved across calls):
--   rbx, rbp, r12-r15
--
-- For closures:
--   r12: environment pointer
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

-- | Word/slot size for x86-64 (8 bytes)
slot-size : ℕ
slot-size = 8

-- | Convert slots to bytes: n slots = n * 8 bytes
slots : ℕ → ℕ
slots n = n *ℕ slot-size

------------------------------------------------------------------------
-- Stack consumption analysis
--
-- Compute how many stack slots an instruction consumes (positive)
-- or frees (negative represented as 0 here since we track max depth).
-- Used to derive stack requirements from codegen.
------------------------------------------------------------------------

-- | Stack slots consumed by a single instruction
-- Only counts allocations, not deallocations (for max depth calculation).
--
-- Note: catch-all-free per Plan 0.9. Adding a new Instr constructor
-- that allocates stack would force this function to be updated
-- (compile error) — preventing silent under-allocation, the same
-- class of bug as the lea-offset hiding place fixed in DirectSim.

-- Per-second-operand slot count for `sub <reg> _`. Only `(reg rsp, imm n)`
-- consumes; everything else is 0.
sub-rsp-consumed : Reg → Operand → ℕ
sub-rsp-consumed rsp (imm n) = n / slot-size
  where open import Data.Nat using (_/_)
sub-rsp-consumed rsp (reg _) = 0
sub-rsp-consumed rsp (mem _) = 0
sub-rsp-consumed rax _ = 0
sub-rsp-consumed rbx _ = 0
sub-rsp-consumed rcx _ = 0
sub-rsp-consumed rdx _ = 0
sub-rsp-consumed rsi _ = 0
sub-rsp-consumed rdi _ = 0
sub-rsp-consumed rbp _ = 0
sub-rsp-consumed r8  _ = 0
sub-rsp-consumed r9  _ = 0
sub-rsp-consumed r10 _ = 0
sub-rsp-consumed r11 _ = 0
sub-rsp-consumed r12 _ = 0
sub-rsp-consumed r13 _ = 0
sub-rsp-consumed r14 _ = 0
sub-rsp-consumed r15 _ = 0

instr-consumed-slots : Instr → ℕ
-- Stack-allocating instructions:
instr-consumed-slots (push _)         = 1                  -- push allocates 1 slot
instr-consumed-slots (sub (reg r) o)  = sub-rsp-consumed r o
instr-consumed-slots (call _)         = 1                  -- call pushes return address
instr-consumed-slots (call-sym _)     = 1                  -- same as call (pushes return address)
-- `sub` with non-register destination: not a stack op.
instr-consumed-slots (sub (mem _) _)  = 0
instr-consumed-slots (sub (imm _) _)  = 0
-- All other instructions don't allocate stack.
instr-consumed-slots (mov _ _)        = 0
instr-consumed-slots (lea _ _)        = 0
instr-consumed-slots (add _ _)        = 0
instr-consumed-slots (cmp _ _)        = 0
instr-consumed-slots (test _ _)       = 0
instr-consumed-slots (jmp _)          = 0
instr-consumed-slots (je _)           = 0
instr-consumed-slots (jne _)          = 0
instr-consumed-slots ret              = 0   -- pop, but only counted as allocation
instr-consumed-slots (pop _)          = 0   -- pop deallocates, not counted
instr-consumed-slots nop              = 0
instr-consumed-slots ud2              = 0
instr-consumed-slots syscall          = 0
instr-consumed-slots (label _)        = 0

-- | Total stack slots consumed by an instruction sequence
-- Note: This counts allocations only, not the net change (ignores pop/add/ret)
instrs-consumed-slots : List Instr → ℕ
instrs-consumed-slots = foldr (λ i acc → instr-consumed-slots i +ℕ acc) 0

-- | Offsets for product fields
fstOffset : ℕ
fstOffset = 0

sndOffset : ℕ
sndOffset = slot-size

-- | Offsets for sum fields
tagOffset : ℕ
tagOffset = 0

valueOffset : ℕ
valueOffset = slot-size

-- | Tag values for sums
inlTag : ℕ
inlTag = 0

inrTag : ℕ
inrTag = 1