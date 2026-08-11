-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.Syntax
--
-- x86-32 (IA-32) instruction subset used by Once.
-- This is a minimal subset sufficient for the 12 categorical generators.
--
-- Key differences from x86-64:
--   - 32-bit registers (eax, ebx, etc. instead of rax, rbx)
--   - 4-byte word size instead of 8-byte
--   - Fewer registers available
--   - Different calling conventions (cdecl, stdcall, fastcall)
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.Syntax where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Integer using (ℤ)
open import Data.List using (List)
open import Data.String using (String)
-- Plan 0.63: label PROVENANCE, shared with x86-64 (D082). `Once.CCC.Label` is
-- arch-agnostic, so the two targets name code addresses the same way — which
-- is the point: the correspondence proofs that today exist only for x86-64 are
-- meant to be generalised over the target, and a bare-ℕ label space here would
-- be the one place they could not be.
open import Once.CCC.Label public using (LabelId; Label; once; sigop; thunk)

------------------------------------------------------------------------
-- Registers
------------------------------------------------------------------------

-- | x86-32 general-purpose registers
--
-- x86-32 has 8 general purpose registers:
--   eax, ebx, ecx, edx: 32-bit versions of accumulator/base/counter/data
--   esi, edi: source/destination index
--   ebp: base pointer (frame pointer)
--   esp: stack pointer
--
-- The physical register file is now the single shared declaration
-- `Once.Target.X86-32.PhysReg` (Plan 0.55), re-exported here so every CCC
-- importer of this module keeps seeing `Reg` unchanged.
open import Once.Target.X86-32.PhysReg public using
  (Reg; eax; ebx; ecx; edx; esi; edi; ebp; esp)

------------------------------------------------------------------------
-- Memory Operands
------------------------------------------------------------------------

-- | Memory addressing modes for x86-32
--
-- x86-32 supports various addressing modes:
--   [reg]            - base only
--   [reg + disp]     - base + displacement
--   [rel label]      - PC-relative (limited in 32-bit mode)
--
data Mem : Set where
  base      : Reg → Mem              -- [reg]
  base+disp : Reg → ℕ → Mem          -- [reg + disp]
  label-rel : ℕ → Mem                -- [label] (for static data)

------------------------------------------------------------------------
-- Operands
------------------------------------------------------------------------

-- | Instruction operands
data Operand : Set where
  reg : Reg → Operand                -- Register operand
  mem : Mem → Operand                -- Memory operand
  imm : ℕ → Operand                  -- Immediate value

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

-- | x86-32 instruction subset for Once
--
-- | Generator | Instructions Used |
-- |-----------|-------------------|
-- | id        | (none/nop)        |
-- | compose   | sequencing        |
-- | fst       | mov eax, [reg]    |
-- | snd       | mov eax, [reg+4]  |
-- | pair      | mov [reg], eax; mov [reg+4], edx |
-- | inl       | mov dword [reg], 0; mov [reg+4], eax |
-- | inr       | mov dword [reg], 1; mov [reg+4], eax |
-- | case      | mov ecx, [reg]; cmp/jne |
-- | terminal  | (none/nop)        |
-- | initial   | ud2 (trap)        |
-- | curry     | lea (address computation) |
-- | apply     | call [reg] (indirect call) |
--
data Instr : Set where
  -- Data movement
  mov   : Operand → Operand → Instr   -- mov dst, src
  lea   : Reg → Mem → Instr           -- lea dst, [mem] (load effective address)
  push  : Operand → Instr             -- push src
  pop   : Reg → Instr                 -- pop dst

  -- Arithmetic
  add   : Operand → Operand → Instr   -- add dst, src
  sub   : Operand → Operand → Instr   -- sub dst, src

  -- Comparison
  cmp   : Operand → Operand → Instr   -- cmp dst, src
  test  : Operand → Operand → Instr   -- test dst, src

  -- Control flow
  jmp   : Operand → Instr             -- jmp target
  jne   : Label → Instr               -- jne label
  je    : Label → Instr               -- je label
  call  : Operand → Instr             -- call target
  -- Plan 0.11: SigOp call by symbolic name. Linker resolves the name.
  call-sym : String → Instr
  ret   : Instr                       -- ret

  -- Special
  nop   : Instr                       -- nop
  ud2   : Instr                       -- ud2 (undefined instruction, trap)

  -- Assembly pseudo-instructions
  label : Label → Instr               -- .L<provenance>:
  -- Plan 0.53: load a code-label (thunk body) address into a register —
  -- `movl $.L_thunk_<n>, <reg>` (absolute; non-PIE static exe). And an
  -- unconditional jump to a label (the plain `jmp (imm n)` prints a bare
  -- number, not a label).
  --
  -- `mov-code` takes a bare ℕ and pins the `thunk` provenance in its
  -- RENDERING, exactly as x86-64's `rip+label : ℕ → Mem` does: the operand
  -- can only ever name a closure body, so the provenance is a property of the
  -- constructor rather than of its argument.
  mov-code : Reg → LabelId → Instr    -- movl $.L_thunk_<n>, reg
  jmp-l    : Label → Instr            -- jmp .L<provenance>

------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------

-- | A program is a list of instructions
Program : Set
Program = List Instr

------------------------------------------------------------------------
-- x86-32 Specific Constants
------------------------------------------------------------------------

-- | Word/slot size for x86-32 (4 bytes)
slot-size : ℕ
slot-size = 4

-- | Convert slots to bytes: n slots = n * 4 bytes
slots : ℕ → ℕ
slots n = n * slot-size

------------------------------------------------------------------------
-- Once-specific conventions (x86-32 cdecl)
--
-- Arguments: pushed on stack right-to-left
-- Return: eax (or eax:edx for 64-bit return)
-- Callee-saved: ebx, esi, edi, ebp
-- Caller-saved: eax, ecx, edx
--
-- For closures:
--   ebx: environment pointer (callee-saved)
--   The closure structure is: [env_ptr (4 bytes), code_ptr (4 bytes)]
--
-- For products (pairs):
--   Memory layout: [fst (4 bytes), snd (4 bytes)]
--   Access: fst at offset 0, snd at offset 4
--
-- For sums (tagged unions):
--   Memory layout: [tag (4 bytes), value (4 bytes)]
--   tag = 0 for inl, tag = 1 for inr
------------------------------------------------------------------------