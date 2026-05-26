-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86.Syntax
--
-- Plan 0.20 Phase D — the x86-64 instruction subset used by arith
-- block codegen.
--
-- Why a NEW (and small) subset, not the existing
-- `Once.CCC.Target.X86-64.Syntax`?
--
--   - The existing CCC subset is dimensioned for the categorical
--     generators (mov/lea/add/sub/cmp/jmp/call/syscall/ud2/…) and
--     intentionally lacks `imul`/`neg`/typed scratch slots.
--   - Arith blocks are opaque from CCC's perspective (D-arith-7);
--     keeping the arith instruction subset isolated mirrors that
--     architectural boundary and lets the backend evolve (peephole,
--     vectorisation) without touching CCC's emit/simulation layers.
--
-- The Boundary module (Phase E) bridges between the two: each arith
-- block emits a `List XInstr` which is wrapped in a CCC-level `SigOp
-- arith.block.<digest>` whose code is the assembled sequence.
------------------------------------------------------------------------

module Once.Arith.Backend.X86.Syntax where

open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.List using (List)

------------------------------------------------------------------------
-- Registers (GPR subset only — arith I64 path)
------------------------------------------------------------------------

-- | The arith subsystem uses callee-saved GPRs r12-r15 as its abstract
-- register file. Phase F's allocator can grow the set; Phase G's
-- comparison ops may need rax/rdx for `idiv` / `cqo`.
data XReg : Set where
  XR12 : XReg   -- AbsReg 0 (accumulator)
  XR13 : XReg   -- AbsReg 1 (reload target)
  XR14 : XReg   -- AbsReg 2
  XR15 : XReg   -- AbsReg 3

------------------------------------------------------------------------
-- Scratch slot addressing (stack-relative)
------------------------------------------------------------------------

-- | A scratch slot is a stable 8-byte stack cell, addressed as
-- `[rsp - 8 * (slot+1)]` after the function's prologue reserves
-- enough room (the block's `required-scratch * 8` bytes).
record XScratch : Set where
  constructor mk-scratch
  field
    slot : ℕ

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

-- | x86-64 arith instruction subset.
--
-- Naming convention: `Xmov-imm dst z` = `mov $z, %dst`;
-- `Xadd-rr a b`     = `add %b, %a`  (Intel-style mnemonics, AT&T
-- ordering: source-then-dest is *flipped* into dest-then-source for
-- readability here).
data XInstr : Set where
  -- Data movement
  Xmov-imm  : XReg → ℤ → XInstr             -- mov $z, %dst
  Xmov-rr   : XReg → XReg → XInstr          -- mov %src, %dst
  Xmov-r-m  : XScratch → XReg → XInstr      -- mov %src, [rsp - …]   (spill)
  Xmov-m-r  : XReg → XScratch → XInstr      -- mov [rsp - …], %dst   (reload)
  Xmov-arg  : XReg → ℕ → XInstr             -- mov  arg-offset(%rdi), %dst
                                            -- (load input from the
                                            -- block's input buffer at
                                            -- 8-byte stride)

  -- Arithmetic (all in-place: dst := dst ⊙ src)
  Xadd-rr   : XReg → XReg → XInstr          -- add %src, %dst
  Xsub-rr   : XReg → XReg → XInstr          -- sub %src, %dst
  Ximul-rr  : XReg → XReg → XInstr          -- imul %src, %dst
  Xneg-r    : XReg → XInstr                 -- neg %dst

  -- Boundary glue
  Xmov-out  : XReg → XInstr                 -- mov %src, %rax  (function
                                            -- result lands in rax per
                                            -- the SysV calling conv;
                                            -- the SigOp wrapper then
                                            -- consumes it.)

------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------

-- | An arith-block code body is a flat list of `XInstr`. The full
-- emitted block is `prologue ++ body ++ epilogue`, where the
-- prologue/epilogue manage the scratch reservation; those are added
-- by `Boundary` (Phase E).
XProgram : Set
XProgram = List XInstr
