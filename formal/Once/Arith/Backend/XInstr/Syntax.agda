-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.XInstr.Syntax
--
-- Plan 0.20 Phase D — the arch-neutral instruction subset used by arith
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

module Once.Arith.Backend.XInstr.Syntax where

open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.List using (List)

open import Once.Arith.Machine.AbsState using (InputPath)
open import Once.Float.Decimal using (Decimal)

------------------------------------------------------------------------
-- Registers (GPR subset only — arith I64 path)
------------------------------------------------------------------------

-- | The arith subsystem uses callee-saved GPRs r12-r15 as its abstract
-- register file. Phase F's allocator can grow the set; Phase G's
-- comparison ops may need rax/rdx for `idiv` / `cqo`.
-- The arith compiler (`compile-abs`) is a 2-register + stack-spill discipline:
-- `compile-go` only ever uses reg 0 (accumulator) and reg 1 (reload target),
-- spilling everything else to scratch slots. So `XReg` needs exactly two
-- constructors; there is no register-pressure case that a third would serve.
data XReg : Set where
  XR0 : XReg   -- accumulator (AbsReg 0)
  XR1 : XReg   -- reload target (AbsReg 1)

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

-- | Arch-neutral arith instruction subset (shared by all backends; only
-- the per-arch Emit renders XReg/offsets to concrete asm).
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
  Xmov-arg  : XReg → InputPath → XInstr     -- Load value at the
                                            -- given InputPath from
                                            -- the block's input
                                            -- (`%rdi`) into `dst`.
                                            -- Nested pair inputs
                                            -- chase pointers via
                                            -- `%rax` exactly the way
                                            -- CCC's `fst`/`snd` chain
                                            -- does: `mov rax,
                                            -- offset(rdi)` then
                                            -- `mov rax, offset(rax)`
                                            -- per intermediate step,
                                            -- final load into `dst`.
                                            -- For path length 1 the
                                            -- chain collapses to one
                                            -- direct `mov` from rdi.

  -- Arithmetic (all in-place: dst := dst ⊙ src)
  Xadd-rr   : XReg → XReg → XInstr          -- add %src, %dst
  Xsub-rr   : XReg → XReg → XInstr          -- sub %src, %dst
  Ximul-rr  : XReg → XReg → XInstr          -- imul %src, %dst
  Xneg-r    : XReg → XInstr                 -- neg %dst

  -- Division / remainder (D055 total signed). THREE-address (dst, dividend,
  -- divisor) — NOT the in-place 2-address form: x86 `idiv` implicitly uses
  -- rax/rdx regardless, so an explicit dividend/divisor pair avoids any
  -- aliasing constraint on `dst`. `dst := a /ˢ b` / `dst := a %ˢ b`.
  Xdiv-rrr  : XReg → XReg → XReg → XInstr    -- dst := dividend /ˢ divisor
  Xrem-rrr  : XReg → XReg → XReg → XInstr    -- dst := dividend %ˢ divisor

  -- Guard-ELIDED division / remainder (Plan: div-guard elision). SAME meaning
  -- as `Xdiv-rrr`/`Xrem-rrr` (`/ˢ`/`%ˢ`); the per-arch Emit renders a BARE
  -- idiv (no D055 test/INT_MIN guard). Emitted ONLY when compile-go proved the
  -- divisor a safe literal (nonzero, ≠ −1), so #DE cannot fire by construction.
  Xdiv-safe-rrr : XReg → XReg → XReg → XInstr
  Xrem-safe-rrr : XReg → XReg → XReg → XInstr

  -- Power-of-two strength reduction (multiply / divide by `2^imm`). SINGLE
  -- write `dst := f src` carrying an immediate shift count `imm`:
  --   `Xshl-rri dst src imm`      = `dst := src `shlᵂ` imm` (= src ⊗ 2^imm);
  --                                 per-arch Emit renders `shl`/`slli`.
  --   `Xsdiv-pow2-rri dst src imm` = `dst := src `sdiv2ᵏ` imm` (= src /ˢ 2^imm,
  --                                 truncate toward zero); per-arch Emit
  --                                 renders the sign-corrected `sar`/`srai`
  --                                 bias sequence. Emitted ONLY for a positive
  --                                 power-of-two literal multiplier/divisor.
  Xshl-rri       : XReg → XReg → ℕ → XInstr
  Xsdiv-pow2-rri : XReg → XReg → ℕ → XInstr

  ----------------------------------------------------------------------
  -- PLAN 0.75 F4: the FLOAT instructions.
  --
  -- Same two-address in-place shape as the integer arithmetic above, and the
  -- same `XReg` operands. `XReg` names an ABSTRACT scratch register; which
  -- physical file it lands in is the per-arch emitter's business, and it
  -- differs — `%xmm0` on x86, `ft0` on RISC-V. That is exactly the split the
  -- abstract machine deliberately does NOT model (see `AbsInstr`): a value is
  -- a bit pattern in either file, and only the OPERATION knows which.
  ----------------------------------------------------------------------
  Xfadd-rr  : XReg → XReg → XInstr           -- dst := dst `fadd` src
  Xfsub-rr  : XReg → XReg → XInstr
  Xfmul-rr  : XReg → XReg → XInstr

  -- | REVERSE subtract: `dst := src − dst`. It exists to avoid a PROOF, and
  -- that is worth stating. `compile-go` leaves the subtrahend in `dst`, so the
  -- integer emitter handles that aliasing with `neg` then `add` — which for
  -- floats would need `a − b ≡ a + (−b)` as a lemma about `decode`/`negV`,
  -- true by IEEE but not cheap here. A reverse subtract is the operation the
  -- aliasing actually calls for, needs no identity, and costs the per-arch
  -- emitter one scratch XMM/F register it already has.
  Xfsubr-rr : XReg → XReg → XInstr

  -- | Sign-bit flip, NOT `0 − x` — the latter turns `−0` into `+0` and
  -- canonicalises a NaN, neither of which negation may do.
  Xfneg-r   : XReg → XInstr

  -- | D125's widening, correctly rounded. The ONE instruction that moves a
  -- value between the two physical register files.
  Xi2f-r    : XReg → XReg → XInstr           -- dst := i2f src

  -- | A float literal, as its `Decimal` payload — NOT as a pattern. The ONE
  -- rounding stays at the target (D117); the emitter materialises
  -- `round F d` itself, so a narrower target rounds narrower.
  Xmov-fimm : XReg → Decimal → XInstr

  -- | A FLOAT input leaf. Distinct from `Xmov-arg` because the projections
  -- differ by kind (`projectF`, not `project`) — a kind-blind load is the
  -- silent type confusion `projectM` already had to be fixed for.
  Xmov-farg : XReg → InputPath → XInstr

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
