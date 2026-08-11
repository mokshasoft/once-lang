-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.Adequacy  (Plan 0.54 Phase B / Option 1)
--
-- The GENERIC arith-backend obligation the apex depends on — ONE interface,
-- instantiated per arch. The apex (`Adequacy/`) never mentions a concrete
-- arch; a fourth arch is a new instance with zero apex edits.
--
-- Field ① (`ArithEmitConfined`) is the compiler-logic half of "the arith
-- subroutine does not clobber CCC state": the emit's clobber footprint is
-- CCC-disjoint. It is stated over the SHARED `RegConvention` (`owner`), so the
-- obligation itself is generic; each arch supplies only `writes` + the witness.
--   * x86-64 / riscv64: `confined` is definitional (`arith`/`io`/`free` ≢ `ccc`).
--   * x86-32 (k=0, borrows CCC regs): the witness is restore-correctness.
--
-- The arch-neutral VALUE correctness (`block-correct : exec-x86 (compile-abs e)
-- ≡ block-semM e`) is proven once in `Backend/Correct` and consumed here.
--
-- Field ② (the ISA-faithfulness residual — the honest per-instruction CPU seam
-- relating `run-trace ∘ decode ∘ assemble` of the emitted arith asm to
-- `exec-x86`, writing ⊆ `writes`) is added when the apex decomposition lands;
-- it necessarily references per-arch CPU State structure the current
-- `ArchSemantics` interface keeps opaque, so it is the explicit end-state trust.
------------------------------------------------------------------------

module Once.Arith.Backend.Adequacy where

open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Target.RegConvention using (RegConvention; RegClass; ccc)

------------------------------------------------------------------------
-- Field ① — CCC-confinement of the arith emit (generic over RegConvention).
------------------------------------------------------------------------

record ArithEmitConfined (RC : RegConvention) : Set where
  open RegConvention RC
  field
    -- Over-approximation of the physical registers each XInstr's emitted text
    -- clobbers (read off the per-arch `instr-text`).
    writes   : XInstr → List Reg
    -- No clobbered register is CCC-live: `All NotCCC (writes i)` ⇒ the arith
    -- subroutine cannot corrupt a register CCC keeps live across the call.
    confined : ∀ i → All (λ r → owner r ≢ ccc) (writes i)

open ArithEmitConfined public
