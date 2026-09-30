-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness — the per-arch backend-correctness
-- witnesses that `Once.Adequacy.Compile.WithCPU` is instantiated with.
--
-- The apex `correct` is GENERIC over the target `Arch`; each target must
-- SUPPLY an `ArchCorrect` record (asm-text + flat-machine meanings, the
-- assemble/printer obligations, and the SigOp-trace obligation). The total
-- dispatcher `arch-correctness` FORCES per-arch coverage: you cannot add an
-- `Arch` constructor without a matching witness here (the coverage checker
-- rejects a missing clause) — a blanket `∀ arch` postulate could not.
--
-- TRUST vs OBLIGATION is NOT baked into the `ArchCorrect` record (every
-- field is phrased `…-correct`); WHETHER a field is a proof or a postulate
-- is decided HERE, per arch. Since Plan 0.53 (2026-07-01) ALL THREE witnesses
-- are constructed from the FS-generic IR-observable theorem `ir-obs-correct`
-- (`Once.Adequacy.ArchCorrectness.{X86-64,X86-32,RiscV64}`) — no longer
-- whole-record postulates. Each arch carries a single named
-- `<arch>-flat-from-obs` residual (the entry-state + prefix FS plumbing);
-- (plan 0.91 S1 deleted the `program-bound` parameter that stood beside it —
-- see D213); that residual is provable (no new mathematics) and nothing assumes
-- the trusted fields can't be proved later (an in-Agda assembler / verified
-- printer). `cata-correct` is load-bearing for the apex on every target.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

open import Data.Nat using (ℕ)

import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBr
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32

module Once.Adequacy.ArchCorrectness
  (o : CanonicalName)
  (x86-64-heap-room : RB.HeapRoom o) (x86-64-stack-room : RB.StackRoom o)
  (x86-64-call-room : RB.CallRoom o)
  (x86-64-reg-range : RB.RegRange o)
  (x86-64-scratch-dec-guarded : RB.ScratchDecGuarded o)
  (x86-64-addr-no-wrap : RB.AddrNoWrap o)
  (x86-64-lit-fits : RB.LitFits o)
  -- riscv64's family, now the SAME EIGHT as x86-64's (plan 0.65 G3): three of
  -- them were all that existed while its simulation was whole-cloth.
  (riscv64-heap-room : RBr.HeapRoom o) (riscv64-stack-room : RBr.StackRoom o)
  (riscv64-call-room : RBr.CallRoom o)
  (riscv64-reg-range : RBr.RegRange o)
  (riscv64-scratch-dec-guarded : RBr.ScratchDecGuarded o)
  (riscv64-slot-addr-no-wrap : RBr.SlotAddrNoWrap o)
  (riscv64-addr-no-wrap : RBr.AddrNoWrap o)
  (riscv64-lit-fits : RBr.LitFits o)
  -- …and x86-32's, the SAME family again (plan 0.66 X3). It had NONE until now,
  -- for the reason D107 names: its simulation was whole-cloth, so nothing above
  -- ever asked what resources the running program needs. Seven, not eight —
  -- `SlotAddrNoWrap` is riscv64's alone (D104: x86-32 computes a slot address
  -- with `lea`, which carries no range obligation, exactly as x86-64 does).
  (x86-32-heap-room : RB32.HeapRoom o) (x86-32-stack-room : RB32.StackRoom o)
  (x86-32-call-room : RB32.CallRoom o)
  (x86-32-reg-range : RB32.RegRange o)
  (x86-32-scratch-dec-guarded : RB32.ScratchDecGuarded o)
  (x86-32-addr-no-wrap : RB32.AddrNoWrap o)
  (x86-32-lit-fits : RB32.LitFits o) where

open import Once.Adequacy.CPU using (Arch; x86-64; x86-32; riscv64; arch-semantics)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Data.List using (List)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.Denotation.Program using (IRFun; table; main)

import Once.Adequacy.ArchCorrectness.X86-64 as A64
import Once.Adequacy.ArchCorrectness.X86-32 as A32
import Once.Adequacy.ArchCorrectness.RiscV64 as ARV

-- D244/D245: each instance is AT A TABLE — the program image it simulates is
-- `main` together with that table's functions. The record below is per
-- PROGRAM, so it instantiates the arch module at the program's own table.
module X64 (tbl : List IRFun) = A64 o tbl x86-64-heap-room x86-64-stack-room x86-64-call-room
       x86-64-reg-range x86-64-scratch-dec-guarded x86-64-addr-no-wrap x86-64-lit-fits
module X32 (tbl : List IRFun) = A32 o tbl x86-32-heap-room x86-32-stack-room x86-32-call-room
       x86-32-reg-range x86-32-scratch-dec-guarded x86-32-addr-no-wrap x86-32-lit-fits
module RV (tbl : List IRFun) = ARV o tbl
       riscv64-heap-room riscv64-stack-room riscv64-call-room
       riscv64-reg-range riscv64-scratch-dec-guarded riscv64-slot-addr-no-wrap
       riscv64-addr-no-wrap riscv64-lit-fits

-- The block-table coherence hypotheses (plan 0.91; D188), one per target and
-- now one per TABLE: every program brings its own image.
BlockRunsHyp-x86-64 : Set
BlockRunsHyp-x86-64 = (tbl : List IRFun) → X64.BlockRunsHyp-x86-64 tbl

BlockRunsHyp-x86-32 : Set
BlockRunsHyp-x86-32 = (tbl : List IRFun) → X32.BlockRunsHyp-x86-32 tbl

BlockRunsHyp-riscv64 : Set
BlockRunsHyp-riscv64 = (tbl : List IRFun) → RV.BlockRunsHyp-riscv64 tbl

x86-64-correct : BlockRunsHyp-x86-64 → ArchCorrect x86-64 (arch-semantics x86-64)
x86-64-correct brs = record
  { asm-sem           = X64.asm-sem-x86-64 []
  ; flat-trace        = λ p lk → X64.flat-x86-64 (table p) (brs (table p)) (main p) lk
  ; assemble-correct  = λ _ _ _ _ _ → refl
  ; asm-trace-correct = λ m asm eq dl lr sr ir mi n →
      X64.asm-flat-x86-64 _ (brs _) m asm eq dl lr sr ir mi refl _ n
  ; ir-flat-correct   = λ p lk → X64.ir-flat-correct-x86-64 (table p) (brs (table p)) (main p) lk
  }

x86-32-correct : BlockRunsHyp-x86-32 → ArchCorrect x86-32 (arch-semantics x86-32)
x86-32-correct brs = record
  { asm-sem           = X32.asm-sem-x86-32 []
  ; flat-trace        = λ p lk → X32.flat-x86-32 (table p) (brs (table p)) (main p) lk
  ; assemble-correct  = λ _ _ _ _ _ → refl
  ; asm-trace-correct = λ m asm eq dl lr sr ir mi n →
      X32.asm-flat-x86-32 _ (brs _) m asm eq dl lr sr ir mi refl _ n
  ; ir-flat-correct   = λ p lk → X32.ir-flat-correct-x86-32 (table p) (brs (table p)) (main p) lk
  }

riscv64-correct : BlockRunsHyp-riscv64 → ArchCorrect riscv64 (arch-semantics riscv64)
riscv64-correct brs = record
  { asm-sem           = RV.asm-sem-riscv64 []
  ; flat-trace        = λ p lk → RV.flat-riscv64 (table p) (brs (table p)) (main p) lk
  ; assemble-correct  = λ _ _ _ _ _ → refl
  ; asm-trace-correct = λ m asm eq dl lr sr ir mi n →
      RV.asm-flat-riscv64 _ (brs _) m asm eq dl lr sr ir mi refl _ n
  ; ir-flat-correct   = λ p lk → RV.ir-flat-correct-riscv64 (table p) (brs (table p)) (main p) lk
  }

arch-correctness : BlockRunsHyp-x86-64 → BlockRunsHyp-x86-32 → BlockRunsHyp-riscv64
                 → ∀ (arch : Arch) → ArchCorrect arch (arch-semantics arch)
arch-correctness b64 b32 brv x86-64  = x86-64-correct b64
arch-correctness b64 b32 brv x86-32  = x86-32-correct b32
arch-correctness b64 b32 brv riscv64 = riscv64-correct brv
