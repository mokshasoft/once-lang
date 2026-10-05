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

open import Once.Denotation.TraceMonad using (Interp)
import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBr
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32

-- plan 0.107: the program's owner is the compiler's own (`Once.Compile.entry-owner`)
-- — fixed, because the file the compiler emits is labelled with it.
import Once.Compile as Co

module Once.Adequacy.ArchCorrectness
  (x86-64-heap-room : ∀ ι → RB.HeapRoom Co.entry-owner ι) (x86-64-stack-room : ∀ ι → RB.StackRoom Co.entry-owner ι)
  (x86-64-call-room : ∀ ι → RB.CallRoom Co.entry-owner ι)
  (x86-64-reg-range : ∀ ι → RB.RegRange Co.entry-owner ι)
  (x86-64-scratch-dec-guarded : ∀ ι → RB.ScratchDecGuarded Co.entry-owner ι)
  (x86-64-addr-no-wrap : ∀ ι → RB.AddrNoWrap Co.entry-owner ι)
  (x86-64-lit-fits : ∀ ι → RB.LitFits Co.entry-owner ι)
  -- riscv64's family, now the SAME EIGHT as x86-64's (plan 0.65 G3): three of
  -- them were all that existed while its simulation was whole-cloth.
  (riscv64-heap-room : ∀ ι → RBr.HeapRoom Co.entry-owner ι) (riscv64-stack-room : ∀ ι → RBr.StackRoom Co.entry-owner ι)
  (riscv64-call-room : ∀ ι → RBr.CallRoom Co.entry-owner ι)
  (riscv64-reg-range : ∀ ι → RBr.RegRange Co.entry-owner ι)
  (riscv64-scratch-dec-guarded : ∀ ι → RBr.ScratchDecGuarded Co.entry-owner ι)
  (riscv64-slot-addr-no-wrap : ∀ ι → RBr.SlotAddrNoWrap Co.entry-owner ι)
  (riscv64-addr-no-wrap : ∀ ι → RBr.AddrNoWrap Co.entry-owner ι)
  (riscv64-lit-fits : ∀ ι → RBr.LitFits Co.entry-owner ι)
  -- …and x86-32's, the SAME family again (plan 0.66 X3). It had NONE until now,
  -- for the reason D107 names: its simulation was whole-cloth, so nothing above
  -- ever asked what resources the running program needs. Seven, not eight —
  -- `SlotAddrNoWrap` is riscv64's alone (D104: x86-32 computes a slot address
  -- with `lea`, which carries no range obligation, exactly as x86-64 does).
  (x86-32-heap-room : ∀ ι → RB32.HeapRoom Co.entry-owner ι) (x86-32-stack-room : ∀ ι → RB32.StackRoom Co.entry-owner ι)
  (x86-32-call-room : ∀ ι → RB32.CallRoom Co.entry-owner ι)
  (x86-32-reg-range : ∀ ι → RB32.RegRange Co.entry-owner ι)
  (x86-32-scratch-dec-guarded : ∀ ι → RB32.ScratchDecGuarded Co.entry-owner ι)
  (x86-32-addr-no-wrap : ∀ ι → RB32.AddrNoWrap Co.entry-owner ι)
  (x86-32-lit-fits : ∀ ι → RB32.LitFits Co.entry-owner ι) where

o : CanonicalName
o = Co.entry-owner

open import Once.Adequacy.CPU using (arch-semantics)
open import Once.Target.Arch using (Arch; x86-64; x86-32; riscv64)
open import Once.Adequacy.Compile using (ArchCorrect)
open import Data.List using (List; [])
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.Denotation.Program using (IRFun; table; main; irProgram; LinkedProgram)
open import Once.Adequacy.SourceTrace using (rewrite-program-linked)
open import Once.Compile using (moduleToIR; moduleTable; rewrite-program)
open import Once.Adequacy.ProgramLinked using (moduleToProgram-linked)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Once.Spec.Module using (moduleSig)
import Once.Parser.Module.Core as P

import Once.Adequacy.FileWF as FileWF
import Once.Adequacy.ArchCorrectness.X86-64 as A64
import Once.Adequacy.ArchCorrectness.X86-32 as A32
import Once.Adequacy.ArchCorrectness.RiscV64 as ARV

-- D244/D245: each instance is AT A TABLE — the program image it simulates is
-- `main` together with that table's functions. The record below is per
-- PROGRAM, so it instantiates the arch module at the program's own table.
module X64 (ι : Interp) (tbl : List IRFun) = A64 o tbl ι (x86-64-heap-room ι) (x86-64-stack-room ι) (x86-64-call-room ι)
       (x86-64-reg-range ι) (x86-64-scratch-dec-guarded ι) (x86-64-addr-no-wrap ι) (x86-64-lit-fits ι)
module X32 (ι : Interp) (tbl : List IRFun) = A32 o tbl ι (x86-32-heap-room ι) (x86-32-stack-room ι) (x86-32-call-room ι)
       (x86-32-reg-range ι) (x86-32-scratch-dec-guarded ι) (x86-32-addr-no-wrap ι) (x86-32-lit-fits ι)
module RV (ι : Interp) (tbl : List IRFun) = ARV o tbl ι
       (riscv64-heap-room ι) (riscv64-stack-room ι) (riscv64-call-room ι)
       (riscv64-reg-range ι) (riscv64-scratch-dec-guarded ι) (riscv64-slot-addr-no-wrap ι)
       (riscv64-addr-no-wrap ι) (riscv64-lit-fits ι)

-- The emitted (arith-rewritten) program's table, and its linkedness.
TP : P.Module → IR ⌊ Unit ⌋ ⌊ Unit ⌋ → List IRFun
TP m ir = table (rewrite-program (irProgram (moduleTable m) ir))

LK : ∀ (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir
   → LinkedProgram (moduleSig m) (rewrite-program (irProgram (moduleTable m) ir))
LK m ir mi = rewrite-program-linked (irProgram (moduleTable m) ir) (moduleToProgram-linked m ir mi)

-- The block-table coherence hypotheses (plan 0.91; D188), one per target and
-- now one per TABLE: every program brings its own image.
BlockRunsHyp-x86-64 : Set
BlockRunsHyp-x86-64 = (ι : Interp) (tbl : List IRFun) → X64.BlockRunsHyp-x86-64 ι tbl

BlockRunsHyp-x86-32 : Set
BlockRunsHyp-x86-32 = (ι : Interp) (tbl : List IRFun) → X32.BlockRunsHyp-x86-32 ι tbl

BlockRunsHyp-riscv64 : Set
BlockRunsHyp-riscv64 = (ι : Interp) (tbl : List IRFun) → RV.BlockRunsHyp-riscv64 ι tbl

x86-64-correct : BlockRunsHyp-x86-64 → ∀ (ι : Interp) → ArchCorrect x86-64 ι
x86-64-correct brs ι = record
  { flat-trace         = λ p lk → X64.flat-x86-64 ι (table p) (brs ι (table p)) (main p) lk
  -- plan 0.107: the emitted FILE is well-formed (proved, per arch) …
  ; file-wf            = λ m F eq → FileWF.file-wf x86-64 m F eq
  -- … and running it is the flat trace of the program it was emitted from.
  ; file-trace-correct = λ m F eq ir mi ls n →
      X64.file-flat-x86-64 ι (TP m ir) (brs ι (TP m ir)) m F eq ir mi refl refl
        (subst (λ σ → LinkedProgram σ (rewrite-program (irProgram (moduleTable m) ir))) ls (LK m ir mi)) n
  ; ir-flat-correct    = λ p lk → X64.ir-flat-correct-x86-64 ι (table p) (brs ι (table p)) (main p) lk
  }

x86-32-correct : BlockRunsHyp-x86-32 → ∀ (ι : Interp) → ArchCorrect x86-32 ι
x86-32-correct brs ι = record
  { flat-trace         = λ p lk → X32.flat-x86-32 ι (table p) (brs ι (table p)) (main p) lk
  -- plan 0.107: the emitted FILE is well-formed (proved, per arch) …
  ; file-wf            = λ m F eq → FileWF.file-wf x86-32 m F eq
  -- … and running it is the flat trace of the program it was emitted from.
  ; file-trace-correct = λ m F eq ir mi ls n →
      X32.file-flat-x86-32 ι (TP m ir) (brs ι (TP m ir)) m F eq ir mi refl refl
        (subst (λ σ → LinkedProgram σ (rewrite-program (irProgram (moduleTable m) ir))) ls (LK m ir mi)) n
  ; ir-flat-correct    = λ p lk → X32.ir-flat-correct-x86-32 ι (table p) (brs ι (table p)) (main p) lk
  }

riscv64-correct : BlockRunsHyp-riscv64 → ∀ (ι : Interp) → ArchCorrect riscv64 ι
riscv64-correct brs ι = record
  { flat-trace         = λ p lk → RV.flat-riscv64 ι (table p) (brs ι (table p)) (main p) lk
  -- plan 0.107: the emitted FILE is well-formed (proved, per arch) …
  ; file-wf            = λ m F eq → FileWF.file-wf riscv64 m F eq
  -- … and running it is the flat trace of the program it was emitted from.
  ; file-trace-correct = λ m F eq ir mi ls n →
      RV.file-flat-riscv64 ι (TP m ir) (brs ι (TP m ir)) m F eq ir mi refl refl
        (subst (λ σ → LinkedProgram σ (rewrite-program (irProgram (moduleTable m) ir))) ls (LK m ir mi)) n
  ; ir-flat-correct    = λ p lk → RV.ir-flat-correct-riscv64 ι (table p) (brs ι (table p)) (main p) lk
  }

arch-correctness : BlockRunsHyp-x86-64 → BlockRunsHyp-x86-32 → BlockRunsHyp-riscv64
                 → ∀ (ι : Interp) (arch : Arch) → ArchCorrect arch ι
arch-correctness b64 b32 brv ι x86-64  = x86-64-correct b64 ι
arch-correctness b64 b32 brv ι x86-32  = x86-32-correct b32 ι
arch-correctness b64 b32 brv ι riscv64 = riscv64-correct brv ι
