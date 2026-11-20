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
open import Once.Spec.Name using (CanonicalName)


open import Once.IR.Semantics.Trace using (Interp)
import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBr
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32

-- plan 0.107: the program's owner is the compiler's own (`Once.Compile.entry-owner`)
-- — fixed, because the file the compiler emits is labelled with it.
import Once.Compile as Co
import Once.Compile.Emit as Emit

module Once.Adequacy.ArchCorrectness
  -- (Each arch's three ROOM bounds — `HeapRoom`, `StackRoom`, `CallRoom` — were
  -- the first parameters here. Plan 0.123 A.4 step 5 retired all nine: the
  -- emitted room checks make running out observable, and the budget they
  -- re-arm, `FlatCore.Budget`, gives every spending instruction its room.)
  (x86-64-reg-range : ∀ ι → RB.RegRange Emit.entry-owner ι)
  (x86-64-addr-no-wrap : ∀ ι → RB.AddrNoWrap Emit.entry-owner ι)
  (x86-64-lit-fits : ∀ ι → RB.LitFits Emit.entry-owner ι)
  -- riscv64's family, now the SAME as x86-64's plus `SlotAddrNoWrap` (plan 0.65
  -- G3): three of them were all that existed while its simulation was
  -- whole-cloth.
  (riscv64-reg-range : ∀ ι → RBr.RegRange Emit.entry-owner ι)
  (riscv64-slot-addr-no-wrap : ∀ ι → RBr.SlotAddrNoWrap Emit.entry-owner ι)
  (riscv64-addr-no-wrap : ∀ ι → RBr.AddrNoWrap Emit.entry-owner ι)
  (riscv64-lit-fits : ∀ ι → RBr.LitFits Emit.entry-owner ι)
  -- …and x86-32's, the SAME family again (plan 0.66 X3). It had NONE until now,
  -- for the reason D107 names: its simulation was whole-cloth, so nothing above
  -- ever asked what resources the running program needs. One fewer than
  -- riscv64's — `SlotAddrNoWrap` is riscv64's alone (D104: x86-32 computes a slot address
  -- with `lea`, which carries no range obligation, exactly as x86-64 does).
  (x86-32-reg-range : ∀ ι → RB32.RegRange Emit.entry-owner ι)
  (x86-32-addr-no-wrap : ∀ ι → RB32.AddrNoWrap Emit.entry-owner ι)
  (x86-32-lit-fits : ∀ ι → RB32.LitFits Emit.entry-owner ι) where

o : CanonicalName
o = Emit.entry-owner

open import Once.Target.Arch using (Arch; x86-64; x86-32; riscv64)
open import Once.Adequacy.Compile using (ArchCorrect)
import Once.Adequacy.CoreArch as Core

-- plan 0.146 (D464): the compiler's file is the linear core's image of the module's sources
-- (`LinCore.Emit.coreFileOf`); on each arch it is what the assembler demands (proved, per arch)
-- and running it has the trace of the program it was emitted from (D320), up to running out
-- (D374): `Adequacy.CoreArch`, over each arch's `ArchSim` (`ArchCorrectness.<Arch>.Sim`).

x86-64-correct : ∀ (ι : Interp) → ArchCorrect x86-64 ι
x86-64-correct ι = record
  { file-wf = Core.X86-64.core-wf ι (x86-64-reg-range ι) (x86-64-addr-no-wrap ι) (x86-64-lit-fits ι)
  ; file-tr = Core.X86-64.core-tr ι (x86-64-reg-range ι) (x86-64-addr-no-wrap ι) (x86-64-lit-fits ι)
  }

x86-32-correct : ∀ (ι : Interp) → ArchCorrect x86-32 ι
x86-32-correct ι = record
  { file-wf = Core.X86-32.core-wf ι (x86-32-reg-range ι) (x86-32-addr-no-wrap ι) (x86-32-lit-fits ι)
  ; file-tr = Core.X86-32.core-tr ι (x86-32-reg-range ι) (x86-32-addr-no-wrap ι) (x86-32-lit-fits ι)
  }

riscv64-correct : ∀ (ι : Interp) → ArchCorrect riscv64 ι
riscv64-correct ι = record
  { file-wf = Core.RiscV64.core-wf ι (riscv64-reg-range ι) (riscv64-slot-addr-no-wrap ι) (riscv64-addr-no-wrap ι) (riscv64-lit-fits ι)
  ; file-tr = Core.RiscV64.core-tr ι (riscv64-reg-range ι) (riscv64-slot-addr-no-wrap ι) (riscv64-addr-no-wrap ι) (riscv64-lit-fits ι)
  }

arch-correctness : ∀ (ι : Interp) (arch : Arch) → ArchCorrect arch ι
arch-correctness ι x86-64  = x86-64-correct ι
arch-correctness ι x86-32  = x86-32-correct ι
arch-correctness ι riscv64 = riscv64-correct ι

-- ★ a module with a compilable `main` Builds: master's gates pass it (`main⇒built`), and the
-- compiler's file of it is its new image's (`LinCore.CoreFile.Prog.core-built`)
open import Data.Bool using (Bool)
open import Data.Maybe using (just)
open import Data.Product using (Σ)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Type using (Unit)
open import Once.Parser.Module.Core using (Resolved; module Resolved)
open import Once.Denotation.Admissible using (AdmissibleM)
import Once.LinCore.Emit
import Once.LinCore.CoreFile

core-built : ∀ (arch : Arch) (doOpt : Bool) (m : Resolved) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) →
             AdmissibleM arch (Resolved.rmodule m) → Co.moduleToIR m ≡ just ir →
             Σ (Emit.FileOf arch) (λ F → Once.LinCore.Emit.coreFileOf arch doOpt m ≡ inj₂ F)
core-built arch doOpt m ir adm mi = Once.LinCore.CoreFile.Prog.core-built arch m ir mi doOpt adm
