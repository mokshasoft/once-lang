-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CPU.X86-64 — X86-64 ArchSemantics instance
--
-- Wires `Once.CCC.Target.X86-64.Semantics` (clean step / exec / run
-- shape, restored from history) into the portable `ArchSemantics`
-- interface.
--
-- Concrete fields (real ISA semantics):
--   - Program      = List Instr  (from Once.CCC.Target.X86-64.Syntax)
--   - State        = the existing record (regs, memory, flags, pc, halted)
--   - initialState = X86-64.Semantics.initState
--   - run          = X86-64.Semantics.run  ← THE TRUST POINT.
--                    Reviewers verify each clause of `execInstr` against
--                    the Intel SDM.
--
-- Postulated bridges (will be discharged):
--   - observe  : Maybe State → Behavior   (waiting for `Behavior`)
--   - decode   : List Byte → Maybe Program (byte-encoding of Instr)
--
-- DirectSimulation remains the lower-level proof tool used to discharge
-- arch-specific lemmas about `run`.
------------------------------------------------------------------------

module Once.Adequacy.CPU.X86-64 where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.String using (String)
open import Data.Nat using (ℕ)

open import Once.Denotation.Behavior      using (Behavior)
open import Once.Adequacy.CPU.Interface using (Byte; ArchSemantics)

import Once.CCC.Target.X86-64.Semantics as X64
import Once.CCC.Target.X86-64.Syntax    as X64S

-- Plan 0.54 Phase B / Option 2: the emit-and-continue trace over the REAL
-- x86-64 machine (arith blocks dispatched, Pure ⇒ no event), instanced from
-- the arch-generic `Arith.Backend.RunTraceCore`. This DERIVES `run-trace` from
-- `X64.run`'s step semantics, replacing the old opaque observable postulate.
open import Once.Arith.Backend.XInstr.Syntax as XI
import Once.Float.Arith as FA
open import Once.Float.Decimal using (round)
open import Once.Float.Dyadic using (binary32; binary64)
  using (XInstr; XReg; XScratch)
open import Once.Target.X86-64.PhysReg using (Reg; rsp; rdi)
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
open import Once.Arith.Machine.Shape using (InputPath; Side; Fst; Snd)
import Once.Arith.Backend.X86-64.RunTrace as RT
open X64 using (State; readReg; readMem)
open X64.State using (regs; memory)
import Once.Word as OnceWord
module W = OnceWord.Word64
open import Data.Nat using (_∸_; _*_; suc) renaming (_+_ to _+ℕ_)
open import Data.Maybe using (just; nothing)

------------------------------------------------------------------------
-- run-trace-x86-64 — DERIVED (no longer an opaque observable postulate).
-- It is `RunTraceCore.run-trace` at the x86-64 telescope; its remaining
-- ingredients are the named gaps below — smaller and more honest than the
-- monolithic observable they replace:
--   * `val-x86-64`        — the concrete XInstr arith interpreter (step 4:
--                           the real per-XInstr semantics over `State`).
--   * `arith-env-x86-64`  — the arith-block table (which `once_arith.block.*`
--                           label ↦ which block), extracted from the program
--                           (step 4: derive from `prog`'s emitted blocks).
--   * `ev-x86-64`         — label→SigOp resolution: the honest boundary axiom.
--   * `step-budget-x86-64`— adequate fuel (event-count ↦ machine steps), the
--                           SAME honest gap `FlatFromObs.flat-trace` carries.
------------------------------------------------------------------------

-- ── val-x86-64 — the concrete XInstr arith interpreter (Plan 0.54 rung B / B2.2).
-- DEFINED (was a postulate). Mirrors `exec-xinstr` (Arith.Backend.Correct, over
-- ArithAbsState) onto the REAL `X64.State`: registers via `readReg`, spill/reload
-- via `readMem` at `rsp − 8·(slot+1)`, arg-load by chasing the InputPath from
-- `rdi` through memory (Fst = +0, Snd = +8, matching CCC's pair layout). The
-- word ops are `Word64` — the SAME width `block-semM` uses (`X64.Word = W.Word = ℕ`),
-- so the value bridge `val = semM` (B2.3) is stated at one width.
-- `val i s r` is the value written to register `r` by `i`; `step-of` only reads
-- it at `r ∈ writes i`, so single-target instructions ignore `r`.
-- Exposed (not private): `scratch-addr` / `path-load` are the memory addresses
-- `val` reads, so the concrete↔abstract R-scratch / R-input correspondences
-- (Once.Adequacy.ArchCorrectness.ArithSimX86-64, B2.3) must be stated against
-- exactly them.
rd : State → XReg → X64.Word
rd s x = readReg (regs s) (arith-reg x)

def : Maybe X64.Word → X64.Word
def (just w) = w
def nothing  = 0

-- Scratch slots live at `8·slot(%rsp)` — ADDITIVE from the reserved frame base
-- (the post-prologue rsp), exactly like riscv64/x86-32's `8·slot(sp)`. Both
-- stacks grow downward (prologue `sub rsp, 8N`); addressing UP from the lowered
-- rsp keeps every slot inside the reserved frame [rsp, rsp+8N) and makes the
-- slot→address map unconditionally injective (see `sa-inj`, no frontier needed).
scratch-addr : State → XScratch → X64.Word
scratch-addr s sc = readReg (regs s) rsp +ℕ (8 * XScratch.slot sc)

side-off : Side → X64.Word
side-off Fst = 0
side-off Snd = 8

-- Chase the input path from an address through memory (each Fst/Snd hop
-- offsets then dereferences; the final leaf is the value at the address).
path-load-go : State → X64.Word → InputPath → X64.Word
path-load-go s addr []          = def (readMem (memory s) addr)
path-load-go s addr (sd ∷ rest) =
  path-load-go s (def (readMem (memory s) (addr +ℕ side-off sd))) rest

path-load : State → InputPath → X64.Word
path-load s p = path-load-go s (readReg (regs s) rdi) p

val-x86-64 : XInstr → X64.State → Reg → X64.Word
val-x86-64 (XI.Xmov-imm d z)          s _ = W.fromℤ z
val-x86-64 (XI.Xmov-rr d src)         s _ = rd s src
val-x86-64 (XI.Xmov-r-m sc src)       s _ = rd s src            -- writes = []; unused
val-x86-64 (XI.Xmov-m-r d sc)         s _ = def (readMem (memory s) (scratch-addr s sc))
val-x86-64 (XI.Xmov-arg d p)          s _ = path-load s p
val-x86-64 (XI.Xadd-rr d src)         s _ = rd s d W.⊕ rd s src
val-x86-64 (XI.Xsub-rr d src)         s _ = rd s d W.⊖ rd s src
val-x86-64 (XI.Ximul-rr d src)        s _ = rd s d W.⊗ rd s src
val-x86-64 (XI.Xdiv-rrr d a b)        s _ = rd s a W./ˢ rd s b
val-x86-64 (XI.Xrem-rrr d a b)        s _ = rd s a W.%ˢ rd s b
val-x86-64 (XI.Xdiv-safe-rrr d a b)   s _ = rd s a W./ˢ rd s b
val-x86-64 (XI.Xrem-safe-rrr d a b)   s _ = rd s a W.%ˢ rd s b
val-x86-64 (XI.Xshl-rri d src imm)    s _ = W.shlᵂ (rd s src) imm
val-x86-64 (XI.Xsdiv-pow2-rri d src imm) s _ = W.sdiv2ᵏ (rd s src) imm
val-x86-64 (XI.Xneg-r d)              s _ = W.⊝ (rd s d)
-- PLAN 0.75 F4: the INTENDED value of each float instruction, DEFINED — the
-- D117 pattern. That the real `addsd` / `fadd.d` computes it is the named
-- `float-xinstr-sim` residual in `ArithSimCore`, and the pins in
-- `Once.Float.Arith` against compiled C are what check it.
val-x86-64 (XI.Xfadd-rr d src)         s _ = FA.fadd binary64 (rd s d) (rd s src)
val-x86-64 (XI.Xfsub-rr d src)         s _ = FA.fsub binary64 (rd s d) (rd s src)
val-x86-64 (XI.Xfmul-rr d src)         s _ = FA.fmul binary64 (rd s d) (rd s src)
val-x86-64 (XI.Xfsubr-rr d src)        s _ = FA.fsub binary64 (rd s src) (rd s d)
val-x86-64 (XI.Xfneg-r d)              s _ = FA.fneg binary64 (rd s d)
val-x86-64 (XI.Xi2f-r d src)           s _ = FA.i2f binary64 (W.toℤ (rd s src))
val-x86-64 (XI.Xmov-fimm d dc)         s _ = round binary64 dc
val-x86-64 (XI.Xmov-farg d p)          s _ = path-load s p
val-x86-64 (XI.Xmov-out src)          s _ = rd s src

postulate
  step-budget-x86-64 : ℕ → ℕ
  ev-x86-64          : RT.EvExtractor val-x86-64
  arith-env-x86-64   : X64S.Program → RT.ArithEnv val-x86-64

run-trace-x86-64 : X64S.Program → X64.State → Behavior
run-trace-x86-64 prog s =
  RT.run-trace val-x86-64 step-budget-x86-64 ev-x86-64 (arith-env-x86-64 prog) prog s

postulate
  -- decode-x86-64 — POSTULATED. Concrete byte-encoder/decoder per the
  -- Intel SDM is significant work; left as a named gap for now.
  decode-x86-64 : List Byte → Maybe X64S.Program

  -- assemble-x86-64 — POSTULATED. GNU `as --target=x86-64` trust point;
  -- removed when the in-Agda assembler (B1) lands.
  assemble-x86-64 : String → List Byte

------------------------------------------------------------------------
-- The instance.
------------------------------------------------------------------------

arch-semantics : ArchSemantics
arch-semantics = record
  { Program      = X64S.Program
  ; State        = X64.State
  ; initialState = X64.initState
  ; run          = X64.run
  ; run-trace    = run-trace-x86-64
  ; decode       = decode-x86-64
  ; assemble     = assemble-x86-64
  }
