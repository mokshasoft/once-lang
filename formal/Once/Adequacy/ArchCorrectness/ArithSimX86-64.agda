-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimX86-64  (Plan 0.54 rung B / B2.3)
--
-- The x86-64 INSTANCE of the arch-generic arith concrete↔abstract simulation
-- (`ArithSimCore.Core`). All the content — R / R-scratch / R-input, the
-- per-instruction step, Rf-sim, the Rf assembly, `result-correct` / `R-init`,
-- and the `arith-block-correct` capstone — lives in the core and is re-exported
-- here (`open Core … public`). This module supplies only the x86-64 surface:
--   * the concrete machine (`X64.State` / readReg / writeReg / readMem / def /
--     scratch-addr / path-load / val-x86-64's exec1 & block fold);
--   * `rf-other` — the frame proof (reading a non-target arith reg is unchanged),
--     which is where x86-64's idiv rax/rdx clobber is PEELED (`peel-io2`);
--   * the 14 `rt-*` read-target facts (target read-back = value), via the arith
--     window frame lemmas (`val-x86-64` mirrors `exec-xinstr`, so the values are
--     definitional and each fact is one frame-lemma application).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimX86-64 where

open import Data.Nat using (ℕ; _∸_; _*_; suc; _≡ᵇ_)
open import Data.Nat.Properties using (≡⇒≡ᵇ)
open import Data.Bool using (true; false; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch)
open XI using (XR0; XR1)
open import Once.Target.X86-64.PhysReg using (Reg; rax; rdx; rsp; r8; r9)
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
import Once.CCC.Target.X86-64.Semantics as X64
open X64 using (State; readReg; writeReg; readMem; writeMem; RegFile; Word)
open X64.State using (regs; memory)
open import Once.Adequacy.CPU.X86-64 using (val-x86-64; scratch-addr; def; path-load)
import Once.Arith.Backend.X86-64.ExecArith as EA
open import Once.Arith.Backend.X86-64.Preserve using (step-of; step-of-preserves; a-rsp)
open import Once.Arith.Backend.X86-64.MemPreserve using (readMem-writeMem-other)
open import Once.Adequacy.ArchCorrectness.ArithSimCore using (tgt; NonSpill; module Core)

------------------------------------------------------------------------
-- Frame lemmas — the 2×2 analysis on the arith window (r8/r9), plus the io
-- clobbers rax/rdx. `val-x86-64` writes single-target instructions to
-- `arith-reg d`, div/rem additionally to rax/rdx, sdiv/arg to rax, out to rax.
------------------------------------------------------------------------

readReg-wr-arith-other : ∀ (rf : RegFile) (x y : XReg) (v : Word)
                       → ¬ (x ≡ y)
                       → readReg (writeReg rf (arith-reg x) v) (arith-reg y) ≡ readReg rf (arith-reg y)
readReg-wr-arith-other rf XR0 XR0 v ¬eq = ⊥-elim (¬eq refl)
readReg-wr-arith-other rf XR0 XR1 v _ = refl
readReg-wr-arith-other rf XR1 XR0 v _ = refl
readReg-wr-arith-other rf XR1 XR1 v ¬eq = ⊥-elim (¬eq refl)

readReg-wr-arith-same : ∀ (rf : RegFile) (x : XReg) (v : Word)
                      → readReg (writeReg rf (arith-reg x) v) (arith-reg x) ≡ v
readReg-wr-arith-same rf XR0 v = refl
readReg-wr-arith-same rf XR1 v = refl

readReg-wr-rax-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                     → readReg (writeReg rf rax v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-rax-arith rf XR0 v = refl
readReg-wr-rax-arith rf XR1 v = refl

readReg-wr-rdx-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                     → readReg (writeReg rf rdx v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-rdx-arith rf XR0 v = refl
readReg-wr-rdx-arith rf XR1 v = refl

readReg-wr-rax-same : ∀ (rf : RegFile) (v : Word) → readReg (writeReg rf rax v) rax ≡ v
readReg-wr-rax-same rf v = refl

-- Peel the rax+rdx clobbers (div/rem write [arith-reg d, rax, rdx]).
peel-io2 : ∀ (rf : RegFile) (x : XReg) (v : Word)
         → readReg (writeReg (writeReg rf rax v) rdx v) (arith-reg x) ≡ readReg rf (arith-reg x)
peel-io2 rf x v = trans (readReg-wr-rdx-arith (writeReg rf rax v) x v) (readReg-wr-rax-arith rf x v)

------------------------------------------------------------------------
-- rr / mem — the core's register / memory readers.
------------------------------------------------------------------------

rr : State → Reg → ℕ
rr s r = readReg (regs s) r

mem : State → ℕ → Maybe ℕ
mem s a = readMem (memory s) a

------------------------------------------------------------------------
-- rf-other — non-target arith registers are unchanged. The `no`-hypothesis
-- `h` gives `¬ (x ≡ d)` via `h d refl`; div/rem/sdiv/arg peel their io writes.
------------------------------------------------------------------------

¬d≡x : ∀ (d x : XReg) → (∀ d' → just d ≡ just d' → ¬ (x ≡ d')) → ¬ (d ≡ x)
¬d≡x d x h d≡x = h d refl (sym d≡x)

-- The value instruction `i` writes to its arith target (val ignores the reg
-- arg, so any reg gives the same value definitionally). Supplied EXPLICITLY to
-- the frame lemmas: the frame conclusion discards the value, so it cannot be
-- inferred through the (unreduced) `regs (e1 i s)` neutral.
V : XInstr → State → Word
V i s = val-x86-64 i s rax

rf-other : ∀ i s x → (∀ d → tgt i ≡ just d → ¬ (x ≡ d))
         → rr (EA.exec1 val-x86-64 i s) (arith-reg x) ≡ rr s (arith-reg x)
rf-other (XI.Xmov-imm d z) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-imm d z) s) (¬d≡x d x h)
rf-other (XI.Xmov-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-rr d src) s) (¬d≡x d x h)
rf-other (XI.Xmov-m-r d sc) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-m-r d sc) s) (¬d≡x d x h)
rf-other (XI.Xmov-arg d p) s x h =
  trans (readReg-wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p) s)) x (V (XI.Xmov-arg d p) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xmov-arg d p) s) (¬d≡x d x h))
rf-other (XI.Xadd-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xadd-rr d src) s) (¬d≡x d x h)
rf-other (XI.Xsub-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xsub-rr d src) s) (¬d≡x d x h)
rf-other (XI.Ximul-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Ximul-rr d src) s) (¬d≡x d x h)
rf-other (XI.Xneg-r d) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xneg-r d) s) (¬d≡x d x h)
rf-other (XI.Xshl-rri d src imm) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xshl-rri d src imm) s) (¬d≡x d x h)
rf-other (XI.Xdiv-rrr d a b) s x h =
  trans (peel-io2 (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-rrr d a b) s)) x (V (XI.Xdiv-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xrem-rrr d a b) s x h =
  trans (peel-io2 (writeReg (regs s) (arith-reg d) (V (XI.Xrem-rrr d a b) s)) x (V (XI.Xrem-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xrem-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xdiv-safe-rrr d a b) s x h =
  trans (peel-io2 (writeReg (regs s) (arith-reg d) (V (XI.Xdiv-safe-rrr d a b) s)) x (V (XI.Xdiv-safe-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-safe-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xrem-safe-rrr d a b) s x h =
  trans (peel-io2 (writeReg (regs s) (arith-reg d) (V (XI.Xrem-safe-rrr d a b) s)) x (V (XI.Xrem-safe-rrr d a b) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xrem-safe-rrr d a b) s) (¬d≡x d x h))
rf-other (XI.Xsdiv-pow2-rri d src imm) s x h =
  trans (readReg-wr-rax-arith (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) x (V (XI.Xsdiv-pow2-rri d src imm) s))
        (readReg-wr-arith-other (regs s) d x (V (XI.Xsdiv-pow2-rri d src imm) s) (¬d≡x d x h))
rf-other (XI.Xmov-r-m sc src) s x h = refl
rf-other (XI.Xmov-out src) s x h = readReg-wr-rax-arith (regs s) x (V (XI.Xmov-out src) s)

------------------------------------------------------------------------
-- Memory-effect primitives (drive the core's scratch-frame).
------------------------------------------------------------------------

-- A write reads back at its own address.
readMem-writeMem-same : ∀ m addr val → readMem (writeMem m addr val) addr ≡ just val
readMem-writeMem-same m addr val with addr ≡ᵇ addr in eq
... | true  = refl
... | false = ⊥-elim (subst T eq (≡⇒≡ᵇ addr addr refl))

-- scratch-addr is step-invariant: arith never writes rsp (CCC-preserved).
sa-inv : ∀ i s sc → scratch-addr (EA.exec1 val-x86-64 i s) sc ≡ scratch-addr s sc
sa-inv i s sc = cong (λ r → r ∸ (8 * suc (XScratch.slot sc)))
                     (sym (a-rsp (step-of-preserves i (val-x86-64 i s) (regs s))))

-- Only spill writes memory; the other 15 leave memory untouched.
mem-keep : ∀ i s addr → NonSpill i → readMem (memory (EA.exec1 val-x86-64 i s)) addr ≡ readMem (memory s) addr
mem-keep (XI.Xmov-imm _ _)         s addr _ = refl
mem-keep (XI.Xmov-rr _ _)          s addr _ = refl
mem-keep (XI.Xmov-m-r _ _)         s addr _ = refl
mem-keep (XI.Xmov-arg _ _)         s addr _ = refl
mem-keep (XI.Xadd-rr _ _)          s addr _ = refl
mem-keep (XI.Xsub-rr _ _)          s addr _ = refl
mem-keep (XI.Ximul-rr _ _)         s addr _ = refl
mem-keep (XI.Xneg-r _)             s addr _ = refl
mem-keep (XI.Xshl-rri _ _ _)       s addr _ = refl
mem-keep (XI.Xdiv-rrr _ _ _)       s addr _ = refl
mem-keep (XI.Xrem-rrr _ _ _)       s addr _ = refl
mem-keep (XI.Xdiv-safe-rrr _ _ _)  s addr _ = refl
mem-keep (XI.Xrem-safe-rrr _ _ _)  s addr _ = refl
mem-keep (XI.Xsdiv-pow2-rri _ _ _) s addr _ = refl
mem-keep (XI.Xmov-out _)           s addr _ = refl

mem-spill-hit : ∀ sc' src s
              → readMem (memory (EA.exec1 val-x86-64 (XI.Xmov-r-m sc' src) s)) (scratch-addr s sc')
                  ≡ just (readReg (regs s) (arith-reg src))
mem-spill-hit sc' src s = readMem-writeMem-same (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src))

mem-spill-miss : ∀ sc' src s addr → ¬ (addr ≡ scratch-addr s sc')
               → readMem (memory (EA.exec1 val-x86-64 (XI.Xmov-r-m sc' src) s)) addr ≡ readMem (memory s) addr
mem-spill-miss sc' src s addr ne =
  readMem-writeMem-other (memory s) (scratch-addr s sc') (readReg (regs s) (arith-reg src)) addr ne

-- scratch-addr injectivity in the slot. x86-64's SUBTRACTIVE addressing
-- (rsp − 8·(slot+1)) is injective only WITHIN the reserved frame (0 ≤ addr),
-- i.e. given the frontier bound `8·(slot+1) ≤ rsp`. That bound is the honest
-- residual — it needs the block's frontier well-formedness threaded (riscv's
-- additive `sp + 8·slot` is unconditionally injective; see ArithSimRiscV64).
postulate
  sa-inj : ∀ s sc sc' → ¬ (XScratch.slot sc ≡ XScratch.slot sc') → ¬ (scratch-addr s sc ≡ scratch-addr s sc')

------------------------------------------------------------------------
-- The instance. `rt-*` facts are passed inline (types from the telescope):
-- single-write = one `readReg-wr-arith-same`; div/rem peel rax/rdx; sdiv/arg
-- peel rax; out reads rax back. Every `eb`/`def-just` is `refl`.
------------------------------------------------------------------------

open Core
  State Reg
  rr mem
  arith-reg rax
  def (λ _ → refl)
  scratch-addr path-load
  (EA.exec1 val-x86-64) (EA.exec-arith-block val-x86-64)
  (λ _ → refl) (λ _ _ _ → refl)
  sa-inv sa-inj mem-keep mem-spill-hit mem-spill-miss
  rf-other
  -- rt-mov-imm rt-mov-rr rt-reload
  (λ d z s   → readReg-wr-arith-same (regs s) d _)
  (λ d src s  → readReg-wr-arith-same (regs s) d _)
  (λ d sc s   → readReg-wr-arith-same (regs s) d _)
  -- rt-arg (peel rax)
  (λ d p s    → trans (readReg-wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _)
                      (readReg-wr-arith-same (regs s) d _))
  -- rt-add rt-sub rt-imul
  (λ d src s  → readReg-wr-arith-same (regs s) d _)
  (λ d src s  → readReg-wr-arith-same (regs s) d _)
  (λ d src s  → readReg-wr-arith-same (regs s) d _)
  -- rt-neg rt-shl
  (λ d s      → readReg-wr-arith-same (regs s) d _)
  (λ d src imm s → readReg-wr-arith-same (regs s) d _)
  -- rt-div rt-rem rt-div-safe rt-rem-safe (peel rax/rdx)
  (λ d a b s  → trans (peel-io2 (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
  (λ d a b s  → trans (peel-io2 (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
  (λ d a b s  → trans (peel-io2 (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
  (λ d a b s  → trans (peel-io2 (writeReg (regs s) (arith-reg d) _) d _) (readReg-wr-arith-same (regs s) d _))
  -- rt-sdiv (peel rax)
  (λ d src imm s → trans (readReg-wr-rax-arith (writeReg (regs s) (arith-reg d) _) d _)
                         (readReg-wr-arith-same (regs s) d _))
  -- rt-out
  (λ src s    → readReg-wr-rax-same (regs s) _)
  public
