-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.ExecArith  (Plan 0.54 Phase B / Option 2)
--
-- x86-64 instance of the arch-generic block fold (`ExecArithCore`): provides the
-- concrete per-instruction step `exec1` over the real X64.State (register writes
-- via `step-of`, spill via `writeMem` at `rsp − N`), the frontier `= rsp`, the
-- `0 < rsp` validity, and the three step lemmas. The block fold + its CCC-state
-- preservation come from the core, re-exported as `exec-arith-block[-preserves]`.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.ExecArith where

open import Data.Nat using (ℕ; suc; _*_; _∸_; _<_; s≤s; z<s)
open import Data.Nat.Properties using (m∸n≤m)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

-- `0 < m → 0 < n → m ∸ n < m` (unconditional; stdlib has only the `n ≤ m` variant).
sub-lt : ∀ {m n} → 0 < m → 0 < n → m ∸ n < m
sub-lt {suc m} {suc n} _ _ = s≤s (m∸n≤m m n)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
open import Once.CCC.Target.X86-64.Semantics
  using (State; mkstate; RegFile; Memory; readReg; writeMem; Word)
open import Once.Target.X86-64.PhysReg using (Reg; rsp)
open State
open import Once.Arith.Backend.X86-64.Preserve using (step-of; step-of-preserves; a-rsp)
open import Once.Arith.Backend.X86-64.MemPreserve using (AgreeMemFrom; AgreeMemFrom-refl; writeMem-below-preserves)
open import Once.Arith.Backend.X86-64.StatePreserve
  using (PreservesCCCState; mkPresState; preserves-state-refl; preserves-state-trans)

-- Scratch slot `8·(slot+1)` bytes BELOW %rsp.
scratch-addr : State → XScratch → Word
scratch-addr s sc = readReg (regs s) rsp ∸ (8 * suc (XScratch.slot sc))

-- Only spill writes memory; everything else leaves memory untouched.
mem-effect : XInstr → State → Memory
mem-effect (Xmov-r-m sc src) s =
  writeMem (memory s) (scratch-addr s sc) (readReg (regs s) (arith-reg src))
mem-effect _ s = memory s

module _ (val : XInstr → State → Reg → Word) where

  exec1 : XInstr → State → State
  exec1 i s = mkstate (step-of i (val i s) (regs s)) (mem-effect i s) (flags s) (suc (pc s)) (halted s)

  frontier : State → ℕ
  frontier s = readReg (regs s) rsp

  Valid : State → ℕ → Set
  Valid _ fr = 0 < fr

  -- Memory half: scratch (`< rsp = fr`) preserves memory ≥ fr; else reflexive.
  mem-preserves : ∀ i s fr → frontier s ≡ fr → 0 < fr →
                  AgreeMemFrom fr (memory s) (mem-effect i s)
  mem-preserves (Xmov-r-m sc src) s fr refl 0<fr =
    writeMem-below-preserves (memory s) fr (scratch-addr s sc)
      (readReg (regs s) (arith-reg src)) (sub-lt 0<fr z<s)
  mem-preserves (Xmov-imm _ _)      s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xmov-rr _ _)       s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xmov-m-r _ _)      s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xmov-arg _ _)      s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xadd-rr _ _)       s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xsub-rr _ _)       s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Ximul-rr _ _)      s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xneg-r _)          s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xdiv-rrr _ _ _)    s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xrem-rrr _ _ _)    s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xdiv-safe-rrr _ _ _) s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xrem-safe-rrr _ _ _) s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xshl-rri _ _ _)    s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xsdiv-pow2-rri _ _ _) s fr _ _ = AgreeMemFrom-refl fr (memory s)
  mem-preserves (Xmov-out _)        s fr _ _ = AgreeMemFrom-refl fr (memory s)

  exec1-preserves : ∀ i s fr → frontier s ≡ fr → Valid s fr → PreservesCCCState fr s (exec1 i s)
  exec1-preserves i s fr f≡ 0<fr =
    mkPresState (step-of-preserves i (val i s) (regs s)) (mem-preserves i s fr f≡ 0<fr)

  -- %rsp is CCC-owned, so `exec1` preserves the frontier (`a-rsp`).
  frontier-inv : ∀ i s fr → frontier s ≡ fr → Valid s fr → frontier (exec1 i s) ≡ fr
  frontier-inv i s fr f≡ _ = trans (sym (a-rsp (step-of-preserves i (val i s) (regs s)))) f≡

  valid-inv : ∀ i s fr → frontier s ≡ fr → Valid s fr → Valid (exec1 i s) fr
  valid-inv i s fr _ 0<fr = 0<fr

  open import Once.Arith.Backend.ExecArithCore
    PreservesCCCState preserves-state-refl preserves-state-trans
    frontier Valid exec1 exec1-preserves frontier-inv valid-inv
    public renaming (exec-block to exec-arith-block; exec-block-preserves to exec-arith-block-preserves)
