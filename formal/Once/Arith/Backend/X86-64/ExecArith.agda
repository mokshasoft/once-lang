-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.ExecArith  (Plan 0.54 Phase B / Option 2)
--
-- Concrete interpretation of the arith `XInstr` over the SHARED `X64.State`
-- (unifying arith onto the real machine), and the proof that each step — hence
-- a whole block — preserves CCC state.
--
--   * REGISTER effect: writes the footprint `Confine.writes i` (via the real
--     `writeReg`), captured by `Preserve.step-of`. Values come from the (real,
--     but here abstract) instruction value-semantics `val` — irrelevant to
--     preservation (value-correctness is Phase A `block-correct`).
--   * MEMORY effect: only spill (`Xmov-r-m`) writes memory, to a scratch slot
--     BELOW `%rsp`; every other instruction leaves memory untouched.
--
-- So `exec-arith-instr` preserves the 7 CCC registers (`step-of-preserves`) and
-- all CCC memory at/above `%rsp` (`writeMem-below-preserves`), and blocks compose
-- via `preserves-state-trans`. Requires `0 < rsp` (a valid stack pointer) for the
-- scratch address to sit below the frontier.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.ExecArith where

open import Data.Nat using (ℕ; zero; suc; _*_; _∸_; _<_; _≤_; s≤s; z≤n; z<s)
open import Data.Nat.Properties using (m∸n≤m)
open import Data.List using (List; []; _∷_)

-- `0 < m → 0 < n → m ∸ n < m` (unconditional: if `n > m` the monus truncates to
-- 0 < m; if `n ≤ m` it drops ≥1). stdlib has only the `n ≤ m` variant.
sub-lt : ∀ {m n} → 0 < m → 0 < n → m ∸ n < m
sub-lt {suc m} {suc n} _ _ = s≤s (m∸n≤m m n)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.X86-64.Emit using (arith-reg)
open import Once.CCC.Target.X86-64.Semantics
  using (State; mkstate; RegFile; Memory; readReg; writeMem; Word)
open import Once.Target.X86-64.PhysReg using (Reg; rsp)
open State
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Once.Arith.Backend.X86-64.Preserve using (step-of; step-of-preserves; AgreeCCC; a-rsp)
open import Once.Arith.Backend.X86-64.MemPreserve using (AgreeMemFrom; writeMem-below-preserves)
open import Once.Arith.Backend.X86-64.StatePreserve
  using (PreservesCCCState; mkPresState; AgreeMemFrom-refl; preserves-state-refl;
         preserves-state-trans)

------------------------------------------------------------------------
-- The scratch slot address: `8·(slot+1)` bytes BELOW the entry %rsp.
------------------------------------------------------------------------

scratch-addr : State → XScratch → Word
scratch-addr s sc = readReg (regs s) rsp ∸ (8 * suc (XScratch.slot sc))

-- Memory effect: only spill writes memory; everything else is a no-op on memory.
mem-effect : XInstr → State → Memory
mem-effect (Xmov-r-m sc src) s =
  writeMem (memory s) (scratch-addr s sc) (readReg (regs s) (arith-reg src))
mem-effect _ s = memory s

------------------------------------------------------------------------
-- Concrete step, parameterised by the (real) instruction value-semantics.
------------------------------------------------------------------------

module _ (val : XInstr → State → Reg → Word) where

  exec-arith-instr : XInstr → State → State
  exec-arith-instr i s =
    mkstate (step-of i (val i s) (regs s)) (mem-effect i s) (flags s) (suc (pc s)) (halted s)

  -- The memory half preserves everything at/above %rsp.
  --   * non-spill: `mem-effect = memory s`, so agreement is reflexive.
  --   * spill: writes at `rsp ∸ 8·(slot+1) < rsp` (needs `0 < rsp`), so
  --     `writeMem-below-preserves` applies.
  mem-preserves : ∀ i s → 0 < readReg (regs s) rsp →
                  AgreeMemFrom (readReg (regs s) rsp) (memory s) (mem-effect i s)
  mem-preserves (Xmov-imm _ _)      s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xmov-rr _ _)       s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xmov-r-m sc src)   s 0<r =
    writeMem-below-preserves (memory s) (readReg (regs s) rsp) (scratch-addr s sc)
      (readReg (regs s) (arith-reg src)) (sub-lt 0<r z<s)
  mem-preserves (Xmov-m-r _ _)      s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xmov-arg _ _)      s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xadd-rr _ _)       s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xsub-rr _ _)       s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Ximul-rr _ _)      s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xneg-r _)          s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xdiv-rrr _ _ _)    s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xrem-rrr _ _ _)    s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xdiv-safe-rrr _ _ _) s _ = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xrem-safe-rrr _ _ _) s _ = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xshl-rri _ _ _)    s _   = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xsdiv-pow2-rri _ _ _) s _ = AgreeMemFrom-refl _ (memory s)
  mem-preserves (Xmov-out _)        s _   = AgreeMemFrom-refl _ (memory s)

  -- One arith step preserves CCC state (registers via step-of, memory above).
  exec-arith-instr-preserves : ∀ i s → 0 < readReg (regs s) rsp →
                               PreservesCCCState (readReg (regs s) rsp) s (exec-arith-instr i s)
  exec-arith-instr-preserves i s 0<r =
    mkPresState (step-of-preserves i (val i s) (regs s)) (mem-preserves i s 0<r)

  ------------------------------------------------------------------------
  -- Block fold: run an arith block (List XInstr) over the concrete State.
  -- `%rsp` is CCC-owned, so every step preserves it (`a-rsp`) — the frontier
  -- is invariant, so the whole block preserves CCC state.
  ------------------------------------------------------------------------

  exec-arith-block : List XInstr → State → State
  exec-arith-block []       s = s
  exec-arith-block (i ∷ is) s = exec-arith-block is (exec-arith-instr i s)

  -- `%rsp` unchanged after a step (it is `ccc`, so `a-rsp` of `regs≈`).
  step-rsp : ∀ i s → 0 < readReg (regs s) rsp →
             readReg (regs (exec-arith-instr i s)) rsp ≡ readReg (regs s) rsp
  step-rsp i s 0<r = sym (a-rsp (PreservesCCCState.regs≈ (exec-arith-instr-preserves i s 0<r)))

  exec-arith-block-preserves : ∀ is fr s → readReg (regs s) rsp ≡ fr → 0 < fr →
                               PreservesCCCState fr s (exec-arith-block is s)
  exec-arith-block-preserves []       fr s _      0<fr = preserves-state-refl fr s
  exec-arith-block-preserves (i ∷ is) fr s rsp≡fr 0<fr =
    preserves-state-trans step1 rest
    where
      0<r : 0 < readReg (regs s) rsp
      0<r = subst (0 <_) (sym rsp≡fr) 0<fr
      step1 : PreservesCCCState fr s (exec-arith-instr i s)
      step1 = subst (λ f → PreservesCCCState f s (exec-arith-instr i s)) rsp≡fr
                    (exec-arith-instr-preserves i s 0<r)
      rsp'≡fr : readReg (regs (exec-arith-instr i s)) rsp ≡ fr
      rsp'≡fr = trans (step-rsp i s 0<r) rsp≡fr
      rest : PreservesCCCState fr (exec-arith-instr i s)
                               (exec-arith-block is (exec-arith-instr i s))
      rest = exec-arith-block-preserves is fr (exec-arith-instr i s) rsp'≡fr 0<fr
