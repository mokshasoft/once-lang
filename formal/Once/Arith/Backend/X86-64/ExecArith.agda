-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.ExecArith  (Plan 0.54 Phase B / Option 2)
--
-- x86-64 instance of the generic block fold + memory effect. Provides the
-- arch base: `scratch-addr = rsp − 8·(slot+1)`, `frontier = rsp`, and
-- `scratch-below` (discharged from `0 < rsp` — x86-64 IGNORES the shared
-- in-frame witness, `InFrame ≡ ⊤`, since subtract-addressing is below the
-- frontier for any slot). `mem-effect`/`mem-preserves` come from MemEffectCore,
-- the block fold from ExecArithCore.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.ExecArith where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc; _*_; _∸_; _<_; s≤s; z<s)
open import Data.Nat.Properties using (m∸n≤m)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

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

-- Every arith block trivially satisfies the (vacuous) x86-64 in-frame witness.
all-InFrame : ∀ (is : List XInstr) → All (λ _ → ⊤) is
all-InFrame []       = []
all-InFrame (_ ∷ is) = tt ∷ all-InFrame is

module _ (val : XInstr → State → Reg → Word) where

  scratch-addr : State → XScratch → Word
  scratch-addr s sc = readReg (regs s) rsp ∸ (8 * suc (XScratch.slot sc))

  frontier : State → ℕ
  frontier s = readReg (regs s) rsp

  scratch-below : ∀ s sc (src : XReg) fr → frontier s ≡ fr → 0 < fr → ⊤ → scratch-addr s sc < fr
  scratch-below s sc src fr f≡ 0<fr _ rewrite f≡ = sub-lt 0<fr z<s

  open import Once.Arith.Backend.MemEffectCore
    {State} {Memory} {RegFile} {Reg}
    memory regs readReg writeMem AgreeMemFrom AgreeMemFrom-refl writeMem-below-preserves
    arith-reg scratch-addr frontier (λ _ → ⊤) scratch-below

  exec1 : XInstr → State → State
  exec1 i s = mkstate (step-of i (val i s) (regs s)) (mem-effect i s) (flags s) (suc (pc s)) (halted s)

  Valid : State → ℕ → Set
  Valid _ fr = 0 < fr

  exec1-preserves : ∀ i s fr → frontier s ≡ fr → Valid s fr → ⊤ → PreservesCCCState fr s (exec1 i s)
  exec1-preserves i s fr f≡ 0<fr inf =
    mkPresState (step-of-preserves i (val i s) (regs s)) (mem-preserves i s fr f≡ 0<fr inf)

  frontier-inv : ∀ i s fr → frontier s ≡ fr → Valid s fr → ⊤ → frontier (exec1 i s) ≡ fr
  frontier-inv i s fr f≡ _ _ = trans (sym (a-rsp (step-of-preserves i (val i s) (regs s)))) f≡

  valid-inv : ∀ i s fr → frontier s ≡ fr → Valid s fr → ⊤ → Valid (exec1 i s) fr
  valid-inv i s fr _ 0<fr _ = 0<fr

  open import Once.Arith.Backend.ExecArithCore
    PreservesCCCState preserves-state-refl preserves-state-trans
    frontier Valid (λ _ → ⊤) exec1 exec1-preserves frontier-inv valid-inv
    public renaming (exec-block to exec-arith-block; exec-block-preserves to exec-arith-block-preserves)
