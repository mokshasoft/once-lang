-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.ExecArith  (Plan 0.54 Phase B / Option 2)
--
-- x86-64 instance of the generic block fold + memory effect. Now ALIGNED with
-- riscv64/x86-32: the prologue lowers `%rsp` (`sub $N, %rsp`) and scratch is
-- addressed as `%rsp + 8·slot` — ADDITIVE, inside the reserved frame
-- [rsp, rsp+N). So it USES the shared in-frame witness `InFrame (Xmov-r-m sc _)
-- = 8·slot < N` (`N = 8·required-scratch`), the frontier is `rsp + N` (= the
-- entry rsp), and `scratch-below` discharges `rsp + 8·slot < rsp + N` from the
-- slot bound (`+-monoʳ-<`). The abstract machine has no stack-growth direction;
-- this arch instance picks additive addressing, making the slot→address map
-- unconditionally injective (see ArithSimX86-64's `sa-inj`, no frontier bound).
-- `mem-effect`/`mem-preserves` come from MemEffectCore, the block fold from
-- ExecArithCore.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.ExecArith where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc; _*_; _+_; _<_)
open import Data.Nat.Properties using (+-monoʳ-<)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

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

-- The block's per-instruction in-frame witness: a spill's slot fits the reserved
-- frame `N`; other instructions carry no obligation.
InFrame : ℕ → XInstr → Set
InFrame N (Xmov-r-m sc _) = 8 * XScratch.slot sc < N
InFrame N _               = ⊤

module _ (val : XInstr → State → Reg → Word) (N : ℕ) where

  scratch-addr : State → XScratch → Word
  scratch-addr s sc = readReg (regs s) rsp + (8 * XScratch.slot sc)

  frontier : State → ℕ
  frontier s = readReg (regs s) rsp + N

  scratch-below : ∀ s sc (src : XReg) fr → frontier s ≡ fr → 0 < fr → InFrame N (Xmov-r-m sc src) →
                  scratch-addr s sc < fr
  scratch-below s sc src fr f≡ _ inf rewrite sym f≡ = +-monoʳ-< (readReg (regs s) rsp) inf

  open import Once.Arith.Backend.MemEffectCore
    {State} {Memory} {RegFile} {Reg}
    memory regs readReg writeMem AgreeMemFrom AgreeMemFrom-refl writeMem-below-preserves
    arith-reg scratch-addr frontier (InFrame N) scratch-below

  exec1 : XInstr → State → State
  exec1 i s = mkstate (step-of i (val i s) (regs s)) (mem-effect i s) (flags s) (suc (pc s)) (halted s)

  Valid : State → ℕ → Set
  Valid _ fr = 0 < fr

  exec1-preserves : ∀ i s fr → frontier s ≡ fr → Valid s fr → InFrame N i → PreservesCCCState fr s (exec1 i s)
  exec1-preserves i s fr f≡ 0<fr inf =
    mkPresState (step-of-preserves i (val i s) (regs s)) (mem-preserves i s fr f≡ 0<fr inf)

  frontier-inv : ∀ i s fr → frontier s ≡ fr → Valid s fr → InFrame N i → frontier (exec1 i s) ≡ fr
  frontier-inv i s fr f≡ _ _ =
    trans (cong (_+ N) (sym (a-rsp (step-of-preserves i (val i s) (regs s))))) f≡

  valid-inv : ∀ i s fr → frontier s ≡ fr → Valid s fr → InFrame N i → Valid (exec1 i s) fr
  valid-inv i s fr _ 0<fr _ = 0<fr

  open import Once.Arith.Backend.ExecArithCore
    PreservesCCCState preserves-state-refl preserves-state-trans
    frontier Valid (InFrame N) exec1 exec1-preserves frontier-inv valid-inv
    public renaming (exec-block to exec-arith-block; exec-block-preserves to exec-arith-block-preserves)
