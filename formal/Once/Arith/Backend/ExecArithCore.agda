-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.ExecArithCore  (Plan 0.54 Phase B / Option 2)
--
-- The arch-generic BLOCK FOLD: given the arch's per-instruction concrete step
-- `exec1` that preserves CCC state relative to a stack `frontier` (invariant
-- across the step because the stack pointer is CCC-owned), a whole arith block
-- preserves CCC state. This absorbs the "accidental" per-arch differences —
-- x86-64's fixed `rsp` / `-N(%rsp)` vs riscv64's lowered `sp` / `sp+offset` —
-- into the arch-provided `frontier` + `exec1-preserves`/`frontier-inv`; the
-- fold itself is identical everywhere.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)

module Once.Arith.Backend.ExecArithCore
  {State : Set}
  (PreservesCCCState    : ℕ → State → State → Set)
  (preserves-state-refl : ∀ fr s → PreservesCCCState fr s s)
  (preserves-state-trans : ∀ {fr s₁ s₂ s₃} →
     PreservesCCCState fr s₁ s₂ → PreservesCCCState fr s₂ s₃ → PreservesCCCState fr s₁ s₃)
  (frontier : State → ℕ)                          -- the CCC/scratch boundary (e.g. entry rsp)
  (Valid    : State → ℕ → Set)                     -- arch precondition at a fixed frontier
  (exec1    : XInstr → State → State)              -- the arch's concrete per-instruction step
  (exec1-preserves : ∀ i s fr → frontier s ≡ fr → Valid s fr →
                     PreservesCCCState fr s (exec1 i s))
  (frontier-inv : ∀ i s fr → frontier s ≡ fr → Valid s fr → frontier (exec1 i s) ≡ fr)
  (valid-inv    : ∀ i s fr → frontier s ≡ fr → Valid s fr → Valid (exec1 i s) fr)
  where

exec-block : List XInstr → State → State
exec-block []       s = s
exec-block (i ∷ is) s = exec-block is (exec1 i s)

exec-block-preserves : ∀ is fr s → frontier s ≡ fr → Valid s fr →
                       PreservesCCCState fr s (exec-block is s)
exec-block-preserves []       fr s _    _  = preserves-state-refl fr s
exec-block-preserves (i ∷ is) fr s f≡ vld =
  preserves-state-trans (exec1-preserves i s fr f≡ vld)
    (exec-block-preserves is fr (exec1 i s) (frontier-inv i s fr f≡ vld) (valid-inv i s fr f≡ vld))
