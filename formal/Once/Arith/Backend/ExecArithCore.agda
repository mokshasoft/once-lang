-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.ExecArithCore  (Plan 0.54 Phase B / Option 2)
--
-- The arch-generic BLOCK FOLD. Given the arch's per-instruction concrete step
-- `exec1` that preserves CCC state relative to a stack `frontier` (invariant,
-- since the stack pointer is CCC-owned), a whole arith block preserves CCC state.
--
-- The block carries a per-instruction `InFrame` witness — the SHARED "scratch is
-- in the reserved frame" invariant (`slot < required-scratch`). This is what
-- streamlines the archs: both x86-64 and riscv64 thread the same witness; x86-64
-- ignores it (its `rsp − N` addressing is below the frontier regardless),
-- riscv64 uses it (its `sp + offset` addressing needs the bound). One shape.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)

module Once.Arith.Backend.ExecArithCore
  {State : Set}
  (PreservesCCCState    : ℕ → State → State → Set)
  (preserves-state-refl : ∀ fr s → PreservesCCCState fr s s)
  (preserves-state-trans : ∀ {fr s₁ s₂ s₃} →
     PreservesCCCState fr s₁ s₂ → PreservesCCCState fr s₂ s₃ → PreservesCCCState fr s₁ s₃)
  (frontier : State → ℕ)
  (Valid    : State → ℕ → Set)
  (InFrame  : XInstr → Set)
  (exec1    : XInstr → State → State)
  (exec1-preserves : ∀ i s fr → frontier s ≡ fr → Valid s fr → InFrame i →
                     PreservesCCCState fr s (exec1 i s))
  (frontier-inv : ∀ i s fr → frontier s ≡ fr → Valid s fr → InFrame i → frontier (exec1 i s) ≡ fr)
  (valid-inv    : ∀ i s fr → frontier s ≡ fr → Valid s fr → InFrame i → Valid (exec1 i s) fr)
  where

exec-block : List XInstr → State → State
exec-block []       s = s
exec-block (i ∷ is) s = exec-block is (exec1 i s)

exec-block-preserves : ∀ is fr s → frontier s ≡ fr → Valid s fr → All InFrame is →
                       PreservesCCCState fr s (exec-block is s)
exec-block-preserves []       fr s _   _   _           = preserves-state-refl fr s
exec-block-preserves (i ∷ is) fr s f≡ vld (inf ∷ infs) =
  preserves-state-trans (exec1-preserves i s fr f≡ vld inf)
    (exec-block-preserves is fr (exec1 i s)
       (frontier-inv i s fr f≡ vld inf) (valid-inv i s fr f≡ vld inf) infs)
