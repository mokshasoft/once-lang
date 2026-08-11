-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.StatePreserveCore  (Plan 0.54 Phase B / Option 2)
--
-- Arch-generic unified CCC-state preservation: agree on the CCC registers AND
-- on memory at/above the entry stack frontier. Parameterised by the arch's
-- `regs`/`memory` projections and its register/memory agreement relations
-- (with refl/trans). Composes, so a whole block preserves CCC state.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module Once.Arith.Backend.StatePreserveCore
  {RegFile Memory State : Set}
  (regs               : State → RegFile)
  (memory             : State → Memory)
  (AgreeCCC           : RegFile → RegFile → Set)
  (agree-refl-ccc     : ∀ rf → AgreeCCC rf rf)
  (AgreeCCC-trans     : ∀ {a b c} → AgreeCCC a b → AgreeCCC b c → AgreeCCC a c)
  (AgreeMemFrom       : ℕ → Memory → Memory → Set)
  (AgreeMemFrom-refl  : ∀ fr m → AgreeMemFrom fr m m)
  (AgreeMemFrom-trans : ∀ {fr m₁ m₂ m₃} →
                        AgreeMemFrom fr m₁ m₂ → AgreeMemFrom fr m₂ m₃ → AgreeMemFrom fr m₁ m₃)
  where

record PreservesCCCState (fr : ℕ) (s s' : State) : Set where
  constructor mkPresState
  field
    regs≈ : AgreeCCC   (regs s)   (regs s')
    mem≈  : AgreeMemFrom fr (memory s) (memory s')
open PreservesCCCState public

preserves-state-refl : ∀ fr s → PreservesCCCState fr s s
preserves-state-refl fr s = mkPresState (agree-refl-ccc (regs s)) (AgreeMemFrom-refl fr (memory s))

preserves-state-trans : ∀ {fr s₁ s₂ s₃} →
                        PreservesCCCState fr s₁ s₂ → PreservesCCCState fr s₂ s₃ →
                        PreservesCCCState fr s₁ s₃
preserves-state-trans (mkPresState r1 m1) (mkPresState r2 m2) =
  mkPresState (AgreeCCC-trans r1 r2) (AgreeMemFrom-trans m1 m2)
