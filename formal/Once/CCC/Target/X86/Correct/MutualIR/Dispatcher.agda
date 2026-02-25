------------------------------------------------------------------------
-- Once.CCC.Target.X86.Correct.MutualIR.Dispatcher
--
-- Helper functions for RbpInvariant preservation.
-- The abstract dispatcher postulate has been removed - implementation
-- modules (Compose, Pair, Case) are now parameterized and opened in
-- MutualIR.agda with the concrete dispatcher.
------------------------------------------------------------------------

module Once.CCC.Target.X86.Correct.MutualIR.Dispatcher where

open import Once.IR
open import Once.Target.X86.Syntax using (rsp; rbp)
open import Once.Target.X86.Semantics
open Once.Target.X86.Semantics.State
open import Once.CCC.Target.X86.Correct.StarBase
  using (IRStarResult; ir-rbp-inv; rbp-inv-preserved-unchanged)
open import Once.CCC.Target.X86.Correct.StackInvariant
  using (RbpInvariant)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Helper functions for RbpInvariant preservation
------------------------------------------------------------------------

-- RbpInvariant is preserved through IR execution when rsp and rbp are unchanged
-- Uses ir-rbp-inv from IRStarResult and register preservation from transfer
rbp-inv-preserved-through-ir : ∀ (s s1 s2 : State) →
  RbpInvariant s →
  ∀ {A B} {ir : IR A B} {prog x offset} →
  IRStarResult ir prog s s1 x offset →
  readReg (regs s2) rsp ≡ readReg (regs s1) rsp →
  readReg (regs s2) rbp ≡ readReg (regs s1) rbp →
  RbpInvariant s2
rbp-inv-preserved-through-ir s s1 s2 _ {ir = ir} r rsp2-eq rbp2-eq =
  -- s1 has RbpInvariant from ir-rbp-inv r
  -- s2 has same rsp and rbp as s1, so RbpInvariant is preserved
  rbp-inv-preserved-unchanged s1 s2 (ir-rbp-inv r) rsp2-eq rbp2-eq
