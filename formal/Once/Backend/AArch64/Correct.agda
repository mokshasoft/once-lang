{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct
--
-- Entry point for AArch64 correctness proofs.
-- Re-exports the main theorem from CorrectBridge.
--
-- Main theorem (Star-based, no fuel):
--   codegen-aarch64-correct : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) →
--     let prog = compile-aarch64 ir
--         s₀ = initWithInput x
--     in ∃[ s ] (Star prog s₀ s
--              × halted s ≡ true
--              × readReg (regs s) x0 ≡ encode (eval ir x))
--
-- Based on the ARM Architecture Reference Manual (ARMv8-A).
-- Aligns with seL4's verified AArch64 target.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct where

-- Re-export everything from CorrectBridge
open import Once.Backend.AArch64.Correct.CorrectBridge public
