------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IR
--
-- Re-exports Once.CCC.IR for backwards compatibility.
--
-- The CCC IR is now defined in Once.CCC.IR.
-- This module re-exports it so existing imports continue to work.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.IR where

-- Re-export everything from CCC.IR
open import Once.CCC.IR public

------------------------------------------------------------------------
-- Additional X86v3-specific definitions
--
-- These are verification-related types that are X86v3-specific,
-- not part of the core CCC IR.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _≤_; z≤n)

-- IsPrimitive: Evidence that a type is primitive
-- Used by Arith proofs to construct ValidAtWF
data IsPrimitive : Type → Set where
  is-unit   : IsPrimitive Unit
  is-int    : IsPrimitive Int
  is-float  : IsPrimitive Float
  is-str    : IsPrimitive Str
  is-buffer : IsPrimitive Buffer

-- PrimContractV3: Contract for primitive operations
-- Used by verification proofs, not embedded in IR
record PrimContractV3 (A B : Type) : Set where
  field
    stack-requirement : ℕ
    output-mode : AllocMode
    stack-req-bounded : stack-requirement ≤ 2

open PrimContractV3 public
