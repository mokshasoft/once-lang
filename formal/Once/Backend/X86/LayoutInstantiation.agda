------------------------------------------------------------------------
-- Once.Backend.X86.LayoutInstantiation
--
-- INTEGRATION module showing how X86.Layout provides concrete bounds
-- that satisfy all required properties.
--
-- This module demonstrates the zero-postulates architecture:
-- - When compiler provides sizes, all "postulates" become proven
-- - stack-lower-zero = refl (definitional)
-- - code-lower-zero = refl (definitional)
-- - stack-sub-preserves is proven
-- - pc-in-code is proven (with precondition)
--
-- USAGE: This module is parameterized by sizes from the compiler.
-- At the top level, instantiate with actual values:
--   open LayoutInstantiation 4096 8192 16384
------------------------------------------------------------------------

module Once.Backend.X86.LayoutInstantiation where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m∸n≤m; <⇒≤)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Once.Backend.X86.Layout using (RegionBounds; Addr; lower; upper)
open import Once.Backend.X86.Layout as Layout

------------------------------------------------------------------------
-- Instantiation Module
--
-- Given concrete sizes from the compiler, provides all memory layout
-- properties as PROOFS (not postulates).
------------------------------------------------------------------------

module Instantiation (code-size heap-size stack-size : ℕ) where

  -- Open the concrete layout with compiler-provided sizes
  open Layout.ConcreteLayout code-size heap-size stack-size public

  ------------------------------------------------------------------------
  -- Properties that become REFL with concrete bounds
  ------------------------------------------------------------------------

  -- These are the key results: what were postulates are now definitional!

  -- | Stack lower bound is 0 - PROVEN by refl
  stack-lower-zero : lower x86-stack-bounds ≡ 0
  stack-lower-zero = refl  -- stack-lower-is-zero from Layout

  -- | Code lower bound is 0 - PROVEN by refl
  code-lower-zero : lower x86-code-bounds ≡ 0
  code-lower-zero = refl  -- code-lower-is-zero from Layout

  ------------------------------------------------------------------------
  -- Derived lemmas that are PROVEN (not postulated)
  ------------------------------------------------------------------------

  -- | Stack subtraction preserves membership - PROVEN
  -- This replaces the postulate x86-stack-lower-zero + stack-sub-preserves
  stack-sub-in-region : ∀ a k →
    InStack a →
    k ≤ a →
    InStack (a ∸ k)
  stack-sub-in-region = stack-sub-preserves

  -- | PC in code region - PROVEN (with precondition)
  -- This replaces prog-fits-in-code + pc-in-code
  pc-in-code-region : ∀ (pc : Addr) (prog-len : ℕ) →
    pc < prog-len →
    prog-len ≤ code-size →
    InCode pc
  pc-in-code-region = pc-in-code

  ------------------------------------------------------------------------
  -- Compatibility with existing abstract interface
  --
  -- These show that our concrete bounds satisfy the same interface
  -- as the postulated bounds in MemoryLayoutSemantics.
  ------------------------------------------------------------------------

  -- | Our InStack is equivalent to the abstract InStack
  -- (both are [lower, upper] intervals, just with concrete vs postulated bounds)

  -- For full integration, we would need to show:
  --   Layout.InStack ≡ MemoryLayoutSemantics.InStack
  -- This requires the bounds to be equal, which they are by instantiation.

  ------------------------------------------------------------------------
  -- Summary of what changes from postulates to proofs:
  --
  -- BEFORE (in X86.Layout):
  --   postulate x86-stack-lower-zero : lower stack-bounds ≡ 0
  --   postulate x86-code-lower-zero : lower code-bounds ≡ 0
  --   postulate prog-fits-in-code : ...
  --
  -- AFTER (with this instantiation):
  --   stack-lower-zero = refl
  --   code-lower-zero = refl
  --   pc-in-code-region = <proven from arithmetic>
  --
  -- The only remaining "assumption" is the compiler-provided sizes,
  -- which are module parameters (not postulates).
  ------------------------------------------------------------------------

------------------------------------------------------------------------
-- Example instantiation with typical sizes
--
-- In practice, the compiler would provide these values.
------------------------------------------------------------------------

module Example where
  -- Typical sizes (in bytes):
  --   code-size  = 4096  (4KB for code)
  --   heap-size  = 8192  (8KB for heap)
  --   stack-size = 16384 (16KB for stack)

  open Instantiation 4096 8192 16384

  -- Now we can use all the proven lemmas:
  -- stack-lower-zero : lower x86-stack-bounds ≡ 0
  -- code-lower-zero : lower x86-code-bounds ≡ 0
  -- stack-sub-in-region : ∀ a k → InStack a → k ≤ a → InStack (a ∸ k)
  -- pc-in-code-region : ∀ pc prog-len → pc < prog-len → prog-len ≤ 4096 → InCode pc

  -- Test: verify stack-lower-zero is refl
  test-stack-lower : lower x86-stack-bounds ≡ 0
  test-stack-lower = refl

  -- Test: verify code-lower-zero is refl
  test-code-lower : lower x86-code-bounds ≡ 0
  test-code-lower = refl
