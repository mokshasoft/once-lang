------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StackInvariant2
--
-- Region-based stack invariants for x86-64 execution.
--
-- This module provides an alternative to StackInvariant that uses
-- the abstract memory regions model from D041 instead of concrete
-- address ordering.
--
-- KEY DIFFERENCE:
-- Old StackInvariant: rsp ≤ r15 (fails when r15 = code-ptr)
-- New approach: track region-of r15, prove disjointness from region membership
--
-- USAGE:
-- During normal execution: r15 = 0 or r15 = heap address
-- During apply thunk: r15 = code-ptr (temporarily in Code region)
-- Memory disjointness: stack writes don't touch heap or code
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StackInvariant2 where

open import Once.Type
open import Once.Semantics

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State

open import Once.Backend.Common.MemoryRegions
  using (Region; stack; heap; code; Addr; region-of;
         regions-disjoint; stack≢heap; stack≢code;
         stack-heap-disjoint; stack-code-disjoint)

open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; _>_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- R15 Region Tracking
------------------------------------------------------------------------

-- | Track what region r15 currently points to
-- This replaces the ordering-based StackInvariant for r15
data R15Status (s : State) : Set where
  -- r15 = 0 (unused, doesn't point to any region)
  r15-unused : readReg (regs s) r15 ≡ 0 → R15Status s

  -- r15 points to heap (e.g., closure pointer, data structure)
  r15-in-heap : region-of (readReg (regs s) r15) ≡ heap → R15Status s

  -- r15 points to code (e.g., during apply when holding code-ptr)
  r15-in-code : region-of (readReg (regs s) r15) ≡ code → R15Status s

------------------------------------------------------------------------
-- Stack Capacity (replaces rsp > 16)
------------------------------------------------------------------------

-- | Abstract stack capacity: stack can accommodate n more slots
-- Each slot is 8 bytes (one word on x86-64)
-- This replaces concrete bounds like `rsp > 16`
record StackCapacity (s : State) (n : ℕ) : Set where
  field
    -- rsp points to stack region
    rsp-in-stack : region-of (readReg (regs s) rsp) ≡ stack

    -- After allocating n slots, still in stack region
    -- (This is the abstract version of "enough space")
    capacity-maintained : ∀ k → k ≤ n →
      region-of (readReg (regs s) rsp ∸ (k *ℕ 8)) ≡ stack

open StackCapacity public

------------------------------------------------------------------------
-- Memory Disjointness from Region Membership
------------------------------------------------------------------------

-- | Stack writes don't affect r15 when r15 is in heap
stack-write-preserves-heap-r15 : ∀ (s : State) (stack-addr : Addr) →
  region-of stack-addr ≡ stack →
  region-of (readReg (regs s) r15) ≡ heap →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-heap-r15 s stack-addr stack-region r15-heap =
  stack-heap-disjoint stack-addr (readReg (regs s) r15) stack-region r15-heap

-- | Stack writes don't affect r15 when r15 is in code
stack-write-preserves-code-r15 : ∀ (s : State) (stack-addr : Addr) →
  region-of stack-addr ≡ stack →
  region-of (readReg (regs s) r15) ≡ code →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-code-r15 s stack-addr stack-region r15-code =
  stack-code-disjoint stack-addr (readReg (regs s) r15) stack-region r15-code

-- | Stack writes don't affect r15 when r15 = 0
-- (Assuming 0 is never a valid stack address)
postulate
  zero-not-in-stack : region-of 0 ≢ stack

stack-write-preserves-zero-r15 : ∀ (s : State) (stack-addr : Addr) →
  region-of stack-addr ≡ stack →
  readReg (regs s) r15 ≡ 0 →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-zero-r15 s stack-addr stack-region r15≡0 eq =
  -- If stack-addr ≡ r15 and r15 ≡ 0, then stack-addr ≡ 0
  -- So region-of stack-addr ≡ region-of 0
  -- But region-of stack-addr ≡ stack, so region-of 0 ≡ stack
  -- This contradicts zero-not-in-stack
  let stack-addr≡0 : stack-addr ≡ 0
      stack-addr≡0 = trans eq r15≡0
      region-0≡stack : region-of 0 ≡ stack
      region-0≡stack = trans (cong region-of (sym stack-addr≡0)) stack-region
  in zero-not-in-stack region-0≡stack

-- | General: stack writes don't affect r15 based on R15Status
stack-write-preserves-r15 : ∀ (s : State) (stack-addr : Addr) →
  R15Status s →
  region-of stack-addr ≡ stack →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-r15 s stack-addr (r15-unused r15≡0) stack-region =
  stack-write-preserves-zero-r15 s stack-addr stack-region r15≡0
stack-write-preserves-r15 s stack-addr (r15-in-heap r15-heap) stack-region =
  stack-write-preserves-heap-r15 s stack-addr stack-region r15-heap
stack-write-preserves-r15 s stack-addr (r15-in-code r15-code) stack-region =
  stack-write-preserves-code-r15 s stack-addr stack-region r15-code

------------------------------------------------------------------------
-- RBP Region (Frame Pointer)
------------------------------------------------------------------------

-- | RBP is always in stack region (it's the caller's frame pointer)
-- Initially set to stackBase, always stays in stack
postulate
  rbp-in-stack : ∀ (s : State) → region-of (readReg (regs s) rbp) ≡ stack

-- | Stack writes at lower addresses don't affect rbp
-- This requires proving that stack writes are at different stack addresses
-- than rbp, which needs the LIFO/ordering properties of stack

-- For now, we capture the key property: if we can show the write address
-- differs from rbp (both in stack but at different positions), they're disjoint
-- This is handled by the existing RbpInvariant (rsp ≤ rbp means rbp is "above")

------------------------------------------------------------------------
-- Compatibility with existing StackInvariant
------------------------------------------------------------------------

-- Import existing StackInvariant
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; r15-unused; stack-below-r15; RbpInvariant)

-- | Convert old StackInvariant to R15Status (for heap case)
-- The stack-below-r15 case assumes r15 is a heap address (rsp ≤ heap addr)
-- This is the standard case outside of apply's thunk execution
stackInvariant-to-r15-status-heap : ∀ (s : State) →
  StackInvariant s →
  region-of (readReg (regs s) r15) ≡ heap →
  R15Status s
stackInvariant-to-r15-status-heap s (r15-unused r15≡0) _ = r15-unused r15≡0
stackInvariant-to-r15-status-heap s (stack-below-r15 _) r15-heap = r15-in-heap r15-heap

-- | Create R15Status for apply's thunk execution phase
-- During apply, r15 = code-ptr which is in Code region
r15-status-for-code : ∀ (s : State) →
  region-of (readReg (regs s) r15) ≡ code →
  R15Status s
r15-status-for-code s r15-code = r15-in-code r15-code
