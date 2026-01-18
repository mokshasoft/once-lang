------------------------------------------------------------------------
-- Once.Backend.X86.Correct.StackInvariant
--
-- ABSTRACT region-based stack invariants for x86-64 execution.
--
-- This module contains ONLY abstract, region-based types. No arithmetic.
--
-- D041 ARCHITECTURE:
-- - StackInvariant.agda (this file): abstract types (R15Status, RbpInvariant)
-- - StackInstantiation.agda: concrete arithmetic, imports this module
--
-- Consumers should import StackInstantiation, which re-exports these types.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.StackInvariant where

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State

open import Once.Backend.Common.MemoryRegions
  using (Addr; InStack; InHeap; InCode;
         stack-heap-disjoint; stack-code-disjoint;
         stack-heap-addr-disjoint; stack-code-addr-disjoint;
         zero-not-in-stack; pc-in-code;
         StackPointer; slot-addr; sp-distinct; offset-distinct;
         frames-disjoint-slots; slot-in-stack; slot-addr-0-is-base)
open import Once.Backend.Common.MemoryRegions using () renaming (addr to sp-addr; in-stack to sp-in-stack)

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≥_; s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- R15 Region Tracking (Abstract)
------------------------------------------------------------------------

-- | Track what region r15 currently points to
-- This is the abstract invariant - no arithmetic here.
data R15Status (s : State) : Set where
  -- r15 = 0 (unused, doesn't point to any region)
  r15-unused : readReg (regs s) r15 ≡ 0 → R15Status s

  -- r15 points to heap (e.g., closure pointer, data structure)
  r15-in-heap : InHeap (readReg (regs s) r15) → R15Status s

  -- r15 points to code (e.g., during apply when holding code-ptr)
  r15-in-code : InCode (readReg (regs s) r15) → R15Status s

  -- r15 points to stack (e.g., during Pair where r15 = result address)
  -- r15 is a slot in some frame, identified by frame and slot index.
  -- The frame-rsp-bound ensures writes below current rsp don't affect r15.
  r15-in-stack : (frame : StackPointer) →
                 (slot : ℕ) →
                 readReg (regs s) r15 ≡ slot-addr frame slot →
                 sp-addr frame ≥ readReg (regs s) rsp →
                 R15Status s

------------------------------------------------------------------------
-- RbpInvariant (Frame Pointer Invariant) - Abstract
------------------------------------------------------------------------

-- | Invariant: rbp points to a frame base (caller's frame)
-- Uses frame identity instead of arithmetic ordering.
record RbpInvariant (s : State) : Set where
  field
    rbp-frame : StackPointer
    rbp-is-base : readReg (regs s) rbp ≡ sp-addr rbp-frame
    frame-bound : sp-addr rbp-frame ≥ readReg (regs s) rsp

  -- Backward compatibility: derive rsp≤rbp from frame-bound + rbp-is-base
  rsp≤rbp : readReg (regs s) rsp ≤ readReg (regs s) rbp
  rsp≤rbp = subst (readReg (regs s) rsp ≤_) (sym rbp-is-base) frame-bound

open RbpInvariant public

------------------------------------------------------------------------
-- Type alias for backward compatibility
------------------------------------------------------------------------

-- | StackInvariant is R15Status (region-based)
StackInvariant : State → Set
StackInvariant = R15Status

------------------------------------------------------------------------
-- Evidence for stack-write preservation (abstract)
------------------------------------------------------------------------

-- | Evidence needed for r15-in-stack case: write frame is different from r15 frame
-- For other R15Status cases, no additional evidence is needed.
FrameEvidenceFor : ∀ {s : State} → StackPointer → R15Status s → Set
FrameEvidenceFor write-frame (r15-unused _) = ⊤
FrameEvidenceFor write-frame (r15-in-heap _) = ⊤
FrameEvidenceFor write-frame (r15-in-code _) = ⊤
FrameEvidenceFor write-frame (r15-in-stack r15-frame r15-slot _ _) =
  sp-addr write-frame ≢ sp-addr r15-frame

------------------------------------------------------------------------
-- Memory Disjointness from Region Membership (Abstract)
------------------------------------------------------------------------

-- | Stack writes don't affect r15 when r15 is in heap
stack-write-preserves-heap-r15 : ∀ (s : State) (stack-addr : Addr) →
  InStack stack-addr →
  InHeap (readReg (regs s) r15) →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-heap-r15 s stack-addr stack-in r15-heap =
  stack-heap-addr-disjoint stack-addr (readReg (regs s) r15) stack-in r15-heap

-- | Stack writes don't affect r15 when r15 is in code
stack-write-preserves-code-r15 : ∀ (s : State) (stack-addr : Addr) →
  InStack stack-addr →
  InCode (readReg (regs s) r15) →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-code-r15 s stack-addr stack-in r15-code =
  stack-code-addr-disjoint stack-addr (readReg (regs s) r15) stack-in r15-code

-- | Stack writes don't affect r15 when r15 is unused (r15 = 0)
stack-write-preserves-unused-r15 : ∀ (s : State) (stack-addr : Addr) →
  InStack stack-addr →
  readReg (regs s) r15 ≡ 0 →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-unused-r15 s stack-addr stack-in r15≡0 eq =
  let stack-addr≡0 : stack-addr ≡ 0
      stack-addr≡0 = trans eq r15≡0
      zero-in-stack : InStack 0
      zero-in-stack = subst InStack stack-addr≡0 stack-in
  in zero-not-in-stack zero-in-stack

-- | Stack writes in one frame don't affect r15 when r15 is in a different frame.
stack-write-preserves-instack-r15 : ∀ (s : State) (stack-addr : Addr) →
  (write-frame : StackPointer) →
  (write-slot : ℕ) →
  stack-addr ≡ slot-addr write-frame write-slot →
  (r15-frame : StackPointer) →
  (r15-slot : ℕ) →
  readReg (regs s) r15 ≡ slot-addr r15-frame r15-slot →
  sp-addr write-frame ≢ sp-addr r15-frame →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-instack-r15 s stack-addr write-frame write-slot addr-eq
                                  r15-frame r15-slot r15-eq frames-neq eq =
  frames-disjoint-slots write-frame r15-frame write-slot r15-slot frames-neq
    (trans (sym addr-eq) (trans eq r15-eq))

-- | General: stack writes don't affect r15 based on R15Status
stack-write-preserves-r15 : ∀ (s : State) (stack-addr : Addr) →
  (write-frame : StackPointer) →
  (write-slot : ℕ) →
  stack-addr ≡ slot-addr write-frame write-slot →
  (r15-inv : R15Status s) →
  FrameEvidenceFor write-frame r15-inv →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-r15 s stack-addr write-frame write-slot addr-eq (r15-unused r15≡0) _ =
  stack-write-preserves-unused-r15 s stack-addr
    (subst InStack (sym addr-eq) (slot-in-stack write-frame write-slot))
    r15≡0
stack-write-preserves-r15 s stack-addr write-frame write-slot addr-eq (r15-in-heap r15-heap) _ =
  stack-write-preserves-heap-r15 s stack-addr
    (subst InStack (sym addr-eq) (slot-in-stack write-frame write-slot))
    r15-heap
stack-write-preserves-r15 s stack-addr write-frame write-slot addr-eq (r15-in-code r15-code) _ =
  stack-write-preserves-code-r15 s stack-addr
    (subst InStack (sym addr-eq) (slot-in-stack write-frame write-slot))
    r15-code
stack-write-preserves-r15 s stack-addr write-frame write-slot addr-eq
                          (r15-in-stack r15-frame r15-slot r15-eq _) frames-neq =
  stack-write-preserves-instack-r15 s stack-addr write-frame write-slot addr-eq
                                    r15-frame r15-slot r15-eq frames-neq

------------------------------------------------------------------------
-- Invariant Preservation (Abstract - no arithmetic)
------------------------------------------------------------------------

-- | StackInvariant preservation when rsp and r15 are unchanged
stack-inv-preserved-unchanged : ∀ (s s' : State) →
  StackInvariant s →
  readReg (regs s') r15 ≡ readReg (regs s) r15 →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackInvariant s'
stack-inv-preserved-unchanged s s' (r15-unused r15≡0) r15-eq _ =
  r15-unused (trans r15-eq r15≡0)
stack-inv-preserved-unchanged s s' (r15-in-heap r15-heap) r15-eq _ =
  r15-in-heap (subst InHeap (sym r15-eq) r15-heap)
stack-inv-preserved-unchanged s s' (r15-in-code r15-code) r15-eq _ =
  r15-in-code (subst InCode (sym r15-eq) r15-code)
stack-inv-preserved-unchanged s s' (r15-in-stack frame slot r15-eq-slot frame-bound) r15-eq rsp-eq =
  r15-in-stack frame slot (trans r15-eq r15-eq-slot)
               (subst (sp-addr frame ≥_) (sym rsp-eq) frame-bound)

-- | Stack invariant preservation when r15 unchanged and rsp decreased/unchanged
open import Data.Nat.Properties using (≤-trans)

stack-inv-preserved-r15-unchanged : ∀ (s s' : State) →
  StackInvariant s →
  readReg (regs s') r15 ≡ readReg (regs s) r15 →
  readReg (regs s') rsp ≤ readReg (regs s) rsp →
  StackInvariant s'
stack-inv-preserved-r15-unchanged s s' (r15-unused r15≡0) r15-eq _ =
  r15-unused (trans r15-eq r15≡0)
stack-inv-preserved-r15-unchanged s s' (r15-in-heap r15-heap) r15-eq _ =
  r15-in-heap (subst InHeap (sym r15-eq) r15-heap)
stack-inv-preserved-r15-unchanged s s' (r15-in-code r15-code) r15-eq _ =
  r15-in-code (subst InCode (sym r15-eq) r15-code)
stack-inv-preserved-r15-unchanged s s' (r15-in-stack frame slot r15-eq-slot frame-bound) r15-eq rsp-ord =
  r15-in-stack frame slot (trans r15-eq r15-eq-slot)
               (≤-trans rsp-ord frame-bound)

-- | Create StackInvariant when r15 holds a code pointer
stack-inv-for-code-ptr : ∀ (s : State) (prog-len : ℕ) →
  readReg (regs s) r15 < prog-len →
  StackInvariant s
stack-inv-for-code-ptr s prog-len r15<len = r15-in-code (pc-in-code (readReg (regs s) r15) prog-len r15<len)
