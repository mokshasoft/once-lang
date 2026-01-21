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

open import Once.Backend.X86.Layout
  using (Addr; InStack; InHeap; InCode;
         stack-heap-disjoint; stack-code-disjoint;
         stack-heap-addr-disjoint; stack-code-addr-disjoint;
         pc-in-code;
         StackPointer; slot-addr; sp-distinct; offset-distinct;
         frame-below-slot0-disjoint;  -- PROVEN lemma for slot 0 disjointness
         slot-in-stack; init-slot-at-base;
         FramePreserved; StackGrew; frame-preserved-under-growth)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr; in-stack to sp-in-stack)

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- R15 Region Tracking (Abstract)
------------------------------------------------------------------------

-- | Track what region r15 currently points to
-- This is the abstract invariant - no arithmetic here.
-- NOTE: r15 is always initialized to a meaningful address (in heap),
-- so there is no "unused" case. r15 is always in one of the three regions.
data R15Status (s : State) : Set where
  -- r15 points to heap (e.g., closure pointer, data structure)
  r15-in-heap : InHeap (readReg (regs s) r15) → R15Status s

  -- r15 points to code (e.g., during apply when holding code-ptr)
  r15-in-code : InCode (readReg (regs s) r15) → R15Status s

  -- r15 points to stack (e.g., during Pair where r15 = result address)
  -- r15 is a slot in some frame, identified by frame and slot index.
  -- The frame-preserved ensures writes at current stack-ptr don't affect r15.
  r15-in-stack : (frame : StackPointer) →
                 (slot : ℕ) →
                 readReg (regs s) r15 ≡ slot-addr frame slot →
                 FramePreserved (sp-addr frame) (readReg (regs s) rsp) →
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
    frame-bound : FramePreserved (sp-addr rbp-frame) (readReg (regs s) rsp)

  -- Backward compatibility: derive rsp≤rbp from frame-bound + rbp-is-base
  -- Note: This relies on x86's FramePreserved = _≥_ instantiation
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

-- | Evidence needed for r15-in-stack case: write frame is BELOW r15 frame
-- This enables proving slot disjointness via arithmetic (not a postulate!)
-- For other R15Status cases, no additional evidence is needed.
FrameEvidenceFor : ∀ {s : State} → StackPointer → R15Status s → Set
FrameEvidenceFor write-frame (r15-in-heap _) = ⊤
FrameEvidenceFor write-frame (r15-in-code _) = ⊤
FrameEvidenceFor write-frame (r15-in-stack r15-frame r15-slot _ _) =
  sp-addr write-frame < sp-addr r15-frame  -- CHANGED: < instead of ≢

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

-- | Stack writes to slot 0 don't affect r15 when write-frame < r15-frame
-- PROVEN using frame-below-slot0-disjoint (no postulate!)
--
-- This is specialized to slot 0 because:
-- 1. All current callers write to slot 0 (push instructions)
-- 2. frame-below-slot0-disjoint is proven for slot 0
-- If other slots are needed, add frame-below-any-slot-disjoint lemma.
stack-write-preserves-instack-r15 : ∀ (s : State) (stack-addr : Addr) →
  (write-frame : StackPointer) →
  stack-addr ≡ slot-addr write-frame 0 →  -- SPECIALIZED: slot 0 only
  (r15-frame : StackPointer) →
  (r15-slot : ℕ) →
  readReg (regs s) r15 ≡ slot-addr r15-frame r15-slot →
  sp-addr write-frame < sp-addr r15-frame →  -- Ordering evidence (not just ≢)
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-instack-r15 s stack-addr write-frame addr-eq
                                  r15-frame r15-slot r15-eq frame< eq =
  frame-below-slot0-disjoint write-frame r15-frame r15-slot frame<
    (trans (sym addr-eq) (trans eq r15-eq))

-- | General: stack writes to slot 0 don't affect r15 based on R15Status
-- Specialized to slot 0 because all callers write to slot 0 (push instructions)
stack-write-preserves-r15 : ∀ (s : State) (stack-addr : Addr) →
  (write-frame : StackPointer) →
  stack-addr ≡ slot-addr write-frame 0 →  -- SPECIALIZED: slot 0 only
  (r15-inv : R15Status s) →
  FrameEvidenceFor write-frame r15-inv →
  stack-addr ≢ readReg (regs s) r15
stack-write-preserves-r15 s stack-addr write-frame addr-eq (r15-in-heap r15-heap) _ =
  stack-write-preserves-heap-r15 s stack-addr
    (subst InStack (sym addr-eq) (slot-in-stack write-frame 0))
    r15-heap
stack-write-preserves-r15 s stack-addr write-frame addr-eq (r15-in-code r15-code) _ =
  stack-write-preserves-code-r15 s stack-addr
    (subst InStack (sym addr-eq) (slot-in-stack write-frame 0))
    r15-code
stack-write-preserves-r15 s stack-addr write-frame addr-eq
                          (r15-in-stack r15-frame r15-slot r15-eq _) frame< =
  stack-write-preserves-instack-r15 s stack-addr write-frame addr-eq
                                    r15-frame r15-slot r15-eq frame<

------------------------------------------------------------------------
-- Invariant Preservation (Abstract - no arithmetic)
------------------------------------------------------------------------

-- | StackInvariant preservation when rsp and r15 are unchanged
stack-inv-preserved-unchanged : ∀ (s s' : State) →
  StackInvariant s →
  readReg (regs s') r15 ≡ readReg (regs s) r15 →
  readReg (regs s') rsp ≡ readReg (regs s) rsp →
  StackInvariant s'
stack-inv-preserved-unchanged s s' (r15-in-heap r15-heap) r15-eq _ =
  r15-in-heap (subst InHeap (sym r15-eq) r15-heap)
stack-inv-preserved-unchanged s s' (r15-in-code r15-code) r15-eq _ =
  r15-in-code (subst InCode (sym r15-eq) r15-code)
stack-inv-preserved-unchanged s s' (r15-in-stack frame slot r15-eq-slot frame-bound) r15-eq rsp-eq =
  r15-in-stack frame slot (trans r15-eq r15-eq-slot)
               (subst (FramePreserved (sp-addr frame)) (sym rsp-eq) frame-bound)

-- | Stack invariant preservation when r15 unchanged and stack grew
-- Note: StackGrew old new means stack expanded from old to new position
stack-inv-preserved-r15-unchanged : ∀ (s s' : State) →
  StackInvariant s →
  readReg (regs s') r15 ≡ readReg (regs s) r15 →
  StackGrew (readReg (regs s) rsp) (readReg (regs s') rsp) →
  StackInvariant s'
stack-inv-preserved-r15-unchanged s s' (r15-in-heap r15-heap) r15-eq _ =
  r15-in-heap (subst InHeap (sym r15-eq) r15-heap)
stack-inv-preserved-r15-unchanged s s' (r15-in-code r15-code) r15-eq _ =
  r15-in-code (subst InCode (sym r15-eq) r15-code)
stack-inv-preserved-r15-unchanged s s' (r15-in-stack frame slot r15-eq-slot frame-bound) r15-eq stack-grew =
  r15-in-stack frame slot (trans r15-eq r15-eq-slot)
               (frame-preserved-under-growth (sp-addr frame) (readReg (regs s) rsp) (readReg (regs s') rsp)
                 frame-bound stack-grew)

-- | Create StackInvariant when r15 holds a code pointer
stack-inv-for-code-ptr : ∀ (s : State) (prog-len : ℕ) →
  readReg (regs s) r15 < prog-len →
  StackInvariant s
stack-inv-for-code-ptr s prog-len r15<len = r15-in-code (pc-in-code (readReg (regs s) r15) prog-len r15<len)
