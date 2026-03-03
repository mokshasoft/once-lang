------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.Refinement.FramelessCorresponds
--
-- Simplified state correspondence for frameless combinators.
--
-- This module provides a minimal correspondence record for combinators
-- that don't create new frames (pair, compose, id, fst, snd, terminal).
--
-- Key simplification: rbp stays constant throughout execution, so we
-- don't need to track frame transitions or frame-scope invariants.
--
-- CONTRAST with StateCorresponds (SlotToX86.agda):
--   StateCorresponds has: current-frame, rbp-is-frame-base, frame-scope
--   FramelessCorresponds has: frame-base (constant), rbp-constant
--
-- Use FramelessCorresponds for: pair, compose, id, fst, snd, terminal
-- Use StateCorresponds for: apply, curry (which manage frames)
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Refinement.FramelessCorresponds where

open import Data.Nat using (ℕ; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; <⇒≢)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

-- Import FrameSemantics
open import Once.CCC.FrameSemantics using (FrameSemantics)

-- Import X86v3 FrameSemantics instance
open import Once.CCC.Target.X86v3.FrameInstantiation
  using (x86v3-frame-semantics; X86Frame; x86-frame-base)

-- Import SlotMachine types
open import Once.CCC.SlotMachine as SM
  using (LocState; ValueLocation; OnStack; OnHeap; HeapLocation; HeapRef;
         Registers; RegId; RAX; RDI; RSI; R12; R14; R15;
         readReg; writeReg; writeReg-same; writeReg-preserves)

open SM.MemOps {x86v3-frame-semantics} using (readLoc)

-- Import X86 semantics
open import Once.Target.X86.Semantics as X86Sem
  using (Word; RegFile; Memory; State)
  renaming (readReg to x86-readReg; writeReg to x86-writeReg;
            readMem to x86-readMem; writeMem to x86-writeMem)

open import Once.Target.X86.Syntax using (rbp; rsp; rax; rdi; rsi; r12; r14; r15)

-- Import from SlotToX86 for reuse
open import Once.CCC.Target.X86v3.Refinement.SlotToX86
  using (RegsCorrespond; MemCorresponds; HeapBaseMap;
         loc-to-addr; stack-loc-to-addr; heap-loc-to-addr)
open RegsCorrespond
open MemCorresponds

-- Import layout for stack region predicates
open import Once.CCC.Target.X86.Layout
  using (InStack; InHeap; slot-addr-≥-base; stack-heap-addr-disjoint)

-- Abbreviation for our FrameSemantics
private
  FS : FrameSemantics
  FS = x86v3-frame-semantics

------------------------------------------------------------------------
-- FramelessCorresponds
--
-- A minimal correspondence record for frameless combinators.
--
-- Key insight: With frameless codegen, rbp never changes. This means:
--   1. frame-base is constant (= initial rbp value)
--   2. All tracked slots are at addresses >= frame-base
--   3. All writes during execution are at addresses < frame-base
--      (since rsp < rbp and we write at rsp-relative addresses)
--   4. Disjointness is automatic: write-addr < frame-base <= slot-addr
------------------------------------------------------------------------

record FramelessCorresponds (σ : LocState FS) (s : State) : Set where
  field
    -- Heap base mapping (established by allocator)
    heap-base : HeapBaseMap

    -- Unit representation: HeapRef 0 maps to address 0
    unit-base-zero : heap-base (SM.mkHeapRef 0) ≡ 0

    -- Register correspondence
    regs-correspond : RegsCorrespond heap-base (SM.LocState.regs σ) (X86Sem.State.regs s)

    -- Memory correspondence
    mem-corresponds : MemCorresponds heap-base σ (X86Sem.State.memory s)

    -- Halted flag correspondence
    halted-corresponds : SM.LocState.halted σ ≡ X86Sem.State.halted s

    -- Frame base: the constant rbp value throughout frameless execution
    -- This is the base address for the caller's frame
    frame-base : Word

    -- rbp holds frame-base (and stays constant)
    rbp-is-frame-base : x86-readReg (X86Sem.State.regs s) rbp ≡ frame-base

    -- Stack pointer validity: rsp is in stack region
    rsp-in-stack : InStack (x86-readReg (X86Sem.State.regs s) rsp)

    -- Stack pointer at or below frame base
    -- This ensures allocated space is below the caller's frame
    rsp-at-or-below-frame : x86-readReg (X86Sem.State.regs s) rsp ≤ frame-base

    -- Heap region: heap addresses are in the heap region
    heap-in-heap : ∀ hl hl' → SM.LocState.heapMem σ hl ≡ just hl' →
                   InHeap (heap-loc-to-addr heap-base hl)

    -- Tracked slots are at or above frame-base
    -- This is the simplified "frame-scope" for the single-frame case
    -- All slots tracked by σ are in the caller's frame (at addresses >= frame-base)
    slots-above-frame : ∀ f k loc' → readLoc σ (OnStack f k) ≡ just loc' →
                        frame-base ≤ x86-frame-base f

open FramelessCorresponds public

------------------------------------------------------------------------
-- Key Lemma: Writes below frame-base are disjoint from tracked slots
--
-- This is the core disjointness lemma for frameless combinators.
-- Since rsp < frame-base and we write at rsp-relative addresses,
-- writes are automatically disjoint from tracked slots.
------------------------------------------------------------------------

-- | Write address below frame-base is disjoint from all tracked stack slots
write-below-frame-disjoint-from-slots :
  ∀ (σ : LocState FS) (s : State) (write-addr : Word) →
  (fc : FramelessCorresponds σ s) →
  write-addr < frame-base fc →
  ∀ f k loc' → readLoc σ (OnStack f k) ≡ just loc' →
  write-addr ≢ stack-loc-to-addr f k
write-below-frame-disjoint-from-slots σ s write-addr fc write-below f k loc' read-eq =
  <⇒≢ write<slot
  where
    -- Chain: write-addr < frame-base ≤ x86-frame-base f ≤ slot-addr f k
    frame≤f : frame-base fc ≤ x86-frame-base f
    frame≤f = slots-above-frame fc f k loc' read-eq

    f≤slot : x86-frame-base f ≤ stack-loc-to-addr f k
    f≤slot = slot-addr-≥-base f k

    write<slot : write-addr < stack-loc-to-addr f k
    write<slot = <-≤-trans write-below (≤-trans frame≤f f≤slot)

-- | Write address in stack region is disjoint from heap addresses
write-stack-disjoint-from-heap :
  ∀ (σ : LocState FS) (s : State) (write-addr : Word) →
  (fc : FramelessCorresponds σ s) →
  InStack write-addr →
  ∀ hl hl' → SM.LocState.heapMem σ hl ≡ just hl' →
  write-addr ≢ heap-loc-to-addr (heap-base fc) hl
write-stack-disjoint-from-heap σ s write-addr fc write-in-stack hl hl' read-eq =
  stack-heap-addr-disjoint write-addr (heap-loc-to-addr (heap-base fc) hl)
                           write-in-stack (heap-in-heap fc hl hl' read-eq)

------------------------------------------------------------------------
-- Conversion: StateCorresponds ↔ FramelessCorresponds
--
-- When entering a frameless combinator from a framed context (or vice versa),
-- we can convert between the correspondence records.
------------------------------------------------------------------------

open import Once.CCC.Target.X86v3.Refinement.SlotToX86 as SlotToX86
  using (StateCorresponds)

-- | Convert StateCorresponds to FramelessCorresponds
-- Used when entering a frameless combinator
from-state-corresponds : ∀ (σ : LocState FS) (s : State) →
  StateCorresponds σ s →
  FramelessCorresponds σ s
from-state-corresponds σ s sc = record
  { heap-base = SlotToX86.StateCorresponds.heap-base sc
  ; unit-base-zero = SlotToX86.StateCorresponds.unit-base-zero sc
  ; regs-correspond = SlotToX86.StateCorresponds.regs-correspond sc
  ; mem-corresponds = SlotToX86.StateCorresponds.mem-corresponds sc
  ; halted-corresponds = SlotToX86.StateCorresponds.halted-corresponds sc
  ; frame-base = x86-frame-base (SlotToX86.StateCorresponds.current-frame sc)
  ; rbp-is-frame-base = SlotToX86.StateCorresponds.rbp-is-frame-base sc
  ; rsp-in-stack = SlotToX86.StateCorresponds.rsp-in-stack sc
  ; rsp-at-or-below-frame = rsp≤frame
  ; heap-in-heap = SlotToX86.StateCorresponds.heap-in-heap sc
  ; slots-above-frame = SlotToX86.StateCorresponds.frame-scope sc
  }
  where
    open import Data.Nat.Properties using (≤-reflexive)
    -- rsp ≤ rbp = frame-base
    rsp≤frame : x86-readReg (X86Sem.State.regs s) rsp ≤ x86-frame-base (SlotToX86.StateCorresponds.current-frame sc)
    rsp≤frame = subst (x86-readReg (X86Sem.State.regs s) rsp ≤_)
                      (SlotToX86.StateCorresponds.rbp-is-frame-base sc)
                      (SlotToX86.StateCorresponds.rsp-at-or-below-rbp sc)
      where open import Relation.Binary.PropositionalEquality using (subst)

-- | Convert FramelessCorresponds back to StateCorresponds
-- Used when exiting a frameless combinator back to framed context
-- Requires an X86Frame whose base matches frame-base
to-state-corresponds : ∀ (σ : LocState FS) (s : State) →
  (fc : FramelessCorresponds σ s) →
  (frame : X86Frame) →
  x86-frame-base frame ≡ frame-base fc →
  StateCorresponds σ s
to-state-corresponds σ s fc frame frame-eq = record
  { heap-base = heap-base fc
  ; unit-base-zero = unit-base-zero fc
  ; regs-correspond = regs-correspond fc
  ; mem-corresponds = mem-corresponds fc
  ; halted-corresponds = halted-corresponds fc
  ; current-frame = frame
  ; rbp-is-frame-base = trans (rbp-is-frame-base fc) (sym frame-eq)
  ; frame-scope = λ f k loc' read-eq → subst (_≤ x86-frame-base f) (sym frame-eq) (slots-above-frame fc f k loc' read-eq)
  ; heap-in-heap = heap-in-heap fc
  ; rsp-at-or-below-rbp = rsp≤rbp
  ; rsp-in-stack = rsp-in-stack fc
  }
  where
    open import Relation.Binary.PropositionalEquality using (subst)
    rsp≤rbp : x86-readReg (X86Sem.State.regs s) rsp ≤ x86-readReg (X86Sem.State.regs s) rbp
    rsp≤rbp = subst (x86-readReg (X86Sem.State.regs s) rsp ≤_)
                    (sym (rbp-is-frame-base fc))
                    (rsp-at-or-below-frame fc)

------------------------------------------------------------------------
-- Preservation lemmas for frameless operations
--
-- These lemmas show how FramelessCorresponds is preserved through
-- stack allocation/deallocation and memory writes.
------------------------------------------------------------------------

open import Once.Target.X86.ExecLemmas
  using (readReg-writeReg-same; readReg-writeReg-diff; readMem-writeMem-diff)

-- | sub rsp preserves FramelessCorresponds
-- Preconditions: new-rsp ≤ frame-base, new-rsp in stack
sub-rsp-preserves-frameless :
  ∀ (σ : LocState FS) (s : State) (n : ℕ) →
  (fc : FramelessCorresponds σ s) →
  let new-rsp = x86-readReg (X86Sem.State.regs s) rsp ∸ n
  in new-rsp ≤ frame-base fc →
     InStack new-rsp →
     FramelessCorresponds σ (record s { regs = x86-writeReg (X86Sem.State.regs s) rsp new-rsp })
sub-rsp-preserves-frameless σ s n fc new≤frame new-in-stack = record
  { heap-base = heap-base fc
  ; unit-base-zero = unit-base-zero fc
  ; regs-correspond = regs-after-rsp-write
  ; mem-corresponds = mem-corresponds fc
  ; halted-corresponds = halted-corresponds fc
  ; frame-base = frame-base fc
  ; rbp-is-frame-base = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp rbp new-rsp (λ ()))
                              (rbp-is-frame-base fc)
  ; rsp-in-stack = subst InStack (sym (readReg-writeReg-same (X86Sem.State.regs s) rsp new-rsp)) new-in-stack
  ; rsp-at-or-below-frame = subst (_≤ frame-base fc)
                                  (sym (readReg-writeReg-same (X86Sem.State.regs s) rsp new-rsp))
                                  new≤frame
  ; heap-in-heap = heap-in-heap fc
  ; slots-above-frame = slots-above-frame fc
  }
  where
    open import Relation.Binary.PropositionalEquality using (subst)
    new-rsp = x86-readReg (X86Sem.State.regs s) rsp ∸ n
    new-regs = x86-writeReg (X86Sem.State.regs s) rsp new-rsp

    -- rsp write doesn't affect tracked registers
    regs-after-rsp-write : RegsCorrespond (heap-base fc) (SM.LocState.regs σ) new-regs
    regs-after-rsp-write = record
      { rax-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp rax new-rsp (λ ()))
                                (rax-corresponds (regs-correspond fc))
      ; rdi-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp rdi new-rsp (λ ()))
                                (rdi-corresponds (regs-correspond fc))
      ; rsi-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp rsi new-rsp (λ ()))
                                (rsi-corresponds (regs-correspond fc))
      ; r12-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp r12 new-rsp (λ ()))
                                (r12-corresponds (regs-correspond fc))
      ; r14-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp r14 new-rsp (λ ()))
                                (r14-corresponds (regs-correspond fc))
      ; r15-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp r15 new-rsp (λ ()))
                                (r15-corresponds (regs-correspond fc))
      }

-- | add rsp preserves FramelessCorresponds
-- Preconditions: new-rsp ≤ frame-base, new-rsp in stack
add-rsp-preserves-frameless :
  ∀ (σ : LocState FS) (s : State) (n : ℕ) →
  (fc : FramelessCorresponds σ s) →
  let new-rsp = x86-readReg (X86Sem.State.regs s) rsp + n
  in new-rsp ≤ frame-base fc →
     InStack new-rsp →
     FramelessCorresponds σ (record s { regs = x86-writeReg (X86Sem.State.regs s) rsp new-rsp })
add-rsp-preserves-frameless σ s n fc new≤frame new-in-stack = record
  { heap-base = heap-base fc
  ; unit-base-zero = unit-base-zero fc
  ; regs-correspond = regs-after-rsp-write
  ; mem-corresponds = mem-corresponds fc
  ; halted-corresponds = halted-corresponds fc
  ; frame-base = frame-base fc
  ; rbp-is-frame-base = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp rbp new-rsp (λ ()))
                              (rbp-is-frame-base fc)
  ; rsp-in-stack = subst InStack (sym (readReg-writeReg-same (X86Sem.State.regs s) rsp new-rsp)) new-in-stack
  ; rsp-at-or-below-frame = subst (_≤ frame-base fc)
                                  (sym (readReg-writeReg-same (X86Sem.State.regs s) rsp new-rsp))
                                  new≤frame
  ; heap-in-heap = heap-in-heap fc
  ; slots-above-frame = slots-above-frame fc
  }
  where
    open import Relation.Binary.PropositionalEquality using (subst)
    new-rsp = x86-readReg (X86Sem.State.regs s) rsp + n
    new-regs = x86-writeReg (X86Sem.State.regs s) rsp new-rsp

    -- rsp write doesn't affect tracked registers
    regs-after-rsp-write : RegsCorrespond (heap-base fc) (SM.LocState.regs σ) new-regs
    regs-after-rsp-write = record
      { rax-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp rax new-rsp (λ ()))
                                (rax-corresponds (regs-correspond fc))
      ; rdi-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp rdi new-rsp (λ ()))
                                (rdi-corresponds (regs-correspond fc))
      ; rsi-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp rsi new-rsp (λ ()))
                                (rsi-corresponds (regs-correspond fc))
      ; r12-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp r12 new-rsp (λ ()))
                                (r12-corresponds (regs-correspond fc))
      ; r14-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp r14 new-rsp (λ ()))
                                (r14-corresponds (regs-correspond fc))
      ; r15-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rsp r15 new-rsp (λ ()))
                                (r15-corresponds (regs-correspond fc))
      }

-- | Memory write below frame-base preserves FramelessCorresponds
write-below-frame-preserves-frameless :
  ∀ (σ : LocState FS) (s : State) (write-addr v : Word) →
  (fc : FramelessCorresponds σ s) →
  write-addr < frame-base fc →
  InStack write-addr →
  FramelessCorresponds σ (record s { memory = x86-writeMem (X86Sem.State.memory s) write-addr v })
write-below-frame-preserves-frameless σ s write-addr v fc write-below write-in-stack = record
  { heap-base = heap-base fc
  ; unit-base-zero = unit-base-zero fc
  ; regs-correspond = regs-correspond fc
  ; mem-corresponds = mem-after-write
  ; halted-corresponds = halted-corresponds fc
  ; frame-base = frame-base fc
  ; rbp-is-frame-base = rbp-is-frame-base fc
  ; rsp-in-stack = rsp-in-stack fc
  ; rsp-at-or-below-frame = rsp-at-or-below-frame fc
  ; heap-in-heap = heap-in-heap fc
  ; slots-above-frame = slots-above-frame fc
  }
  where
    -- Stack disjointness: write-addr < frame-base ≤ slot-addr
    stack-disj : ∀ f k loc' → readLoc σ (OnStack f k) ≡ just loc' →
                 write-addr ≢ stack-loc-to-addr f k
    stack-disj = write-below-frame-disjoint-from-slots σ s write-addr fc write-below

    -- Heap disjointness: write-addr in stack, heap-addr in heap
    heap-disj : ∀ hl hl' → SM.LocState.heapMem σ hl ≡ just hl' →
                write-addr ≢ heap-loc-to-addr (heap-base fc) hl
    heap-disj = write-stack-disjoint-from-heap σ s write-addr fc write-in-stack

    -- Memory corresponds after write
    mem-after-write : MemCorresponds (heap-base fc) σ (x86-writeMem (X86Sem.State.memory s) write-addr v)
    mem-after-write = record
      { stack-corresponds = λ f k loc' read-eq →
          trans (readMem-writeMem-diff (X86Sem.State.memory s) write-addr (stack-loc-to-addr f k) v
                                       (stack-disj f k loc' read-eq))
                (MemCorresponds.stack-corresponds (mem-corresponds fc) f k loc' read-eq)
      ; heap-corresponds = λ hl hl' read-eq →
          trans (readMem-writeMem-diff (X86Sem.State.memory s) write-addr (heap-loc-to-addr (heap-base fc) hl) v
                                       (heap-disj hl hl' read-eq))
                (MemCorresponds.heap-corresponds (mem-corresponds fc) hl hl' read-eq)
      }

-- | Write to RAX preserves FramelessCorresponds when updating slot machine RAX coherently
-- Used when executing "mov rax, ..." while updating slot machine RAX to corresponding location
write-rax-preserves-frameless :
  ∀ (σ : LocState FS) (s : State) (loc : ValueLocation FS) →
  (fc : FramelessCorresponds σ s) →
  let new-val = loc-to-addr (heap-base fc) loc
      new-σ-regs = SM.writeReg (SM.LocState.regs σ) SM.RAX loc
      new-x86-regs = x86-writeReg (X86Sem.State.regs s) rax new-val
  in FramelessCorresponds (record σ { regs = new-σ-regs }) (record s { regs = new-x86-regs })
write-rax-preserves-frameless σ s loc fc = record
  { heap-base = heap-base fc
  ; unit-base-zero = unit-base-zero fc
  ; regs-correspond = regs-after-write
  ; mem-corresponds = mem-after-write
  ; halted-corresponds = halted-corresponds fc
  ; frame-base = frame-base fc
  ; rbp-is-frame-base = trans (readReg-writeReg-diff (X86Sem.State.regs s) rax rbp new-val (λ ()))
                              (rbp-is-frame-base fc)
  ; rsp-in-stack = subst InStack (sym (readReg-writeReg-diff (X86Sem.State.regs s) rax rsp new-val (λ ())))
                         (rsp-in-stack fc)
  ; rsp-at-or-below-frame = subst (_≤ frame-base fc)
                                  (sym (readReg-writeReg-diff (X86Sem.State.regs s) rax rsp new-val (λ ())))
                                  (rsp-at-or-below-frame fc)
  ; heap-in-heap = heap-in-heap fc
  ; slots-above-frame = slots-above-frame fc
  }
  where
    open import Relation.Binary.PropositionalEquality using (subst)
    new-val = loc-to-addr (heap-base fc) loc
    new-σ-regs = SM.writeReg (SM.LocState.regs σ) SM.RAX loc
    new-x86-regs = x86-writeReg (X86Sem.State.regs s) rax new-val
    new-σ = record σ { regs = new-σ-regs }

    -- MemCorresponds only depends on stackMem and heapMem, which are unchanged
    mem-after-write : MemCorresponds (heap-base fc) new-σ (X86Sem.State.memory s)
    mem-after-write = record
      { stack-corresponds = MemCorresponds.stack-corresponds (mem-corresponds fc)
      ; heap-corresponds = MemCorresponds.heap-corresponds (mem-corresponds fc)
      }

    regs-after-write : RegsCorrespond (heap-base fc) new-σ-regs new-x86-regs
    regs-after-write = record
      { rax-corresponds = trans (readReg-writeReg-same (X86Sem.State.regs s) rax new-val)
                                (cong (loc-to-addr (heap-base fc)) (sym (SM.writeReg-same (SM.LocState.regs σ) SM.RAX loc)))
      ; rdi-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rax rdi new-val (λ ()))
                                (trans (rdi-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RAX SM.RDI loc (λ ()))))
      ; rsi-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rax rsi new-val (λ ()))
                                (trans (rsi-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RAX SM.RSI loc (λ ()))))
      ; r12-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rax r12 new-val (λ ()))
                                (trans (r12-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RAX SM.R12 loc (λ ()))))
      ; r14-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rax r14 new-val (λ ()))
                                (trans (r14-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RAX SM.R14 loc (λ ()))))
      ; r15-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rax r15 new-val (λ ()))
                                (trans (r15-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RAX SM.R15 loc (λ ()))))
      }

-- | Write to RDI preserves FramelessCorresponds when updating slot machine RDI coherently
-- Used when executing "mov rdi, ..." while updating slot machine RDI to corresponding location
write-rdi-preserves-frameless :
  ∀ (σ : LocState FS) (s : State) (loc : ValueLocation FS) →
  (fc : FramelessCorresponds σ s) →
  let new-val = loc-to-addr (heap-base fc) loc
      new-σ-regs = SM.writeReg (SM.LocState.regs σ) SM.RDI loc
      new-x86-regs = x86-writeReg (X86Sem.State.regs s) rdi new-val
  in FramelessCorresponds (record σ { regs = new-σ-regs }) (record s { regs = new-x86-regs })
write-rdi-preserves-frameless σ s loc fc = record
  { heap-base = heap-base fc
  ; unit-base-zero = unit-base-zero fc
  ; regs-correspond = regs-after-write
  ; mem-corresponds = mem-after-write
  ; halted-corresponds = halted-corresponds fc
  ; frame-base = frame-base fc
  ; rbp-is-frame-base = trans (readReg-writeReg-diff (X86Sem.State.regs s) rdi rbp new-val (λ ()))
                              (rbp-is-frame-base fc)
  ; rsp-in-stack = subst InStack (sym (readReg-writeReg-diff (X86Sem.State.regs s) rdi rsp new-val (λ ())))
                         (rsp-in-stack fc)
  ; rsp-at-or-below-frame = subst (_≤ frame-base fc)
                                  (sym (readReg-writeReg-diff (X86Sem.State.regs s) rdi rsp new-val (λ ())))
                                  (rsp-at-or-below-frame fc)
  ; heap-in-heap = heap-in-heap fc
  ; slots-above-frame = slots-above-frame fc
  }
  where
    open import Relation.Binary.PropositionalEquality using (subst)
    new-val = loc-to-addr (heap-base fc) loc
    new-σ-regs = SM.writeReg (SM.LocState.regs σ) SM.RDI loc
    new-x86-regs = x86-writeReg (X86Sem.State.regs s) rdi new-val
    new-σ = record σ { regs = new-σ-regs }

    -- MemCorresponds only depends on stackMem and heapMem, which are unchanged
    mem-after-write : MemCorresponds (heap-base fc) new-σ (X86Sem.State.memory s)
    mem-after-write = record
      { stack-corresponds = MemCorresponds.stack-corresponds (mem-corresponds fc)
      ; heap-corresponds = MemCorresponds.heap-corresponds (mem-corresponds fc)
      }

    regs-after-write : RegsCorrespond (heap-base fc) new-σ-regs new-x86-regs
    regs-after-write = record
      { rax-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rdi rax new-val (λ ()))
                                (trans (rax-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RDI SM.RAX loc (λ ()))))
      ; rdi-corresponds = trans (readReg-writeReg-same (X86Sem.State.regs s) rdi new-val)
                                (cong (loc-to-addr (heap-base fc)) (sym (SM.writeReg-same (SM.LocState.regs σ) SM.RDI loc)))
      ; rsi-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rdi rsi new-val (λ ()))
                                (trans (rsi-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RDI SM.RSI loc (λ ()))))
      ; r12-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rdi r12 new-val (λ ()))
                                (trans (r12-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RDI SM.R12 loc (λ ()))))
      ; r14-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rdi r14 new-val (λ ()))
                                (trans (r14-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RDI SM.R14 loc (λ ()))))
      ; r15-corresponds = trans (readReg-writeReg-diff (X86Sem.State.regs s) rdi r15 new-val (λ ()))
                                (trans (r15-corresponds (regs-correspond fc))
                                       (cong (loc-to-addr (heap-base fc)) (SM.writeReg-preserves (SM.LocState.regs σ) SM.RDI SM.R15 loc (λ ()))))
      }

-- | PC and flags changes preserve FramelessCorresponds
pc-flags-preserve-frameless :
  ∀ (σ : LocState FS) (s : State) (new-pc : ℕ) →
  (fc : FramelessCorresponds σ s) →
  (new-flags : X86Sem.Flags) →
  FramelessCorresponds σ (record s { pc = new-pc ; flags = new-flags })
pc-flags-preserve-frameless σ s new-pc fc new-flags = record
  { heap-base = heap-base fc
  ; unit-base-zero = unit-base-zero fc
  ; regs-correspond = regs-correspond fc
  ; mem-corresponds = mem-corresponds fc
  ; halted-corresponds = halted-corresponds fc
  ; frame-base = frame-base fc
  ; rbp-is-frame-base = rbp-is-frame-base fc
  ; rsp-in-stack = rsp-in-stack fc
  ; rsp-at-or-below-frame = rsp-at-or-below-frame fc
  ; heap-in-heap = heap-in-heap fc
  ; slots-above-frame = slots-above-frame fc
  }

------------------------------------------------------------------------
-- Summary
--
-- FramelessCorresponds simplifies proofs for frameless combinators by:
--   1. Using a constant frame-base instead of tracking current-frame
--   2. Eliminating frame-scope proofs (trivial with one frame)
--   3. Providing automatic disjointness: write-addr < frame-base ≤ slot-addr
--
-- Key lemmas:
--   - write-below-frame-disjoint-from-slots: writes below frame are safe
--   - sub-rsp-preserves-frameless: stack allocation preserves correspondence
--   - add-rsp-preserves-frameless: stack deallocation preserves correspondence
--   - write-below-frame-preserves-frameless: memory writes below frame are safe
--
-- Conversions:
--   - from-state-corresponds: StateCorresponds → FramelessCorresponds
--   - to-state-corresponds: FramelessCorresponds → StateCorresponds
------------------------------------------------------------------------
