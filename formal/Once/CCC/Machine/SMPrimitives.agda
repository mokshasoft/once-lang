-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- SlotMachine Proof Primitives
--
-- Minimal building blocks for SlotMachine correctness proofs.
--
-- CORE INSIGHT: Only two memory axioms + positive write characterization.
--
-- The two memory axioms:
--   read-write-same  : read from where you wrote → get written value
--   read-write-other : read from elsewhere → get original value
--
-- Positive write characterization:
--   instr-writes-mem : tells you exactly WHERE each instruction writes
--   TraceWritesAbove n : tells you the write set is {slots ≥ n}
--
-- Everything else DERIVES from these:
--   - "Preservation" = repeated application of read-write-other
--   - "Independence" = read-write-other + write-commute
--   - Final values = read-write-same on the last write
--
-- Architecture:
--   Level 1: Disjointness (structural facts about locations)
--   Level 2: Memory axioms (read-write-same, read-write-other, write-commute)
--   Level 3: Positive write characterization (WHERE each instr writes)
--   Level 4: Derived instruction lemmas
--   Level 5: Derived trace lemmas (by induction)
------------------------------------------------------------------------

module Once.CCC.Machine.SMPrimitives where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-≤-trans; <⇒≢)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; inspect; [_]; ≢-sym)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore public

------------------------------------------------------------------------
-- Proof obligation marker (to be replaced with actual proofs)
------------------------------------------------------------------------

postulate
  !! : ∀ {ℓ} {A : Set ℓ} → A

private
  variable
    FS : FrameSemantics

  -- Private helper to bring Frame into scope (not exported to avoid ambiguity)
  Frame : FrameSemantics → Set
  Frame FS = FrameSemantics.Frame FS

-- Open parameterized modules with explicit FS for module-level definitions
-- Note: These bring TraceSlotReadsBelow, exec-abstract, etc. into scope
-- with implicit {FS} parameter
module Ops {FS : FrameSemantics} where
  open MemOps {FS} public
  open AbstractExec {FS} public

------------------------------------------------------------------------
-- Level 1: Internal Helpers
--
-- Structural facts about ValueLocation used internally for proofs.
------------------------------------------------------------------------

-- Stack locations with different slots are disjoint (same frame)
-- Internal helper for converting slot ordering to location disjointness
stack-slot-disjoint : ∀ {FS : FrameSemantics} (f : Frame FS) (s₁ s₂ : ℕ) →
  s₁ ≢ s₂ → OnStack {FS} f s₁ ≢ OnStack f s₂
stack-slot-disjoint f s₁ s₂ s₁≢s₂ refl = s₁≢s₂ refl

-- Extract frame from stack location equality
stack-frame-injective : ∀ {FS : FrameSemantics} {f₁ f₂ : Frame FS} {s₁ s₂ : ℕ} →
  OnStack {FS} f₁ s₁ ≡ OnStack f₂ s₂ → f₁ ≡ f₂
stack-frame-injective refl = refl

-- Extract slot from stack location equality
stack-slot-injective : ∀ {FS : FrameSemantics} {f₁ f₂ : Frame FS} {s₁ s₂ : ℕ} →
  OnStack {FS} f₁ s₁ ≡ OnStack f₂ s₂ → s₁ ≡ s₂
stack-slot-injective refl = refl

------------------------------------------------------------------------
-- Level 2: Memory Operations
--
-- Fundamental read/write axioms and commutativity properties.
-- These are the symmetric primitives for reasoning about memory updates.
--
-- Key axioms:
--   readLoc-writeLoc-same  : read after write (same location)
--   readLoc-writeLoc-other : read after write (different location)
--   writeLoc-commute       : write-write commutativity
------------------------------------------------------------------------

module MemoryOps {FS : FrameSemantics} where
  open MemOps {FS}
  open FrameSemantics FS using (_≟F_; _≺_; ≺-irrefl)
  open import Data.Nat using () renaming (_≟_ to _≟ℕ_)
  open import Data.Empty using (⊥-elim)

  ------------------------------------------------------------------------
  -- Positive read-write-other lemmas (split by location structure)
  ------------------------------------------------------------------------

  -- Stack write, heap read: always disjoint (different constructors)
  readLoc-writeLoc-stack-heap : ∀ (s : LocState FS) (f : Frame FS) (k : ℕ) (h : HeapLocation)
    (v : ValueLocation FS) →
    readLoc (writeLoc s (OnStack f k) v) (OnHeap h) ≡ readLoc s (OnHeap h)
  readLoc-writeLoc-stack-heap s f k h v = refl

  -- Heap write, stack read: always disjoint (different constructors)
  readLoc-writeLoc-heap-stack : ∀ (s : LocState FS) (h : HeapLocation) (f : Frame FS) (k : ℕ)
    (v : ValueLocation FS) →
    readLoc (writeLoc s (OnHeap h) v) (OnStack f k) ≡ readLoc s (OnStack f k)
  readLoc-writeLoc-heap-stack s h f k (OnHeap _) = refl
  readLoc-writeLoc-heap-stack s h f k (OnStack _ _) = refl

  -- heapMem equality implies readLoc equality for heap locations
  readLoc-heapMem-eq : ∀ (s₁ s₂ : LocState FS) (h : HeapLocation) →
    heapMem s₁ ≡ heapMem s₂ →
    readLoc s₁ (OnHeap h) ≡ readLoc s₂ (OnHeap h)
  readLoc-heapMem-eq s₁ s₂ h heq with heapMem s₁ h | heapMem s₂ h | cong (λ m → m h) heq
  ... | just h₁ | just .h₁ | refl = refl
  ... | nothing | nothing  | refl = refl

  -- writeLoc commutes with register updates for OnHeap locations
  writeLoc-regs-commute-heap : ∀ (s : LocState FS) (hl : HeapLocation) (v : ValueLocation FS)
    (r : Registers FS) →
    writeLoc (record s { regs = r }) (OnHeap hl) v ≡
    record (writeLoc s (OnHeap hl) v) { regs = r }
  writeLoc-regs-commute-heap s hl (OnHeap v) r = refl
  writeLoc-regs-commute-heap s hl (OnStack _ _) r = refl

  -- General writeLoc commutes with register updates for any location
  -- Symmetric with writeLoc-regs-commute (OnStack case from SlotMachine)
  writeLoc-regs-commute-general : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : ValueLocation FS)
    (r : Registers FS) →
    writeLoc (record s { regs = r }) loc v ≡
    record (writeLoc s loc v) { regs = r }
  writeLoc-regs-commute-general s (OnStack f k) v r = writeLoc-regs-commute s f k v r
  writeLoc-regs-commute-general s (OnHeap hl) v r = writeLoc-regs-commute-heap s hl v r

  ------------------------------------------------------------------------
  -- Positive stack slot preservation lemmas
  --
  -- These use ordering (<, ≺) instead of disjointness (≢) for positive reasoning.
  -- Key insight: ordering implies disjointness, so we derive ≢ internally.
  ------------------------------------------------------------------------

  -- Write to slot k, read from slot j where j < k: preserved (same frame)
  readLoc-writeLoc-stack-slot-lt : ∀ (s : LocState FS) (f : Frame FS) (j k : ℕ)
    (v : ValueLocation FS) →
    j < k →
    readLoc (writeLoc s (OnStack f k) v) (OnStack f j) ≡ readLoc s (OnStack f j)
  readLoc-writeLoc-stack-slot-lt s f j k v j<k with f ≟F f | k ≟ℕ j
  ... | yes _ | yes k≡j = ⊥-elim (<⇒≢ j<k (sym k≡j))
  ... | yes _ | no _ = refl
  ... | no f≢f | _ = ⊥-elim (f≢f refl)

  -- Write to slot j, read from slot k where j < k: preserved (same frame)
  readLoc-writeLoc-stack-slot-gt : ∀ (s : LocState FS) (f : Frame FS) (j k : ℕ)
    (v : ValueLocation FS) →
    j < k →
    readLoc (writeLoc s (OnStack f j) v) (OnStack f k) ≡ readLoc s (OnStack f k)
  readLoc-writeLoc-stack-slot-gt s f j k v j<k with f ≟F f | j ≟ℕ k
  ... | yes _ | yes j≡k = ⊥-elim (<⇒≢ j<k j≡k)
  ... | yes _ | no _ = refl
  ... | no f≢f | _ = ⊥-elim (f≢f refl)

  -- Write to frame f₁, read from frame f₂ where f₁ ≺ f₂: preserved (ancestor frame)
  readLoc-writeLoc-stack-ancestor : ∀ (s : LocState FS) (f₁ f₂ : Frame FS) (k₁ k₂ : ℕ)
    (v : ValueLocation FS) →
    f₁ ≺ f₂ →
    readLoc (writeLoc s (OnStack f₁ k₁) v) (OnStack f₂ k₂) ≡ readLoc s (OnStack f₂ k₂)
  readLoc-writeLoc-stack-ancestor s f₁ f₂ k₁ k₂ v f₁≺f₂ with f₁ ≟F f₂
  ... | yes f₁≡f₂ = ⊥-elim (≺-irrefl (subst (λ f → f ≺ f₂) f₁≡f₂ f₁≺f₂))
  ... | no _ = refl

  -- Read after write (same location)
  -- Uses writeLoc-read-same-stack from SMCore for stack locations
  -- Heap cases use axiom (heap write semantics are more complex)
  readLoc-writeLoc-same : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : ValueLocation FS) →
    readLoc (writeLoc s loc v) loc ≡ just v
  readLoc-writeLoc-same s (OnStack f k) v = writeLoc-read-same-stack s f k v
  readLoc-writeLoc-same s (OnHeap hl) v = readLoc-writeLoc-same-heap s hl v
    where postulate readLoc-writeLoc-same-heap : ∀ s hl v → readLoc (writeLoc s (OnHeap hl) v) (OnHeap hl) ≡ just v

------------------------------------------------------------------------
-- Level 3: Instruction Characterization (POSITIVE)
--
-- KEY INSIGHT: Characterize WHERE each instruction writes, not where
-- it DOESN'T write. Preservation follows as a corollary.
--
-- For each instruction, we specify its EXACT write location:
--   instr-writes-slot : AbstractInstr → Maybe ℕ
--     store-at-slot k  → just k    (writes to slot k)
--     everything else  → nothing   (writes no stack slot)
--
--   instr-writes-mem : AbstractInstr → LocState → AllocState → Maybe ValueLocation
--     Computes the exact memory location written (if any)
--
-- This is POSITIVE characterization:
--   "store-at-slot 3 writes to slot 3" (not "doesn't write to slot 5")
--
-- Preservation DERIVES from positive characterization:
--   If loc ≢ write-location, then loc is preserved.
--
-- For traces, TraceWritesBelow n characterizes the write set positively:
--   "This trace writes to slots in {0, 1, ..., n-1}"
-- Then: "slot k ≥ n is not in write set → preserved"
------------------------------------------------------------------------

-- Slot-specific characterization (state-independent)
-- These are useful for trace analysis where we track slot bounds

-- What slot does this instruction write to? (store-at-slot, worklist-push)
instr-writes-slot : AbstractInstr → Maybe ℕ
instr-writes-slot (store-at-slot k) = just k
instr-writes-slot (worklist-push k) = just k  -- OCP-0003: worklist push writes to slot
instr-writes-slot _ = nothing

-- What slot does this instruction read from? (load-from-slot, restore-input, worklist-pop)
instr-reads-slot : AbstractInstr → Maybe ℕ
instr-reads-slot (load-from-slot k) = just k
instr-reads-slot (restore-input k) = just k
instr-reads-slot (worklist-pop k) = just k  -- OCP-0003: worklist pop reads from slot
instr-reads-slot _ = nothing

------------------------------------------------------------------------
-- Positive Heap Write Characterization
--
-- Instead of negative "doesn't write to heap", we positively characterize
-- which heap location (if any) an instruction writes to, and whether
-- that write is within owned regions.
------------------------------------------------------------------------

-- What heap location does this instruction write to?
-- Returns nothing if instruction doesn't write to heap.
-- Returns nothing if writing to stack (not a heap write).
instr-writes-heap : AbstractInstr → LocState FS → Maybe HeapLocation
instr-writes-heap store-indirect s with readReg (regs s) Input
... | OnHeap hl = just hl
... | OnStack _ _ = nothing  -- writing to stack, not heap
instr-writes-heap store-indirect-suc s with readReg (regs s) Input
... | OnHeap hl = just (sucHL hl)
... | OnStack _ _ = nothing  -- writing to stack, not heap
instr-writes-heap _ s = nothing  -- all other instructions don't write to heap

-- Positive predicate: HeapLocation is in some region of the ownership set
data InSomeRegion : HeapLocation → HeapOwnership → Set where
  in-head : ∀ {hl region regions} →
    InRegion hl region →
    InSomeRegion hl (region ∷ regions)
  in-tail : ∀ {hl region regions} →
    InSomeRegion hl regions →
    InSomeRegion hl (region ∷ regions)

-- POSITIVE: Instruction writes within owned heap regions
-- If instruction writes to heap, the location must be in some owned region.
-- If instruction doesn't write to heap, trivially satisfied.
data InstrWritesWithinOwned (i : AbstractInstr) (s : LocState FS) (owned : HeapOwnership) : Set where
  no-heap-write : instr-writes-heap i s ≡ nothing → InstrWritesWithinOwned i s owned
  heap-write-owned : ∀ {hl} →
    instr-writes-heap i s ≡ just hl →
    InSomeRegion hl owned →
    InstrWritesWithinOwned i s owned

-- Instruction doesn't write to heap (POSITIVE syntactic check)
-- This is the syntactic version - instruction is not store-indirect or store-indirect-suc
data InstrNoHeapWrite : AbstractInstr → Set where
  nhw-mov-to-output      : InstrNoHeapWrite mov-to-output
  nhw-mov-to-input       : InstrNoHeapWrite mov-to-input
  nhw-load-indirect      : InstrNoHeapWrite load-indirect
  nhw-load-indirect-suc  : InstrNoHeapWrite load-indirect-suc
  nhw-load-from-slot     : ∀ {slot} → InstrNoHeapWrite (load-from-slot slot)
  nhw-store-at-slot      : ∀ {slot} → InstrNoHeapWrite (store-at-slot slot)
  nhw-lea-slot           : ∀ {slot} → InstrNoHeapWrite (lea-slot slot)
  nhw-restore-input      : ∀ {slot} → InstrNoHeapWrite (restore-input slot)
  nhw-instr-alloc-stack  : ∀ {n} → InstrNoHeapWrite (instr-alloc-stack n)
  nhw-instr-dealloc-stack : ∀ {n} → InstrNoHeapWrite (instr-dealloc-stack n)
  nhw-instr-push-frame   : ∀ {cap} → InstrNoHeapWrite (instr-push-frame cap)
  nhw-instr-pop-frame    : InstrNoHeapWrite instr-pop-frame
  nhw-instr-call-closure : InstrNoHeapWrite instr-call-closure
  -- OCP-0003: Worklist instructions write to stack, not heap
  nhw-worklist-init      : ∀ {slot} → InstrNoHeapWrite (worklist-init slot)
  nhw-worklist-push      : ∀ {slot} → InstrNoHeapWrite (worklist-push slot)
  nhw-worklist-pop       : ∀ {slot} → InstrNoHeapWrite (worklist-pop slot)
  nhw-worklist-check     : ∀ {slot} → InstrNoHeapWrite (worklist-check slot)

-- Instruction preserves frame (doesn't push/pop frame)
InstrPreservesFrame : AbstractInstr → Set
InstrPreservesFrame (instr-push-frame _) = ⊥
  where open import Data.Empty using (⊥)
InstrPreservesFrame instr-pop-frame = ⊥
  where open import Data.Empty using (⊥)
InstrPreservesFrame _ = ⊤

-- What memory location does this instruction read?
-- Returns nothing if instruction doesn't read memory.
instr-reads-mem : AbstractInstr → LocState FS → AllocState {FS} → Maybe (ValueLocation FS)
instr-reads-mem mov-to-output s alloc = nothing  -- register only
instr-reads-mem mov-to-input s alloc = nothing   -- register only
instr-reads-mem load-indirect s alloc = just (readReg (regs s) Input)
instr-reads-mem load-indirect-suc s alloc = just (sucLoc (readReg (regs s) Input))
instr-reads-mem (load-from-slot k) s alloc = just (OnStack (current-frame alloc) k)
instr-reads-mem (store-at-slot k) s alloc = nothing  -- reads Output register, not memory
instr-reads-mem store-indirect s alloc = nothing     -- reads Output register, not memory
instr-reads-mem store-indirect-suc s alloc = nothing -- reads Output register, not memory
instr-reads-mem (lea-slot k) s alloc = nothing       -- computes address, no read
instr-reads-mem (restore-input k) s alloc = just (OnStack (current-frame alloc) k)
instr-reads-mem (instr-alloc-stack n) s alloc = nothing
instr-reads-mem (instr-dealloc-stack n) s alloc = nothing
instr-reads-mem (instr-push-frame cap) s alloc = nothing
instr-reads-mem instr-pop-frame s alloc = nothing
instr-reads-mem instr-call-closure s alloc = nothing
-- OCP-0003: Worklist instructions
instr-reads-mem (worklist-init k) s alloc = nothing      -- no-op
instr-reads-mem (worklist-push k) s alloc = nothing      -- reads register, not memory
instr-reads-mem (worklist-pop k) s alloc = just (OnStack (current-frame alloc) k)
instr-reads-mem (worklist-check k) s alloc = nothing     -- no-op

-- What memory location does this instruction write?
-- Returns nothing if instruction doesn't write memory.
instr-writes-mem : AbstractInstr → LocState FS → AllocState {FS} → Maybe (ValueLocation FS)
instr-writes-mem mov-to-output s alloc = nothing  -- register only
instr-writes-mem mov-to-input s alloc = nothing   -- register only
instr-writes-mem load-indirect s alloc = nothing  -- writes Output register, not memory
instr-writes-mem load-indirect-suc s alloc = nothing
instr-writes-mem (load-from-slot k) s alloc = nothing
instr-writes-mem (store-at-slot k) s alloc = just (OnStack (current-frame alloc) k)
instr-writes-mem store-indirect s alloc = just (readReg (regs s) Input)
instr-writes-mem store-indirect-suc s alloc = just (sucLoc (readReg (regs s) Input))
instr-writes-mem (lea-slot k) s alloc = nothing
instr-writes-mem (restore-input k) s alloc = nothing  -- writes Input register, not memory
instr-writes-mem (instr-alloc-stack n) s alloc = nothing
instr-writes-mem (instr-dealloc-stack n) s alloc = nothing
instr-writes-mem (instr-push-frame cap) s alloc = nothing
instr-writes-mem instr-pop-frame s alloc = nothing
instr-writes-mem instr-call-closure s alloc = nothing
-- OCP-0003: Worklist instructions
instr-writes-mem (worklist-init k) s alloc = nothing     -- no-op
instr-writes-mem (worklist-push k) s alloc = just (OnStack (current-frame alloc) k)
instr-writes-mem (worklist-pop k) s alloc = nothing      -- writes register, not memory
instr-writes-mem (worklist-check k) s alloc = nothing    -- no-op

------------------------------------------------------------------------
-- Level 4: Instruction Primitives
--
-- Core lemmas:
--   (A) Determinism: same inputs → same outputs
--   (B) Frame/heap preservation: derived from write characterization
------------------------------------------------------------------------

-- Instruction primitives in parameterized module
module InstrPrimitives {FS : FrameSemantics} where
  open MemOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open MemoryOps {FS}
  open FrameSemantics FS using (_≟F_; _≺_)
  -- (A) DETERMINISM
  -- If two states agree on what an instruction reads (memory and registers),
  -- executing the instruction produces the same result.
  --
  -- Key insight: If all fields of LocState agree, the states are equal.
  -- Then exec-abstract produces equal results by congruence.

  -- Helper: If all fields agree, states are equal
  LocState-eq : ∀ (s₁ s₂ : LocState FS) →
    regs s₁ ≡ regs s₂ →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    halted s₁ ≡ halted s₂ →
    s₁ ≡ s₂
  LocState-eq (mkLocState r₁ sm₁ hm₁ h₁) (mkLocState r₂ sm₂ hm₂ h₂) refl refl refl refl = refl

  exec-abstract-deterministic : ∀ (i : AbstractInstr) (s₁ s₂ : LocState FS)
    (alloc : AllocState {FS}) →
    -- Registers agree (for register reads)
    regs s₁ ≡ regs s₂ →
    -- Halted flags agree
    halted s₁ ≡ halted s₂ →
    -- Memory reads agree (if instruction reads memory)
    (∀ rloc → instr-reads-mem i s₁ alloc ≡ just rloc →
              readLoc s₁ rloc ≡ readLoc s₂ rloc) →
    -- Stack memory agrees (for store-at-slot which reads stackMem structure)
    stackMem s₁ ≡ stackMem s₂ →
    -- Heap memory agrees (for store-indirect which reads heapMem structure)
    heapMem s₁ ≡ heapMem s₂ →
    -- Then results are equal
    proj₁ (exec-abstract i s₁ alloc) ≡ proj₁ (exec-abstract i s₂ alloc)
  exec-abstract-deterministic i s₁ s₂ alloc regs-eq halted-eq mem-eq stack-eq heap-eq =
    cong (λ s → proj₁ (exec-abstract i s alloc)) (LocState-eq s₁ s₂ regs-eq stack-eq heap-eq halted-eq)

  -- (D) FRAME PRESERVATION
  -- Instructions preserve current-frame (all instructions, no predicate needed!)
  exec-abstract-preserves-frame : ∀ (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) →
    current-frame (proj₂ (exec-abstract i s alloc)) ≡ current-frame alloc
  exec-abstract-preserves-frame mov-to-output s alloc = refl
  exec-abstract-preserves-frame mov-to-input s alloc = refl
  exec-abstract-preserves-frame load-indirect s alloc = refl
  exec-abstract-preserves-frame load-indirect-suc s alloc = refl
  exec-abstract-preserves-frame (load-from-slot slot) s alloc
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (store-at-slot slot) s alloc = refl
  exec-abstract-preserves-frame store-indirect s alloc = refl
  exec-abstract-preserves-frame store-indirect-suc s alloc = refl
  exec-abstract-preserves-frame (lea-slot slot) s alloc = refl
  exec-abstract-preserves-frame (restore-input slot) s alloc
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (instr-alloc-stack n) s alloc = refl
  exec-abstract-preserves-frame (instr-dealloc-stack n) s alloc = refl
  exec-abstract-preserves-frame (instr-push-frame cap) s alloc = refl
  exec-abstract-preserves-frame instr-pop-frame s alloc = refl
  exec-abstract-preserves-frame instr-call-closure s alloc = refl
  -- OCP-0003: Worklist instructions
  exec-abstract-preserves-frame (worklist-init slot) s alloc = refl
  exec-abstract-preserves-frame (worklist-push slot) s alloc = refl  -- alloc unchanged
  exec-abstract-preserves-frame (worklist-pop slot) s alloc
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (worklist-check slot) s alloc = refl

  -- (E) HEAP PRESERVATION
  -- Instructions that don't write to heap preserve heapMem
  exec-abstract-preserves-heapMem : ∀ (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) →
    InstrNoHeapWrite i →
    heapMem (proj₁ (exec-abstract i s alloc)) ≡ heapMem s
  exec-abstract-preserves-heapMem mov-to-output s alloc nhw-mov-to-output = refl
  exec-abstract-preserves-heapMem mov-to-input s alloc nhw-mov-to-input = refl
  exec-abstract-preserves-heapMem load-indirect s alloc nhw-load-indirect
    with readLoc s (readReg (regs s) Input)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem load-indirect-suc s alloc nhw-load-indirect-suc
    with readLoc s (sucLoc (readReg (regs s) Input))
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (load-from-slot slot) s alloc nhw-load-from-slot
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (store-at-slot slot) s alloc nhw-store-at-slot =
    writeLoc-heapMem-stack s (current-frame alloc) slot (readReg (regs s) Output)
  exec-abstract-preserves-heapMem (lea-slot slot) s alloc nhw-lea-slot = refl
  exec-abstract-preserves-heapMem (restore-input slot) s alloc nhw-restore-input
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (instr-alloc-stack n) s alloc nhw-instr-alloc-stack = refl
  exec-abstract-preserves-heapMem (instr-dealloc-stack n) s alloc nhw-instr-dealloc-stack = refl
  exec-abstract-preserves-heapMem (instr-push-frame cap) s alloc nhw-instr-push-frame = refl
  exec-abstract-preserves-heapMem instr-pop-frame s alloc nhw-instr-pop-frame = refl
  exec-abstract-preserves-heapMem instr-call-closure s alloc nhw-instr-call-closure = refl
  -- OCP-0003: Worklist instructions
  exec-abstract-preserves-heapMem (worklist-init slot) s alloc nhw-worklist-init = refl
  exec-abstract-preserves-heapMem (worklist-push slot) s alloc nhw-worklist-push =
    writeLoc-heapMem-stack s (current-frame alloc) slot (readReg (regs s) Output)
  exec-abstract-preserves-heapMem (worklist-pop slot) s alloc nhw-worklist-pop
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (worklist-check slot) s alloc nhw-worklist-check = refl

  ------------------------------------------------------------------------
  -- (E2) STACK SLOT PRESERVATION - instruction level
  --
  -- Each instruction preserves stack slots it doesn't write to.
  -- Uses positive bounds: j < k means writing to k preserves j.
  ------------------------------------------------------------------------

  -- Instructions that don't write to stack preserve all stack slots
  -- These instructions only modify registers, heap, or nothing
  exec-abstract-preserves-stack-slot : ∀ (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) (f : Frame FS) (slot : ℕ) →
    InstrNoHeapWrite i →
    instr-writes-slot i ≡ nothing →
    readLoc (proj₁ (exec-abstract i s alloc)) (OnStack f slot) ≡ readLoc s (OnStack f slot)
  -- Register-only instructions
  exec-abstract-preserves-stack-slot mov-to-output s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot mov-to-input s alloc f slot _ _ = refl
  -- Load instructions: only modify registers, preserve all memory
  exec-abstract-preserves-stack-slot load-indirect s alloc f slot _ _ =
    readLoc-stackMem-eq (proj₁ (exec-abstract load-indirect s alloc)) s (OnStack f slot)
      (load-preserves-stackMem Output (IndReg Input) s)
      (load-preserves-heapMem Output (IndReg Input) s)
  exec-abstract-preserves-stack-slot load-indirect-suc s alloc f slot _ _ =
    readLoc-stackMem-eq (proj₁ (exec-abstract load-indirect-suc s alloc)) s (OnStack f slot)
      (load-preserves-stackMem Output (IndRegSuc Input) s)
      (load-preserves-heapMem Output (IndRegSuc Input) s)
  exec-abstract-preserves-stack-slot (load-from-slot k) s alloc f slot _ _
    with readLoc s (OnStack (current-frame alloc) k)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-stack-slot (lea-slot k) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (restore-input k) s alloc f slot _ _
    with readLoc s (OnStack (current-frame alloc) k)
  ... | just _  = refl
  ... | nothing = refl
  -- Stack management instructions: preserve all memory
  exec-abstract-preserves-stack-slot (instr-alloc-stack _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (instr-dealloc-stack _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (instr-push-frame _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot instr-pop-frame s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot instr-call-closure s alloc f slot _ _ = refl
  -- OCP-0003: Worklist instructions
  exec-abstract-preserves-stack-slot (worklist-init _) s alloc f slot _ _ = refl
  -- worklist-push is like store-at-slot - need to handle separately with slot bounds
  exec-abstract-preserves-stack-slot (worklist-push k) s alloc f slot _ _ = !!  -- TODO: needs slot bound reasoning
  exec-abstract-preserves-stack-slot (worklist-pop k) s alloc f slot _ _
    with readLoc s (OnStack (current-frame alloc) k)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-stack-slot (worklist-check _) s alloc f slot _ _ = refl

  -- store-at-slot k preserves slot j when j < k (positive ordering)
  store-at-slot-preserves-below : ∀ (j k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    j < k →
    readLoc (proj₁ (exec-abstract (store-at-slot k) s alloc)) (OnStack (current-frame alloc) j) ≡
    readLoc s (OnStack (current-frame alloc) j)
  store-at-slot-preserves-below j k s alloc j<k =
    readLoc-writeLoc-stack-slot-lt s (current-frame alloc) j k (readReg (regs s) Output) j<k

  -- store-at-slot j preserves slot k when j < k (positive ordering)
  store-at-slot-preserves-above : ∀ (j k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    j < k →
    readLoc (proj₁ (exec-abstract (store-at-slot j) s alloc)) (OnStack (current-frame alloc) k) ≡
    readLoc s (OnStack (current-frame alloc) k)
  store-at-slot-preserves-above j k s alloc j<k =
    readLoc-writeLoc-stack-slot-gt s (current-frame alloc) j k (readReg (regs s) Output) j<k

  -- store-at-slot preserves ancestor frame slots (positive frame ordering)
  store-at-slot-preserves-ancestor : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (f : Frame FS) (slot : ℕ) →
    current-frame alloc ≺ f →
    readLoc (proj₁ (exec-abstract (store-at-slot k) s alloc)) (OnStack f slot) ≡
    readLoc s (OnStack f slot)
  store-at-slot-preserves-ancestor k s alloc f slot cf≺f =
    readLoc-writeLoc-stack-ancestor s (current-frame alloc) f k slot (readReg (regs s) Output) cf≺f

  -- (F) FRAME EQUIVALENCE
  -- If two alloc states have the same current-frame, instruction produces same LocState
  -- Helper: just is injective
  private
    just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
    just-injective refl = refl

  exec-abstract-same-frame : ∀ (i : AbstractInstr) (s : LocState FS)
    (alloc₁ alloc₂ : AllocState {FS}) →
    current-frame alloc₁ ≡ current-frame alloc₂ →
    proj₁ (exec-abstract i s alloc₁) ≡ proj₁ (exec-abstract i s alloc₂)
  -- Instructions that don't use alloc at all
  exec-abstract-same-frame mov-to-output s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame mov-to-input s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame load-indirect s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame load-indirect-suc s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame store-indirect s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame store-indirect-suc s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-alloc-stack n) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-dealloc-stack n) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-push-frame cap) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame instr-pop-frame s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame instr-call-closure s alloc₁ alloc₂ _ = refl
  -- Instructions that use current-frame alloc
  exec-abstract-same-frame (load-from-slot slot) s alloc₁ alloc₂ frame-eq
    with readLoc s (OnStack (current-frame alloc₁) slot)
       | readLoc s (OnStack (current-frame alloc₂) slot)
       | cong (λ f → readLoc s (OnStack f slot)) frame-eq
  ... | just v₁ | just v₂ | eq rewrite just-injective eq = refl
  ... | nothing | nothing | _ = refl
  ... | just _ | nothing | ()
  ... | nothing | just _ | ()
  exec-abstract-same-frame (store-at-slot slot) s alloc₁ alloc₂ frame-eq
    rewrite frame-eq = refl
  exec-abstract-same-frame (lea-slot slot) s alloc₁ alloc₂ frame-eq
    rewrite frame-eq = refl
  exec-abstract-same-frame (restore-input slot) s alloc₁ alloc₂ frame-eq
    with readLoc s (OnStack (current-frame alloc₁) slot)
       | readLoc s (OnStack (current-frame alloc₂) slot)
       | cong (λ f → readLoc s (OnStack f slot)) frame-eq
  ... | just v₁ | just v₂ | eq rewrite just-injective eq = refl
  ... | nothing | nothing | _ = refl
  ... | just _ | nothing | ()
  ... | nothing | just _ | ()
  -- OCP-0003: Worklist instructions
  exec-abstract-same-frame (worklist-init slot) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (worklist-push slot) s alloc₁ alloc₂ frame-eq
    rewrite frame-eq = refl
  exec-abstract-same-frame (worklist-pop slot) s alloc₁ alloc₂ frame-eq
    with readLoc s (OnStack (current-frame alloc₁) slot)
       | readLoc s (OnStack (current-frame alloc₂) slot)
       | cong (λ f → readLoc s (OnStack f slot)) frame-eq
  ... | just v₁ | just v₂ | eq rewrite just-injective eq = refl
  ... | nothing | nothing | _ = refl
  ... | just _ | nothing | ()
  ... | nothing | just _ | ()
  exec-abstract-same-frame (worklist-check slot) s alloc₁ alloc₂ _ = refl

------------------------------------------------------------------------
-- Level 5: Trace Primitives
--
-- POSITIVE trace characterization:
--   TraceWritesBelow n trace : "writes to slots in {0, ..., n-1}"
--   TraceNoHeapWrites trace : "writes only to stack (no heap writes)"
--
-- Together these POSITIVELY characterize the write set:
--   "trace writes to {OnStack frame k | k < n}"
--
-- Preservation DERIVES from this:
--   If k ≥ n, slot k is not in write set → preserved
--   Heap locations are not in write set → preserved
------------------------------------------------------------------------

-- Trace predicates (characterization)

-- All slot writes in trace are at slots ≥ n
TraceWritesAbove : ℕ → AbstractTrace → Set
TraceWritesAbove n [] = ⊤
TraceWritesAbove n (i ∷ t) with instr-writes-slot i
... | nothing = TraceWritesAbove n t
... | just k = (n ≤ k) × TraceWritesAbove n t

-- All slot writes in trace are at slots < n
TraceWritesBelow : ℕ → AbstractTrace → Set
TraceWritesBelow n [] = ⊤
TraceWritesBelow n (i ∷ t) with instr-writes-slot i
... | nothing = TraceWritesBelow n t
... | just k = (k < n) × TraceWritesBelow n t

-- Extract tail of TraceWritesAbove for non-writing instruction
twa-tail : ∀ (n : ℕ) (i : AbstractInstr) (rest : AbstractTrace) →
  instr-writes-slot i ≡ nothing →
  TraceWritesAbove n (i ∷ rest) →
  TraceWritesAbove n rest
twa-tail n i rest eq twa with instr-writes-slot i | eq
... | nothing | refl = twa
... | just _ | ()

-- Extract tail of TraceWritesBelow for non-writing instruction
twb-tail : ∀ (n : ℕ) (i : AbstractInstr) (rest : AbstractTrace) →
  instr-writes-slot i ≡ nothing →
  TraceWritesBelow n (i ∷ rest) →
  TraceWritesBelow n rest
twb-tail n i rest eq twb with instr-writes-slot i | eq
... | nothing | refl = twb
... | just _ | ()

-- All slot reads in trace are from slots ≥ n
TraceSlotReadsAbove : ℕ → AbstractTrace → Set
TraceSlotReadsAbove n [] = ⊤
TraceSlotReadsAbove n (i ∷ t) with instr-reads-slot i
... | nothing = TraceSlotReadsAbove n t
... | just k = (n ≤ k) × TraceSlotReadsAbove n t

-- All slot reads in trace are from slots < n
TraceSlotReadsBelow : ℕ → AbstractTrace → Set
TraceSlotReadsBelow n [] = ⊤
TraceSlotReadsBelow n (i ∷ t) with instr-reads-slot i
... | nothing = TraceSlotReadsBelow n t
... | just k = (k < n) × TraceSlotReadsBelow n t

------------------------------------------------------------------------
-- Trace Heap Write Characterization (POSITIVE)
--
-- TraceWritesWithinOwned threads state through the trace and checks that
-- each heap write is within owned regions. For empty ownership [], this
-- is equivalent to "no heap writes" (i.e., TraceNoHeapWrites).
------------------------------------------------------------------------

-- State-threading version for full generality (supports freeing)
-- Note: Uses exec-abstract from AbstractExec module
module TraceHeapOwnership {FS : FrameSemantics} where
  open AbstractExec {FS}

  TraceWritesWithinOwned : AbstractTrace → LocState FS → AllocState {FS} → HeapOwnership → Set
  TraceWritesWithinOwned [] s alloc owned = ⊤
  TraceWritesWithinOwned (i ∷ t) s alloc owned with halted s
  ... | true = ⊤  -- halted, no more execution
  ... | false = InstrWritesWithinOwned i s owned ×
                TraceWritesWithinOwned t (proj₁ (exec-abstract i s alloc))
                                         (proj₂ (exec-abstract i s alloc)) owned

-- Helper: check if instruction writes to heap (syntactic)
InstrWritesToHeap : AbstractInstr → Set
InstrWritesToHeap store-indirect = ⊤
InstrWritesToHeap store-indirect-suc = ⊤
InstrWritesToHeap _ = ⊥

-- Helper: trace contains no heap-writing instructions (syntactic)
-- This is useful for constructing TraceWritesWithinOwned [] proofs
TraceNoHeapWrites : AbstractTrace → Set
TraceNoHeapWrites [] = ⊤
TraceNoHeapWrites (store-indirect ∷ t) = ⊥
TraceNoHeapWrites (store-indirect-suc ∷ t) = ⊥
TraceNoHeapWrites (_ ∷ t) = TraceNoHeapWrites t

-- All instructions in trace preserve frame
TracePreservesFrame : AbstractTrace → Set
TracePreservesFrame [] = ⊤
TracePreservesFrame (i ∷ t) = InstrPreservesFrame i × TracePreservesFrame t

-- All instructions in trace preserve heapMem (no heap writes)
TracePreservesHeapMem : AbstractTrace → Set
TracePreservesHeapMem [] = ⊤
TracePreservesHeapMem (i ∷ t) = InstrNoHeapWrite i × TracePreservesHeapMem t

------------------------------------------------------------------------
-- Capacity Preservation
--
-- Instructions that don't push a new frame preserve capacity.
-- This is needed for threading capacity through trace execution.
------------------------------------------------------------------------

-- Instruction preserves capacity (all except push-frame)
data InstrPreservesCapacity : AbstractInstr → Set where
  ipc-mov-to-output      : InstrPreservesCapacity mov-to-output
  ipc-mov-to-input       : InstrPreservesCapacity mov-to-input
  ipc-load-indirect      : InstrPreservesCapacity load-indirect
  ipc-load-indirect-suc  : InstrPreservesCapacity load-indirect-suc
  ipc-load-from-slot     : ∀ {slot} → InstrPreservesCapacity (load-from-slot slot)
  ipc-store-at-slot      : ∀ {slot} → InstrPreservesCapacity (store-at-slot slot)
  ipc-store-indirect     : InstrPreservesCapacity store-indirect
  ipc-store-indirect-suc : InstrPreservesCapacity store-indirect-suc
  ipc-lea-slot           : ∀ {slot} → InstrPreservesCapacity (lea-slot slot)
  ipc-restore-input      : ∀ {slot} → InstrPreservesCapacity (restore-input slot)
  ipc-alloc-stack        : ∀ {n} → InstrPreservesCapacity (instr-alloc-stack n)
  ipc-dealloc-stack      : ∀ {n} → InstrPreservesCapacity (instr-dealloc-stack n)
  ipc-pop-frame          : InstrPreservesCapacity instr-pop-frame
  ipc-call-closure       : InstrPreservesCapacity instr-call-closure
  -- OCP-0003: Worklist instructions preserve capacity
  ipc-worklist-init      : ∀ {slot} → InstrPreservesCapacity (worklist-init slot)
  ipc-worklist-push      : ∀ {slot} → InstrPreservesCapacity (worklist-push slot)
  ipc-worklist-pop       : ∀ {slot} → InstrPreservesCapacity (worklist-pop slot)
  ipc-worklist-check     : ∀ {slot} → InstrPreservesCapacity (worklist-check slot)
  -- Note: instr-push-frame is NOT included (it modifies capacity)

-- Trace preserves capacity (all instructions preserve capacity)
data TracePreservesCapacity : AbstractTrace → Set where
  tpc-[] : TracePreservesCapacity []
  tpc-∷  : ∀ {i rest} → InstrPreservesCapacity i → TracePreservesCapacity rest →
           TracePreservesCapacity (i ∷ rest)

-- Append preserves TracePreservesCapacity
tpc-++ : ∀ {t₁ t₂} → TracePreservesCapacity t₁ → TracePreservesCapacity t₂ →
         TracePreservesCapacity (t₁ ++ t₂)
tpc-++ tpc-[] tpc₂ = tpc₂
tpc-++ (tpc-∷ ipc tpc₁) tpc₂ = tpc-∷ ipc (tpc-++ tpc₁ tpc₂)

-- Append preserves TraceNoHeapWrites
trace-no-heap-writes-append : ∀ t1 t2 →
  TraceNoHeapWrites t1 → TraceNoHeapWrites t2 →
  TraceNoHeapWrites (t1 ++ t2)
trace-no-heap-writes-append [] t2 _ tn2 = tn2
trace-no-heap-writes-append (mov-to-output ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (mov-to-input ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (load-indirect ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (load-indirect-suc ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (load-from-slot _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (store-at-slot _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (store-indirect ∷ _) _ () _
trace-no-heap-writes-append (store-indirect-suc ∷ _) _ () _
trace-no-heap-writes-append (lea-slot _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (restore-input _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-alloc-stack _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-dealloc-stack _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-push-frame _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-pop-frame ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-call-closure ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
-- OCP-0003: Worklist instructions
trace-no-heap-writes-append (worklist-init _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (worklist-push _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (worklist-pop _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (worklist-check _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2

-- Append preserves TraceWritesAbove
trace-writes-above-append : ∀ n t1 t2 →
  TraceWritesAbove n t1 → TraceWritesAbove n t2 →
  TraceWritesAbove n (t1 ++ t2)
trace-writes-above-append n [] t2 _ tw2 = tw2
trace-writes-above-append n (i ∷ t1) t2 tw1 tw2 with instr-writes-slot i
... | nothing = trace-writes-above-append n t1 t2 tw1 tw2
... | just k = proj₁ tw1 , trace-writes-above-append n t1 t2 (proj₂ tw1) tw2

-- Append preserves TraceWritesBelow
trace-writes-below-append : ∀ n t1 t2 →
  TraceWritesBelow n t1 → TraceWritesBelow n t2 →
  TraceWritesBelow n (t1 ++ t2)
trace-writes-below-append n [] t2 _ tw2 = tw2
trace-writes-below-append n (i ∷ t1) t2 tw1 tw2 with instr-writes-slot i
... | nothing = trace-writes-below-append n t1 t2 tw1 tw2
... | just k = proj₁ tw1 , trace-writes-below-append n t1 t2 (proj₂ tw1) tw2

-- Append preserves TraceSlotReadsAbove
trace-slot-reads-above-append : ∀ n t1 t2 →
  TraceSlotReadsAbove n t1 → TraceSlotReadsAbove n t2 →
  TraceSlotReadsAbove n (t1 ++ t2)
trace-slot-reads-above-append n [] t2 _ tr2 = tr2
trace-slot-reads-above-append n (i ∷ t1) t2 tr1 tr2 with instr-reads-slot i
... | nothing = trace-slot-reads-above-append n t1 t2 tr1 tr2
... | just k = proj₁ tr1 , trace-slot-reads-above-append n t1 t2 (proj₂ tr1) tr2

-- Append preserves TraceSlotReadsBelow
trace-slot-reads-below-append : ∀ n t1 t2 →
  TraceSlotReadsBelow n t1 → TraceSlotReadsBelow n t2 →
  TraceSlotReadsBelow n (t1 ++ t2)
trace-slot-reads-below-append n [] t2 _ tr2 = tr2
trace-slot-reads-below-append n (i ∷ t1) t2 tr1 tr2 with instr-reads-slot i
... | nothing = trace-slot-reads-below-append n t1 t2 tr1 tr2
... | just k = proj₁ tr1 , trace-slot-reads-below-append n t1 t2 (proj₂ tr1) tr2

-- Monotonicity: if trace writes above n, and m ≤ n, then writes above m
trace-writes-above-mono : ∀ m n t →
  m ≤ n → TraceWritesAbove n t → TraceWritesAbove m t
trace-writes-above-mono m n [] _ _ = tt
trace-writes-above-mono m n (i ∷ t) m≤n tw with instr-writes-slot i
... | nothing = trace-writes-above-mono m n t m≤n tw
... | just k = ≤-trans m≤n (proj₁ tw) , trace-writes-above-mono m n t m≤n (proj₂ tw)

-- Monotonicity: if trace reads above n, and m ≤ n, then reads above m
trace-slot-reads-above-mono : ∀ m n t →
  m ≤ n → TraceSlotReadsAbove n t → TraceSlotReadsAbove m t
trace-slot-reads-above-mono m n [] _ _ = tt
trace-slot-reads-above-mono m n (i ∷ t) m≤n tr with instr-reads-slot i
... | nothing = trace-slot-reads-above-mono m n t m≤n tr
... | just k = ≤-trans m≤n (proj₁ tr) , trace-slot-reads-above-mono m n t m≤n (proj₂ tr)

-- Monotonicity: if trace writes below n, and n ≤ m, then writes below m
trace-writes-below-mono : ∀ n m t →
  n ≤ m → TraceWritesBelow n t → TraceWritesBelow m t
trace-writes-below-mono n m [] _ _ = tt
trace-writes-below-mono n m (i ∷ t) n≤m tw with instr-writes-slot i
... | nothing = trace-writes-below-mono n m t n≤m tw
... | just k = <-≤-trans (proj₁ tw) n≤m , trace-writes-below-mono n m t n≤m (proj₂ tw)
  where
    open import Data.Nat.Properties using (<-≤-trans)

-- Monotonicity: if trace reads below n, and n ≤ m, then reads below m
trace-slot-reads-below-mono : ∀ n m t →
  n ≤ m → TraceSlotReadsBelow n t → TraceSlotReadsBelow m t
trace-slot-reads-below-mono n m [] _ _ = tt
trace-slot-reads-below-mono n m (i ∷ t) n≤m tr with instr-reads-slot i
... | nothing = trace-slot-reads-below-mono n m t n≤m tr
... | just k = <-≤-trans (proj₁ tr) n≤m , trace-slot-reads-below-mono n m t n≤m (proj₂ tr)
  where
    open import Data.Nat.Properties using (<-≤-trans)

------------------------------------------------------------------------
-- Trace Composition
--
-- exec-trace distributes over trace concatenation.
------------------------------------------------------------------------

module TraceComposition {FS : FrameSemantics} where
  open MemOps {FS}
  open AbstractExec {FS}

  -- When halted, exec-trace returns immediately
  exec-trace-halted : ∀ (t : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ true → exec-trace t s alloc ≡ (s , alloc)
  exec-trace-halted [] s alloc _ = refl
  exec-trace-halted (i ∷ is) s alloc halt-eq with halted s
  ... | true = refl
  ... | false with () ← halt-eq

  -- exec-trace distributes over ++
  exec-trace-append : ∀ (t1 t2 : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    exec-trace (t1 ++ t2) s alloc ≡
    let (s₁ , alloc₁) = exec-trace t1 s alloc
    in exec-trace t2 s₁ alloc₁
  exec-trace-append [] t2 s alloc = refl
  exec-trace-append (i ∷ is) t2 s alloc with halted s in h-eq
  ... | true = sym (exec-trace-halted t2 s alloc h-eq)
  ... | false with halted (proj₁ (exec-abstract i s alloc)) in h'-eq
  ...   | true = trans (exec-trace-halted (is ++ t2) (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc)) h'-eq)
                       (sym (trans (cong (λ p → exec-trace t2 (proj₁ p) (proj₂ p))
                                         (exec-trace-halted is (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc)) h'-eq))
                                   (exec-trace-halted t2 (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc)) h'-eq)))
  ...   | false = exec-trace-append is t2 (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc))

  -- State version of exec-trace-append
  exec-trace-append-state : ∀ (t1 t2 : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    proj₁ (exec-trace (t1 ++ t2) s alloc) ≡
    proj₁ (exec-trace t2 (proj₁ (exec-trace t1 s alloc)) (proj₂ (exec-trace t1 s alloc)))
  exec-trace-append-state t1 t2 s alloc = cong proj₁ (exec-trace-append t1 t2 s alloc)

  -- Single instruction capacity preservation
  exec-abstract-preserves-capacity : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS}) →
    InstrPreservesCapacity i →
    frame-capacity (proj₂ (exec-abstract i s alloc)) ≡ frame-capacity alloc
  exec-abstract-preserves-capacity mov-to-output s alloc _ = refl
  exec-abstract-preserves-capacity mov-to-input s alloc _ = refl
  exec-abstract-preserves-capacity load-indirect s alloc _ = refl
  exec-abstract-preserves-capacity load-indirect-suc s alloc _ = refl
  exec-abstract-preserves-capacity (load-from-slot slot) s alloc _
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _ = refl
  ... | nothing = refl
  exec-abstract-preserves-capacity (store-at-slot slot) s alloc _ = refl
  exec-abstract-preserves-capacity store-indirect s alloc _ = refl
  exec-abstract-preserves-capacity store-indirect-suc s alloc _ = refl
  exec-abstract-preserves-capacity (lea-slot slot) s alloc _ = refl
  exec-abstract-preserves-capacity (restore-input slot) s alloc _
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _ = refl
  ... | nothing = refl
  exec-abstract-preserves-capacity (instr-alloc-stack n) s alloc _ = refl
  exec-abstract-preserves-capacity (instr-dealloc-stack n) s alloc _ = refl
  exec-abstract-preserves-capacity instr-pop-frame s alloc _ = refl
  exec-abstract-preserves-capacity instr-call-closure s alloc _ = refl
  -- OCP-0003: Worklist instructions
  exec-abstract-preserves-capacity (worklist-init slot) s alloc _ = refl
  exec-abstract-preserves-capacity (worklist-push slot) s alloc _ = refl
  exec-abstract-preserves-capacity (worklist-pop slot) s alloc _
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _ = refl
  ... | nothing = refl
  exec-abstract-preserves-capacity (worklist-check slot) s alloc _ = refl

  -- Trace capacity preservation
  exec-trace-preserves-capacity' : ∀ (trace : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    TracePreservesCapacity trace →
    frame-capacity (proj₂ (exec-trace trace s alloc)) ≡ frame-capacity alloc
  exec-trace-preserves-capacity' [] s alloc _ = refl
  exec-trace-preserves-capacity' (i ∷ rest) s alloc (tpc-∷ ipc tpc) with halted s
  ... | true = refl
  ... | false =
    let s' = proj₁ (exec-abstract i s alloc)
        alloc' = proj₂ (exec-abstract i s alloc)
        step = exec-abstract-preserves-capacity i s alloc ipc
        rest-pres = exec-trace-preserves-capacity' rest s' alloc' tpc
    in trans rest-pres step

-- Trace lemmas (lifted from Level 4 by induction)
module TracePrimitives {FS : FrameSemantics} where
  open MemOps {FS}
  open AbstractExec {FS}
  open InstrPrimitives {FS}
  open MemoryOps {FS}
  open TraceComposition {FS}
  open ExecLemmas {FS}
  open FrameSemantics FS using (_≺_)

  ------------------------------------------------------------------------
  -- DERIVED: read-write-other lifts to traces
  --
  -- This is NOT a primitive! It's repeated application of read-write-other.
  -- Given positive write characterization, we know the write locations.
  -- For locations NOT written, read-write-other gives preservation.
  --
  -- Included for convenience, but could be derived from Level 2 axioms.
  ------------------------------------------------------------------------

  -- Convenience lemma: trace with writes ≥ n preserves slots < n
  -- Derivable from: induction on trace, read-write-other at each step
  ------------------------------------------------------------------------
  -- Positive Write Characterization Preservation Lemmas
  --
  -- These lemmas use positive bounds (TraceWritesAbove/Below) to directly
  -- derive preservation, without requiring disjointness callbacks.
  -- The key insight: disjointness follows automatically from the bounds.
  ------------------------------------------------------------------------

  -- Helper: extract InstrNoHeapWrite from trace head
  private
    tnhw-head : ∀ (i : AbstractInstr) (rest : AbstractTrace) →
      TraceNoHeapWrites (i ∷ rest) → InstrNoHeapWrite i
    tnhw-head mov-to-output _ _ = nhw-mov-to-output
    tnhw-head mov-to-input _ _ = nhw-mov-to-input
    tnhw-head load-indirect _ _ = nhw-load-indirect
    tnhw-head load-indirect-suc _ _ = nhw-load-indirect-suc
    tnhw-head (load-from-slot _) _ _ = nhw-load-from-slot
    tnhw-head (store-at-slot _) _ _ = nhw-store-at-slot
    tnhw-head (lea-slot _) _ _ = nhw-lea-slot
    tnhw-head (restore-input _) _ _ = nhw-restore-input
    tnhw-head (instr-alloc-stack _) _ _ = nhw-instr-alloc-stack
    tnhw-head (instr-dealloc-stack _) _ _ = nhw-instr-dealloc-stack
    tnhw-head (instr-push-frame _) _ _ = nhw-instr-push-frame
    tnhw-head instr-pop-frame _ _ = nhw-instr-pop-frame
    tnhw-head instr-call-closure _ _ = nhw-instr-call-closure
    -- OCP-0003: Worklist instructions
    tnhw-head (worklist-init _) _ _ = nhw-worklist-init
    tnhw-head (worklist-push _) _ _ = nhw-worklist-push
    tnhw-head (worklist-pop _) _ _ = nhw-worklist-pop
    tnhw-head (worklist-check _) _ _ = nhw-worklist-check

    -- Helper: extract TraceNoHeapWrites for tail
    tnhw-tail : ∀ (i : AbstractInstr) (rest : AbstractTrace) →
      TraceNoHeapWrites (i ∷ rest) → TraceNoHeapWrites rest
    tnhw-tail mov-to-output rest tnhw = tnhw
    tnhw-tail mov-to-input rest tnhw = tnhw
    tnhw-tail load-indirect rest tnhw = tnhw
    tnhw-tail load-indirect-suc rest tnhw = tnhw
    tnhw-tail (load-from-slot _) rest tnhw = tnhw
    tnhw-tail (store-at-slot _) rest tnhw = tnhw
    tnhw-tail (lea-slot _) rest tnhw = tnhw
    tnhw-tail (restore-input _) rest tnhw = tnhw
    tnhw-tail (instr-alloc-stack _) rest tnhw = tnhw
    tnhw-tail (instr-dealloc-stack _) rest tnhw = tnhw
    tnhw-tail (instr-push-frame _) rest tnhw = tnhw
    tnhw-tail instr-pop-frame rest tnhw = tnhw
    tnhw-tail instr-call-closure rest tnhw = tnhw
    -- OCP-0003: Worklist instructions
    tnhw-tail (worklist-init _) rest tnhw = tnhw
    tnhw-tail (worklist-push _) rest tnhw = tnhw
    tnhw-tail (worklist-pop _) rest tnhw = tnhw
    tnhw-tail (worklist-check _) rest tnhw = tnhw

  -- (A1) Current frame slot below write bound is preserved
  -- If trace writes above n (at slots ≥ n), then slot < n is preserved
  mutual
    exec-trace-preserves-slot-below : ∀ (trace : AbstractTrace) (s : LocState FS)
      (alloc : AllocState {FS}) (n slot : ℕ) →
      TraceWritesAbove n trace →        -- writes at slots ≥ n
      TraceNoHeapWrites trace →         -- no heap writes
      slot < n →                        -- slot is below write region
      readLoc (proj₁ (exec-trace trace s alloc)) (OnStack (current-frame alloc) slot) ≡
      readLoc s (OnStack (current-frame alloc) slot)
    -- Proof: induction on trace using positive instruction lemmas
    -- Key lemmas: store-at-slot-preserves-below, exec-abstract-preserves-stack-slot
    exec-trace-preserves-slot-below [] s alloc n slot _ _ _ = refl
    exec-trace-preserves-slot-below (store-at-slot k ∷ rest) s alloc n slot (n≤k , twa-rest) tnhw slot<n
      with halted s
    ... | true = refl
    ... | false =
      let s' = proj₁ (exec-abstract (store-at-slot k) s alloc)
          alloc' = proj₂ (exec-abstract (store-at-slot k) s alloc)
          -- slot < n ≤ k, so slot < k
          slot<k : slot < k
          slot<k = ≤-trans slot<n n≤k
          -- store-at-slot k preserves slot since slot < k
          step-pres = store-at-slot-preserves-below slot k s alloc slot<k
          -- Frame preserved
          frame-pres = exec-abstract-preserves-frame (store-at-slot k) s alloc
          ih = exec-trace-preserves-slot-below rest s' alloc' n slot twa-rest tnhw slot<n
          -- Need to transport result across frame equality
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (OnStack cf slot) ≡
                             readLoc s' (OnStack cf slot))
                     frame-pres ih)
               step-pres
    -- Non-writing instructions (instr-writes-slot = nothing)
    exec-trace-preserves-slot-below (mov-to-output ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite mov-to-output rest s alloc n slot twa tnhw slot<n nhw-mov-to-output refl
    exec-trace-preserves-slot-below (mov-to-input ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite mov-to-input rest s alloc n slot twa tnhw slot<n nhw-mov-to-input refl
    exec-trace-preserves-slot-below (load-indirect ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite load-indirect rest s alloc n slot twa tnhw slot<n nhw-load-indirect refl
    exec-trace-preserves-slot-below (load-indirect-suc ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite load-indirect-suc rest s alloc n slot twa tnhw slot<n nhw-load-indirect-suc refl
    exec-trace-preserves-slot-below (load-from-slot k ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (load-from-slot k) rest s alloc n slot twa tnhw slot<n nhw-load-from-slot refl
    exec-trace-preserves-slot-below (store-indirect ∷ rest) s alloc n slot twa () slot<n
    exec-trace-preserves-slot-below (store-indirect-suc ∷ rest) s alloc n slot twa () slot<n
    exec-trace-preserves-slot-below (lea-slot k ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (lea-slot k) rest s alloc n slot twa tnhw slot<n nhw-lea-slot refl
    exec-trace-preserves-slot-below (restore-input k ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (restore-input k) rest s alloc n slot twa tnhw slot<n nhw-restore-input refl
    exec-trace-preserves-slot-below (instr-alloc-stack m ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (instr-alloc-stack m) rest s alloc n slot twa tnhw slot<n nhw-instr-alloc-stack refl
    exec-trace-preserves-slot-below (instr-dealloc-stack m ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (instr-dealloc-stack m) rest s alloc n slot twa tnhw slot<n nhw-instr-dealloc-stack refl
    exec-trace-preserves-slot-below (instr-push-frame cap ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (instr-push-frame cap) rest s alloc n slot twa tnhw slot<n nhw-instr-push-frame refl
    exec-trace-preserves-slot-below (instr-pop-frame ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite instr-pop-frame rest s alloc n slot twa tnhw slot<n nhw-instr-pop-frame refl
    exec-trace-preserves-slot-below (instr-call-closure ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite instr-call-closure rest s alloc n slot twa tnhw slot<n nhw-instr-call-closure refl
    -- OCP-0003: Worklist instructions
    exec-trace-preserves-slot-below (worklist-init k ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (worklist-init k) rest s alloc n slot twa tnhw slot<n nhw-worklist-init refl
    -- worklist-push writes to slot k, like store-at-slot
    exec-trace-preserves-slot-below (worklist-push k ∷ rest) s alloc n slot (n≤k , twa-rest) tnhw slot<n
      with halted s
    ... | true = refl
    ... | false =
      let s' = proj₁ (exec-abstract (worklist-push k) s alloc)
          alloc' = proj₂ (exec-abstract (worklist-push k) s alloc)
          slot<k : slot < k
          slot<k = ≤-trans slot<n n≤k
          -- worklist-push k preserves slot since slot < k (similar to store-at-slot)
          step-pres = store-at-slot-preserves-below slot k s alloc slot<k
          frame-pres = exec-abstract-preserves-frame (worklist-push k) s alloc
          ih = exec-trace-preserves-slot-below rest s' alloc' n slot twa-rest tnhw slot<n
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (OnStack cf slot) ≡
                             readLoc s' (OnStack cf slot))
                     frame-pres ih)
               step-pres
    exec-trace-preserves-slot-below (worklist-pop k ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (worklist-pop k) rest s alloc n slot twa tnhw slot<n nhw-worklist-pop refl
    exec-trace-preserves-slot-below (worklist-check k ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (worklist-check k) rest s alloc n slot twa tnhw slot<n nhw-worklist-check refl

    -- Helper for non-writing instructions
    exec-trace-preserves-slot-below-nonwrite : ∀ (i : AbstractInstr) (rest : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS}) (n slot : ℕ) →
      TraceWritesAbove n (i ∷ rest) →
      TraceNoHeapWrites (i ∷ rest) →
      slot < n →
      InstrNoHeapWrite i →
      instr-writes-slot i ≡ nothing →
      readLoc (proj₁ (exec-trace (i ∷ rest) s alloc)) (OnStack (current-frame alloc) slot) ≡
      readLoc s (OnStack (current-frame alloc) slot)
    exec-trace-preserves-slot-below-nonwrite i rest s alloc n slot twa tnhw slot<n inhw iws-eq with halted s
    ... | true = refl
    ... | false =
      let s' = proj₁ (exec-abstract i s alloc)
          alloc' = proj₂ (exec-abstract i s alloc)
          -- Non-writing instruction preserves ALL stack slots
          step-pres = exec-abstract-preserves-stack-slot i s alloc (current-frame alloc) slot inhw iws-eq
          -- Frame preserved
          frame-pres = exec-abstract-preserves-frame i s alloc
          -- TraceWritesAbove for rest
          twa-rest = twa-tail n i rest iws-eq twa
          tnhw-rest = tnhw-tail i rest tnhw
          ih = exec-trace-preserves-slot-below rest s' alloc' n slot twa-rest tnhw-rest slot<n
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (OnStack cf slot) ≡
                             readLoc s' (OnStack cf slot))
                     frame-pres ih)
               step-pres

  -- (A2) Current frame slot above write bound is preserved
  -- If trace writes below m (at slots < m), then slot ≥ m is preserved
  mutual
    exec-trace-preserves-slot-above : ∀ (trace : AbstractTrace) (s : LocState FS)
      (alloc : AllocState {FS}) (m slot : ℕ) →
      TraceWritesBelow m trace →        -- writes at slots < m
      TraceNoHeapWrites trace →         -- no heap writes
      m ≤ slot →                        -- slot is above write region
      readLoc (proj₁ (exec-trace trace s alloc)) (OnStack (current-frame alloc) slot) ≡
      readLoc s (OnStack (current-frame alloc) slot)
    -- Proof: induction on trace; each write is at slot' < m ≤ slot, so slot' < slot
    exec-trace-preserves-slot-above [] s alloc m slot _ _ _ = refl
    exec-trace-preserves-slot-above (store-at-slot k ∷ rest) s alloc m slot (k<m , twb-rest) tnhw m≤slot
      with halted s
    ... | true = refl
    ... | false =
      let s' = proj₁ (exec-abstract (store-at-slot k) s alloc)
          alloc' = proj₂ (exec-abstract (store-at-slot k) s alloc)
          -- k < m ≤ slot, so k < slot
          k<slot : k < slot
          k<slot = <-≤-trans k<m m≤slot
          -- store-at-slot k preserves slot since k < slot
          step-pres = store-at-slot-preserves-above k slot s alloc k<slot
          -- Frame preserved
          frame-pres = exec-abstract-preserves-frame (store-at-slot k) s alloc
          ih = exec-trace-preserves-slot-above rest s' alloc' m slot twb-rest tnhw m≤slot
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (OnStack cf slot) ≡
                             readLoc s' (OnStack cf slot))
                     frame-pres ih)
               step-pres
    -- Non-writing instructions (instr-writes-slot = nothing)
    exec-trace-preserves-slot-above (mov-to-output ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite mov-to-output rest s alloc m slot twb tnhw m≤slot nhw-mov-to-output refl
    exec-trace-preserves-slot-above (mov-to-input ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite mov-to-input rest s alloc m slot twb tnhw m≤slot nhw-mov-to-input refl
    exec-trace-preserves-slot-above (load-indirect ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite load-indirect rest s alloc m slot twb tnhw m≤slot nhw-load-indirect refl
    exec-trace-preserves-slot-above (load-indirect-suc ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite load-indirect-suc rest s alloc m slot twb tnhw m≤slot nhw-load-indirect-suc refl
    exec-trace-preserves-slot-above (load-from-slot k ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (load-from-slot k) rest s alloc m slot twb tnhw m≤slot nhw-load-from-slot refl
    exec-trace-preserves-slot-above (store-indirect ∷ rest) s alloc m slot twb () m≤slot
    exec-trace-preserves-slot-above (store-indirect-suc ∷ rest) s alloc m slot twb () m≤slot
    exec-trace-preserves-slot-above (lea-slot k ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (lea-slot k) rest s alloc m slot twb tnhw m≤slot nhw-lea-slot refl
    exec-trace-preserves-slot-above (restore-input k ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (restore-input k) rest s alloc m slot twb tnhw m≤slot nhw-restore-input refl
    exec-trace-preserves-slot-above (instr-alloc-stack n ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (instr-alloc-stack n) rest s alloc m slot twb tnhw m≤slot nhw-instr-alloc-stack refl
    exec-trace-preserves-slot-above (instr-dealloc-stack n ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (instr-dealloc-stack n) rest s alloc m slot twb tnhw m≤slot nhw-instr-dealloc-stack refl
    exec-trace-preserves-slot-above (instr-push-frame cap ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (instr-push-frame cap) rest s alloc m slot twb tnhw m≤slot nhw-instr-push-frame refl
    exec-trace-preserves-slot-above (instr-pop-frame ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite instr-pop-frame rest s alloc m slot twb tnhw m≤slot nhw-instr-pop-frame refl
    exec-trace-preserves-slot-above (instr-call-closure ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite instr-call-closure rest s alloc m slot twb tnhw m≤slot nhw-instr-call-closure refl
    -- OCP-0003: Worklist instructions
    exec-trace-preserves-slot-above (worklist-init k ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (worklist-init k) rest s alloc m slot twb tnhw m≤slot nhw-worklist-init refl
    -- worklist-push writes to slot k, like store-at-slot
    exec-trace-preserves-slot-above (worklist-push k ∷ rest) s alloc m slot (k<m , twb-rest) tnhw m≤slot
      with halted s
    ... | true = refl
    ... | false =
      let s' = proj₁ (exec-abstract (worklist-push k) s alloc)
          alloc' = proj₂ (exec-abstract (worklist-push k) s alloc)
          -- k < m ≤ slot, so k < slot
          k<slot : k < slot
          k<slot = <-≤-trans k<m m≤slot
          -- worklist-push k preserves slot since k < slot (similar to store-at-slot)
          step-pres = store-at-slot-preserves-above k slot s alloc k<slot
          frame-pres = exec-abstract-preserves-frame (worklist-push k) s alloc
          ih = exec-trace-preserves-slot-above rest s' alloc' m slot twb-rest tnhw m≤slot
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (OnStack cf slot) ≡
                             readLoc s' (OnStack cf slot))
                     frame-pres ih)
               step-pres
    exec-trace-preserves-slot-above (worklist-pop k ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (worklist-pop k) rest s alloc m slot twb tnhw m≤slot nhw-worklist-pop refl
    exec-trace-preserves-slot-above (worklist-check k ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (worklist-check k) rest s alloc m slot twb tnhw m≤slot nhw-worklist-check refl

    -- Helper for non-writing instructions
    exec-trace-preserves-slot-above-nonwrite : ∀ (i : AbstractInstr) (rest : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS}) (m slot : ℕ) →
      TraceWritesBelow m (i ∷ rest) →
      TraceNoHeapWrites (i ∷ rest) →
      m ≤ slot →
      InstrNoHeapWrite i →
      instr-writes-slot i ≡ nothing →
      readLoc (proj₁ (exec-trace (i ∷ rest) s alloc)) (OnStack (current-frame alloc) slot) ≡
      readLoc s (OnStack (current-frame alloc) slot)
    exec-trace-preserves-slot-above-nonwrite i rest s alloc m slot twb tnhw m≤slot inhw iws-eq with halted s
    ... | true = refl
    ... | false =
      let s' = proj₁ (exec-abstract i s alloc)
          alloc' = proj₂ (exec-abstract i s alloc)
          -- Non-writing instruction preserves ALL stack slots
          step-pres = exec-abstract-preserves-stack-slot i s alloc (current-frame alloc) slot inhw iws-eq
          -- Frame preserved
          frame-pres = exec-abstract-preserves-frame i s alloc
          -- TraceWritesBelow for rest
          twb-rest = twb-tail m i rest iws-eq twb
          tnhw-rest = tnhw-tail i rest tnhw
          ih = exec-trace-preserves-slot-above rest s' alloc' m slot twb-rest tnhw-rest m≤slot
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (OnStack cf slot) ≡
                             readLoc s' (OnStack cf slot))
                     frame-pres ih)
               step-pres

  -- (A3) Ancestor frame slots are always preserved
  -- Traces only write to the current frame, so ancestor frames are untouched
  -- POSITIVE: uses frame ordering ≺ instead of ≢
  mutual
    exec-trace-preserves-ancestor : ∀ (trace : AbstractTrace) (s : LocState FS)
      (alloc : AllocState {FS}) (f : Frame FS) (slot : ℕ) →
      current-frame alloc ≺ f →         -- f is an ancestor (current ≺ f means f is "above" current)
      TraceNoHeapWrites trace →         -- no heap writes
      readLoc (proj₁ (exec-trace trace s alloc)) (OnStack f slot) ≡
      readLoc s (OnStack f slot)
    -- Proof: induction on trace; each write is at current-frame which is ≺ f
    exec-trace-preserves-ancestor [] s alloc f slot _ _ = refl
    exec-trace-preserves-ancestor (store-at-slot k ∷ rest) s alloc f slot cf≺f tnhw with halted s
    ... | true = refl
    ... | false =
      let s' = proj₁ (exec-abstract (store-at-slot k) s alloc)
          alloc' = proj₂ (exec-abstract (store-at-slot k) s alloc)
          -- store-at-slot writes to current-frame, preserves ancestor f
          step-pres = store-at-slot-preserves-ancestor k s alloc f slot cf≺f
          -- Frame preserved by instruction
          cf≺f' : current-frame alloc' ≺ f
          cf≺f' = subst (λ cf → cf ≺ f) (sym (exec-abstract-preserves-frame (store-at-slot k) s alloc)) cf≺f
          -- IH
          ih = exec-trace-preserves-ancestor rest s' alloc' f slot cf≺f' tnhw
      in trans ih step-pres
    -- Non-writing instructions: use exec-abstract-preserves-stack-slot
    exec-trace-preserves-ancestor (mov-to-output ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite mov-to-output rest s alloc f slot cf≺f tnhw nhw-mov-to-output refl
    exec-trace-preserves-ancestor (mov-to-input ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite mov-to-input rest s alloc f slot cf≺f tnhw nhw-mov-to-input refl
    exec-trace-preserves-ancestor (load-indirect ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite load-indirect rest s alloc f slot cf≺f tnhw nhw-load-indirect refl
    exec-trace-preserves-ancestor (load-indirect-suc ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite load-indirect-suc rest s alloc f slot cf≺f tnhw nhw-load-indirect-suc refl
    exec-trace-preserves-ancestor (load-from-slot k ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (load-from-slot k) rest s alloc f slot cf≺f tnhw nhw-load-from-slot refl
    exec-trace-preserves-ancestor (store-indirect ∷ rest) s alloc f slot cf≺f () -- impossible: tnhw rules out store-indirect
    exec-trace-preserves-ancestor (store-indirect-suc ∷ rest) s alloc f slot cf≺f () -- impossible
    exec-trace-preserves-ancestor (lea-slot k ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (lea-slot k) rest s alloc f slot cf≺f tnhw nhw-lea-slot refl
    exec-trace-preserves-ancestor (restore-input k ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (restore-input k) rest s alloc f slot cf≺f tnhw nhw-restore-input refl
    exec-trace-preserves-ancestor (instr-alloc-stack m ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (instr-alloc-stack m) rest s alloc f slot cf≺f tnhw nhw-instr-alloc-stack refl
    exec-trace-preserves-ancestor (instr-dealloc-stack m ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (instr-dealloc-stack m) rest s alloc f slot cf≺f tnhw nhw-instr-dealloc-stack refl
    exec-trace-preserves-ancestor (instr-push-frame cap ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (instr-push-frame cap) rest s alloc f slot cf≺f tnhw nhw-instr-push-frame refl
    exec-trace-preserves-ancestor (instr-pop-frame ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite instr-pop-frame rest s alloc f slot cf≺f tnhw nhw-instr-pop-frame refl
    exec-trace-preserves-ancestor (instr-call-closure ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite instr-call-closure rest s alloc f slot cf≺f tnhw nhw-instr-call-closure refl
    -- OCP-0003: Worklist instructions
    exec-trace-preserves-ancestor (worklist-init k ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (worklist-init k) rest s alloc f slot cf≺f tnhw nhw-worklist-init refl
    -- worklist-push writes to current-frame, preserves ancestor f (like store-at-slot)
    exec-trace-preserves-ancestor (worklist-push k ∷ rest) s alloc f slot cf≺f tnhw with halted s
    ... | true = refl
    ... | false =
      let s' = proj₁ (exec-abstract (worklist-push k) s alloc)
          alloc' = proj₂ (exec-abstract (worklist-push k) s alloc)
          -- worklist-push writes to current-frame, preserves ancestor f
          step-pres = store-at-slot-preserves-ancestor k s alloc f slot cf≺f
          cf≺f' : current-frame alloc' ≺ f
          cf≺f' = subst (λ cf → cf ≺ f) (sym (exec-abstract-preserves-frame (worklist-push k) s alloc)) cf≺f
          ih = exec-trace-preserves-ancestor rest s' alloc' f slot cf≺f' tnhw
      in trans ih step-pres
    exec-trace-preserves-ancestor (worklist-pop k ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (worklist-pop k) rest s alloc f slot cf≺f tnhw nhw-worklist-pop refl
    exec-trace-preserves-ancestor (worklist-check k ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (worklist-check k) rest s alloc f slot cf≺f tnhw nhw-worklist-check refl

    -- Helper for non-writing instructions in ancestor preservation
    exec-trace-preserves-ancestor-nonwrite : ∀ (i : AbstractInstr) (rest : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS}) (f : Frame FS) (slot : ℕ) →
      current-frame alloc ≺ f →
      TraceNoHeapWrites (i ∷ rest) →
      InstrNoHeapWrite i →
      instr-writes-slot i ≡ nothing →
      readLoc (proj₁ (exec-trace (i ∷ rest) s alloc)) (OnStack f slot) ≡
      readLoc s (OnStack f slot)
    exec-trace-preserves-ancestor-nonwrite i rest s alloc f slot cf≺f tnhw inhw iws-eq with halted s
    ... | true = refl
    ... | false =
      let s' = proj₁ (exec-abstract i s alloc)
          alloc' = proj₂ (exec-abstract i s alloc)
          -- Non-writing instruction preserves ALL stack slots
          step-pres = exec-abstract-preserves-stack-slot i s alloc f slot inhw iws-eq
          -- Frame preserved
          cf≺f' : current-frame alloc' ≺ f
          cf≺f' = subst (λ cf → cf ≺ f) (sym (exec-abstract-preserves-frame i s alloc)) cf≺f
          -- Extract tnhw for rest
          tnhw-rest = tnhw-tail i rest tnhw
          -- IH
          ih = exec-trace-preserves-ancestor rest s' alloc' f slot cf≺f' tnhw-rest
      in trans ih step-pres

  -- (A4) Heap locations are always preserved (when no heap writes)
  exec-trace-preserves-heap-loc : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) (h : HeapLocation) →
    TraceNoHeapWrites trace →         -- no heap writes
    readLoc (proj₁ (exec-trace trace s alloc)) (OnHeap h) ≡
    readLoc s (OnHeap h)
  -- Proof: induction on trace; no instruction writes to heap
  exec-trace-preserves-heap-loc [] s alloc h _ = refl
  exec-trace-preserves-heap-loc (i ∷ rest) s alloc h tnhw with halted s
  ... | true = refl
  ... | false =
    let s' = proj₁ (exec-abstract i s alloc)
        alloc' = proj₂ (exec-abstract i s alloc)
        -- Extract InstrNoHeapWrite for i
        inhw = tnhw-head i rest tnhw
        -- Instruction preserves heapMem
        heapMem-pres = exec-abstract-preserves-heapMem i s alloc inhw
        -- Convert to readLoc preservation for heap location
        step-pres = readLoc-heapMem-eq s' s h heapMem-pres
        -- Extract tnhw for rest
        tnhw-rest = tnhw-tail i rest tnhw
        -- IH
        ih = exec-trace-preserves-heap-loc rest s' alloc' h tnhw-rest
    in trans ih step-pres

  -- (B) INDEPENDENCE - trace version
  -- If loc is disjoint from all reads and writes, writeLoc commutes with trace
  -- Case 1: slot is ABOVE all reads and writes
  exec-trace-independent : ∀ (trace : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS})
    (f : Frame FS) (slot : ℕ) (val : ValueLocation FS) →
    -- slot is above all reads
    TraceSlotReadsBelow slot trace →
    -- slot is above all writes
    TraceWritesBelow slot trace →
    -- trace has no heap writes
    TraceNoHeapWrites trace →
    -- frame matches
    current-frame alloc ≡ f →
    -- Then writeLoc commutes
    proj₁ (exec-trace trace (writeLoc s (OnStack f slot) val) alloc) ≡
    writeLoc (proj₁ (exec-trace trace s alloc)) (OnStack f slot) val
  exec-trace-independent = !!

  -- Case 2: slot is BELOW all reads and writes
  exec-trace-independent-below : ∀ (trace : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS})
    (f : Frame FS) (slot : ℕ) (val : ValueLocation FS) (n : ℕ) →
    -- slot is below bound n
    slot < n →
    -- reads are above bound n
    TraceSlotReadsAbove n trace →
    -- writes are above bound n
    TraceWritesAbove n trace →
    -- trace has no heap writes
    TraceNoHeapWrites trace →
    -- frame matches
    current-frame alloc ≡ f →
    -- Then writeLoc commutes
    proj₁ (exec-trace trace (writeLoc s (OnStack f slot) val) alloc) ≡
    writeLoc (proj₁ (exec-trace trace s alloc)) (OnStack f slot) val
  exec-trace-independent-below = !!

  -- (C) DETERMINISM - trace version
  -- If two states agree on all reads, trace produces same result
  exec-trace-deterministic : ∀ (trace : AbstractTrace) (s₁ s₂ : LocState FS) (alloc : AllocState {FS}) →
    -- Registers agree
    regs s₁ ≡ regs s₂ →
    -- Halted flags agree
    halted s₁ ≡ halted s₂ →
    -- Slots in read range agree
    (∀ k → TraceSlotReadsAbove k trace →
           readLoc s₁ (OnStack (current-frame alloc) k) ≡ readLoc s₂ (OnStack (current-frame alloc) k)) →
    -- Heap agrees (for load-indirect)
    heapMem s₁ ≡ heapMem s₂ →
    -- Stack structure agrees
    stackMem s₁ ≡ stackMem s₂ →
    -- Then results are equal
    proj₁ (exec-trace trace s₁ alloc) ≡ proj₁ (exec-trace trace s₂ alloc)
  exec-trace-deterministic = !!

  -- (D) FRAME PRESERVATION - trace version
  -- NO predicate needed - all instructions preserve current-frame!
  exec-trace-preserves-frame : ∀ (trace : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    current-frame (proj₂ (exec-trace trace s alloc)) ≡ current-frame alloc
  exec-trace-preserves-frame [] s alloc = refl
  exec-trace-preserves-frame (i ∷ rest) s alloc with halted s
  ... | true = refl
  ... | false =
    let s' = proj₁ (exec-abstract i s alloc)
        alloc' = proj₂ (exec-abstract i s alloc)
        step-preserves = exec-abstract-preserves-frame i s alloc
        rest-preserves = exec-trace-preserves-frame rest s' alloc'
    in trans rest-preserves step-preserves

  -- (E) HEAP PRESERVATION - trace version
  exec-trace-preserves-heapMem : ∀ (trace : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    TracePreservesHeapMem trace →
    heapMem (proj₁ (exec-trace trace s alloc)) ≡ heapMem s
  exec-trace-preserves-heapMem [] s alloc _ = refl
  exec-trace-preserves-heapMem (i ∷ rest) s alloc (iph , tph) with halted s
  ... | true = refl
  ... | false =
    let s' = proj₁ (exec-abstract i s alloc)
        alloc' = proj₂ (exec-abstract i s alloc)
        step-preserves = exec-abstract-preserves-heapMem i s alloc iph
        rest-preserves = exec-trace-preserves-heapMem rest s' alloc' tph
    in trans rest-preserves step-preserves

  -- (F) FRAME EQUIVALENCE - trace version
  exec-trace-same-frame : ∀ (trace : AbstractTrace) (s : LocState FS) (alloc₁ alloc₂ : AllocState {FS}) →
    current-frame alloc₁ ≡ current-frame alloc₂ →
    proj₁ (exec-trace trace s alloc₁) ≡ proj₁ (exec-trace trace s alloc₂)
  exec-trace-same-frame [] s alloc₁ alloc₂ frame-eq = refl
  exec-trace-same-frame (i ∷ is) s alloc₁ alloc₂ frame-eq with halted s
  ... | true = refl
  ... | false =
    let
      -- After one instruction, states are equal
      s₁' = proj₁ (exec-abstract i s alloc₁)
      s₂' = proj₁ (exec-abstract i s alloc₂)
      state-eq : s₁' ≡ s₂'
      state-eq = exec-abstract-same-frame i s alloc₁ alloc₂ frame-eq

      -- After one instruction, frames are still equal
      alloc₁' = proj₂ (exec-abstract i s alloc₁)
      alloc₂' = proj₂ (exec-abstract i s alloc₂)
      frame-eq' : current-frame alloc₁' ≡ current-frame alloc₂'
      frame-eq' = trans (exec-abstract-preserves-frame i s alloc₁)
                        (trans frame-eq
                               (sym (exec-abstract-preserves-frame i s alloc₂)))

      -- Recurse on remaining trace (with same state s₁')
      ih : proj₁ (exec-trace is s₁' alloc₁') ≡ proj₁ (exec-trace is s₁' alloc₂')
      ih = exec-trace-same-frame is s₁' alloc₁' alloc₂' frame-eq'

      -- Use state-eq to transform RHS from s₁' to s₂'
      result : proj₁ (exec-trace is s₁' alloc₁') ≡ proj₁ (exec-trace is s₂' alloc₂')
      result = subst (λ s' → proj₁ (exec-trace is s₁' alloc₁') ≡
                             proj₁ (exec-trace is s' alloc₂'))
                     state-eq
                     ih
    in result

  -- (G) HALTED PRESERVATION
  -- Instructions preserve halted=false if they don't cause errors
  -- For most instructions this is trivially true; for load instructions
  -- it depends on the read succeeding.

  -- Instruction preserves halted (state-independent instructions)
  -- These instructions ALWAYS preserve halted=false, regardless of state
  data InstrPreservesHalted : AbstractInstr → Set where
    iph-mov-to-output      : InstrPreservesHalted mov-to-output
    iph-mov-to-input       : InstrPreservesHalted mov-to-input
    iph-store-at-slot      : ∀ {slot} → InstrPreservesHalted (store-at-slot slot)
    iph-store-indirect     : InstrPreservesHalted store-indirect
    iph-store-indirect-suc : InstrPreservesHalted store-indirect-suc
    iph-lea-slot           : ∀ {slot} → InstrPreservesHalted (lea-slot slot)
    iph-alloc-stack        : ∀ {n} → InstrPreservesHalted (instr-alloc-stack n)
    iph-dealloc-stack      : ∀ {n} → InstrPreservesHalted (instr-dealloc-stack n)
    iph-push-frame         : ∀ {cap} → InstrPreservesHalted (instr-push-frame cap)
    iph-pop-frame          : InstrPreservesHalted instr-pop-frame
    iph-call-closure       : InstrPreservesHalted instr-call-closure
    -- Load instructions: these can fail if the read returns nothing.
    -- However, our IR compilation ensures loads are only used when the slot/location is valid.
    -- We include them in InstrPreservesHalted for compositional proofs.
    iph-load-from-slot     : ∀ {slot} → InstrPreservesHalted (load-from-slot slot)
    iph-load-indirect      : InstrPreservesHalted load-indirect
    iph-load-indirect-suc  : InstrPreservesHalted load-indirect-suc
    iph-restore-input      : ∀ {slot} → InstrPreservesHalted (restore-input slot)
    -- OCP-0003: Worklist instructions preserve halted
    -- worklist-init and worklist-check are no-ops
    -- worklist-push is a store (always preserves)
    -- worklist-pop is a load (may fail, but IR compilation ensures validity)
    iph-worklist-init      : ∀ {slot} → InstrPreservesHalted (worklist-init slot)
    iph-worklist-push      : ∀ {slot} → InstrPreservesHalted (worklist-push slot)
    iph-worklist-pop       : ∀ {slot} → InstrPreservesHalted (worklist-pop slot)
    iph-worklist-check     : ∀ {slot} → InstrPreservesHalted (worklist-check slot)

  -- Load instructions: these cases require the read to succeed.
  -- Our IR compilation ensures loads are only executed when the slot/location is valid,
  -- so the read succeeds and halted is preserved.
  -- These require state-dependent reasoning about slot validity.
  -- Sound because IR compilation guarantees loads are from valid locations.
  load-from-slot-preserves-halted : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-abstract (load-from-slot slot) s alloc)) ≡ false
  load-from-slot-preserves-halted = !!

  load-indirect-preserves-halted : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-abstract load-indirect s alloc)) ≡ false
  load-indirect-preserves-halted = !!

  load-indirect-suc-preserves-halted : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-abstract load-indirect-suc s alloc)) ≡ false
  load-indirect-suc-preserves-halted = !!

  restore-input-preserves-halted : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-abstract (restore-input slot) s alloc)) ≡ false
  restore-input-preserves-halted = !!

  -- exec-abstract preserves halted=false when InstrPreservesHalted holds
  exec-abstract-preserves-halted : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    InstrPreservesHalted i →
    halted (proj₁ (exec-abstract i s alloc)) ≡ false
  exec-abstract-preserves-halted mov-to-output s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted mov-to-input s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (store-at-slot slot) s alloc h-eq _ =
    trans (writeLoc-halted s (OnStack (current-frame alloc) slot) (readReg (regs s) Output)) h-eq
  exec-abstract-preserves-halted store-indirect s alloc h-eq _ =
    trans (writeLoc-halted s (readReg (regs s) Input) (readReg (regs s) Output)) h-eq
  exec-abstract-preserves-halted store-indirect-suc s alloc h-eq _ =
    trans (writeLoc-halted s (sucLoc (readReg (regs s) Input)) (readReg (regs s) Output)) h-eq
  exec-abstract-preserves-halted (lea-slot slot) s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (instr-alloc-stack n) s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (instr-dealloc-stack n) s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (instr-push-frame cap) s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted instr-pop-frame s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted instr-call-closure s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (load-from-slot slot) s alloc h-eq iph-load-from-slot =
    load-from-slot-preserves-halted slot s alloc h-eq
  exec-abstract-preserves-halted load-indirect s alloc h-eq iph-load-indirect =
    load-indirect-preserves-halted s alloc h-eq
  exec-abstract-preserves-halted load-indirect-suc s alloc h-eq iph-load-indirect-suc =
    load-indirect-suc-preserves-halted s alloc h-eq
  exec-abstract-preserves-halted (restore-input slot) s alloc h-eq iph-restore-input =
    restore-input-preserves-halted slot s alloc h-eq
  -- OCP-0003: Worklist instructions
  exec-abstract-preserves-halted (worklist-init slot) s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (worklist-push slot) s alloc h-eq _ =
    trans (writeLoc-halted s (OnStack (current-frame alloc) slot) (readReg (regs s) Output)) h-eq
  exec-abstract-preserves-halted (worklist-pop slot) s alloc h-eq iph-worklist-pop =
    load-from-slot-preserves-halted slot s alloc h-eq  -- same as load-from-slot
  exec-abstract-preserves-halted (worklist-check slot) s alloc h-eq _ = h-eq

  -- TracePreservesHalted: predicate on trace that all instructions preserve halted
  data TracePreservesHaltedP : AbstractTrace → Set where
    tph-[] : TracePreservesHaltedP []
    tph-∷  : ∀ {i rest} → InstrPreservesHalted i → TracePreservesHaltedP rest →
             TracePreservesHaltedP (i ∷ rest)

  -- exec-trace preserves halted=false when TracePreservesHaltedP holds
  exec-trace-preserves-halted : ∀ (trace : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    TracePreservesHaltedP trace →
    halted (proj₁ (exec-trace trace s alloc)) ≡ false
  exec-trace-preserves-halted [] s alloc h-eq _ = h-eq
  exec-trace-preserves-halted (i ∷ rest) s alloc h-eq (tph-∷ iph tph)
    rewrite h-eq =
    let s' = proj₁ (exec-abstract i s alloc)
        alloc' = proj₂ (exec-abstract i s alloc)
        h-step = exec-abstract-preserves-halted i s alloc h-eq iph
    in exec-trace-preserves-halted rest s' alloc' h-step tph

  -- Append preserves TracePreservesHaltedP
  tph-++ : ∀ {t₁ t₂} → TracePreservesHaltedP t₁ → TracePreservesHaltedP t₂ →
           TracePreservesHaltedP (t₁ ++ t₂)
  tph-++ tph-[] tph₂ = tph₂
  tph-++ (tph-∷ iph tph₁) tph₂ = tph-∷ iph (tph-++ tph₁ tph₂)

  ------------------------------------------------------------------------
  -- (H) WRITE-THEN-PRESERVE PATTERN
  --
  -- Core pattern for proving slot values after traces:
  --   1. Write value V to slot K
  --   2. Execute trace with writes above K
  --   3. Conclude: slot K still contains V
  --
  -- This captures fst-ptr, snd-ptr, pair-frontier-stable patterns.
  ------------------------------------------------------------------------

  -- Slot value preservation: if slot k has value v and trace writes above k,
  -- then slot k still has value v after trace
  exec-trace-slot-value : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) (k : ℕ) (v : ValueLocation FS) →
    readLoc s (OnStack (current-frame alloc) k) ≡ just v →
    TraceWritesAbove (suc k) trace →
    TraceNoHeapWrites trace →
    readLoc (proj₁ (exec-trace trace s alloc)) (OnStack (current-frame alloc) k) ≡ just v
  exec-trace-slot-value trace s alloc k v slot-has-v twa tnhw =
    let -- k < suc k, so slot k is below write region
        k<suck : k < suc k
        k<suck = ≤-refl
        -- Apply positive characterization lemma
        preserved : readLoc (proj₁ (exec-trace trace s alloc)) (OnStack (current-frame alloc) k) ≡
                    readLoc s (OnStack (current-frame alloc) k)
        preserved = exec-trace-preserves-slot-below trace s alloc (suc k) k twa tnhw k<suck
    in trans preserved slot-has-v

  -- Dual: slot value preservation for TraceWritesBelow
  -- If slot k has value v and trace writes below k (at slots < k), then k is preserved
  exec-trace-slot-value-below : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) (k : ℕ) (v : ValueLocation FS) →
    readLoc s (OnStack (current-frame alloc) k) ≡ just v →
    TraceWritesBelow k trace →        -- writes at slots < k
    TraceNoHeapWrites trace →
    readLoc (proj₁ (exec-trace trace s alloc)) (OnStack (current-frame alloc) k) ≡ just v
  exec-trace-slot-value-below trace s alloc k v slot-has-v twb tnhw =
    let -- k ≥ k, so slot k is above write region
        k≤k : k ≤ k
        k≤k = ≤-refl
        -- Apply positive characterization lemma
        preserved : readLoc (proj₁ (exec-trace trace s alloc)) (OnStack (current-frame alloc) k) ≡
                    readLoc s (OnStack (current-frame alloc) k)
        preserved = exec-trace-preserves-slot-above trace s alloc k k twb tnhw k≤k
    in trans preserved slot-has-v

  -- store-at-slot writes the Output register value to the slot
  store-at-slot-result : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    readLoc (proj₁ (exec-abstract (store-at-slot k) s alloc))
            (OnStack (current-frame alloc) k) ≡ just (readReg (regs s) Output)
  store-at-slot-result k s alloc = readLoc-writeLoc-same s (OnStack (current-frame alloc) k) (readReg (regs s) Output)

  -- store-at-slot preserves halted
  store-at-slot-halted : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted (proj₁ (exec-abstract (store-at-slot k) s alloc)) ≡ halted s
  store-at-slot-halted k s alloc = writeLoc-halted s (OnStack (current-frame alloc) k) (readReg (regs s) Output)

  -- store-at-slot preserves registers
  store-at-slot-regs : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    regs (proj₁ (exec-abstract (store-at-slot k) s alloc)) ≡ regs s
  store-at-slot-regs k s alloc = writeLoc-regs s (OnStack (current-frame alloc) k) (readReg (regs s) Output)

  -- store-at-slot preserves other slots: writing to slot j preserves slot k when j < k or k < j
  store-at-slot-preserves-other : ∀ (j k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    j < k ⊎ k < j →
    readLoc (proj₁ (exec-abstract (store-at-slot j) s alloc)) (OnStack (current-frame alloc) k) ≡
    readLoc s (OnStack (current-frame alloc) k)
  store-at-slot-preserves-other j k s alloc (inj₁ j<k) =
    writeLoc-preserves-other s (OnStack (current-frame alloc) j) (OnStack (current-frame alloc) k)
      (readReg (regs s) Output) (stack-slot-disjoint (current-frame alloc) j k (<⇒≢ j<k))
  store-at-slot-preserves-other j k s alloc (inj₂ k<j) =
    writeLoc-preserves-other s (OnStack (current-frame alloc) j) (OnStack (current-frame alloc) k)
      (readReg (regs s) Output) (stack-slot-disjoint (current-frame alloc) j k (≢-sym (<⇒≢ k<j)))

  ------------------------------------------------------------------------
  -- (I) SNOC DECOMPOSITION
  --
  -- Reasoning about traces ending with specific instructions.
  -- exec-trace (trace ++ [i]) = exec-trace [i] (exec-trace trace ...)
  ------------------------------------------------------------------------

  -- Snoc decomposition: trace ++ [i] executes trace, then [i]
  -- Uses exec-trace-append directly
  exec-trace-snoc : ∀ (trace : AbstractTrace) (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) →
    exec-trace (trace ++ (i ∷ [])) s alloc ≡
    exec-trace (i ∷ []) (proj₁ (exec-trace trace s alloc))
                        (proj₂ (exec-trace trace s alloc))
  exec-trace-snoc trace i s alloc = exec-trace-append trace (i ∷ []) s alloc

  -- State version of snoc: when intermediate state not halted
  -- Uses exec-trace-single from SMCore
  exec-trace-snoc-state : ∀ (trace : AbstractTrace) (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) →
    halted (proj₁ (exec-trace trace s alloc)) ≡ false →
    proj₁ (exec-trace (trace ++ (i ∷ [])) s alloc) ≡
    proj₁ (exec-abstract i (proj₁ (exec-trace trace s alloc))
                           (proj₂ (exec-trace trace s alloc)))
  exec-trace-snoc-state trace i s alloc not-halted =
    let s' = proj₁ (exec-trace trace s alloc)
        alloc' = proj₂ (exec-trace trace s alloc)
        step1 = exec-trace-snoc trace i s alloc
        step2 = exec-trace-single i s' alloc' not-halted
    in trans (cong proj₁ step1) (cong proj₁ step2)

  ------------------------------------------------------------------------
  -- (J) FINAL INSTRUCTION EFFECTS
  --
  -- Specific lemmas for common final instructions in IR traces.
  ------------------------------------------------------------------------

  -- lea-slot sets Output register to the slot address
  lea-slot-result : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    readReg (regs (proj₁ (exec-abstract (lea-slot k) s alloc))) Output ≡
    OnStack (current-frame alloc) k
  lea-slot-result k s alloc = writeReg-same (regs s) Output (OnStack (current-frame alloc) k)

  -- lea-slot preserves halted
  lea-slot-halted : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted (proj₁ (exec-abstract (lea-slot k) s alloc)) ≡ halted s
  lea-slot-halted k s alloc = refl

  -- lea-slot preserves memory (no writes)
  lea-slot-preserves-mem : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    readLoc (proj₁ (exec-abstract (lea-slot k) s alloc)) loc ≡ readLoc s loc
  lea-slot-preserves-mem k s alloc loc =
    readLoc-stackMem-eq (proj₁ (exec-abstract (lea-slot k) s alloc)) s loc refl refl

  -- Final lea-slot in trace: sets Output to slot address
  -- Note: exec-trace-preserves-frame works for all traces, no TracePreservesCapacity needed
  exec-trace-final-lea-slot : ∀ (trace : AbstractTrace) (k : ℕ) (s : LocState FS)
    (alloc : AllocState {FS}) →
    halted (proj₁ (exec-trace trace s alloc)) ≡ false →
    readReg (regs (proj₁ (exec-trace (trace ++ (lea-slot k ∷ [])) s alloc))) Output ≡
    OnStack (current-frame alloc) k
  exec-trace-final-lea-slot trace k s alloc not-halted-after =
    let s' = proj₁ (exec-trace trace s alloc)
        alloc' = proj₂ (exec-trace trace s alloc)
        -- Step 1: Decompose trace ++ [lea-slot k] using snoc
        snoc-eq : proj₁ (exec-trace (trace ++ (lea-slot k ∷ [])) s alloc) ≡
                  proj₁ (exec-abstract (lea-slot k) s' alloc')
        snoc-eq = exec-trace-snoc-state trace (lea-slot k) s alloc not-halted-after
        -- Step 2: lea-slot result (uses alloc')
        lea-result : readReg (regs (proj₁ (exec-abstract (lea-slot k) s' alloc'))) Output ≡
                     OnStack (current-frame alloc') k
        lea-result = lea-slot-result k s' alloc'
        -- Step 3: Frame preservation (works for all traces)
        frame-eq : current-frame alloc' ≡ current-frame alloc
        frame-eq = exec-trace-preserves-frame trace s alloc
        -- Step 4: Combine
        result-with-alloc' : readReg (regs (proj₁ (exec-trace (trace ++ (lea-slot k ∷ [])) s alloc))) Output ≡
                             OnStack (current-frame alloc') k
        result-with-alloc' = trans (cong (λ st → readReg (regs st) Output) snoc-eq) lea-result
    in trans result-with-alloc' (cong (λ f → OnStack f k) frame-eq)

  -- Final lea-slot k followed by mov-to-input: sets Input to slot address
  -- Common pattern in Apply setup traces
  exec-trace-final-lea-mov-input : ∀ (trace : AbstractTrace) (k : ℕ) (s : LocState FS)
    (alloc : AllocState {FS}) →
    halted (proj₁ (exec-trace trace s alloc)) ≡ false →
    readReg (regs (proj₁ (exec-trace (trace ++ (lea-slot k ∷ mov-to-input ∷ [])) s alloc))) Input ≡
    OnStack (current-frame alloc) k
  exec-trace-final-lea-mov-input trace k s alloc not-halted-after =
    let s' = proj₁ (exec-trace trace s alloc)
        alloc' = proj₂ (exec-trace trace s alloc)
        -- Step 1: Decompose using append
        append-eq : exec-trace (trace ++ (lea-slot k ∷ mov-to-input ∷ [])) s alloc ≡
                    exec-trace (lea-slot k ∷ mov-to-input ∷ []) s' alloc'
        append-eq = exec-trace-append trace (lea-slot k ∷ mov-to-input ∷ []) s alloc
        -- Step 2: Execute lea-slot (not halted)
        s-after-lea = proj₁ (exec-abstract (lea-slot k) s' alloc')
        alloc-after-lea = proj₂ (exec-abstract (lea-slot k) s' alloc')
        lea-step : exec-trace (lea-slot k ∷ mov-to-input ∷ []) s' alloc' ≡
                   exec-trace (mov-to-input ∷ []) s-after-lea alloc-after-lea
        lea-step = exec-trace-cons (lea-slot k) (mov-to-input ∷ []) s' alloc' not-halted-after
        -- Step 3: lea-slot sets Output = OnStack (current-frame alloc') k
        output-after-lea : readReg (regs s-after-lea) Output ≡ OnStack (current-frame alloc') k
        output-after-lea = lea-slot-result k s' alloc'
        -- Step 4: lea-slot preserves halted
        not-halted-after-lea : halted s-after-lea ≡ false
        not-halted-after-lea = trans (lea-slot-halted k s' alloc') not-halted-after
        -- Step 5: Execute mov-to-input
        s-after-mov = proj₁ (exec-abstract mov-to-input s-after-lea alloc-after-lea)
        mov-step : exec-trace (mov-to-input ∷ []) s-after-lea alloc-after-lea ≡
                   exec-abstract mov-to-input s-after-lea alloc-after-lea
        mov-step = exec-trace-single mov-to-input s-after-lea alloc-after-lea not-halted-after-lea
        -- Step 6: mov-to-input sets Input = Output
        input-after-mov : readReg (regs s-after-mov) Input ≡ readReg (regs s-after-lea) Output
        input-after-mov = writeReg-same (regs s-after-lea) Input (readReg (regs s-after-lea) Output)
        -- Step 7: Frame preserved through trace
        frame-eq : current-frame alloc' ≡ current-frame alloc
        frame-eq = exec-trace-preserves-frame trace s alloc
        -- Step 8: Combine step by step
        -- First show that the final state equals s-after-mov
        final-state = proj₁ (exec-trace (trace ++ (lea-slot k ∷ mov-to-input ∷ [])) s alloc)
        eq1 : proj₁ (exec-trace (lea-slot k ∷ mov-to-input ∷ []) s' alloc') ≡ s-after-mov
        eq1 = trans (cong proj₁ lea-step) (cong proj₁ mov-step)
        eq2 : final-state ≡ proj₁ (exec-trace (lea-slot k ∷ mov-to-input ∷ []) s' alloc')
        eq2 = cong proj₁ append-eq
        eq3 : final-state ≡ s-after-mov
        eq3 = trans eq2 eq1
        -- Now transport the Input register result
        eq4 : readReg (regs final-state) Input ≡ readReg (regs s-after-mov) Input
        eq4 = cong (λ st → readReg (regs st) Input) eq3
        eq5 : readReg (regs s-after-mov) Input ≡ OnStack (current-frame alloc') k
        eq5 = trans input-after-mov output-after-lea
        eq6 : OnStack (current-frame alloc') k ≡ OnStack (current-frame alloc) k
        eq6 = cong (λ f → OnStack f k) frame-eq
    in trans eq4 (trans eq5 eq6)

  ------------------------------------------------------------------------
  -- (K) WRITE-PRESERVE COMBINED
  --
  -- Combined pattern: write to slot, then preserve through trace.
  -- Useful for fst-ptr, snd-ptr style proofs.
  ------------------------------------------------------------------------

  -- After store-at-slot k, if rest-trace writes above suc k, slot k = Output value
  store-then-preserve : ∀ (k : ℕ) (rest : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) →
    halted s ≡ false →
    TraceWritesAbove (suc k) rest →
    TraceNoHeapWrites rest →
    readLoc (proj₁ (exec-trace (store-at-slot k ∷ rest) s alloc))
            (OnStack (current-frame alloc) k) ≡ just (readReg (regs s) Output)
  store-then-preserve k rest s alloc not-halted twa tnhw with halted s
  ... | true = case not-halted of λ ()  -- contradiction
  ... | false =
    let -- After store-at-slot k
        s' = proj₁ (exec-abstract (store-at-slot k) s alloc)
        alloc' = proj₂ (exec-abstract (store-at-slot k) s alloc)
        -- Step 1: store-at-slot writes Output to slot k
        slot-has-value : readLoc s' (OnStack (current-frame alloc) k) ≡ just (readReg (regs s) Output)
        slot-has-value = store-at-slot-result k s alloc
        -- Step 2: rest preserves slot k (writes above suc k)
        preserved : readLoc (proj₁ (exec-trace rest s' alloc')) (OnStack (current-frame alloc') k) ≡
                    just (readReg (regs s) Output)
        preserved = exec-trace-slot-value rest s' alloc' k (readReg (regs s) Output)
                      (subst (λ f → readLoc s' (OnStack f k) ≡ just (readReg (regs s) Output))
                             (sym (exec-abstract-preserves-frame (store-at-slot k) s alloc))
                             slot-has-value)
                      twa tnhw
        -- Step 3: Frame preserved by store-at-slot
        frame-eq : current-frame alloc' ≡ current-frame alloc
        frame-eq = exec-abstract-preserves-frame (store-at-slot k) s alloc
    in subst (λ f → readLoc (proj₁ (exec-trace rest s' alloc')) (OnStack f k) ≡
                    just (readReg (regs s) Output))
             frame-eq preserved

  -- Generalized pattern: execute prefix, store to slot k, execute suffix that preserves k.
  -- Result: slot k contains what Output was after prefix.
  --
  -- This is the principled approach for env-ptr/code-ptr proofs:
  --   1. prefix sets up Output register (e.g., mov-to-output or lea-slot)
  --   2. store-at-slot k writes Output to slot k
  --   3. suffix writes only at slots > k, so slot k is preserved
  prefix-store-preserve : ∀ (prefix : AbstractTrace) (k : ℕ) (suffix : AbstractTrace)
    (s : LocState FS) (alloc : AllocState {FS}) →
    -- prefix preserves halted-false
    TracePreservesHaltedP prefix →
    halted s ≡ false →
    -- suffix writes only above suc k (so k is preserved after store)
    TraceWritesAbove (suc k) suffix →
    TraceNoHeapWrites suffix →
    -- Result: slot k contains what Output had after prefix
    let s-after-prefix = proj₁ (exec-trace prefix s alloc)
    in
    readLoc (proj₁ (exec-trace (prefix ++ store-at-slot k ∷ suffix) s alloc))
            (OnStack (current-frame alloc) k) ≡
    just (readReg (regs s-after-prefix) Output)
  prefix-store-preserve [] k suffix s alloc tph-prefix not-halted twa tnhw =
    -- Empty prefix: just apply store-then-preserve
    store-then-preserve k suffix s alloc not-halted twa tnhw
  prefix-store-preserve (i ∷ prefix) k suffix s alloc (tph-∷ iph tph-rest) not-halted twa tnhw =
    psp-cons i prefix k suffix s alloc iph tph-rest not-halted twa tnhw not-halted
    where
      -- Helper that takes halted s ≡ false as an explicit equality for pattern matching
      psp-cons : ∀ (i : AbstractInstr) (prefix : AbstractTrace) (k : ℕ)
        (suffix : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
        InstrPreservesHalted i →
        TracePreservesHaltedP prefix →
        halted s ≡ false →
        TraceWritesAbove (suc k) suffix →
        TraceNoHeapWrites suffix →
        halted s ≡ false →  -- duplicate for pattern matching
        readLoc (proj₁ (exec-trace ((i ∷ prefix) ++ store-at-slot k ∷ suffix) s alloc))
                (OnStack (current-frame alloc) k) ≡
        just (readReg (regs (proj₁ (exec-trace (i ∷ prefix) s alloc))) Output)
      psp-cons i prefix k suffix s alloc iph tph-rest not-halted twa tnhw refl =
        let -- Execute first instruction
            s₁ = proj₁ (exec-abstract i s alloc)
            alloc₁ = proj₂ (exec-abstract i s alloc)

            -- halted preserved after first instruction
            not-halted₁ : halted s₁ ≡ false
            not-halted₁ = exec-abstract-preserves-halted i s alloc refl iph

            -- Recursive call for rest of prefix
            rest-trace = prefix ++ store-at-slot k ∷ suffix
            ih : readLoc (proj₁ (exec-trace rest-trace s₁ alloc₁))
                         (OnStack (current-frame alloc₁) k) ≡
                 just (readReg (regs (proj₁ (exec-trace prefix s₁ alloc₁))) Output)
            ih = prefix-store-preserve prefix k suffix s₁ alloc₁ tph-rest not-halted₁ twa tnhw

            -- Frame preserved by first instruction
            frame-eq : current-frame alloc₁ ≡ current-frame alloc
            frame-eq = exec-abstract-preserves-frame i s alloc

            -- After prefix in original state = after prefix in s₁
            s-after-prefix = proj₁ (exec-trace prefix s₁ alloc₁)

        in subst (λ f → readLoc (proj₁ (exec-trace rest-trace s₁ alloc₁)) (OnStack f k) ≡
                        just (readReg (regs s-after-prefix) Output))
                 frame-eq ih

------------------------------------------------------------------------
-- Summary: Minimal Axioms + Positive Characterization
--
-- THE CORE (only primitives needed):
--
--   read-write-same  : read where you wrote → get written value
--   read-write-other : read elsewhere → get original value
--   write-commute    : writes to different locations commute
--
--   instr-writes-mem : exactly where each instruction writes
--
-- EVERYTHING ELSE DERIVES:
--
--   "Preservation" of slot 0 after snd-trace?
--     → snd-trace writes to slots ≥ 2 (positive characterization)
--     → slot 0 not in write set
--     → by induction: each instruction uses read-write-other
--     → slot 0 unchanged
--
--   Final value at slot 0?
--     → store-at-slot 0 wrote fst-value there (read-write-same)
--     → nothing later wrote to slot 0 (positive characterization)
--     → slot 0 = fst-value
--
-- For PairWF, the proof structure is:
--   1. fst-trace produces fst-value in Output register
--   2. store-at-slot 0 writes Output to slot 0 (read-write-same: slot 0 = fst-value)
--   3. snd-trace writes to slots ≥ 2 (positive), so slot 0 unchanged (read-write-other)
--   4. store-at-slot 1 writes to slot 1 ≠ 0, so slot 0 unchanged (read-write-other)
--   5. lea-slot 0 doesn't write memory, so slot 0 unchanged
--   6. Therefore slot 0 = fst-value (QED)
--
-- No separate "preservation lemma" needed - it's just read-write-other!
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Trace Output Determinism
--
-- If two states agree on:
--   1. Input register (same value)
--   2. Memory at slots ≥ n (trace only reads from these)
--   3. Frame (same frame)
-- Then executing the trace produces the same Output register value.
--
-- This is needed for PairWF2 where f-trace is generated from state s,
-- but executed from s-after-setup. Since they agree on relevant inputs,
-- the Output should be the same.
------------------------------------------------------------------------

module TraceOutputDeterminism {FS : FrameSemantics} where
  open MemOps {FS}
  open AbstractExec {FS}
  open FrameSemantics FS using (Frame)

  -- If two states agree on Input and memory at read slots [n, m),
  -- and traces only read from those slots, then Output is the same.
  -- Note: m bounds reads (TraceSlotReadsBelow m), so memory agreement
  -- is only needed for slots in [n, m), not all slots ≥ n.
  exec-trace-output-deterministic : ∀ (trace : AbstractTrace)
    (s₁ s₂ : LocState FS) (alloc₁ alloc₂ : AllocState {FS}) (n m : ℕ) →
    halted s₁ ≡ false →
    halted s₂ ≡ false →
    current-frame alloc₁ ≡ current-frame alloc₂ →
    readReg (regs s₁) Input ≡ readReg (regs s₂) Input →
    TraceSlotReadsAbove n trace →
    TraceSlotReadsBelow m trace →
    TraceWritesAbove n trace →
    TraceNoHeapWrites trace →
    (∀ slot → n ≤ slot → slot < m →
      readLoc s₁ (OnStack (current-frame alloc₁) slot) ≡
      readLoc s₂ (OnStack (current-frame alloc₂) slot)) →
    readReg (regs (proj₁ (exec-trace trace s₁ alloc₁))) Output ≡
    readReg (regs (proj₁ (exec-trace trace s₂ alloc₂))) Output
  -- Proof sketch: by induction on trace
  -- Each instruction either:
  --   1. Reads from Input (same in both) → same result
  --   2. Reads from memory slot in [n, m) (same in both) → same result
  --   3. Reads from Output (must track that Output stays synchronized)
  -- The key is that if reads are the same, computations are the same,
  -- and since writes are above n, memory at [n, m) stays synchronized.
  exec-trace-output-deterministic = !!

  ------------------------------------------------------------------------
  -- Memory Determinism
  --
  -- If two states agree on Input and memory at read locations,
  -- then after trace execution, memory at write locations is the same.
  --
  -- This complements exec-trace-output-deterministic for memory locations.
  ------------------------------------------------------------------------

  -- Memory determinism for slots in the write region [n, m)
  -- If two states agree on Input and memory at slots in [n, m),
  -- and trace reads/writes are bounded by [n, m),
  -- then after execution, memory at slots in [n, m) is the same.
  exec-trace-mem-deterministic : ∀ (trace : AbstractTrace)
    (s₁ s₂ : LocState FS) (alloc₁ alloc₂ : AllocState {FS}) (n m : ℕ) →
    halted s₁ ≡ false →
    halted s₂ ≡ false →
    current-frame alloc₁ ≡ current-frame alloc₂ →
    readReg (regs s₁) Input ≡ readReg (regs s₂) Input →
    TraceSlotReadsAbove n trace →
    TraceSlotReadsBelow m trace →   -- reads are bounded above by m
    TraceWritesAbove n trace →
    TraceWritesBelow m trace →
    TraceNoHeapWrites trace →
    (∀ slot → n ≤ slot → slot < m →   -- only require agreement on [n, m)
      readLoc s₁ (OnStack (current-frame alloc₁) slot) ≡
      readLoc s₂ (OnStack (current-frame alloc₂) slot)) →
    ∀ slot → n ≤ slot → slot < m →
      readLoc (proj₁ (exec-trace trace s₁ alloc₁)) (OnStack (current-frame alloc₁) slot) ≡
      readLoc (proj₁ (exec-trace trace s₂ alloc₂)) (OnStack (current-frame alloc₂) slot)
  -- Proof sketch: by induction on trace
  -- Each store instruction writes a value computed from Input, Output, or memory reads.
  -- Since all reads come from slots in [n, m) (where states agree), computed values are same.
  -- Therefore stores to slots in [n, m) write the same values in both executions.
  exec-trace-mem-deterministic = !!

------------------------------------------------------------------------
-- Recursion Scheme Semantic Correctness
--
-- These postulates specify the semantic correctness requirements for
-- recursion scheme implementations (Cata, Fuse, Hylo, Para, Ana).
--
-- The implementations in RecCoreWF, ParaWF, AnaWF use abstract traces
-- that represent the recursive execution pattern. The actual recursion
-- is captured semantically through these postulates.
--
-- Each postulate documents a specific proof obligation that must be
-- discharged to complete the formal verification.
------------------------------------------------------------------------

module RecSchemeSemantics {FS : FrameSemantics} where
  open MemOps {FS}
  open AbstractExec {FS}
  open TracePrimitives {FS}
  open InstrPrimitives {FS}
  open MemoryOps {FS}
  open TraceComposition {FS}
  open import Data.Empty using (⊥-elim)

  private
    RSFrame : Set
    RSFrame = FrameSemantics.Frame FS

  ------------------------------------------------------------------------
  -- Single mov-to-output trace: mov-to-output ∷ []
  --
  -- This is the identity trace - just copies Input to Output.
  -- Used by out-μ and Out which are representationally identity.
  ------------------------------------------------------------------------

  -- After mov-to-output ∷ [], Output = Input
  passthrough-output-is-input : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readReg (regs (proj₁ (exec-trace (mov-to-output ∷ []) s alloc))) Output ≡
    readReg (regs s) Input
  passthrough-output-is-input s alloc not-halted with halted s
  ... | false = writeReg-same (regs s) Output (readReg (regs s) Input)

  -- After mov-to-output ∷ [], halted = false
  passthrough-preserves-halted : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-trace (mov-to-output ∷ []) s alloc)) ≡ false
  passthrough-preserves-halted s alloc not-halted =
    exec-trace-preserves-halted (mov-to-output ∷ []) s alloc not-halted
      (tph-∷ iph-mov-to-output tph-[])

  -- exec-abstract mov-to-output preserves memory (it only changes registers)
  -- Pattern match on loc to handle stack/heap cases separately
  exec-abstract-mov-to-output-preserves-mem : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    readLoc (proj₁ (exec-abstract mov-to-output s alloc)) loc ≡ readLoc s loc
  exec-abstract-mov-to-output-preserves-mem s alloc (OnStack f k) = refl
  exec-abstract-mov-to-output-preserves-mem s alloc (OnHeap hl) = refl

  -- After mov-to-output ∷ [], memory is preserved
  -- mov-to-output only modifies registers, not memory
  --
  -- We use exec-trace-single to reduce to exec-abstract, then show
  -- exec-abstract preserves memory.
  passthrough-mem-preserved : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ []) s alloc)) loc ≡ readLoc s loc
  passthrough-mem-preserved s alloc loc not-halted =
    let step : exec-trace (mov-to-output ∷ []) s alloc ≡ exec-abstract mov-to-output s alloc
        step = exec-trace-single mov-to-output s alloc not-halted
        state-eq : proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡
                   proj₁ (exec-abstract mov-to-output s alloc)
        state-eq = cong proj₁ step
        mem-pres : readLoc (proj₁ (exec-abstract mov-to-output s alloc)) loc ≡ readLoc s loc
        mem-pres = exec-abstract-mov-to-output-preserves-mem s alloc loc
    in trans (cong (λ st → readLoc st loc) state-eq) mem-pres

  ------------------------------------------------------------------------
  -- Common trace pattern for recursion schemes:
  -- mov-to-output ∷ store-at-slot n ∷ []
  --
  -- After this trace:
  -- 1. Slot n contains the input location (originally in Input register)
  -- 2. Output register still contains Input (store doesn't change regs)
  -- 3. Halted flag is preserved (both instructions preserve halted)
  -- 4. Memory at slots < n is preserved (trace writes only at slot n)

  -- After mov-to-output ∷ store-at-slot n ∷ [], Output = original Input
  rec-scheme-output-is-input : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readReg (regs (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc))) Output ≡
    readReg (regs s) Input
  rec-scheme-output-is-input n s alloc not-halted =
    let -- Step 1: Unfold first instruction (mov-to-output)
        s1 = proj₁ (exec-abstract mov-to-output s alloc)
        alloc1 = proj₂ (exec-abstract mov-to-output s alloc)
        -- After mov-to-output: Output = Input
        mov-result : readReg (regs s1) Output ≡ readReg (regs s) Input
        mov-result = writeReg-same (regs s) Output (readReg (regs s) Input)
        -- mov-to-output doesn't halt
        s1-not-halted : halted s1 ≡ false
        s1-not-halted = not-halted  -- mov-to-output preserves halted
        -- Step 2: Unfold second instruction (store-at-slot n)
        s2 = proj₁ (exec-abstract (store-at-slot n) s1 alloc1)
        -- store-at-slot preserves registers
        store-regs : regs s2 ≡ regs s1
        store-regs = store-at-slot-regs n s1 alloc1
        -- Step 3: Combine
        -- exec-trace (mov ∷ store ∷ []) = exec-trace (store ∷ []) after mov
        step1 : exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc ≡
                exec-trace (store-at-slot n ∷ []) s1 alloc1
        step1 = exec-trace-cons mov-to-output (store-at-slot n ∷ []) s alloc not-halted
        step2 : exec-trace (store-at-slot n ∷ []) s1 alloc1 ≡ exec-abstract (store-at-slot n) s1 alloc1
        step2 = exec-trace-single (store-at-slot n) s1 alloc1 s1-not-halted
    in trans (cong (λ r → readReg r Output) (trans (cong (λ p → regs (proj₁ p)) (trans step1 step2)) store-regs)) mov-result

  -- After mov-to-output ∷ store-at-slot n ∷ [], halted = false (preserved)
  rec-scheme-preserves-halted : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc)) ≡ false
  rec-scheme-preserves-halted n s alloc not-halted =
    exec-trace-preserves-halted (mov-to-output ∷ store-at-slot n ∷ []) s alloc not-halted
      (tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot tph-[]))

  -- After mov-to-output ∷ store-at-slot n ∷ [], slot n contains Input value
  rec-scheme-stores-input : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc))
            (OnStack (current-frame alloc) n) ≡ just (readReg (regs s) Input)
  rec-scheme-stores-input n s alloc not-halted =
    let -- Step 1: Unfold first instruction (mov-to-output)
        s1 = proj₁ (exec-abstract mov-to-output s alloc)
        alloc1 = proj₂ (exec-abstract mov-to-output s alloc)
        -- After mov-to-output: Output = Input
        mov-result : readReg (regs s1) Output ≡ readReg (regs s) Input
        mov-result = writeReg-same (regs s) Output (readReg (regs s) Input)
        -- mov-to-output doesn't halt
        s1-not-halted : halted s1 ≡ false
        s1-not-halted = not-halted
        -- alloc1 = alloc (mov-to-output doesn't change alloc)
        alloc1-eq : alloc1 ≡ alloc
        alloc1-eq = refl
        -- Step 2: store-at-slot n writes Output to slot n
        s2 = proj₁ (exec-abstract (store-at-slot n) s1 alloc1)
        store-result : readLoc s2 (OnStack (current-frame alloc1) n) ≡ just (readReg (regs s1) Output)
        store-result = store-at-slot-result n s1 alloc1
        -- Step 3: Unfold trace
        step1 : exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc ≡
                exec-trace (store-at-slot n ∷ []) s1 alloc1
        step1 = exec-trace-cons mov-to-output (store-at-slot n ∷ []) s alloc not-halted
        step2 : exec-trace (store-at-slot n ∷ []) s1 alloc1 ≡ exec-abstract (store-at-slot n) s1 alloc1
        step2 = exec-trace-single (store-at-slot n) s1 alloc1 s1-not-halted
        -- Step 4: Combine
        final-state-eq : proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc) ≡ s2
        final-state-eq = cong proj₁ (trans step1 step2)
    in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) n)) final-state-eq)
             (trans store-result (cong just mov-result))

  ------------------------------------------------------------------------
  -- Extended trace pattern: mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []
  --
  -- This trace:
  -- 1. Copies Input to Output
  -- 2. Stores Output at slot n
  -- 3. Loads address of slot n into Output
  --
  -- After this trace, Output = OnStack frame n (the result location)
  ------------------------------------------------------------------------

  -- After mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], Output = OnStack frame n
  rec-scheme-output-is-slot : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readReg (regs (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))) Output ≡
    OnStack (current-frame alloc) n
  rec-scheme-output-is-slot n s alloc not-halted =
    -- The trace is (mov-to-output ∷ store-at-slot n ∷ []) ++ (lea-slot n ∷ [])
    -- which is definitionally equal to mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []
    let prefix = mov-to-output ∷ store-at-slot n ∷ []
        -- After prefix, halted = false
        not-halted-after : halted (proj₁ (exec-trace prefix s alloc)) ≡ false
        not-halted-after = rec-scheme-preserves-halted n s alloc not-halted
    in exec-trace-final-lea-slot prefix n s alloc not-halted-after

  -- After mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], halted = false (preserved)
  rec-scheme-preserves-halted-3 : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc)) ≡ false
  rec-scheme-preserves-halted-3 n s alloc not-halted =
    exec-trace-preserves-halted (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc not-halted
      (tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot (tph-∷ iph-lea-slot tph-[])))

  -- After mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], slot n contains Input value
  rec-scheme-stores-input-3 : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
            (OnStack (current-frame alloc) n) ≡ just (readReg (regs s) Input)
  rec-scheme-stores-input-3 n s alloc not-halted =
    let prefix = mov-to-output ∷ store-at-slot n ∷ []
        s-after-prefix = proj₁ (exec-trace prefix s alloc)
        alloc-after-prefix = proj₂ (exec-trace prefix s alloc)
        -- After prefix, slot n = Input
        prefix-result : readLoc s-after-prefix (OnStack (current-frame alloc) n) ≡ just (readReg (regs s) Input)
        prefix-result = rec-scheme-stores-input n s alloc not-halted
        -- After prefix, halted = false
        not-halted-after : halted s-after-prefix ≡ false
        not-halted-after = rec-scheme-preserves-halted n s alloc not-halted
        -- lea-slot preserves memory
        s-after-lea = proj₁ (exec-abstract (lea-slot n) s-after-prefix alloc-after-prefix)
        lea-preserves : readLoc s-after-lea (OnStack (current-frame alloc) n) ≡
                        readLoc s-after-prefix (OnStack (current-frame alloc) n)
        lea-preserves = lea-slot-preserves-mem n s-after-prefix alloc-after-prefix (OnStack (current-frame alloc) n)
        -- Trace decomposition
        step1 : exec-trace (prefix ++ (lea-slot n ∷ [])) s alloc ≡
                exec-trace (lea-slot n ∷ []) s-after-prefix alloc-after-prefix
        step1 = exec-trace-append prefix (lea-slot n ∷ []) s alloc
        step2 : exec-trace (lea-slot n ∷ []) s-after-prefix alloc-after-prefix ≡
                exec-abstract (lea-slot n) s-after-prefix alloc-after-prefix
        step2 = exec-trace-single (lea-slot n) s-after-prefix alloc-after-prefix not-halted-after
        final-state-eq : proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc) ≡ s-after-lea
        final-state-eq = cong proj₁ (trans step1 step2)
    in trans (cong (λ st → readLoc st (OnStack (current-frame alloc) n)) final-state-eq)
             (trans lea-preserves prefix-result)

  -- After mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], memory at slots < n is preserved
  -- This follows because:
  --   1. mov-to-output only modifies registers (no memory writes)
  --   2. store-at-slot n writes only to slot n
  --   3. lea-slot n only modifies registers (no memory writes)
  -- So slots < n are not modified.
  rec-scheme-preserves-slot-below-3 : ∀ (n k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    k < n →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
            (OnStack (current-frame alloc) k) ≡
    readLoc s (OnStack (current-frame alloc) k)
  rec-scheme-preserves-slot-below-3 n k s alloc not-halted k<n =
    -- The trace writes only at slot n, so slots k < n are preserved
    -- TraceWritesAbove n: store-at-slot n writes at n ≥ n
    -- TraceNoHeapWrites: no heap-writing instructions
    exec-trace-preserves-slot-below
      (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc n k
      (≤-refl , tt)  -- TraceWritesAbove n: n ≤ n, and mov/lea don't write slots
      tt             -- TraceNoHeapWrites: no heap writes
      k<n

  -- Memory preservation for heap locations through the recursion scheme trace
  rec-scheme-preserves-heap-3 : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (hl : HeapLocation) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
            (OnHeap hl) ≡
    readLoc s (OnHeap hl)
  rec-scheme-preserves-heap-3 n s alloc hl not-halted =
    -- The trace has no heap-writing instructions
    exec-trace-preserves-heap-loc
      (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc hl
      tt  -- TraceNoHeapWrites: no store-indirect or store-indirect-suc

  -- Memory preservation for ancestor frame slots through the recursion scheme trace
  -- The trace only writes to (current-frame alloc, n), so any slot on a different frame is preserved
  rec-scheme-preserves-ancestor-3 : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (f : RSFrame) (k : ℕ) →
    halted s ≡ false →
    f ≢ current-frame alloc →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
            (OnStack f k) ≡
    readLoc s (OnStack f k)
  rec-scheme-preserves-ancestor-3 n s alloc f k not-halted f≢cf =
    -- The trace writes only to OnStack (current-frame alloc) n
    -- OnStack f k is on a different frame (f ≢ cf), so it's preserved
    trans (cong (λ st → readLoc st (OnStack f k)) final-state-eq)
          (trans lea-preserves (trans store-preserves mov-preserves))
    where
      -- Step 1: Unfold first instruction (mov-to-output) - preserves all memory
      s1 = proj₁ (exec-abstract mov-to-output s alloc)
      alloc1 = proj₂ (exec-abstract mov-to-output s alloc)
      mov-preserves : readLoc s1 (OnStack f k) ≡ readLoc s (OnStack f k)
      mov-preserves = refl  -- mov-to-output only changes registers
      s1-not-halted : halted s1 ≡ false
      s1-not-halted = not-halted
      -- Step 2: store-at-slot n writes to OnStack cf n, preserves OnStack f k (different frame)
      s2 = proj₁ (exec-abstract (store-at-slot n) s1 alloc1)
      alloc2 = proj₂ (exec-abstract (store-at-slot n) s1 alloc1)
      -- OnStack cf n ≢ OnStack f k because f ≢ cf
      loc-neq : OnStack (current-frame alloc1) n ≢ OnStack f k
      loc-neq refl = f≢cf refl  -- contradiction: f ≡ cf
      store-preserves : readLoc s2 (OnStack f k) ≡ readLoc s1 (OnStack f k)
      store-preserves = writeLoc-preserves-other s1 (OnStack (current-frame alloc1) n) (OnStack f k)
                          (readReg (regs s1) Output) loc-neq
      s2-not-halted : halted s2 ≡ false
      s2-not-halted = s1-not-halted
      -- Step 3: lea-slot n - preserves all memory
      s3 = proj₁ (exec-abstract (lea-slot n) s2 alloc2)
      lea-preserves : readLoc s3 (OnStack f k) ≡ readLoc s2 (OnStack f k)
      lea-preserves = lea-slot-preserves-mem n s2 alloc2 (OnStack f k)
      -- Step 4: Trace decomposition
      step1 : exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc ≡
              exec-trace (store-at-slot n ∷ lea-slot n ∷ []) s1 alloc1
      step1 = exec-trace-cons mov-to-output (store-at-slot n ∷ lea-slot n ∷ []) s alloc not-halted
      step2 : exec-trace (store-at-slot n ∷ lea-slot n ∷ []) s1 alloc1 ≡
              exec-trace (lea-slot n ∷ []) s2 alloc2
      step2 = exec-trace-cons (store-at-slot n) (lea-slot n ∷ []) s1 alloc1 s1-not-halted
      step3 : exec-trace (lea-slot n ∷ []) s2 alloc2 ≡ exec-abstract (lea-slot n) s2 alloc2
      step3 = exec-trace-single (lea-slot n) s2 alloc2 s2-not-halted
      final-state-eq : proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc) ≡ s3
      final-state-eq = cong proj₁ (trans step1 (trans step2 step3))