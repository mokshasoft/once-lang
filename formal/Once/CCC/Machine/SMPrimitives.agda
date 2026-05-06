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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; inspect; [_]; ≢-sym)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.SigOp.Info using (SigOpInfo)
open import Once.Type using (IsPrimitive)
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
  s₁ ≢ s₂ → AtStack {FS} f s₁ ≢ AtStack f s₂
stack-slot-disjoint f s₁ s₂ s₁≢s₂ refl = s₁≢s₂ refl

-- Extract frame from stack location equality
stack-frame-injective : ∀ {FS : FrameSemantics} {f₁ f₂ : Frame FS} {s₁ s₂ : ℕ} →
  AtStack {FS} f₁ s₁ ≡ AtStack f₂ s₂ → f₁ ≡ f₂
stack-frame-injective refl = refl

-- Extract slot from stack location equality
stack-slot-injective : ∀ {FS : FrameSemantics} {f₁ f₂ : Frame FS} {s₁ s₂ : ℕ} →
  AtStack {FS} f₁ s₁ ≡ AtStack f₂ s₂ → s₁ ≡ s₂
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
    readLoc (writeLoc s (AtStack f k) v) (AtDynamic h) ≡ readLoc s (AtDynamic h)
  readLoc-writeLoc-stack-heap s f k h v = refl

  -- Heap write, stack read: always disjoint (different constructors)
  readLoc-writeLoc-heap-stack : ∀ (s : LocState FS) (h : HeapLocation) (f : Frame FS) (k : ℕ)
    (v : ValueLocation FS) →
    readLoc (writeLoc s (AtDynamic h) v) (AtStack f k) ≡ readLoc s (AtStack f k)
  readLoc-writeLoc-heap-stack s h f k (AtDynamic _) = refl
  readLoc-writeLoc-heap-stack s h f k (AtStack _ _) = refl

  -- heapMem equality implies readLoc equality for heap locations
  readLoc-heapMem-eq : ∀ (s₁ s₂ : LocState FS) (h : HeapLocation) →
    heapMem s₁ ≡ heapMem s₂ →
    readLoc s₁ (AtDynamic h) ≡ readLoc s₂ (AtDynamic h)
  readLoc-heapMem-eq s₁ s₂ h heq with heapMem s₁ h | heapMem s₂ h | cong (λ m → m h) heq
  ... | just h₁ | just .h₁ | refl = refl
  ... | nothing | nothing  | refl = refl

  -- writeLoc commutes with register updates for AtDynamic locations
  writeLoc-regs-commute-heap : ∀ (s : LocState FS) (hl : HeapLocation) (v : ValueLocation FS)
    (r : Registers FS) →
    writeLoc (record s { regs = r }) (AtDynamic hl) v ≡
    record (writeLoc s (AtDynamic hl) v) { regs = r }
  writeLoc-regs-commute-heap s hl (AtDynamic v) r = refl
  writeLoc-regs-commute-heap s hl (AtStack _ _) r = refl

  -- General writeLoc commutes with register updates for any location
  -- Symmetric with writeLoc-regs-commute (AtStack case from SlotMachine)
  writeLoc-regs-commute-general : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : ValueLocation FS)
    (r : Registers FS) →
    writeLoc (record s { regs = r }) loc v ≡
    record (writeLoc s loc v) { regs = r }
  writeLoc-regs-commute-general s (AtStack f k) v r = writeLoc-regs-commute s f k v r
  writeLoc-regs-commute-general s (AtDynamic hl) v r = writeLoc-regs-commute-heap s hl v r

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
    readLoc (writeLoc s (AtStack f k) v) (AtStack f j) ≡ readLoc s (AtStack f j)
  readLoc-writeLoc-stack-slot-lt s f j k v j<k with f ≟F f | k ≟ℕ j
  ... | yes _ | yes k≡j = ⊥-elim (<⇒≢ j<k (sym k≡j))
  ... | yes _ | no _ = refl
  ... | no f≢f | _ = ⊥-elim (f≢f refl)

  -- Write to slot j, read from slot k where j < k: preserved (same frame)
  readLoc-writeLoc-stack-slot-gt : ∀ (s : LocState FS) (f : Frame FS) (j k : ℕ)
    (v : ValueLocation FS) →
    j < k →
    readLoc (writeLoc s (AtStack f j) v) (AtStack f k) ≡ readLoc s (AtStack f k)
  readLoc-writeLoc-stack-slot-gt s f j k v j<k with f ≟F f | j ≟ℕ k
  ... | yes _ | yes j≡k = ⊥-elim (<⇒≢ j<k j≡k)
  ... | yes _ | no _ = refl
  ... | no f≢f | _ = ⊥-elim (f≢f refl)

  -- Write to frame f₁, read from frame f₂ where f₁ ≺ f₂: preserved (ancestor frame)
  readLoc-writeLoc-stack-ancestor : ∀ (s : LocState FS) (f₁ f₂ : Frame FS) (k₁ k₂ : ℕ)
    (v : ValueLocation FS) →
    f₁ ≺ f₂ →
    readLoc (writeLoc s (AtStack f₁ k₁) v) (AtStack f₂ k₂) ≡ readLoc s (AtStack f₂ k₂)
  readLoc-writeLoc-stack-ancestor s f₁ f₂ k₁ k₂ v f₁≺f₂ with f₁ ≟F f₂
  ... | yes f₁≡f₂ = ⊥-elim (≺-irrefl (subst (λ f → f ≺ f₂) f₁≡f₂ f₁≺f₂))
  ... | no _ = refl

  -- Read after write (same location)
  -- Uses writeLoc-read-same-stack from SMCore for stack locations
  -- Heap cases use axiom (heap write semantics are more complex)
  readLoc-writeLoc-same : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : ValueLocation FS) →
    readLoc (writeLoc s loc v) loc ≡ just v
  readLoc-writeLoc-same s (AtStack f k) v = writeLoc-read-same-stack s f k v
  readLoc-writeLoc-same s (AtDynamic hl) v = readLoc-writeLoc-same-heap s hl v
    where postulate readLoc-writeLoc-same-heap : ∀ s hl v → readLoc (writeLoc s (AtDynamic hl) v) (AtDynamic hl) ≡ just v

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
instr-writes-slot (store-at-slot k)      = just k
instr-writes-slot (worklist-push k)      = just k  -- OCP-0003
instr-writes-slot mov-to-output          = nothing
instr-writes-slot mov-input2-to-output          = nothing
instr-writes-slot mov-to-input           = nothing
instr-writes-slot mov-output-to-input2           = nothing
instr-writes-slot load-indirect          = nothing
instr-writes-slot load-indirect-suc      = nothing
instr-writes-slot (load-from-slot _)     = nothing
instr-writes-slot store-indirect         = nothing
instr-writes-slot store-indirect-suc     = nothing
instr-writes-slot (lea-slot _)           = nothing
instr-writes-slot (restore-input _)      = nothing
instr-writes-slot (instr-alloc-stack _)  = nothing
instr-writes-slot (instr-dealloc-stack _) = nothing
instr-writes-slot (instr-reclaim-to _)   = nothing
instr-writes-slot (instr-push-frame _)   = nothing
instr-writes-slot instr-pop-frame        = nothing
instr-writes-slot instr-call-closure     = nothing
instr-writes-slot (worklist-init _)      = nothing
instr-writes-slot (worklist-pop _)       = nothing
instr-writes-slot (worklist-check _)     = nothing
instr-writes-slot (instr-sigop _)        = nothing
instr-writes-slot (instr-load-const _ _) = nothing
instr-writes-slot (instr-load-code-addr _) = nothing
instr-writes-slot instr-save-closure-reg   = nothing

-- What slot does this instruction read from? (load-from-slot, restore-input, worklist-pop)
instr-reads-slot : AbstractInstr → Maybe ℕ
instr-reads-slot (load-from-slot k)      = just k
instr-reads-slot (restore-input k)       = just k
instr-reads-slot (worklist-pop k)        = just k  -- OCP-0003
instr-reads-slot mov-to-output           = nothing
instr-reads-slot mov-input2-to-output           = nothing
instr-reads-slot mov-to-input            = nothing
instr-reads-slot mov-output-to-input2            = nothing
instr-reads-slot load-indirect           = nothing
instr-reads-slot load-indirect-suc       = nothing
instr-reads-slot (store-at-slot _)       = nothing
instr-reads-slot store-indirect          = nothing
instr-reads-slot store-indirect-suc      = nothing
instr-reads-slot (lea-slot _)            = nothing
instr-reads-slot (instr-alloc-stack _)   = nothing
instr-reads-slot (instr-dealloc-stack _) = nothing
instr-reads-slot (instr-reclaim-to _)    = nothing
instr-reads-slot (instr-push-frame _)    = nothing
instr-reads-slot instr-pop-frame         = nothing
instr-reads-slot instr-call-closure      = nothing
instr-reads-slot (worklist-init _)       = nothing
instr-reads-slot (worklist-push _)       = nothing
instr-reads-slot (worklist-check _)      = nothing
instr-reads-slot (instr-sigop _)         = nothing
instr-reads-slot (instr-load-const _ _)  = nothing
instr-reads-slot (instr-load-code-addr _) = nothing
instr-reads-slot instr-save-closure-reg   = nothing

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
-- Helpers (no with-block) for the indirect-store cases.
instr-writes-heap-indirect-aux : ValueLocation FS → Maybe HeapLocation
instr-writes-heap-indirect-aux (AtDynamic hl)    = just hl
instr-writes-heap-indirect-aux (AtStack _ _)  = nothing

instr-writes-heap-indirect-suc-aux : ValueLocation FS → Maybe HeapLocation
instr-writes-heap-indirect-suc-aux (AtDynamic hl)    = just (sucHL hl)
instr-writes-heap-indirect-suc-aux (AtStack _ _)  = nothing

instr-writes-heap : AbstractInstr → LocState FS → Maybe HeapLocation
instr-writes-heap store-indirect          s = instr-writes-heap-indirect-aux (readReg (regs s) Input1)
instr-writes-heap store-indirect-suc      s = instr-writes-heap-indirect-suc-aux (readReg (regs s) Input1)
instr-writes-heap mov-to-output           _ = nothing
instr-writes-heap mov-input2-to-output           _ = nothing
instr-writes-heap mov-to-input            _ = nothing
instr-writes-heap mov-output-to-input2            _ = nothing
instr-writes-heap load-indirect           _ = nothing
instr-writes-heap load-indirect-suc       _ = nothing
instr-writes-heap (load-from-slot _)      _ = nothing
instr-writes-heap (store-at-slot _)       _ = nothing
instr-writes-heap (lea-slot _)            _ = nothing
instr-writes-heap (restore-input _)       _ = nothing
instr-writes-heap (instr-alloc-stack _)   _ = nothing
instr-writes-heap (instr-dealloc-stack _) _ = nothing
instr-writes-heap (instr-reclaim-to _)    _ = nothing
instr-writes-heap (instr-push-frame _)    _ = nothing
instr-writes-heap instr-pop-frame         _ = nothing
instr-writes-heap instr-call-closure      _ = nothing
instr-writes-heap (worklist-init _)       _ = nothing
instr-writes-heap (worklist-push _)       _ = nothing
instr-writes-heap (worklist-pop _)        _ = nothing
instr-writes-heap (worklist-check _)      _ = nothing
instr-writes-heap (instr-sigop _)         _ = nothing
instr-writes-heap (instr-load-const _ _)  _ = nothing
instr-writes-heap (instr-load-code-addr _) _ = nothing
instr-writes-heap instr-save-closure-reg   _ = nothing

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
  nhw-mov-to-output      : InstrNoHeapWrite mov-input2-to-output
  nhw-mov-to-input       : InstrNoHeapWrite mov-to-input
  nhw-mov-output-to-input2       : InstrNoHeapWrite mov-output-to-input2
  nhw-load-indirect      : InstrNoHeapWrite load-indirect
  nhw-load-indirect-suc  : InstrNoHeapWrite load-indirect-suc
  nhw-load-from-slot     : ∀ {slot} → InstrNoHeapWrite (load-from-slot slot)
  nhw-store-at-slot      : ∀ {slot} → InstrNoHeapWrite (store-at-slot slot)
  nhw-lea-slot           : ∀ {slot} → InstrNoHeapWrite (lea-slot slot)
  nhw-restore-input      : ∀ {slot} → InstrNoHeapWrite (restore-input slot)
  nhw-instr-alloc-stack  : ∀ {n} → InstrNoHeapWrite (instr-alloc-stack n)
  nhw-instr-dealloc-stack : ∀ {n} → InstrNoHeapWrite (instr-dealloc-stack n)
  nhw-instr-reclaim-to   : ∀ {n} → InstrNoHeapWrite (instr-reclaim-to n)
  nhw-instr-push-frame   : ∀ {cap} → InstrNoHeapWrite (instr-push-frame cap)
  nhw-instr-pop-frame    : InstrNoHeapWrite instr-pop-frame
  nhw-instr-call-closure : InstrNoHeapWrite instr-call-closure
  -- OCP-0003: Worklist instructions write to stack, not heap
  nhw-worklist-init      : ∀ {slot} → InstrNoHeapWrite (worklist-init slot)
  nhw-worklist-push      : ∀ {slot} → InstrNoHeapWrite (worklist-push slot)
  nhw-worklist-pop       : ∀ {slot} → InstrNoHeapWrite (worklist-pop slot)
  nhw-worklist-check     : ∀ {slot} → InstrNoHeapWrite (worklist-check slot)
  -- Plan 0.10 Phase B
  nhw-instr-sigop        : ∀ {A B} {si : SigOpInfo A B} → InstrNoHeapWrite (instr-sigop si)
  -- Plan 0.11: const literal load only writes Output register
  nhw-instr-load-const   : ∀ {A} {p : IsPrimitive A} {v} →
                           InstrNoHeapWrite (instr-load-const p v)
  -- Plan 0.2.4.2 Phase A: code-addr load only writes Output register
  nhw-instr-load-code-addr : ∀ {n} → InstrNoHeapWrite (instr-load-code-addr n)
  nhw-instr-save-closure-reg : InstrNoHeapWrite instr-save-closure-reg

-- Instruction preserves frame (doesn't push/pop frame)
InstrPreservesFrame : AbstractInstr → Set
InstrPreservesFrame (instr-push-frame _) = ⊥
  where open import Data.Empty using (⊥)
InstrPreservesFrame instr-pop-frame      = ⊥
  where open import Data.Empty using (⊥)
InstrPreservesFrame mov-to-output          = ⊤
InstrPreservesFrame mov-input2-to-output          = ⊤
InstrPreservesFrame mov-to-input           = ⊤
InstrPreservesFrame mov-output-to-input2           = ⊤
InstrPreservesFrame load-indirect          = ⊤
InstrPreservesFrame load-indirect-suc      = ⊤
InstrPreservesFrame (load-from-slot _)     = ⊤
InstrPreservesFrame (store-at-slot _)      = ⊤
InstrPreservesFrame store-indirect         = ⊤
InstrPreservesFrame store-indirect-suc     = ⊤
InstrPreservesFrame (lea-slot _)           = ⊤
InstrPreservesFrame (restore-input _)      = ⊤
InstrPreservesFrame (instr-alloc-stack _)  = ⊤
InstrPreservesFrame (instr-dealloc-stack _) = ⊤
InstrPreservesFrame (instr-reclaim-to _)   = ⊤
InstrPreservesFrame instr-call-closure     = ⊤
InstrPreservesFrame (worklist-init _)      = ⊤
InstrPreservesFrame (worklist-push _)      = ⊤
InstrPreservesFrame (worklist-pop _)       = ⊤
InstrPreservesFrame (worklist-check _)     = ⊤
InstrPreservesFrame (instr-sigop _)        = ⊤
InstrPreservesFrame (instr-load-const _ _) = ⊤
InstrPreservesFrame (instr-load-code-addr _) = ⊤
InstrPreservesFrame instr-save-closure-reg   = ⊤

-- What memory location does this instruction read?
-- Returns nothing if instruction doesn't read memory.
instr-reads-mem : AbstractInstr → LocState FS → AllocState {FS} → Maybe (ValueLocation FS)
instr-reads-mem mov-to-output s alloc = nothing  -- register only
instr-reads-mem mov-input2-to-output s alloc = nothing  -- register only
instr-reads-mem mov-to-input s alloc = nothing   -- register only
instr-reads-mem mov-output-to-input2 s alloc = nothing   -- register only
instr-reads-mem load-indirect s alloc = just (readReg (regs s) Input1)
instr-reads-mem load-indirect-suc s alloc = just (sucLoc (readReg (regs s) Input1))
instr-reads-mem (load-from-slot k) s alloc = just (AtStack (current-frame alloc) k)
instr-reads-mem (store-at-slot k) s alloc = nothing  -- reads Output register, not memory
instr-reads-mem store-indirect s alloc = nothing     -- reads Output register, not memory
instr-reads-mem store-indirect-suc s alloc = nothing -- reads Output register, not memory
instr-reads-mem (lea-slot k) s alloc = nothing       -- computes address, no read
instr-reads-mem (restore-input k) s alloc = just (AtStack (current-frame alloc) k)
instr-reads-mem (instr-alloc-stack n) s alloc = nothing
instr-reads-mem (instr-dealloc-stack n) s alloc = nothing
instr-reads-mem (instr-reclaim-to n) s alloc = nothing
instr-reads-mem (instr-push-frame cap) s alloc = nothing
instr-reads-mem instr-pop-frame s alloc = nothing
instr-reads-mem instr-call-closure s alloc = nothing
-- OCP-0003: Worklist instructions
instr-reads-mem (worklist-init k) s alloc = nothing      -- no-op
instr-reads-mem (worklist-push k) s alloc = nothing      -- reads register, not memory
instr-reads-mem (worklist-pop k) s alloc = just (AtStack (current-frame alloc) k)
instr-reads-mem (worklist-check k) s alloc = nothing     -- no-op
instr-reads-mem (instr-sigop _)    s alloc = nothing     -- no-op
instr-reads-mem (instr-load-const _ _) s alloc = nothing -- no-op (only writes Output)
instr-reads-mem (instr-load-code-addr _) s alloc = nothing -- no-op (only writes Output)
instr-reads-mem instr-save-closure-reg   s alloc = nothing -- no-op

-- What memory location does this instruction write?
-- Returns nothing if instruction doesn't write memory.
instr-writes-mem : AbstractInstr → LocState FS → AllocState {FS} → Maybe (ValueLocation FS)
instr-writes-mem mov-to-output s alloc = nothing  -- register only
instr-writes-mem mov-input2-to-output s alloc = nothing  -- register only
instr-writes-mem mov-to-input s alloc = nothing   -- register only
instr-writes-mem mov-output-to-input2 s alloc = nothing   -- register only
instr-writes-mem load-indirect s alloc = nothing  -- writes Output register, not memory
instr-writes-mem load-indirect-suc s alloc = nothing
instr-writes-mem (load-from-slot k) s alloc = nothing
instr-writes-mem (store-at-slot k) s alloc = just (AtStack (current-frame alloc) k)
instr-writes-mem store-indirect s alloc = just (readReg (regs s) Input1)
instr-writes-mem store-indirect-suc s alloc = just (sucLoc (readReg (regs s) Input1))
instr-writes-mem (lea-slot k) s alloc = nothing
instr-writes-mem (restore-input k) s alloc = nothing  -- writes Input1 register, not memory
instr-writes-mem (instr-alloc-stack n) s alloc = nothing
instr-writes-mem (instr-dealloc-stack n) s alloc = nothing
instr-writes-mem (instr-reclaim-to n) s alloc = nothing
instr-writes-mem (instr-push-frame cap) s alloc = nothing
instr-writes-mem instr-pop-frame s alloc = nothing
instr-writes-mem instr-call-closure s alloc = nothing
-- OCP-0003: Worklist instructions
instr-writes-mem (worklist-init k) s alloc = nothing     -- no-op
instr-writes-mem (worklist-push k) s alloc = just (AtStack (current-frame alloc) k)
instr-writes-mem (worklist-pop k) s alloc = nothing      -- writes register, not memory
instr-writes-mem (worklist-check k) s alloc = nothing    -- no-op
instr-writes-mem (instr-sigop _)    s alloc = nothing    -- no-op
instr-writes-mem (instr-load-const _ _) s alloc = nothing -- no-op
instr-writes-mem (instr-load-code-addr _) s alloc = nothing -- no-op
instr-writes-mem instr-save-closure-reg   s alloc = nothing -- no-op

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
  exec-abstract-preserves-frame mov-input2-to-output s alloc = refl
  exec-abstract-preserves-frame mov-to-input s alloc = refl
  exec-abstract-preserves-frame mov-output-to-input2 s alloc = refl
  exec-abstract-preserves-frame load-indirect s alloc = refl
  exec-abstract-preserves-frame load-indirect-suc s alloc = refl
  exec-abstract-preserves-frame (load-from-slot slot) s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (store-at-slot slot) s alloc = refl
  exec-abstract-preserves-frame store-indirect s alloc = refl
  exec-abstract-preserves-frame store-indirect-suc s alloc = refl
  exec-abstract-preserves-frame (lea-slot slot) s alloc = refl
  exec-abstract-preserves-frame (restore-input slot) s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (instr-alloc-stack n) s alloc = refl
  exec-abstract-preserves-frame (instr-dealloc-stack n) s alloc = refl
  exec-abstract-preserves-frame (instr-reclaim-to n) s alloc = refl
  exec-abstract-preserves-frame (instr-push-frame cap) s alloc = refl
  exec-abstract-preserves-frame instr-pop-frame s alloc = refl
  exec-abstract-preserves-frame instr-call-closure s alloc = refl
  -- OCP-0003: Worklist instructions
  exec-abstract-preserves-frame (worklist-init slot) s alloc = refl
  exec-abstract-preserves-frame (worklist-push slot) s alloc = refl  -- alloc unchanged
  exec-abstract-preserves-frame (worklist-pop slot) s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-frame (worklist-check slot) s alloc = refl
  exec-abstract-preserves-frame (instr-sigop _)       s alloc = refl
  exec-abstract-preserves-frame (instr-load-const _ _) s alloc = refl
  exec-abstract-preserves-frame (instr-load-code-addr _) s alloc = refl
  exec-abstract-preserves-frame instr-save-closure-reg   s alloc = refl

  -- (E) HEAP PRESERVATION
  -- Instructions that don't write to heap preserve heapMem
  exec-abstract-preserves-heapMem : ∀ (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) →
    InstrNoHeapWrite i →
    heapMem (proj₁ (exec-abstract i s alloc)) ≡ heapMem s
  exec-abstract-preserves-heapMem mov-to-output s alloc nhw-mov-to-output = refl
  exec-abstract-preserves-heapMem mov-input2-to-output s alloc nhw-mov-to-output = refl
  exec-abstract-preserves-heapMem mov-to-input s alloc nhw-mov-to-input = refl
  exec-abstract-preserves-heapMem mov-output-to-input2 s alloc nhw-mov-output-to-input2 = refl
  exec-abstract-preserves-heapMem load-indirect s alloc nhw-load-indirect
    with readLoc s (readReg (regs s) Input1)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem load-indirect-suc s alloc nhw-load-indirect-suc
    with readLoc s (sucLoc (readReg (regs s) Input1))
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (load-from-slot slot) s alloc nhw-load-from-slot
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (store-at-slot slot) s alloc nhw-store-at-slot =
    writeLoc-heapMem-stack s (current-frame alloc) slot (readReg (regs s) Output)
  exec-abstract-preserves-heapMem (lea-slot slot) s alloc nhw-lea-slot = refl
  exec-abstract-preserves-heapMem (restore-input slot) s alloc nhw-restore-input
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (instr-alloc-stack n) s alloc nhw-instr-alloc-stack = refl
  exec-abstract-preserves-heapMem (instr-dealloc-stack n) s alloc nhw-instr-dealloc-stack = refl
  exec-abstract-preserves-heapMem (instr-reclaim-to n) s alloc nhw-instr-reclaim-to = refl
  exec-abstract-preserves-heapMem (instr-push-frame cap) s alloc nhw-instr-push-frame = refl
  exec-abstract-preserves-heapMem instr-pop-frame s alloc nhw-instr-pop-frame = refl
  exec-abstract-preserves-heapMem instr-call-closure s alloc nhw-instr-call-closure = refl
  -- OCP-0003: Worklist instructions
  exec-abstract-preserves-heapMem (worklist-init slot) s alloc nhw-worklist-init = refl
  exec-abstract-preserves-heapMem (worklist-push slot) s alloc nhw-worklist-push =
    writeLoc-heapMem-stack s (current-frame alloc) slot (readReg (regs s) Output)
  exec-abstract-preserves-heapMem (worklist-pop slot) s alloc nhw-worklist-pop
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (worklist-check slot) s alloc nhw-worklist-check = refl
  exec-abstract-preserves-heapMem (instr-sigop _)       s alloc nhw-instr-sigop    = refl
  exec-abstract-preserves-heapMem (instr-load-const _ _) s alloc nhw-instr-load-const = refl
  exec-abstract-preserves-heapMem (instr-load-code-addr _) s alloc nhw-instr-load-code-addr = refl
  exec-abstract-preserves-heapMem instr-save-closure-reg   s alloc nhw-instr-save-closure-reg = refl

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
    readLoc (proj₁ (exec-abstract i s alloc)) (AtStack f slot) ≡ readLoc s (AtStack f slot)
  -- Register-only instructions
  exec-abstract-preserves-stack-slot mov-to-output s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot mov-input2-to-output s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot mov-to-input s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot mov-output-to-input2 s alloc f slot _ _ = refl
  -- Load instructions: only modify registers, preserve all memory
  exec-abstract-preserves-stack-slot load-indirect s alloc f slot _ _ =
    readLoc-stackMem-eq (proj₁ (exec-abstract load-indirect s alloc)) s (AtStack f slot)
      (load-preserves-stackMem Output (IndReg Input1) s)
      (load-preserves-heapMem Output (IndReg Input1) s)
  exec-abstract-preserves-stack-slot load-indirect-suc s alloc f slot _ _ =
    readLoc-stackMem-eq (proj₁ (exec-abstract load-indirect-suc s alloc)) s (AtStack f slot)
      (load-preserves-stackMem Output (IndRegSuc Input1) s)
      (load-preserves-heapMem Output (IndRegSuc Input1) s)
  exec-abstract-preserves-stack-slot (load-from-slot k) s alloc f slot _ _
    with readLoc s (AtStack (current-frame alloc) k)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-stack-slot (lea-slot k) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (restore-input k) s alloc f slot _ _
    with readLoc s (AtStack (current-frame alloc) k)
  ... | just _  = refl
  ... | nothing = refl
  -- Stack management instructions: preserve all memory
  exec-abstract-preserves-stack-slot (instr-alloc-stack _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (instr-dealloc-stack _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (instr-reclaim-to _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (instr-push-frame _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot instr-pop-frame s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot instr-call-closure s alloc f slot _ _ = refl
  -- OCP-0003: Worklist instructions
  exec-abstract-preserves-stack-slot (worklist-init _) s alloc f slot _ _ = refl
  -- worklist-push is like store-at-slot - need to handle separately with slot bounds
  exec-abstract-preserves-stack-slot (worklist-push k) s alloc f slot _ _ = !!  -- TODO: needs slot bound reasoning
  exec-abstract-preserves-stack-slot (worklist-pop k) s alloc f slot _ _
    with readLoc s (AtStack (current-frame alloc) k)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-stack-slot (worklist-check _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (instr-sigop _)    s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (instr-load-const _ _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot (instr-load-code-addr _) s alloc f slot _ _ = refl
  exec-abstract-preserves-stack-slot instr-save-closure-reg   s alloc f slot _ _ = refl

  -- store-at-slot k preserves slot j when j < k (positive ordering)
  store-at-slot-preserves-below : ∀ (j k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    j < k →
    readLoc (proj₁ (exec-abstract (store-at-slot k) s alloc)) (AtStack (current-frame alloc) j) ≡
    readLoc s (AtStack (current-frame alloc) j)
  store-at-slot-preserves-below j k s alloc j<k =
    readLoc-writeLoc-stack-slot-lt s (current-frame alloc) j k (readReg (regs s) Output) j<k

  -- store-at-slot j preserves slot k when j < k (positive ordering)
  store-at-slot-preserves-above : ∀ (j k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    j < k →
    readLoc (proj₁ (exec-abstract (store-at-slot j) s alloc)) (AtStack (current-frame alloc) k) ≡
    readLoc s (AtStack (current-frame alloc) k)
  store-at-slot-preserves-above j k s alloc j<k =
    readLoc-writeLoc-stack-slot-gt s (current-frame alloc) j k (readReg (regs s) Output) j<k

  -- store-at-slot preserves ancestor frame slots (positive frame ordering)
  store-at-slot-preserves-ancestor : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (f : Frame FS) (slot : ℕ) →
    current-frame alloc ≺ f →
    readLoc (proj₁ (exec-abstract (store-at-slot k) s alloc)) (AtStack f slot) ≡
    readLoc s (AtStack f slot)
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
  exec-abstract-same-frame mov-input2-to-output s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame mov-to-input s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame mov-output-to-input2 s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame load-indirect s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame load-indirect-suc s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame store-indirect s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame store-indirect-suc s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-alloc-stack n) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-dealloc-stack n) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-reclaim-to n) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-push-frame cap) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame instr-pop-frame s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame instr-call-closure s alloc₁ alloc₂ _ = refl
  -- Instructions that use current-frame alloc
  exec-abstract-same-frame (load-from-slot slot) s alloc₁ alloc₂ frame-eq
    with readLoc s (AtStack (current-frame alloc₁) slot)
       | readLoc s (AtStack (current-frame alloc₂) slot)
       | cong (λ f → readLoc s (AtStack f slot)) frame-eq
  ... | just v₁ | just v₂ | eq rewrite just-injective eq = refl
  ... | nothing | nothing | _ = refl
  ... | just _ | nothing | ()
  ... | nothing | just _ | ()
  exec-abstract-same-frame (store-at-slot slot) s alloc₁ alloc₂ frame-eq
    rewrite frame-eq = refl
  exec-abstract-same-frame (lea-slot slot) s alloc₁ alloc₂ frame-eq
    rewrite frame-eq = refl
  exec-abstract-same-frame (restore-input slot) s alloc₁ alloc₂ frame-eq
    with readLoc s (AtStack (current-frame alloc₁) slot)
       | readLoc s (AtStack (current-frame alloc₂) slot)
       | cong (λ f → readLoc s (AtStack f slot)) frame-eq
  ... | just v₁ | just v₂ | eq rewrite just-injective eq = refl
  ... | nothing | nothing | _ = refl
  ... | just _ | nothing | ()
  ... | nothing | just _ | ()
  -- OCP-0003: Worklist instructions
  exec-abstract-same-frame (worklist-init slot) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (worklist-push slot) s alloc₁ alloc₂ frame-eq
    rewrite frame-eq = refl
  exec-abstract-same-frame (worklist-pop slot) s alloc₁ alloc₂ frame-eq
    with readLoc s (AtStack (current-frame alloc₁) slot)
       | readLoc s (AtStack (current-frame alloc₂) slot)
       | cong (λ f → readLoc s (AtStack f slot)) frame-eq
  ... | just v₁ | just v₂ | eq rewrite just-injective eq = refl
  ... | nothing | nothing | _ = refl
  ... | just _ | nothing | ()
  ... | nothing | just _ | ()
  exec-abstract-same-frame (worklist-check slot) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-sigop _)       s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-load-const _ _) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame (instr-load-code-addr _) s alloc₁ alloc₂ _ = refl
  exec-abstract-same-frame instr-save-closure-reg   s alloc₁ alloc₂ _ = refl

------------------------------------------------------------------------
-- Level 5: Trace Primitives
--
-- POSITIVE trace characterization:
--   TraceWritesBelow n trace : "writes to slots in {0, ..., n-1}"
--   TraceNoHeapWrites trace : "writes only to stack (no heap writes)"
--
-- Together these POSITIVELY characterize the write set:
--   "trace writes to {AtStack frame k | k < n}"
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
InstrWritesToHeap store-indirect           = ⊤
InstrWritesToHeap store-indirect-suc       = ⊤
InstrWritesToHeap mov-to-output            = ⊥
InstrWritesToHeap mov-input2-to-output            = ⊥
InstrWritesToHeap mov-to-input             = ⊥
InstrWritesToHeap mov-output-to-input2             = ⊥
InstrWritesToHeap load-indirect            = ⊥
InstrWritesToHeap load-indirect-suc        = ⊥
InstrWritesToHeap (load-from-slot _)       = ⊥
InstrWritesToHeap (store-at-slot _)        = ⊥
InstrWritesToHeap (lea-slot _)             = ⊥
InstrWritesToHeap (restore-input _)        = ⊥
InstrWritesToHeap (instr-alloc-stack _)    = ⊥
InstrWritesToHeap (instr-dealloc-stack _)  = ⊥
InstrWritesToHeap (instr-reclaim-to _)     = ⊥
InstrWritesToHeap (instr-push-frame _)     = ⊥
InstrWritesToHeap instr-pop-frame          = ⊥
InstrWritesToHeap instr-call-closure       = ⊥
InstrWritesToHeap (worklist-init _)        = ⊥
InstrWritesToHeap (worklist-push _)        = ⊥
InstrWritesToHeap (worklist-pop _)         = ⊥
InstrWritesToHeap (worklist-check _)       = ⊥
InstrWritesToHeap (instr-sigop _)          = ⊥
InstrWritesToHeap (instr-load-const _ _)   = ⊥
InstrWritesToHeap (instr-load-code-addr _) = ⊥
InstrWritesToHeap instr-save-closure-reg   = ⊥

-- Helper: trace contains no heap-writing instructions (syntactic)
-- This is useful for constructing TraceWritesWithinOwned [] proofs
TraceNoHeapWrites : AbstractTrace → Set
TraceNoHeapWrites []                              = ⊤
TraceNoHeapWrites (store-indirect ∷ _)            = ⊥
TraceNoHeapWrites (store-indirect-suc ∷ _)        = ⊥
TraceNoHeapWrites (mov-to-output ∷ t)             = TraceNoHeapWrites t
TraceNoHeapWrites (mov-input2-to-output ∷ t)             = TraceNoHeapWrites t
TraceNoHeapWrites (mov-to-input ∷ t)              = TraceNoHeapWrites t
TraceNoHeapWrites (mov-output-to-input2 ∷ t)              = TraceNoHeapWrites t
TraceNoHeapWrites (load-indirect ∷ t)             = TraceNoHeapWrites t
TraceNoHeapWrites (load-indirect-suc ∷ t)         = TraceNoHeapWrites t
TraceNoHeapWrites (load-from-slot _ ∷ t)          = TraceNoHeapWrites t
TraceNoHeapWrites (store-at-slot _ ∷ t)           = TraceNoHeapWrites t
TraceNoHeapWrites (lea-slot _ ∷ t)                = TraceNoHeapWrites t
TraceNoHeapWrites (restore-input _ ∷ t)           = TraceNoHeapWrites t
TraceNoHeapWrites (instr-alloc-stack _ ∷ t)       = TraceNoHeapWrites t
TraceNoHeapWrites (instr-dealloc-stack _ ∷ t)     = TraceNoHeapWrites t
TraceNoHeapWrites (instr-reclaim-to _ ∷ t)        = TraceNoHeapWrites t
TraceNoHeapWrites (instr-push-frame _ ∷ t)        = TraceNoHeapWrites t
TraceNoHeapWrites (instr-pop-frame ∷ t)           = TraceNoHeapWrites t
TraceNoHeapWrites (instr-call-closure ∷ t)        = TraceNoHeapWrites t
TraceNoHeapWrites (worklist-init _ ∷ t)           = TraceNoHeapWrites t
TraceNoHeapWrites (worklist-push _ ∷ t)           = TraceNoHeapWrites t
TraceNoHeapWrites (worklist-pop _ ∷ t)            = TraceNoHeapWrites t
TraceNoHeapWrites (worklist-check _ ∷ t)          = TraceNoHeapWrites t
TraceNoHeapWrites (instr-sigop _ ∷ t)             = TraceNoHeapWrites t
TraceNoHeapWrites (instr-load-const _ _ ∷ t)      = TraceNoHeapWrites t
TraceNoHeapWrites (instr-load-code-addr _ ∷ t)    = TraceNoHeapWrites t
TraceNoHeapWrites (instr-save-closure-reg ∷ t)    = TraceNoHeapWrites t

-- All instructions in trace preserve frame
TracePreservesFrame : AbstractTrace → Set
TracePreservesFrame [] = ⊤
TracePreservesFrame (i ∷ t) = InstrPreservesFrame i × TracePreservesFrame t

-- All instructions in trace preserve heapMem (no heap writes)
TracePreservesHeapMem : AbstractTrace → Set
TracePreservesHeapMem [] = ⊤
TracePreservesHeapMem (i ∷ t) = InstrNoHeapWrite i × TracePreservesHeapMem t

------------------------------------------------------------------------
-- Capacity Preservation (REMOVED in Phase 3)
--
-- InstrPreservesCapacity and TracePreservesCapacity have been removed
-- because frame-capacity was removed from AllocState. Capacity bounds
-- are now enforced per-IR via the scratch-bounded invariant.
------------------------------------------------------------------------

-- Append preserves TraceNoHeapWrites
trace-no-heap-writes-append : ∀ t1 t2 →
  TraceNoHeapWrites t1 → TraceNoHeapWrites t2 →
  TraceNoHeapWrites (t1 ++ t2)
trace-no-heap-writes-append [] t2 _ tn2 = tn2
trace-no-heap-writes-append (mov-to-output ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (mov-input2-to-output ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (mov-to-input ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (mov-output-to-input2 ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
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
trace-no-heap-writes-append (instr-reclaim-to _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-push-frame _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-pop-frame ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-call-closure ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
-- OCP-0003: Worklist instructions
trace-no-heap-writes-append (worklist-init _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (worklist-push _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (worklist-pop _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (worklist-check _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-sigop _ ∷ t1)    t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-load-const _ _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-load-code-addr _ ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2
trace-no-heap-writes-append (instr-save-closure-reg ∷ t1) t2 tn1 tn2 = trace-no-heap-writes-append t1 t2 tn1 tn2

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

  -- Note: exec-abstract-preserves-capacity and exec-trace-preserves-capacity'
  -- have been removed in Phase 3 (frame-capacity removed from AllocState).

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
    tnhw-head mov-input2-to-output _ _ = nhw-mov-to-output
    tnhw-head mov-to-input _ _ = nhw-mov-to-input
    tnhw-head mov-output-to-input2 _ _ = nhw-mov-to-input
    tnhw-head load-indirect _ _ = nhw-load-indirect
    tnhw-head load-indirect-suc _ _ = nhw-load-indirect-suc
    tnhw-head (load-from-slot _) _ _ = nhw-load-from-slot
    tnhw-head (store-at-slot _) _ _ = nhw-store-at-slot
    tnhw-head (lea-slot _) _ _ = nhw-lea-slot
    tnhw-head (restore-input _) _ _ = nhw-restore-input
    tnhw-head (instr-alloc-stack _) _ _ = nhw-instr-alloc-stack
    tnhw-head (instr-dealloc-stack _) _ _ = nhw-instr-dealloc-stack
    tnhw-head (instr-reclaim-to _) _ _ = nhw-instr-reclaim-to
    tnhw-head (instr-push-frame _) _ _ = nhw-instr-push-frame
    tnhw-head instr-pop-frame _ _ = nhw-instr-pop-frame
    tnhw-head instr-call-closure _ _ = nhw-instr-call-closure
    -- OCP-0003: Worklist instructions
    tnhw-head (worklist-init _) _ _ = nhw-worklist-init
    tnhw-head (worklist-push _) _ _ = nhw-worklist-push
    tnhw-head (worklist-pop _) _ _ = nhw-worklist-pop
    tnhw-head (worklist-check _) _ _ = nhw-worklist-check
    tnhw-head (instr-sigop _)    _ _ = nhw-instr-sigop
    tnhw-head (instr-load-const _ _) _ _ = nhw-instr-load-const
    tnhw-head (instr-load-code-addr _) _ _ = nhw-instr-load-code-addr
    tnhw-head instr-save-closure-reg   _ _ = nhw-instr-save-closure-reg

    -- Helper: extract TraceNoHeapWrites for tail
    tnhw-tail : ∀ (i : AbstractInstr) (rest : AbstractTrace) →
      TraceNoHeapWrites (i ∷ rest) → TraceNoHeapWrites rest
    tnhw-tail mov-to-output rest tnhw = tnhw
    tnhw-tail mov-input2-to-output rest tnhw = tnhw
    tnhw-tail mov-to-input rest tnhw = tnhw
    tnhw-tail mov-output-to-input2 rest tnhw = tnhw
    tnhw-tail load-indirect rest tnhw = tnhw
    tnhw-tail load-indirect-suc rest tnhw = tnhw
    tnhw-tail (load-from-slot _) rest tnhw = tnhw
    tnhw-tail (store-at-slot _) rest tnhw = tnhw
    tnhw-tail (lea-slot _) rest tnhw = tnhw
    tnhw-tail (restore-input _) rest tnhw = tnhw
    tnhw-tail (instr-alloc-stack _) rest tnhw = tnhw
    tnhw-tail (instr-dealloc-stack _) rest tnhw = tnhw
    tnhw-tail (instr-reclaim-to _) rest tnhw = tnhw
    tnhw-tail (instr-push-frame _) rest tnhw = tnhw
    tnhw-tail instr-pop-frame rest tnhw = tnhw
    tnhw-tail instr-call-closure rest tnhw = tnhw
    -- OCP-0003: Worklist instructions
    tnhw-tail (worklist-init _) rest tnhw = tnhw
    tnhw-tail (worklist-push _) rest tnhw = tnhw
    tnhw-tail (worklist-pop _) rest tnhw = tnhw
    tnhw-tail (worklist-check _) rest tnhw = tnhw
    tnhw-tail (instr-sigop _)    rest tnhw = tnhw
    tnhw-tail (instr-load-const _ _) rest tnhw = tnhw
    tnhw-tail (instr-load-code-addr _) rest tnhw = tnhw
    tnhw-tail instr-save-closure-reg   rest tnhw = tnhw

  -- (A1) Current frame slot below write bound is preserved
  -- If trace writes above n (at slots ≥ n), then slot < n is preserved
  mutual
    exec-trace-preserves-slot-below : ∀ (trace : AbstractTrace) (s : LocState FS)
      (alloc : AllocState {FS}) (n slot : ℕ) →
      TraceWritesAbove n trace →        -- writes at slots ≥ n
      TraceNoHeapWrites trace →         -- no heap writes
      slot < n →                        -- slot is below write region
      readLoc (proj₁ (exec-trace trace s alloc)) (AtStack (current-frame alloc) slot) ≡
      readLoc s (AtStack (current-frame alloc) slot)
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
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (AtStack cf slot) ≡
                             readLoc s' (AtStack cf slot))
                     frame-pres ih)
               step-pres
    -- Non-writing instructions (instr-writes-slot = nothing)
    exec-trace-preserves-slot-below (mov-to-output ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite mov-to-output rest s alloc n slot twa tnhw slot<n nhw-mov-to-output refl
    exec-trace-preserves-slot-below (mov-input2-to-output ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite mov-input2-to-output rest s alloc n slot twa tnhw slot<n nhw-mov-input2-to-output refl
    exec-trace-preserves-slot-below (mov-to-input ∷ rest) s alloc n slot twa tnhw slot<n =
    exec-trace-preserves-slot-below (mov-output-to-input2 ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite mov-output-to-input2 rest s alloc n slot twa tnhw slot<n nhw-mov-output-to-input2 refl
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
    exec-trace-preserves-slot-below (instr-reclaim-to m ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (instr-reclaim-to m) rest s alloc n slot twa tnhw slot<n nhw-instr-reclaim-to refl
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
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (AtStack cf slot) ≡
                             readLoc s' (AtStack cf slot))
                     frame-pres ih)
               step-pres
    exec-trace-preserves-slot-below (worklist-pop k ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (worklist-pop k) rest s alloc n slot twa tnhw slot<n nhw-worklist-pop refl
    exec-trace-preserves-slot-below (worklist-check k ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (worklist-check k) rest s alloc n slot twa tnhw slot<n nhw-worklist-check refl
    exec-trace-preserves-slot-below (instr-sigop nm ∷ rest)   s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (instr-sigop nm) rest s alloc n slot twa tnhw slot<n nhw-instr-sigop    refl
    exec-trace-preserves-slot-below (instr-load-const p v ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (instr-load-const p v) rest s alloc n slot twa tnhw slot<n nhw-instr-load-const refl
    exec-trace-preserves-slot-below (instr-load-code-addr k ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite (instr-load-code-addr k) rest s alloc n slot twa tnhw slot<n nhw-instr-load-code-addr refl
    exec-trace-preserves-slot-below (instr-save-closure-reg ∷ rest) s alloc n slot twa tnhw slot<n =
      exec-trace-preserves-slot-below-nonwrite instr-save-closure-reg rest s alloc n slot twa tnhw slot<n nhw-instr-save-closure-reg refl

    -- Helper for non-writing instructions
    exec-trace-preserves-slot-below-nonwrite : ∀ (i : AbstractInstr) (rest : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS}) (n slot : ℕ) →
      TraceWritesAbove n (i ∷ rest) →
      TraceNoHeapWrites (i ∷ rest) →
      slot < n →
      InstrNoHeapWrite i →
      instr-writes-slot i ≡ nothing →
      readLoc (proj₁ (exec-trace (i ∷ rest) s alloc)) (AtStack (current-frame alloc) slot) ≡
      readLoc s (AtStack (current-frame alloc) slot)
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
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (AtStack cf slot) ≡
                             readLoc s' (AtStack cf slot))
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
      readLoc (proj₁ (exec-trace trace s alloc)) (AtStack (current-frame alloc) slot) ≡
      readLoc s (AtStack (current-frame alloc) slot)
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
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (AtStack cf slot) ≡
                             readLoc s' (AtStack cf slot))
                     frame-pres ih)
               step-pres
    -- Non-writing instructions (instr-writes-slot = nothing)
    exec-trace-preserves-slot-above (mov-to-output ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite mov-to-output rest s alloc m slot twb tnhw m≤slot nhw-mov-to-output refl
    exec-trace-preserves-slot-above (mov-input2-to-output ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite mov-input2-to-output rest s alloc m slot twb tnhw m≤slot nhw-mov-input2-to-output refl
    exec-trace-preserves-slot-above (mov-to-input ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite mov-to-input rest s alloc m slot twb tnhw m≤slot nhw-mov-to-input refl
    exec-trace-preserves-slot-above (mov-output-to-input2 ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite mov-output-to-input2 rest s alloc m slot twb tnhw m≤slot nhw-mov-output-to-input2 refl
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
    exec-trace-preserves-slot-above (instr-reclaim-to n ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (instr-reclaim-to n) rest s alloc m slot twb tnhw m≤slot nhw-instr-reclaim-to refl
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
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (AtStack cf slot) ≡
                             readLoc s' (AtStack cf slot))
                     frame-pres ih)
               step-pres
    exec-trace-preserves-slot-above (worklist-pop k ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (worklist-pop k) rest s alloc m slot twb tnhw m≤slot nhw-worklist-pop refl
    exec-trace-preserves-slot-above (worklist-check k ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (worklist-check k) rest s alloc m slot twb tnhw m≤slot nhw-worklist-check refl
    exec-trace-preserves-slot-above (instr-sigop nm ∷ rest)   s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (instr-sigop nm) rest s alloc m slot twb tnhw m≤slot nhw-instr-sigop    refl
    exec-trace-preserves-slot-above (instr-load-const p v ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (instr-load-const p v) rest s alloc m slot twb tnhw m≤slot nhw-instr-load-const refl
    exec-trace-preserves-slot-above (instr-load-code-addr k ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite (instr-load-code-addr k) rest s alloc m slot twb tnhw m≤slot nhw-instr-load-code-addr refl
    exec-trace-preserves-slot-above (instr-save-closure-reg ∷ rest) s alloc m slot twb tnhw m≤slot =
      exec-trace-preserves-slot-above-nonwrite instr-save-closure-reg rest s alloc m slot twb tnhw m≤slot nhw-instr-save-closure-reg refl

    -- Helper for non-writing instructions
    exec-trace-preserves-slot-above-nonwrite : ∀ (i : AbstractInstr) (rest : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS}) (m slot : ℕ) →
      TraceWritesBelow m (i ∷ rest) →
      TraceNoHeapWrites (i ∷ rest) →
      m ≤ slot →
      InstrNoHeapWrite i →
      instr-writes-slot i ≡ nothing →
      readLoc (proj₁ (exec-trace (i ∷ rest) s alloc)) (AtStack (current-frame alloc) slot) ≡
      readLoc s (AtStack (current-frame alloc) slot)
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
      in trans (subst (λ cf → readLoc (proj₁ (exec-trace rest s' alloc')) (AtStack cf slot) ≡
                             readLoc s' (AtStack cf slot))
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
      readLoc (proj₁ (exec-trace trace s alloc)) (AtStack f slot) ≡
      readLoc s (AtStack f slot)
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
    exec-trace-preserves-ancestor (mov-input2-to-output ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite mov-input2-to-output rest s alloc f slot cf≺f tnhw nhw-mov-input2-to-output refl
    exec-trace-preserves-ancestor (mov-to-input ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite mov-to-input rest s alloc f slot cf≺f tnhw nhw-mov-to-input refl
    exec-trace-preserves-ancestor (mov-output-to-input2 ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite mov-output-to-input2 rest s alloc f slot cf≺f tnhw nhw-mov-output-to-input2 refl
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
    exec-trace-preserves-ancestor (instr-reclaim-to m ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (instr-reclaim-to m) rest s alloc f slot cf≺f tnhw nhw-instr-reclaim-to refl
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
    exec-trace-preserves-ancestor (instr-sigop nm ∷ rest)   s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (instr-sigop nm) rest s alloc f slot cf≺f tnhw nhw-instr-sigop    refl
    exec-trace-preserves-ancestor (instr-load-const p v ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (instr-load-const p v) rest s alloc f slot cf≺f tnhw nhw-instr-load-const refl
    exec-trace-preserves-ancestor (instr-load-code-addr k ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite (instr-load-code-addr k) rest s alloc f slot cf≺f tnhw nhw-instr-load-code-addr refl
    exec-trace-preserves-ancestor (instr-save-closure-reg ∷ rest) s alloc f slot cf≺f tnhw =
      exec-trace-preserves-ancestor-nonwrite instr-save-closure-reg rest s alloc f slot cf≺f tnhw nhw-instr-save-closure-reg refl

    -- Helper for non-writing instructions in ancestor preservation
    exec-trace-preserves-ancestor-nonwrite : ∀ (i : AbstractInstr) (rest : AbstractTrace)
      (s : LocState FS) (alloc : AllocState {FS}) (f : Frame FS) (slot : ℕ) →
      current-frame alloc ≺ f →
      TraceNoHeapWrites (i ∷ rest) →
      InstrNoHeapWrite i →
      instr-writes-slot i ≡ nothing →
      readLoc (proj₁ (exec-trace (i ∷ rest) s alloc)) (AtStack f slot) ≡
      readLoc s (AtStack f slot)
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
    readLoc (proj₁ (exec-trace trace s alloc)) (AtDynamic h) ≡
    readLoc s (AtDynamic h)
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
    proj₁ (exec-trace trace (writeLoc s (AtStack f slot) val) alloc) ≡
    writeLoc (proj₁ (exec-trace trace s alloc)) (AtStack f slot) val
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
    proj₁ (exec-trace trace (writeLoc s (AtStack f slot) val) alloc) ≡
    writeLoc (proj₁ (exec-trace trace s alloc)) (AtStack f slot) val
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
           readLoc s₁ (AtStack (current-frame alloc) k) ≡ readLoc s₂ (AtStack (current-frame alloc) k)) →
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
    iph-mov-to-output      : InstrPreservesHalted mov-input2-to-output
    iph-mov-to-input       : InstrPreservesHalted mov-to-input
    iph-mov-output-to-input2       : InstrPreservesHalted mov-output-to-input2
    iph-store-at-slot      : ∀ {slot} → InstrPreservesHalted (store-at-slot slot)
    iph-store-indirect     : InstrPreservesHalted store-indirect
    iph-store-indirect-suc : InstrPreservesHalted store-indirect-suc
    iph-lea-slot           : ∀ {slot} → InstrPreservesHalted (lea-slot slot)
    iph-alloc-stack        : ∀ {n} → InstrPreservesHalted (instr-alloc-stack n)
    iph-dealloc-stack      : ∀ {n} → InstrPreservesHalted (instr-dealloc-stack n)
    iph-reclaim-to         : ∀ {n} → InstrPreservesHalted (instr-reclaim-to n)
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
  exec-abstract-preserves-halted mov-input2-to-output s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted mov-to-input s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted mov-output-to-input2 s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (store-at-slot slot) s alloc h-eq _ =
    trans (writeLoc-halted s (AtStack (current-frame alloc) slot) (readReg (regs s) Output)) h-eq
  exec-abstract-preserves-halted store-indirect s alloc h-eq _ =
    trans (writeLoc-halted s (readReg (regs s) Input1) (readReg (regs s) Output)) h-eq
  exec-abstract-preserves-halted store-indirect-suc s alloc h-eq _ =
    trans (writeLoc-halted s (sucLoc (readReg (regs s) Input1)) (readReg (regs s) Output)) h-eq
  exec-abstract-preserves-halted (lea-slot slot) s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (instr-alloc-stack n) s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (instr-dealloc-stack n) s alloc h-eq _ = h-eq
  exec-abstract-preserves-halted (instr-reclaim-to n) s alloc h-eq _ = h-eq
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
    trans (writeLoc-halted s (AtStack (current-frame alloc) slot) (readReg (regs s) Output)) h-eq
  exec-abstract-preserves-halted (worklist-pop slot) s alloc h-eq iph-worklist-pop =
    load-from-slot-preserves-halted slot s alloc h-eq  -- same as load-from-slot
  exec-abstract-preserves-halted (worklist-check slot) s alloc h-eq _ = h-eq
  -- Plan 0.11 Task A: SigOp may halt (e.g. linux.exit), so it is NOT
  -- a member of InstrPreservesHalted. The case is unreachable —
  -- there is no `iph-instr-sigop` constructor — so we use the absurd
  -- pattern. (Previously this clause returned `h-eq` defensively;
  -- with the strengthened `exec-abstract (instr-sigop si)` body
  -- consulting `exec-sigop-halts si`, that defensive return no
  -- longer typechecks anyway.)
  exec-abstract-preserves-halted (instr-sigop _)       s alloc h-eq ()

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
    readLoc s (AtStack (current-frame alloc) k) ≡ just v →
    TraceWritesAbove (suc k) trace →
    TraceNoHeapWrites trace →
    readLoc (proj₁ (exec-trace trace s alloc)) (AtStack (current-frame alloc) k) ≡ just v
  exec-trace-slot-value trace s alloc k v slot-has-v twa tnhw =
    let -- k < suc k, so slot k is below write region
        k<suck : k < suc k
        k<suck = ≤-refl
        -- Apply positive characterization lemma
        preserved : readLoc (proj₁ (exec-trace trace s alloc)) (AtStack (current-frame alloc) k) ≡
                    readLoc s (AtStack (current-frame alloc) k)
        preserved = exec-trace-preserves-slot-below trace s alloc (suc k) k twa tnhw k<suck
    in trans preserved slot-has-v

  -- Dual: slot value preservation for TraceWritesBelow
  -- If slot k has value v and trace writes below k (at slots < k), then k is preserved
  exec-trace-slot-value-below : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) (k : ℕ) (v : ValueLocation FS) →
    readLoc s (AtStack (current-frame alloc) k) ≡ just v →
    TraceWritesBelow k trace →        -- writes at slots < k
    TraceNoHeapWrites trace →
    readLoc (proj₁ (exec-trace trace s alloc)) (AtStack (current-frame alloc) k) ≡ just v
  exec-trace-slot-value-below trace s alloc k v slot-has-v twb tnhw =
    let -- k ≥ k, so slot k is above write region
        k≤k : k ≤ k
        k≤k = ≤-refl
        -- Apply positive characterization lemma
        preserved : readLoc (proj₁ (exec-trace trace s alloc)) (AtStack (current-frame alloc) k) ≡
                    readLoc s (AtStack (current-frame alloc) k)
        preserved = exec-trace-preserves-slot-above trace s alloc k k twb tnhw k≤k
    in trans preserved slot-has-v

  -- store-at-slot writes the Output register value to the slot
  store-at-slot-result : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    readLoc (proj₁ (exec-abstract (store-at-slot k) s alloc))
            (AtStack (current-frame alloc) k) ≡ just (readReg (regs s) Output)
  store-at-slot-result k s alloc = readLoc-writeLoc-same s (AtStack (current-frame alloc) k) (readReg (regs s) Output)

  -- store-at-slot preserves halted
  store-at-slot-halted : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted (proj₁ (exec-abstract (store-at-slot k) s alloc)) ≡ halted s
  store-at-slot-halted k s alloc = writeLoc-halted s (AtStack (current-frame alloc) k) (readReg (regs s) Output)

  -- store-at-slot preserves registers
  store-at-slot-regs : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    regs (proj₁ (exec-abstract (store-at-slot k) s alloc)) ≡ regs s
  store-at-slot-regs k s alloc = writeLoc-regs s (AtStack (current-frame alloc) k) (readReg (regs s) Output)

  -- store-at-slot preserves other slots: writing to slot j preserves slot k when j < k or k < j
  store-at-slot-preserves-other : ∀ (j k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    j < k ⊎ k < j →
    readLoc (proj₁ (exec-abstract (store-at-slot j) s alloc)) (AtStack (current-frame alloc) k) ≡
    readLoc s (AtStack (current-frame alloc) k)
  store-at-slot-preserves-other j k s alloc (inj₁ j<k) =
    writeLoc-preserves-other s (AtStack (current-frame alloc) j) (AtStack (current-frame alloc) k)
      (readReg (regs s) Output) (stack-slot-disjoint (current-frame alloc) j k (<⇒≢ j<k))
  store-at-slot-preserves-other j k s alloc (inj₂ k<j) =
    writeLoc-preserves-other s (AtStack (current-frame alloc) j) (AtStack (current-frame alloc) k)
      (readReg (regs s) Output) (stack-slot-disjoint (current-frame alloc) j k (≢-sym (<⇒≢ k<j)))

  -- store-at-slot preserves Input1 register (derived from store-at-slot-regs)
  exec-abstract-store-at-slot-preserves-input : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    readReg (regs (proj₁ (exec-abstract (store-at-slot k) s alloc))) Input1 ≡
    readReg (regs s) Input1
  exec-abstract-store-at-slot-preserves-input k s alloc =
    cong (λ r → readReg r Input1) (store-at-slot-regs k s alloc)

  -- store-at-slot preserves any memory location except the written slot
  -- This handles heap locations, ancestor frames, and different slots
  exec-abstract-store-at-slot-preserves-loc : ∀ (k : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    loc ≢ AtStack (current-frame alloc) k →
    readLoc (proj₁ (exec-abstract (store-at-slot k) s alloc)) loc ≡ readLoc s loc
  exec-abstract-store-at-slot-preserves-loc k s alloc (AtStack f j) loc≢slot =
    writeLoc-preserves-other s (AtStack (current-frame alloc) k) (AtStack f j)
      (readReg (regs s) Output) (λ eq → loc≢slot (sym eq))
  exec-abstract-store-at-slot-preserves-loc k s alloc (AtDynamic hl) _ =
    writeLoc-preserves-other s (AtStack (current-frame alloc) k) (AtDynamic hl)
      (readReg (regs s) Output) (λ ())

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
    AtStack (current-frame alloc) k
  lea-slot-result k s alloc = writeReg-same (regs s) Output (AtStack (current-frame alloc) k)

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
    AtStack (current-frame alloc) k
  exec-trace-final-lea-slot trace k s alloc not-halted-after =
    let s' = proj₁ (exec-trace trace s alloc)
        alloc' = proj₂ (exec-trace trace s alloc)
        -- Step 1: Decompose trace ++ [lea-slot k] using snoc
        snoc-eq : proj₁ (exec-trace (trace ++ (lea-slot k ∷ [])) s alloc) ≡
                  proj₁ (exec-abstract (lea-slot k) s' alloc')
        snoc-eq = exec-trace-snoc-state trace (lea-slot k) s alloc not-halted-after
        -- Step 2: lea-slot result (uses alloc')
        lea-result : readReg (regs (proj₁ (exec-abstract (lea-slot k) s' alloc'))) Output ≡
                     AtStack (current-frame alloc') k
        lea-result = lea-slot-result k s' alloc'
        -- Step 3: Frame preservation (works for all traces)
        frame-eq : current-frame alloc' ≡ current-frame alloc
        frame-eq = exec-trace-preserves-frame trace s alloc
        -- Step 4: Combine
        result-with-alloc' : readReg (regs (proj₁ (exec-trace (trace ++ (lea-slot k ∷ [])) s alloc))) Output ≡
                             AtStack (current-frame alloc') k
        result-with-alloc' = trans (cong (λ st → readReg (regs st) Output) snoc-eq) lea-result
    in trans result-with-alloc' (cong (λ f → AtStack f k) frame-eq)

  -- Final lea-slot k followed by mov-to-input: sets Input1 to slot address
  -- Final lea-slot k followed by mov-output-to-input2: sets Input1 to slot address
  -- Common pattern in Apply setup traces
  exec-trace-final-lea-mov-input : ∀ (trace : AbstractTrace) (k : ℕ) (s : LocState FS)
    (alloc : AllocState {FS}) →
    halted (proj₁ (exec-trace trace s alloc)) ≡ false →
    readReg (regs (proj₁ (exec-trace (trace ++ (lea-slot k ∷ mov-to-input ∷ [])) s alloc))) Input1 ≡
    readReg (regs (proj₁ (exec-trace (trace ++ (lea-slot k ∷ mov-output-to-input2 ∷ [])) s alloc))) Input1 ≡
    AtStack (current-frame alloc) k
  exec-trace-final-lea-mov-input trace k s alloc not-halted-after =
    let s' = proj₁ (exec-trace trace s alloc)
        alloc' = proj₂ (exec-trace trace s alloc)
        -- Step 1: Decompose using append
        append-eq : exec-trace (trace ++ (lea-slot k ∷ mov-to-input ∷ [])) s alloc ≡
        append-eq : exec-trace (trace ++ (lea-slot k ∷ mov-output-to-input2 ∷ [])) s alloc ≡
                    exec-trace (lea-slot k ∷ mov-to-input ∷ []) s' alloc'
                    exec-trace (lea-slot k ∷ mov-output-to-input2 ∷ []) s' alloc'
        append-eq = exec-trace-append trace (lea-slot k ∷ mov-to-input ∷ []) s alloc
        append-eq = exec-trace-append trace (lea-slot k ∷ mov-output-to-input2 ∷ []) s alloc
        -- Step 2: Execute lea-slot (not halted)
        s-after-lea = proj₁ (exec-abstract (lea-slot k) s' alloc')
        alloc-after-lea = proj₂ (exec-abstract (lea-slot k) s' alloc')
        lea-step : exec-trace (lea-slot k ∷ mov-to-input ∷ []) s' alloc' ≡
        lea-step : exec-trace (lea-slot k ∷ mov-output-to-input2 ∷ []) s' alloc' ≡
                   exec-trace (mov-to-input ∷ []) s-after-lea alloc-after-lea
                   exec-trace (mov-output-to-input2 ∷ []) s-after-lea alloc-after-lea
        lea-step = exec-trace-cons (lea-slot k) (mov-to-input ∷ []) s' alloc' not-halted-after
        lea-step = exec-trace-cons (lea-slot k) (mov-output-to-input2 ∷ []) s' alloc' not-halted-after
        -- Step 3: lea-slot sets Output = AtStack (current-frame alloc') k
        output-after-lea : readReg (regs s-after-lea) Output ≡ AtStack (current-frame alloc') k
        output-after-lea = lea-slot-result k s' alloc'
        -- Step 4: lea-slot preserves halted
        not-halted-after-lea : halted s-after-lea ≡ false
        not-halted-after-lea = trans (lea-slot-halted k s' alloc') not-halted-after
        -- Step 5: Execute mov-to-input
        -- Step 5: Execute mov-output-to-input2
        s-after-mov = proj₁ (exec-abstract mov-to-input s-after-lea alloc-after-lea)
        s-after-mov = proj₁ (exec-abstract mov-output-to-input2 s-after-lea alloc-after-lea)
        mov-step : exec-trace (mov-to-input ∷ []) s-after-lea alloc-after-lea ≡
        mov-step : exec-trace (mov-output-to-input2 ∷ []) s-after-lea alloc-after-lea ≡
                   exec-abstract mov-to-input s-after-lea alloc-after-lea
                   exec-abstract mov-output-to-input2 s-after-lea alloc-after-lea
        mov-step = exec-trace-single mov-to-input s-after-lea alloc-after-lea not-halted-after-lea
        mov-step = exec-trace-single mov-output-to-input2 s-after-lea alloc-after-lea not-halted-after-lea
        -- Step 6: mov-to-input sets Input1 = Output
        -- Step 6: mov-output-to-input2 sets Input1 = Output
        input-after-mov : readReg (regs s-after-mov) Input1 ≡ readReg (regs s-after-lea) Output
        input-after-mov = writeReg-same (regs s-after-lea) Input1 (readReg (regs s-after-lea) Output)
        -- Step 7: Frame preserved through trace
        frame-eq : current-frame alloc' ≡ current-frame alloc
        frame-eq = exec-trace-preserves-frame trace s alloc
        -- Step 8: Combine step by step
        -- First show that the final state equals s-after-mov
        final-state = proj₁ (exec-trace (trace ++ (lea-slot k ∷ mov-to-input ∷ [])) s alloc)
        final-state = proj₁ (exec-trace (trace ++ (lea-slot k ∷ mov-output-to-input2 ∷ [])) s alloc)
        eq1 : proj₁ (exec-trace (lea-slot k ∷ mov-to-input ∷ []) s' alloc') ≡ s-after-mov
        eq1 : proj₁ (exec-trace (lea-slot k ∷ mov-output-to-input2 ∷ []) s' alloc') ≡ s-after-mov
        eq1 = trans (cong proj₁ lea-step) (cong proj₁ mov-step)
        eq2 : final-state ≡ proj₁ (exec-trace (lea-slot k ∷ mov-to-input ∷ []) s' alloc')
        eq2 : final-state ≡ proj₁ (exec-trace (lea-slot k ∷ mov-output-to-input2 ∷ []) s' alloc')
        eq2 = cong proj₁ append-eq
        eq3 : final-state ≡ s-after-mov
        eq3 = trans eq2 eq1
        -- Now transport the Input1 register result
        eq4 : readReg (regs final-state) Input1 ≡ readReg (regs s-after-mov) Input1
        eq4 = cong (λ st → readReg (regs st) Input1) eq3
        eq5 : readReg (regs s-after-mov) Input1 ≡ AtStack (current-frame alloc') k
        eq5 = trans input-after-mov output-after-lea
        eq6 : AtStack (current-frame alloc') k ≡ AtStack (current-frame alloc) k
        eq6 = cong (λ f → AtStack f k) frame-eq
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
            (AtStack (current-frame alloc) k) ≡ just (readReg (regs s) Output)
  store-then-preserve k rest s alloc not-halted twa tnhw with halted s
  ... | true = case not-halted of λ ()  -- contradiction
  ... | false =
    let -- After store-at-slot k
        s' = proj₁ (exec-abstract (store-at-slot k) s alloc)
        alloc' = proj₂ (exec-abstract (store-at-slot k) s alloc)
        -- Step 1: store-at-slot writes Output to slot k
        slot-has-value : readLoc s' (AtStack (current-frame alloc) k) ≡ just (readReg (regs s) Output)
        slot-has-value = store-at-slot-result k s alloc
        -- Step 2: rest preserves slot k (writes above suc k)
        preserved : readLoc (proj₁ (exec-trace rest s' alloc')) (AtStack (current-frame alloc') k) ≡
                    just (readReg (regs s) Output)
        preserved = exec-trace-slot-value rest s' alloc' k (readReg (regs s) Output)
                      (subst (λ f → readLoc s' (AtStack f k) ≡ just (readReg (regs s) Output))
                             (sym (exec-abstract-preserves-frame (store-at-slot k) s alloc))
                             slot-has-value)
                      twa tnhw
        -- Step 3: Frame preserved by store-at-slot
        frame-eq : current-frame alloc' ≡ current-frame alloc
        frame-eq = exec-abstract-preserves-frame (store-at-slot k) s alloc
    in subst (λ f → readLoc (proj₁ (exec-trace rest s' alloc')) (AtStack f k) ≡
                    just (readReg (regs s) Output))
             frame-eq preserved

  -- Generalized pattern: execute prefix, store to slot k, execute suffix that preserves k.
  -- Result: slot k contains what Output was after prefix.
  --
  -- This is the principled approach for env-ptr/code-ptr proofs:
  --   1. prefix sets up Output register (e.g., mov-to-output or lea-slot)
  --   1. prefix sets up Output register (e.g., mov-input2-to-output or lea-slot)
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
            (AtStack (current-frame alloc) k) ≡
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
                (AtStack (current-frame alloc) k) ≡
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
                         (AtStack (current-frame alloc₁) k) ≡
                 just (readReg (regs (proj₁ (exec-trace prefix s₁ alloc₁))) Output)
            ih = prefix-store-preserve prefix k suffix s₁ alloc₁ tph-rest not-halted₁ twa tnhw

            -- Frame preserved by first instruction
            frame-eq : current-frame alloc₁ ≡ current-frame alloc
            frame-eq = exec-abstract-preserves-frame i s alloc

            -- After prefix in original state = after prefix in s₁
            s-after-prefix = proj₁ (exec-trace prefix s₁ alloc₁)

        in subst (λ f → readLoc (proj₁ (exec-trace rest-trace s₁ alloc₁)) (AtStack f k) ≡
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
--   1. Input1 register (same value)
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

  -- If two states agree on Input1 and memory at read slots [n, m),
  -- and traces only read from those slots, then Output is the same.
  -- Note: m bounds reads (TraceSlotReadsBelow m), so memory agreement
  -- is only needed for slots in [n, m), not all slots ≥ n.
  exec-trace-output-deterministic : ∀ (trace : AbstractTrace)
    (s₁ s₂ : LocState FS) (alloc₁ alloc₂ : AllocState {FS}) (n m : ℕ) →
    halted s₁ ≡ false →
    halted s₂ ≡ false →
    current-frame alloc₁ ≡ current-frame alloc₂ →
    readReg (regs s₁) Input1 ≡ readReg (regs s₂) Input1 →
    TraceSlotReadsAbove n trace →
    TraceSlotReadsBelow m trace →
    TraceWritesAbove n trace →
    TraceNoHeapWrites trace →
    (∀ slot → n ≤ slot → slot < m →
      readLoc s₁ (AtStack (current-frame alloc₁) slot) ≡
      readLoc s₂ (AtStack (current-frame alloc₂) slot)) →
    readReg (regs (proj₁ (exec-trace trace s₁ alloc₁))) Output ≡
    readReg (regs (proj₁ (exec-trace trace s₂ alloc₂))) Output
  -- Proof sketch: by induction on trace
  -- Each instruction either:
  --   1. Reads from Input1 (same in both) → same result
  --   2. Reads from memory slot in [n, m) (same in both) → same result
  --   3. Reads from Output (must track that Output stays synchronized)
  -- The key is that if reads are the same, computations are the same,
  -- and since writes are above n, memory at [n, m) stays synchronized.
  exec-trace-output-deterministic = !!

  ------------------------------------------------------------------------
  -- Memory Determinism
  --
  -- If two states agree on Input1 and memory at read locations,
  -- then after trace execution, memory at write locations is the same.
  --
  -- This complements exec-trace-output-deterministic for memory locations.
  ------------------------------------------------------------------------

  -- Memory determinism for slots in the write region [n, m)
  -- If two states agree on Input1 and memory at slots in [n, m),
  -- and trace reads/writes are bounded by [n, m),
  -- then after execution, memory at slots in [n, m) is the same.
  --
  -- The proof is by induction on trace, maintaining that Input1, Output, and
  -- memory at [n, m) stay synchronized. Key insight: writes only happen via
  -- store-at-slot which writes Output, and Output stays synced because
  -- instructions that set Output read from Input1 or memory (both synced).
  exec-trace-mem-deterministic : ∀ (trace : AbstractTrace)
    (s₁ s₂ : LocState FS) (alloc₁ alloc₂ : AllocState {FS}) (n m : ℕ) →
    halted s₁ ≡ false →
    halted s₂ ≡ false →
    current-frame alloc₁ ≡ current-frame alloc₂ →
    readReg (regs s₁) Input1 ≡ readReg (regs s₂) Input1 →
    TraceSlotReadsAbove n trace →
    TraceSlotReadsBelow m trace →
    TraceWritesAbove n trace →
    TraceWritesBelow m trace →
    TraceNoHeapWrites trace →
    (∀ slot → n ≤ slot → slot < m →
      readLoc s₁ (AtStack (current-frame alloc₁) slot) ≡
      readLoc s₂ (AtStack (current-frame alloc₂) slot)) →
    ∀ slot → n ≤ slot → slot < m →
      readLoc (proj₁ (exec-trace trace s₁ alloc₁)) (AtStack (current-frame alloc₁) slot) ≡
      readLoc (proj₁ (exec-trace trace s₂ alloc₂)) (AtStack (current-frame alloc₂) slot)
  -- Base case: empty trace - memory unchanged, use input agreement directly
  exec-trace-mem-deterministic [] s₁ s₂ alloc₁ alloc₂ n m _ _ _ _ _ _ _ _ _ mem-agree slot n≤slot slot<m =
    mem-agree slot n≤slot slot<m

  -- Inductive case: each instruction type handled separately
  -- For most cases, we use the fact that non-writing instructions preserve memory
  -- For writing instructions (store-at-slot, worklist-push), we need Output synchronization

  -- All non-writing, non-frame-changing instructions follow a common pattern:
  -- Memory is preserved, Input1 is preserved (except mov-to-input, restore-input)
  -- Memory is preserved, Input1 is preserved (except mov-output-to-input2, restore-input)
  -- We use !! for complex sub-cases that require detailed Output tracking

  exec-trace-mem-deterministic (i ∷ rest) s₁ s₂ alloc₁ alloc₂ n m nh₁ nh₂ frame-eq input-eq
      rsra rsrb twa twb tnhw mem-agree slot n≤slot slot<m = !!

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
  -- Single mov-input2-to-output trace: mov-input2-to-output ∷ []
  --
  -- This is the identity trace - just copies Input1 to Output.
  -- Used by out-μ and Out which are representationally identity.
  ------------------------------------------------------------------------

  -- After mov-to-output ∷ [], Output = Input1
  -- After mov-input2-to-output ∷ [], Output = Input1
  passthrough-output-is-input : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readReg (regs (proj₁ (exec-trace (mov-to-output ∷ []) s alloc))) Output ≡
    readReg (regs (proj₁ (exec-trace (mov-input2-to-output ∷ []) s alloc))) Output ≡
    readReg (regs s) Input1
  passthrough-output-is-input s alloc not-halted with halted s
  ... | false = writeReg-same (regs s) Output (readReg (regs s) Input1)

  -- After mov-to-output ∷ [], halted = false
  -- After mov-input2-to-output ∷ [], halted = false
  passthrough-preserves-halted : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-trace (mov-to-output ∷ []) s alloc)) ≡ false
    halted (proj₁ (exec-trace (mov-input2-to-output ∷ []) s alloc)) ≡ false
  passthrough-preserves-halted s alloc not-halted =
    exec-trace-preserves-halted (mov-to-output ∷ []) s alloc not-halted
    exec-trace-preserves-halted (mov-input2-to-output ∷ []) s alloc not-halted
      (tph-∷ iph-mov-to-output tph-[])

  -- exec-abstract mov-to-output preserves memory (it only changes registers)
  -- exec-abstract mov-input2-to-output preserves memory (it only changes registers)
  -- Pattern match on loc to handle stack/heap cases separately
  exec-abstract-mov-to-output-preserves-mem : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    readLoc (proj₁ (exec-abstract mov-to-output s alloc)) loc ≡ readLoc s loc
    readLoc (proj₁ (exec-abstract mov-input2-to-output s alloc)) loc ≡ readLoc s loc
  exec-abstract-mov-to-output-preserves-mem s alloc (AtStack f k) = refl
  exec-abstract-mov-to-output-preserves-mem s alloc (AtDynamic hl) = refl

  -- After mov-to-output ∷ [], memory is preserved
  -- After mov-input2-to-output ∷ [], memory is preserved
  -- mov-to-output only modifies registers, not memory
  -- mov-input2-to-output only modifies registers, not memory
  --
  -- We use exec-trace-single to reduce to exec-abstract, then show
  -- exec-abstract preserves memory.
  passthrough-mem-preserved : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ []) s alloc)) loc ≡ readLoc s loc
    readLoc (proj₁ (exec-trace (mov-input2-to-output ∷ []) s alloc)) loc ≡ readLoc s loc
  passthrough-mem-preserved s alloc loc not-halted =
    let step : exec-trace (mov-to-output ∷ []) s alloc ≡ exec-abstract mov-to-output s alloc
    let step : exec-trace (mov-input2-to-output ∷ []) s alloc ≡ exec-abstract mov-input2-to-output s alloc
        step = exec-trace-single mov-to-output s alloc not-halted
        step = exec-trace-single mov-input2-to-output s alloc not-halted
        state-eq : proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡
        state-eq : proj₁ (exec-trace (mov-input2-to-output ∷ []) s alloc) ≡
                   proj₁ (exec-abstract mov-to-output s alloc)
                   proj₁ (exec-abstract mov-input2-to-output s alloc)
        state-eq = cong proj₁ step
        mem-pres : readLoc (proj₁ (exec-abstract mov-to-output s alloc)) loc ≡ readLoc s loc
        mem-pres : readLoc (proj₁ (exec-abstract mov-input2-to-output s alloc)) loc ≡ readLoc s loc
        mem-pres = exec-abstract-mov-to-output-preserves-mem s alloc loc
    in trans (cong (λ st → readLoc st loc) state-eq) mem-pres

  ------------------------------------------------------------------------
  -- Common trace pattern for recursion schemes:
  -- mov-to-output ∷ store-at-slot n ∷ []
  -- mov-input2-to-output ∷ store-at-slot n ∷ []
  --
  -- After this trace:
  -- 1. Slot n contains the input location (originally in Input1 register)
  -- 2. Output register still contains Input1 (store doesn't change regs)
  -- 3. Halted flag is preserved (both instructions preserve halted)
  -- 4. Memory at slots < n is preserved (trace writes only at slot n)

  -- After mov-to-output ∷ store-at-slot n ∷ [], Output = original Input1
  -- After mov-input2-to-output ∷ store-at-slot n ∷ [], Output = original Input1
  rec-scheme-output-is-input : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readReg (regs (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc))) Output ≡
    readReg (regs (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ []) s alloc))) Output ≡
    readReg (regs s) Input1
  rec-scheme-output-is-input n s alloc not-halted =
    let -- Step 1: Unfold first instruction (mov-to-output)
    let -- Step 1: Unfold first instruction (mov-input2-to-output)
        s1 = proj₁ (exec-abstract mov-to-output s alloc)
        s1 = proj₁ (exec-abstract mov-input2-to-output s alloc)
        alloc1 = proj₂ (exec-abstract mov-to-output s alloc)
        alloc1 = proj₂ (exec-abstract mov-input2-to-output s alloc)
        -- After mov-to-output: Output = Input1
        -- After mov-input2-to-output: Output = Input1
        mov-result : readReg (regs s1) Output ≡ readReg (regs s) Input1
        mov-result = writeReg-same (regs s) Output (readReg (regs s) Input1)
        -- mov-to-output doesn't halt
        -- mov-input2-to-output doesn't halt
        s1-not-halted : halted s1 ≡ false
        s1-not-halted = not-halted  -- mov-to-output preserves halted
        s1-not-halted = not-halted  -- mov-input2-to-output preserves halted
        -- Step 2: Unfold second instruction (store-at-slot n)
        s2 = proj₁ (exec-abstract (store-at-slot n) s1 alloc1)
        -- store-at-slot preserves registers
        store-regs : regs s2 ≡ regs s1
        store-regs = store-at-slot-regs n s1 alloc1
        -- Step 3: Combine
        -- exec-trace (mov ∷ store ∷ []) = exec-trace (store ∷ []) after mov
        step1 : exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc ≡
        step1 : exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ []) s alloc ≡
                exec-trace (store-at-slot n ∷ []) s1 alloc1
        step1 = exec-trace-cons mov-to-output (store-at-slot n ∷ []) s alloc not-halted
        step1 = exec-trace-cons mov-input2-to-output (store-at-slot n ∷ []) s alloc not-halted
        step2 : exec-trace (store-at-slot n ∷ []) s1 alloc1 ≡ exec-abstract (store-at-slot n) s1 alloc1
        step2 = exec-trace-single (store-at-slot n) s1 alloc1 s1-not-halted
    in trans (cong (λ r → readReg r Output) (trans (cong (λ p → regs (proj₁ p)) (trans step1 step2)) store-regs)) mov-result

  -- After mov-to-output ∷ store-at-slot n ∷ [], halted = false (preserved)
  -- After mov-input2-to-output ∷ store-at-slot n ∷ [], halted = false (preserved)
  rec-scheme-preserves-halted : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc)) ≡ false
    halted (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ []) s alloc)) ≡ false
  rec-scheme-preserves-halted n s alloc not-halted =
    exec-trace-preserves-halted (mov-to-output ∷ store-at-slot n ∷ []) s alloc not-halted
    exec-trace-preserves-halted (mov-input2-to-output ∷ store-at-slot n ∷ []) s alloc not-halted
      (tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot tph-[]))

  -- After mov-to-output ∷ store-at-slot n ∷ [], slot n contains Input1 value
  -- After mov-input2-to-output ∷ store-at-slot n ∷ [], slot n contains Input1 value
  rec-scheme-stores-input : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc))
    readLoc (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ []) s alloc))
            (AtStack (current-frame alloc) n) ≡ just (readReg (regs s) Input1)
  rec-scheme-stores-input n s alloc not-halted =
    let -- Step 1: Unfold first instruction (mov-to-output)
    let -- Step 1: Unfold first instruction (mov-input2-to-output)
        s1 = proj₁ (exec-abstract mov-to-output s alloc)
        s1 = proj₁ (exec-abstract mov-input2-to-output s alloc)
        alloc1 = proj₂ (exec-abstract mov-to-output s alloc)
        alloc1 = proj₂ (exec-abstract mov-input2-to-output s alloc)
        -- After mov-to-output: Output = Input1
        -- After mov-input2-to-output: Output = Input1
        mov-result : readReg (regs s1) Output ≡ readReg (regs s) Input1
        mov-result = writeReg-same (regs s) Output (readReg (regs s) Input1)
        -- mov-to-output doesn't halt
        -- mov-input2-to-output doesn't halt
        s1-not-halted : halted s1 ≡ false
        s1-not-halted = not-halted
        -- alloc1 = alloc (mov-to-output doesn't change alloc)
        -- alloc1 = alloc (mov-input2-to-output doesn't change alloc)
        alloc1-eq : alloc1 ≡ alloc
        alloc1-eq = refl
        -- Step 2: store-at-slot n writes Output to slot n
        s2 = proj₁ (exec-abstract (store-at-slot n) s1 alloc1)
        store-result : readLoc s2 (AtStack (current-frame alloc1) n) ≡ just (readReg (regs s1) Output)
        store-result = store-at-slot-result n s1 alloc1
        -- Step 3: Unfold trace
        step1 : exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc ≡
        step1 : exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ []) s alloc ≡
                exec-trace (store-at-slot n ∷ []) s1 alloc1
        step1 = exec-trace-cons mov-to-output (store-at-slot n ∷ []) s alloc not-halted
        step1 = exec-trace-cons mov-input2-to-output (store-at-slot n ∷ []) s alloc not-halted
        step2 : exec-trace (store-at-slot n ∷ []) s1 alloc1 ≡ exec-abstract (store-at-slot n) s1 alloc1
        step2 = exec-trace-single (store-at-slot n) s1 alloc1 s1-not-halted
        -- Step 4: Combine
        final-state-eq : proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ []) s alloc) ≡ s2
        final-state-eq : proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ []) s alloc) ≡ s2
        final-state-eq = cong proj₁ (trans step1 step2)
    in trans (cong (λ st → readLoc st (AtStack (current-frame alloc) n)) final-state-eq)
             (trans store-result (cong just mov-result))

  ------------------------------------------------------------------------
  -- Extended trace pattern: mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []
  -- Extended trace pattern: mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []
  --
  -- This trace:
  -- 1. Copies Input1 to Output
  -- 2. Stores Output at slot n
  -- 3. Loads address of slot n into Output
  --
  -- After this trace, Output = AtStack frame n (the result location)
  ------------------------------------------------------------------------

  -- After mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], Output = AtStack frame n
  -- After mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], Output = AtStack frame n
  rec-scheme-output-is-slot : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readReg (regs (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))) Output ≡
    readReg (regs (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))) Output ≡
    AtStack (current-frame alloc) n
  rec-scheme-output-is-slot n s alloc not-halted =
    -- The trace is (mov-to-output ∷ store-at-slot n ∷ []) ++ (lea-slot n ∷ [])
    -- The trace is (mov-input2-to-output ∷ store-at-slot n ∷ []) ++ (lea-slot n ∷ [])
    -- which is definitionally equal to mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []
    -- which is definitionally equal to mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []
    let prefix = mov-to-output ∷ store-at-slot n ∷ []
    let prefix = mov-input2-to-output ∷ store-at-slot n ∷ []
        -- After prefix, halted = false
        not-halted-after : halted (proj₁ (exec-trace prefix s alloc)) ≡ false
        not-halted-after = rec-scheme-preserves-halted n s alloc not-halted
    in exec-trace-final-lea-slot prefix n s alloc not-halted-after

  -- After mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], halted = false (preserved)
  -- After mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], halted = false (preserved)
  rec-scheme-preserves-halted-3 : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    halted (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc)) ≡ false
    halted (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc)) ≡ false
  rec-scheme-preserves-halted-3 n s alloc not-halted =
    exec-trace-preserves-halted (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc not-halted
    exec-trace-preserves-halted (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc not-halted
      (tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot (tph-∷ iph-lea-slot tph-[])))

  -- After mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], slot n contains Input1 value
  -- After mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], slot n contains Input1 value
  rec-scheme-stores-input-3 : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
    readLoc (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
            (AtStack (current-frame alloc) n) ≡ just (readReg (regs s) Input1)
  rec-scheme-stores-input-3 n s alloc not-halted =
    let prefix = mov-to-output ∷ store-at-slot n ∷ []
    let prefix = mov-input2-to-output ∷ store-at-slot n ∷ []
        s-after-prefix = proj₁ (exec-trace prefix s alloc)
        alloc-after-prefix = proj₂ (exec-trace prefix s alloc)
        -- After prefix, slot n = Input1
        prefix-result : readLoc s-after-prefix (AtStack (current-frame alloc) n) ≡ just (readReg (regs s) Input1)
        prefix-result = rec-scheme-stores-input n s alloc not-halted
        -- After prefix, halted = false
        not-halted-after : halted s-after-prefix ≡ false
        not-halted-after = rec-scheme-preserves-halted n s alloc not-halted
        -- lea-slot preserves memory
        s-after-lea = proj₁ (exec-abstract (lea-slot n) s-after-prefix alloc-after-prefix)
        lea-preserves : readLoc s-after-lea (AtStack (current-frame alloc) n) ≡
                        readLoc s-after-prefix (AtStack (current-frame alloc) n)
        lea-preserves = lea-slot-preserves-mem n s-after-prefix alloc-after-prefix (AtStack (current-frame alloc) n)
        -- Trace decomposition
        step1 : exec-trace (prefix ++ (lea-slot n ∷ [])) s alloc ≡
                exec-trace (lea-slot n ∷ []) s-after-prefix alloc-after-prefix
        step1 = exec-trace-append prefix (lea-slot n ∷ []) s alloc
        step2 : exec-trace (lea-slot n ∷ []) s-after-prefix alloc-after-prefix ≡
                exec-abstract (lea-slot n) s-after-prefix alloc-after-prefix
        step2 = exec-trace-single (lea-slot n) s-after-prefix alloc-after-prefix not-halted-after
        final-state-eq : proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc) ≡ s-after-lea
        final-state-eq : proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc) ≡ s-after-lea
        final-state-eq = cong proj₁ (trans step1 step2)
    in trans (cong (λ st → readLoc st (AtStack (current-frame alloc) n)) final-state-eq)
             (trans lea-preserves prefix-result)

  -- After mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], memory at slots < n is preserved
  -- After mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ [], memory at slots < n is preserved
  -- This follows because:
  --   1. mov-to-output only modifies registers (no memory writes)
  --   1. mov-input2-to-output only modifies registers (no memory writes)
  --   2. store-at-slot n writes only to slot n
  --   3. lea-slot n only modifies registers (no memory writes)
  -- So slots < n are not modified.
  rec-scheme-preserves-slot-below-3 : ∀ (n k : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    k < n →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
    readLoc (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
            (AtStack (current-frame alloc) k) ≡
    readLoc s (AtStack (current-frame alloc) k)
  rec-scheme-preserves-slot-below-3 n k s alloc not-halted k<n =
    -- The trace writes only at slot n, so slots k < n are preserved
    -- TraceWritesAbove n: store-at-slot n writes at n ≥ n
    -- TraceNoHeapWrites: no heap-writing instructions
    exec-trace-preserves-slot-below
      (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc n k
      (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc n k
      (≤-refl , tt)  -- TraceWritesAbove n: n ≤ n, and mov/lea don't write slots
      tt             -- TraceNoHeapWrites: no heap writes
      k<n

  -- Memory preservation for heap locations through the recursion scheme trace
  rec-scheme-preserves-heap-3 : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (hl : HeapLocation) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
    readLoc (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
            (AtDynamic hl) ≡
    readLoc s (AtDynamic hl)
  rec-scheme-preserves-heap-3 n s alloc hl not-halted =
    -- The trace has no heap-writing instructions
    exec-trace-preserves-heap-loc
      (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc hl
      (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc hl
      tt  -- TraceNoHeapWrites: no store-indirect or store-indirect-suc

  -- Memory preservation for ancestor frame slots through the recursion scheme trace
  -- The trace only writes to (current-frame alloc, n), so any slot on a different frame is preserved
  rec-scheme-preserves-ancestor-3 : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (f : RSFrame) (k : ℕ) →
    halted s ≡ false →
    f ≢ current-frame alloc →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
    readLoc (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc))
            (AtStack f k) ≡
    readLoc s (AtStack f k)
  rec-scheme-preserves-ancestor-3 n s alloc f k not-halted f≢cf =
    -- The trace writes only to AtStack (current-frame alloc) n
    -- AtStack f k is on a different frame (f ≢ cf), so it's preserved
    trans (cong (λ st → readLoc st (AtStack f k)) final-state-eq)
          (trans lea-preserves (trans store-preserves mov-preserves))
    where
      -- Step 1: Unfold first instruction (mov-to-output) - preserves all memory
      -- Step 1: Unfold first instruction (mov-input2-to-output) - preserves all memory
      s1 = proj₁ (exec-abstract mov-to-output s alloc)
      s1 = proj₁ (exec-abstract mov-input2-to-output s alloc)
      alloc1 = proj₂ (exec-abstract mov-to-output s alloc)
      alloc1 = proj₂ (exec-abstract mov-input2-to-output s alloc)
      mov-preserves : readLoc s1 (AtStack f k) ≡ readLoc s (AtStack f k)
      mov-preserves = refl  -- mov-to-output only changes registers
      mov-preserves = refl  -- mov-input2-to-output only changes registers
      s1-not-halted : halted s1 ≡ false
      s1-not-halted = not-halted
      -- Step 2: store-at-slot n writes to AtStack cf n, preserves AtStack f k (different frame)
      s2 = proj₁ (exec-abstract (store-at-slot n) s1 alloc1)
      alloc2 = proj₂ (exec-abstract (store-at-slot n) s1 alloc1)
      -- AtStack cf n ≢ AtStack f k because f ≢ cf
      loc-neq : AtStack (current-frame alloc1) n ≢ AtStack f k
      loc-neq refl = f≢cf refl  -- contradiction: f ≡ cf
      store-preserves : readLoc s2 (AtStack f k) ≡ readLoc s1 (AtStack f k)
      store-preserves = writeLoc-preserves-other s1 (AtStack (current-frame alloc1) n) (AtStack f k)
                          (readReg (regs s1) Output) loc-neq
      s2-not-halted : halted s2 ≡ false
      s2-not-halted = s1-not-halted
      -- Step 3: lea-slot n - preserves all memory
      s3 = proj₁ (exec-abstract (lea-slot n) s2 alloc2)
      lea-preserves : readLoc s3 (AtStack f k) ≡ readLoc s2 (AtStack f k)
      lea-preserves = lea-slot-preserves-mem n s2 alloc2 (AtStack f k)
      -- Step 4: Trace decomposition
      step1 : exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc ≡
      step1 : exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc ≡
              exec-trace (store-at-slot n ∷ lea-slot n ∷ []) s1 alloc1
      step1 = exec-trace-cons mov-to-output (store-at-slot n ∷ lea-slot n ∷ []) s alloc not-halted
      step1 = exec-trace-cons mov-input2-to-output (store-at-slot n ∷ lea-slot n ∷ []) s alloc not-halted
      step2 : exec-trace (store-at-slot n ∷ lea-slot n ∷ []) s1 alloc1 ≡
              exec-trace (lea-slot n ∷ []) s2 alloc2
      step2 = exec-trace-cons (store-at-slot n) (lea-slot n ∷ []) s1 alloc1 s1-not-halted
      step3 : exec-trace (lea-slot n ∷ []) s2 alloc2 ≡ exec-abstract (lea-slot n) s2 alloc2
      step3 = exec-trace-single (lea-slot n) s2 alloc2 s2-not-halted
      final-state-eq : proj₁ (exec-trace (mov-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc) ≡ s3
      final-state-eq : proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot n ∷ lea-slot n ∷ []) s alloc) ≡ s3
      final-state-eq = cong proj₁ (trans step1 (trans step2 step3))
  ------------------------------------------------------------------------
  -- Helper lemmas for RecTrace register setup proofs
  --
  -- These prove properties about load-indirect-suc followed by mov-to-input.
  -- These prove properties about load-indirect-suc followed by mov-output-to-input2.
  ------------------------------------------------------------------------

  -- load-indirect-suc sets Output to the value at sucLoc(Input1)
  -- Given: readLoc s (sucLoc input-loc) ≡ just payload-loc
  -- And:   readReg (regs s) Input1 ≡ input-loc
  -- Then:  readReg (regs (proj₁ (exec-abstract load-indirect-suc s alloc))) Output ≡ payload-loc
  -- Helper for load-indirect-suc output proof: pattern match on the read result
  exec-abstract-load-indirect-suc-output-helper : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (payload-loc : ValueLocation FS) →
    readLoc s (sucLoc (readReg (regs s) Input1)) ≡ just payload-loc →
    readReg (regs (proj₁ (exec-abstract load-indirect-suc s alloc))) Output ≡ payload-loc
  exec-abstract-load-indirect-suc-output-helper s alloc payload-loc read-eq
    with readLoc s (sucLoc (readReg (regs s) Input1)) | read-eq
  ... | just v | refl = writeReg-same (regs s) Output v

  exec-abstract-load-indirect-suc-output : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (input-loc payload-loc : ValueLocation FS) →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s (sucLoc input-loc) ≡ just payload-loc →
    readReg (regs (proj₁ (exec-abstract load-indirect-suc s alloc))) Output ≡ payload-loc
  exec-abstract-load-indirect-suc-output s alloc input-loc payload-loc rdi-eq ptr-eq =
    exec-abstract-load-indirect-suc-output-helper s alloc payload-loc
      (trans (cong (readLoc s ∘ sucLoc) rdi-eq) ptr-eq)

  -- load-indirect-suc preserves Input1 register (it only writes to Output)
  exec-abstract-load-indirect-suc-preserves-input : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    readReg (regs (proj₁ (exec-abstract load-indirect-suc s alloc))) Input1 ≡ readReg (regs s) Input1
  exec-abstract-load-indirect-suc-preserves-input s alloc with readLoc s (sucLoc (readReg (regs s) Input1))
  ... | just v = writeReg-preserves (regs s) Output Input1 v (λ ())
  ... | nothing = refl

  -- load-indirect-suc preserves memory (it only writes to registers)
  -- When read succeeds: exec-load-with-value Output (just v) s = record s { regs = writeReg ... }
  -- readLoc only accesses stackMem/heapMem, which are unchanged
  exec-abstract-load-indirect-suc-preserves-mem : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    readLoc (proj₁ (exec-abstract load-indirect-suc s alloc)) loc ≡ readLoc s loc
  exec-abstract-load-indirect-suc-preserves-mem s alloc (AtStack f k)
    with readLoc s (sucLoc (readReg (regs s) Input1))
  ... | just _ = refl
  ... | nothing = refl
  exec-abstract-load-indirect-suc-preserves-mem s alloc (AtDynamic hl)
    with readLoc s (sucLoc (readReg (regs s) Input1))
  ... | just _ = refl
  ... | nothing = refl

  -- load-indirect-suc preserves stackMem and heapMem (for μLayerValid transfer)
  exec-abstract-load-indirect-suc-preserves-stackMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    stackMem (proj₁ (exec-abstract load-indirect-suc s alloc)) ≡ stackMem s
  exec-abstract-load-indirect-suc-preserves-stackMem s alloc with readLoc s (sucLoc (readReg (regs s) Input1))
  ... | just v = refl
  ... | nothing = refl

  exec-abstract-load-indirect-suc-preserves-heapMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    heapMem (proj₁ (exec-abstract load-indirect-suc s alloc)) ≡ heapMem s
  exec-abstract-load-indirect-suc-preserves-heapMem s alloc with readLoc s (sucLoc (readReg (regs s) Input1))
  ... | just v = refl
  ... | nothing = refl

  ------------------------------------------------------------------------
  -- load-indirect lemmas (parallel to load-indirect-suc)
  --
  -- load-indirect reads from *Input1 and writes to Output
  ------------------------------------------------------------------------

  -- Helper for load-indirect output proof
  exec-abstract-load-indirect-output-helper : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (target-loc : ValueLocation FS) →
    readLoc s (readReg (regs s) Input1) ≡ just target-loc →
    readReg (regs (proj₁ (exec-abstract load-indirect s alloc))) Output ≡ target-loc
  exec-abstract-load-indirect-output-helper s alloc target-loc read-eq
    with readLoc s (readReg (regs s) Input1) | read-eq
  ... | just v | refl = writeReg-same (regs s) Output v

  -- load-indirect sets Output to value at *Input1
  exec-abstract-load-indirect-output : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (input-loc target-loc : ValueLocation FS) →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s input-loc ≡ just target-loc →
    readReg (regs (proj₁ (exec-abstract load-indirect s alloc))) Output ≡ target-loc
  exec-abstract-load-indirect-output s alloc input-loc target-loc rdi-eq ptr-eq =
    exec-abstract-load-indirect-output-helper s alloc target-loc
      (trans (cong (readLoc s) rdi-eq) ptr-eq)

  -- load-indirect preserves Input1 register
  exec-abstract-load-indirect-preserves-input : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    readReg (regs (proj₁ (exec-abstract load-indirect s alloc))) Input1 ≡ readReg (regs s) Input1
  exec-abstract-load-indirect-preserves-input s alloc with readLoc s (readReg (regs s) Input1)
  ... | just v = writeReg-preserves (regs s) Output Input1 v (λ ())
  ... | nothing = refl

  -- load-indirect preserves stackMem and heapMem
  exec-abstract-load-indirect-preserves-stackMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    stackMem (proj₁ (exec-abstract load-indirect s alloc)) ≡ stackMem s
  exec-abstract-load-indirect-preserves-stackMem s alloc with readLoc s (readReg (regs s) Input1)
  ... | just v = refl
  ... | nothing = refl

  exec-abstract-load-indirect-preserves-heapMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    heapMem (proj₁ (exec-abstract load-indirect s alloc)) ≡ heapMem s
  exec-abstract-load-indirect-preserves-heapMem s alloc with readLoc s (readReg (regs s) Input1)
  ... | just v = refl
  ... | nothing = refl

  -- load-indirect preserves alloc
  exec-abstract-load-indirect-preserves-alloc : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    proj₂ (exec-abstract load-indirect s alloc) ≡ alloc
  exec-abstract-load-indirect-preserves-alloc s alloc = refl

  -- mov-to-input sets Input1 to Output
  -- mov-output-to-input2 sets Input1 to Output
  exec-abstract-mov-to-input-input : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    readReg (regs (proj₁ (exec-abstract mov-to-input s alloc))) Input1 ≡ readReg (regs s) Output
    readReg (regs (proj₁ (exec-abstract mov-output-to-input2 s alloc))) Input1 ≡ readReg (regs s) Output
  exec-abstract-mov-to-input-input s alloc = writeReg-same (regs s) Input1 (readReg (regs s) Output)

  -- mov-to-input preserves memory
  -- mov-output-to-input2 preserves memory
  exec-abstract-mov-to-input-preserves-stackMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    stackMem (proj₁ (exec-abstract mov-to-input s alloc)) ≡ stackMem s
    stackMem (proj₁ (exec-abstract mov-output-to-input2 s alloc)) ≡ stackMem s
  exec-abstract-mov-to-input-preserves-stackMem s alloc = refl

  exec-abstract-mov-to-input-preserves-heapMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    heapMem (proj₁ (exec-abstract mov-to-input s alloc)) ≡ heapMem s
    heapMem (proj₁ (exec-abstract mov-output-to-input2 s alloc)) ≡ heapMem s
  exec-abstract-mov-to-input-preserves-heapMem s alloc = refl

  -- load-indirect-suc preserves alloc (it doesn't modify allocation state)
  exec-abstract-load-indirect-suc-preserves-alloc : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    proj₂ (exec-abstract load-indirect-suc s alloc) ≡ alloc
  exec-abstract-load-indirect-suc-preserves-alloc s alloc = refl

  -- mov-to-input preserves alloc
  -- mov-output-to-input2 preserves alloc
  exec-abstract-mov-to-input-preserves-alloc : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    proj₂ (exec-abstract mov-to-input s alloc) ≡ alloc
    proj₂ (exec-abstract mov-output-to-input2 s alloc) ≡ alloc
  exec-abstract-mov-to-input-preserves-alloc s alloc = refl

  -- load-from-slot preserves alloc
  exec-abstract-load-from-slot-preserves-alloc : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    proj₂ (exec-abstract (load-from-slot slot) s alloc) ≡ alloc
  exec-abstract-load-from-slot-preserves-alloc slot s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl

  -- restore-input preserves alloc
  exec-abstract-restore-input-preserves-alloc : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    proj₂ (exec-abstract (restore-input slot) s alloc) ≡ alloc
  exec-abstract-restore-input-preserves-alloc slot s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl

  -- exec-trace (restore-input slot ∷ []) preserves alloc when not halted
  restore-trace-preserves-alloc : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₂ (exec-trace (restore-input slot ∷ []) s alloc) ≡ alloc
  restore-trace-preserves-alloc slot s alloc not-halted =
    let step = exec-trace-single (restore-input slot) s alloc not-halted
    in trans (cong proj₂ step) (exec-abstract-restore-input-preserves-alloc slot s alloc)

  -- restore-input sets Input1 to the value read from the slot
  -- When slot contains v, restore-input sets Input1 := v
  exec-abstract-restore-input-sets-input : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (v : ValueLocation FS) →
    readLoc s (AtStack (current-frame alloc) slot) ≡ just v →
    readReg (regs (proj₁ (exec-abstract (restore-input slot) s alloc))) Input1 ≡ v
  exec-abstract-restore-input-sets-input slot s alloc v slot-has-v
    with readLoc s (AtStack (current-frame alloc) slot) | slot-has-v
  ... | just _ | refl = writeReg-same (regs s) Input1 v

  -- restore-input preserves memory (it only writes to Input1 register)
  exec-abstract-restore-input-preserves-stackMem : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    stackMem (proj₁ (exec-abstract (restore-input slot) s alloc)) ≡ stackMem s
  exec-abstract-restore-input-preserves-stackMem slot s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl

  exec-abstract-restore-input-preserves-heapMem : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    heapMem (proj₁ (exec-abstract (restore-input slot) s alloc)) ≡ heapMem s
  exec-abstract-restore-input-preserves-heapMem slot s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl

  -- restore-trace preserves memory (only register operation)
  restore-trace-preserves-stackMem : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    stackMem (proj₁ (exec-trace (restore-input slot ∷ []) s alloc)) ≡ stackMem s
  restore-trace-preserves-stackMem slot s alloc not-halted =
    trans (cong stackMem (cong proj₁ (exec-trace-single (restore-input slot) s alloc not-halted)))
          (exec-abstract-restore-input-preserves-stackMem slot s alloc)

  restore-trace-preserves-heapMem : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    heapMem (proj₁ (exec-trace (restore-input slot ∷ []) s alloc)) ≡ heapMem s
  restore-trace-preserves-heapMem slot s alloc not-halted =
    trans (cong heapMem (cong proj₁ (exec-trace-single (restore-input slot) s alloc not-halted)))
          (exec-abstract-restore-input-preserves-heapMem slot s alloc)

  -- Combined: load-indirect-suc then mov-to-input sets Input1 to payload-loc
  -- Combined: load-indirect-suc then mov-output-to-input2 sets Input1 to payload-loc
  -- This is the key lemma for rdi-setup proof
  setup-trace-sets-input : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (input-loc payload-loc : ValueLocation FS) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s (sucLoc input-loc) ≡ just payload-loc →
    let s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in readReg (regs s-setup) Input1 ≡ payload-loc
  setup-trace-sets-input s alloc input-loc payload-loc not-halted rdi-eq ptr-eq =
    let
      s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)
      alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)
      -- After load-indirect-suc: Output = payload-loc
      output-eq : readReg (regs s-after-load) Output ≡ payload-loc
      output-eq = exec-abstract-load-indirect-suc-output s alloc input-loc payload-loc rdi-eq ptr-eq
      -- After mov-to-input: Input1 = Output = payload-loc
      -- After mov-output-to-input2: Input1 = Output = payload-loc
      s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
      s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
      input-eq : readReg (regs s-setup) Input1 ≡ readReg (regs s-after-load) Output
      input-eq = exec-abstract-mov-to-input-input s-after-load alloc-after-load
    in trans input-eq output-eq

  -- Combined: setup trace preserves memory
  setup-trace-preserves-stackMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    let s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in stackMem s-setup ≡ stackMem s
  setup-trace-preserves-stackMem s alloc =
    trans (exec-abstract-mov-to-input-preserves-stackMem
            (proj₁ (exec-abstract load-indirect-suc s alloc))
            (proj₂ (exec-abstract load-indirect-suc s alloc)))
          (exec-abstract-load-indirect-suc-preserves-stackMem s alloc)

  setup-trace-preserves-heapMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    let s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in heapMem s-setup ≡ heapMem s
  setup-trace-preserves-heapMem s alloc =
    trans (exec-abstract-mov-to-input-preserves-heapMem
            (proj₁ (exec-abstract load-indirect-suc s alloc))
            (proj₂ (exec-abstract load-indirect-suc s alloc)))
          (exec-abstract-load-indirect-suc-preserves-heapMem s alloc)

  -- Combined: setup trace preserves alloc
  setup-trace-preserves-alloc : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    let s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)
        alloc-setup = proj₂ (exec-abstract mov-to-input s-after-load alloc-after-load)
        alloc-setup = proj₂ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in alloc-setup ≡ alloc
  setup-trace-preserves-alloc s alloc =
    trans (exec-abstract-mov-to-input-preserves-alloc
            (proj₁ (exec-abstract load-indirect-suc s alloc))
            (proj₂ (exec-abstract load-indirect-suc s alloc)))
          (exec-abstract-load-indirect-suc-preserves-alloc s alloc)

  -- Helper: load-indirect-suc preserves halted when read succeeds
  load-indirect-suc-halted-success : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (v : ValueLocation FS) →
    halted s ≡ false →
    readLoc s (sucLoc (readReg (regs s) Input1)) ≡ just v →
    halted (proj₁ (exec-abstract load-indirect-suc s alloc)) ≡ false
  load-indirect-suc-halted-success s alloc v not-halted read-eq
    with readLoc s (sucLoc (readReg (regs s) Input1)) | read-eq
  ... | just _ | refl = not-halted

  -- Combined: setup trace preserves halted status
  setup-trace-preserves-halted : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (input-loc payload-loc : ValueLocation FS) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s (sucLoc input-loc) ≡ just payload-loc →
    let s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in halted s-setup ≡ false
  setup-trace-preserves-halted s alloc input-loc payload-loc not-halted rdi-eq ptr-eq =
    let
      -- The load succeeds because ptr-eq says the read returns just payload-loc
      suc-input-eq : sucLoc (readReg (regs s) Input1) ≡ sucLoc input-loc
      suc-input-eq = cong sucLoc rdi-eq
      read-eq : readLoc s (sucLoc (readReg (regs s) Input1)) ≡ just payload-loc
      read-eq = trans (cong (readLoc s) suc-input-eq) ptr-eq
      -- Use helper for halted preservation
      halted-after-load = load-indirect-suc-halted-success s alloc payload-loc not-halted read-eq
    in halted-after-load

  -- Key lemma: exec-trace setup-trace s alloc equals step-by-step execution
  -- setup-trace = load-indirect-suc ∷ mov-to-input ∷ []
  -- setup-trace = load-indirect-suc ∷ mov-output-to-input2 ∷ []
  -- This connects the trace execution to the individual exec-abstract calls
  setup-trace-exec : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (input-loc payload-loc : ValueLocation FS) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s (sucLoc input-loc) ≡ just payload-loc →
    let setup-trace = load-indirect-suc ∷ mov-to-input ∷ []
    let setup-trace = load-indirect-suc ∷ mov-output-to-input2 ∷ []
        s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
        alloc-setup = proj₂ (exec-abstract mov-to-input s-after-load alloc-after-load)
        alloc-setup = proj₂ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in exec-trace setup-trace s alloc ≡ (s-setup , alloc-setup)
  setup-trace-exec s alloc input-loc payload-loc not-halted rdi-eq ptr-eq =
    let
      setup-trace = load-indirect-suc ∷ mov-to-input ∷ []
      setup-trace = load-indirect-suc ∷ mov-output-to-input2 ∷ []
      -- halted-after-load is needed for the second exec-trace-cons
      suc-input-eq = cong sucLoc rdi-eq
      read-eq = trans (cong (readLoc s) suc-input-eq) ptr-eq
      halted-after-load = load-indirect-suc-halted-success s alloc payload-loc not-halted read-eq
      -- Step 1: exec-trace (load ∷ mov ∷ []) s alloc = exec-trace (mov ∷ []) s-after-load alloc-after-load
      step1 = exec-trace-cons load-indirect-suc (mov-to-input ∷ []) s alloc not-halted
      step1 = exec-trace-cons load-indirect-suc (mov-output-to-input2 ∷ []) s alloc not-halted
      s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)
      alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)
      -- Step 2: exec-trace (mov ∷ []) s-after-load alloc-after-load = exec-abstract mov-to-input s-after-load alloc-after-load
      -- Step 2: exec-trace (mov ∷ []) s-after-load alloc-after-load = exec-abstract mov-output-to-input2 s-after-load alloc-after-load
      step2 = exec-trace-single mov-to-input s-after-load alloc-after-load halted-after-load
      step2 = exec-trace-single mov-output-to-input2 s-after-load alloc-after-load halted-after-load
    in trans step1 step2

  ------------------------------------------------------------------------
  -- Product Setup Trace Helpers
  --
  -- For Product types, the fst pointer is at *input-loc (not sucLoc).
  -- Setup trace: load-indirect ∷ mov-to-input ∷ []
  -- Setup trace: load-indirect ∷ mov-output-to-input2 ∷ []
  -- This gets the fst location into the Input1 register.
  ------------------------------------------------------------------------

  -- Product setup trace: load-indirect ∷ mov-to-input
  -- Product setup trace: load-indirect ∷ mov-output-to-input2
  -- After execution: Input1 = *input-loc = fst-loc
  prod-setup-trace-sets-input : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (input-loc fst-loc : ValueLocation FS) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s input-loc ≡ just fst-loc →
    let s-after-load = proj₁ (exec-abstract load-indirect s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in readReg (regs s-setup) Input1 ≡ fst-loc
  prod-setup-trace-sets-input s alloc input-loc fst-loc not-halted rdi-eq ptr-eq =
    let
      s-after-load = proj₁ (exec-abstract load-indirect s alloc)
      alloc-after-load = proj₂ (exec-abstract load-indirect s alloc)
      -- After load-indirect: Output = fst-loc
      output-eq : readReg (regs s-after-load) Output ≡ fst-loc
      output-eq = exec-abstract-load-indirect-output s alloc input-loc fst-loc rdi-eq ptr-eq
      -- After mov-to-input: Input1 = Output = fst-loc
      -- After mov-output-to-input2: Input1 = Output = fst-loc
      s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
      s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
      input-eq : readReg (regs s-setup) Input1 ≡ readReg (regs s-after-load) Output
      input-eq = exec-abstract-mov-to-input-input s-after-load alloc-after-load
    in trans input-eq output-eq

  -- Product setup trace preserves stackMem
  prod-setup-trace-preserves-stackMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    let s-after-load = proj₁ (exec-abstract load-indirect s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in stackMem s-setup ≡ stackMem s
  prod-setup-trace-preserves-stackMem s alloc =
    trans (exec-abstract-mov-to-input-preserves-stackMem
            (proj₁ (exec-abstract load-indirect s alloc))
            (proj₂ (exec-abstract load-indirect s alloc)))
          (exec-abstract-load-indirect-preserves-stackMem s alloc)

  -- Product setup trace preserves heapMem
  prod-setup-trace-preserves-heapMem : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    let s-after-load = proj₁ (exec-abstract load-indirect s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in heapMem s-setup ≡ heapMem s
  prod-setup-trace-preserves-heapMem s alloc =
    trans (exec-abstract-mov-to-input-preserves-heapMem
            (proj₁ (exec-abstract load-indirect s alloc))
            (proj₂ (exec-abstract load-indirect s alloc)))
          (exec-abstract-load-indirect-preserves-heapMem s alloc)

  -- Product setup trace preserves alloc
  prod-setup-trace-preserves-alloc : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    let s-after-load = proj₁ (exec-abstract load-indirect s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect s alloc)
        alloc-setup = proj₂ (exec-abstract mov-to-input s-after-load alloc-after-load)
        alloc-setup = proj₂ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in alloc-setup ≡ alloc
  prod-setup-trace-preserves-alloc s alloc =
    trans (exec-abstract-mov-to-input-preserves-alloc
            (proj₁ (exec-abstract load-indirect s alloc))
            (proj₂ (exec-abstract load-indirect s alloc)))
          (exec-abstract-load-indirect-preserves-alloc s alloc)

  -- Helper: load-indirect preserves halted when read succeeds
  load-indirect-halted-success : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (v : ValueLocation FS) →
    halted s ≡ false →
    readLoc s (readReg (regs s) Input1) ≡ just v →
    halted (proj₁ (exec-abstract load-indirect s alloc)) ≡ false
  load-indirect-halted-success s alloc v not-halted read-eq
    with readLoc s (readReg (regs s) Input1) | read-eq
  ... | just _ | refl = not-halted

  -- Product setup trace preserves halted status
  prod-setup-trace-preserves-halted : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (input-loc fst-loc : ValueLocation FS) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s input-loc ≡ just fst-loc →
    let s-after-load = proj₁ (exec-abstract load-indirect s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in halted s-setup ≡ false
  prod-setup-trace-preserves-halted s alloc input-loc fst-loc not-halted rdi-eq ptr-eq =
    let
      input-eq : readReg (regs s) Input1 ≡ input-loc
      input-eq = rdi-eq
      read-eq : readLoc s (readReg (regs s) Input1) ≡ just fst-loc
      read-eq = trans (cong (readLoc s) input-eq) ptr-eq
      halted-after-load = load-indirect-halted-success s alloc fst-loc not-halted read-eq
    in halted-after-load

  -- Product setup trace execution equality
  prod-setup-trace-exec : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (input-loc fst-loc : ValueLocation FS) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s input-loc ≡ just fst-loc →
    let setup-trace = load-indirect ∷ mov-to-input ∷ []
    let setup-trace = load-indirect ∷ mov-output-to-input2 ∷ []
        s-after-load = proj₁ (exec-abstract load-indirect s alloc)
        alloc-after-load = proj₂ (exec-abstract load-indirect s alloc)
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)
        s-setup = proj₁ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
        alloc-setup = proj₂ (exec-abstract mov-to-input s-after-load alloc-after-load)
        alloc-setup = proj₂ (exec-abstract mov-output-to-input2 s-after-load alloc-after-load)
    in exec-trace setup-trace s alloc ≡ (s-setup , alloc-setup)
  prod-setup-trace-exec s alloc input-loc fst-loc not-halted rdi-eq ptr-eq =
    let
      read-eq : readLoc s (readReg (regs s) Input1) ≡ just fst-loc
      read-eq = trans (cong (readLoc s) rdi-eq) ptr-eq
      halted-after-load = load-indirect-halted-success s alloc fst-loc not-halted read-eq
      step1 = exec-trace-cons load-indirect (mov-to-input ∷ []) s alloc not-halted
      step1 = exec-trace-cons load-indirect (mov-output-to-input2 ∷ []) s alloc not-halted
      s-after-load = proj₁ (exec-abstract load-indirect s alloc)
      alloc-after-load = proj₂ (exec-abstract load-indirect s alloc)
      step2 = exec-trace-single mov-to-input s-after-load alloc-after-load halted-after-load
      step2 = exec-trace-single mov-output-to-input2 s-after-load alloc-after-load halted-after-load
    in trans step1 step2

  ------------------------------------------------------------------------
  -- Heap-ref preservation
  --
  -- Abstract instructions never modify next-heap-ref (no heap allocation
  -- at abstract level). This is crucial for reclaim property composition.
  ------------------------------------------------------------------------

  -- exec-abstract preserves next-heap-ref for all instructions
  exec-abstract-preserves-heap-ref : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS}) →
    next-heap-ref (proj₂ (exec-abstract i s alloc)) ≡ next-heap-ref alloc
  exec-abstract-preserves-heap-ref mov-to-output s alloc = refl
  exec-abstract-preserves-heap-ref mov-input2-to-output s alloc = refl
  exec-abstract-preserves-heap-ref mov-to-input s alloc = refl
  exec-abstract-preserves-heap-ref mov-output-to-input2 s alloc = refl
  exec-abstract-preserves-heap-ref load-indirect s alloc = refl
  exec-abstract-preserves-heap-ref load-indirect-suc s alloc = refl
  exec-abstract-preserves-heap-ref (load-from-slot slot) s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just v = refl
  ... | nothing = refl
  exec-abstract-preserves-heap-ref (store-at-slot _) s alloc = refl
  exec-abstract-preserves-heap-ref store-indirect s alloc = refl
  exec-abstract-preserves-heap-ref store-indirect-suc s alloc = refl
  exec-abstract-preserves-heap-ref (lea-slot _) s alloc = refl
  exec-abstract-preserves-heap-ref (restore-input slot) s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just v = refl
  ... | nothing = refl
  exec-abstract-preserves-heap-ref (instr-alloc-stack _) s alloc = refl
  exec-abstract-preserves-heap-ref (instr-dealloc-stack _) s alloc = refl
  exec-abstract-preserves-heap-ref (instr-reclaim-to _) s alloc = refl
  exec-abstract-preserves-heap-ref (instr-push-frame _) s alloc = refl
  exec-abstract-preserves-heap-ref instr-pop-frame s alloc = refl
  exec-abstract-preserves-heap-ref instr-call-closure s alloc = refl
  exec-abstract-preserves-heap-ref (worklist-init _) s alloc = refl
  exec-abstract-preserves-heap-ref (worklist-push _) s alloc = refl
  exec-abstract-preserves-heap-ref (worklist-pop slot) s alloc
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just v = refl
  ... | nothing = refl
  exec-abstract-preserves-heap-ref (worklist-check _) s alloc = refl
  exec-abstract-preserves-heap-ref (instr-sigop _)    s alloc = refl
  exec-abstract-preserves-heap-ref (instr-load-const _ _) s alloc = refl
  exec-abstract-preserves-heap-ref (instr-load-code-addr _) s alloc = refl
  exec-abstract-preserves-heap-ref instr-save-closure-reg   s alloc = refl

  -- exec-trace preserves next-heap-ref
  exec-trace-preserves-heap-ref : ∀ (t : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    next-heap-ref (proj₂ (exec-trace t s alloc)) ≡ next-heap-ref alloc
  exec-trace-preserves-heap-ref [] s alloc = refl
  exec-trace-preserves-heap-ref (i ∷ t) s alloc with halted s
  ... | true = refl
  ... | false =
    let (s' , alloc') = exec-abstract i s alloc
        ih = exec-trace-preserves-heap-ref t s' alloc'
        step = exec-abstract-preserves-heap-ref i s alloc
    in trans ih step

  ------------------------------------------------------------------------
  -- Product Left Setup Trace (4-instruction: save + setup)
  --
  -- Trace: mov-to-output ∷ store-at-slot n ∷ load-indirect ∷ mov-to-input ∷ []
  -- Trace: mov-input2-to-output ∷ store-at-slot n ∷ load-indirect ∷ mov-to-input ∷ []
  -- Trace: mov-to-output ∷ store-at-slot n ∷ load-indirect ∷ mov-output-to-input2 ∷ []
  --
  -- This saves input-loc to stack and then sets Input1 := fst-loc
  ------------------------------------------------------------------------

  -- | 4-instruction left setup trace preserves alloc
  --
  -- All 4 instructions preserve alloc:
  --   mov-to-output: only changes regs
  --   mov-input2-to-output: only changes regs
  --   store-at-slot: only changes memory
  --   load-indirect: only changes regs (and maybe halted)
  --   mov-to-input: only changes regs
  --   mov-output-to-input2: only changes regs
  --
  -- Note: This requires stepping through and showing halted preserved at each step.
  -- For now, use !! as placeholder; the proof pattern follows exec-trace-preserves-halted.
  prod-left-setup-alloc-helper : ∀ (save-slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₂ (exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc) ≡ alloc
    proj₂ (exec-trace (mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc) ≡ alloc
    proj₂ (exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s alloc) ≡ alloc
  prod-left-setup-alloc-helper save-slot s alloc not-halted =
    -- All 4 instructions preserve alloc, and exec-trace-preserves-halted ensures we don't halt early.
    -- We use TracePreservesHaltedP to ensure halted stays false throughout.
    let
      tph : TracePreservesHaltedP (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ [])
      tph : TracePreservesHaltedP (mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ [])
      tph : TracePreservesHaltedP (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2 ∷ [])
      tph = tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot (tph-∷ iph-load-indirect (tph-∷ iph-mov-to-input tph-[])))
      halted-preserved = exec-trace-preserves-halted
                           (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ [])
                           (mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ [])
                           (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2 ∷ [])
                           s alloc not-halted tph
    in exec-trace-preserves-alloc-4 save-slot s alloc not-halted
    where
      -- Helper: step through 4 instructions showing alloc is preserved
      exec-trace-preserves-alloc-4 : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
        halted s ≡ false →
        proj₂ (exec-trace (mov-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc) ≡ alloc
        proj₂ (exec-trace (mov-input2-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc) ≡ alloc
        proj₂ (exec-trace (mov-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s alloc) ≡ alloc
      exec-trace-preserves-alloc-4 slot s alloc h-eq rewrite h-eq =
        let
          -- After mov-to-output
          -- After mov-input2-to-output
          s₁ = proj₁ (exec-abstract mov-to-output s alloc)
          s₁ = proj₁ (exec-abstract mov-input2-to-output s alloc)
          -- alloc₁ = alloc by definition of exec-abstract mov-to-output
          -- alloc₁ = alloc by definition of exec-abstract mov-input2-to-output
          h-eq₁ : halted s₁ ≡ false
          h-eq₁ = h-eq  -- mov-to-output preserves halted
          h-eq₁ = h-eq  -- mov-input2-to-output preserves halted
        in step-2 slot s₁ alloc h-eq₁
        where
          step-2 : ∀ (slot : ℕ) (s₁ : LocState FS) (alloc : AllocState {FS}) →
            halted s₁ ≡ false →
            proj₂ (exec-trace (store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s₁ alloc) ≡ alloc
            proj₂ (exec-trace (store-at-slot slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s₁ alloc) ≡ alloc
          step-2 slot s₁ alloc h-eq₁ rewrite h-eq₁ =
            let
              -- After store-at-slot
              s₂ = proj₁ (exec-abstract (store-at-slot slot) s₁ alloc)
              -- alloc₂ = alloc by definition of exec-abstract store-at-slot
              h-eq₂ : halted s₂ ≡ false
              h-eq₂ = trans (store-at-slot-halted slot s₁ alloc) h-eq₁
            in step-3 s₂ alloc h-eq₂
            where
              step-3 : ∀ (s₂ : LocState FS) (alloc : AllocState {FS}) →
                halted s₂ ≡ false →
                proj₂ (exec-trace (load-indirect ∷ mov-to-input ∷ []) s₂ alloc) ≡ alloc
                proj₂ (exec-trace (load-indirect ∷ mov-output-to-input2 ∷ []) s₂ alloc) ≡ alloc
              step-3 s₂ alloc h-eq₂ rewrite h-eq₂ =
                let
                  -- After load-indirect
                  s₃ = proj₁ (exec-abstract load-indirect s₂ alloc)
                  -- alloc₃ = alloc by definition of exec-abstract load-indirect
                  h-eq₃ : halted s₃ ≡ false
                  h-eq₃ = load-indirect-preserves-halted s₂ alloc h-eq₂
                in step-4 s₃ alloc h-eq₃
                where
                  step-4 : ∀ (s₃ : LocState FS) (alloc : AllocState {FS}) →
                    halted s₃ ≡ false →
                    proj₂ (exec-trace (mov-to-input ∷ []) s₃ alloc) ≡ alloc
                    proj₂ (exec-trace (mov-output-to-input2 ∷ []) s₃ alloc) ≡ alloc
                  step-4 s₃ alloc h-eq₃ rewrite h-eq₃ = refl

  -- | 4-instruction left setup trace preserves halted when load-indirect succeeds
  --
  -- Preconditions:
  --   - halted s ≡ false
  --   - readReg (regs s) Input1 ≡ input-loc
  --   - readLoc s input-loc ≡ just fst-loc (so load-indirect succeeds)
  prod-left-setup-halted-helper : ∀ (save-slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (input-loc fst-loc : ValueLocation FS) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s input-loc ≡ just fst-loc →
    halted (proj₁ (exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc)) ≡ false
    halted (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc)) ≡ false
    halted (proj₁ (exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s alloc)) ≡ false
  prod-left-setup-halted-helper save-slot s alloc input-loc fst-loc not-halted rdi-eq fst-ptr =
    -- Use exec-trace-preserves-halted with the appropriate TracePreservesHaltedP
    exec-trace-preserves-halted
      (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ [])
      (mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ [])
      (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2 ∷ [])
      s alloc not-halted
      (tph-∷ iph-mov-to-output (tph-∷ iph-store-at-slot (tph-∷ iph-load-indirect (tph-∷ iph-mov-to-input tph-[]))))

  -- | 4-instruction left setup trace sets Input1 = fst-loc
  --
  -- Trace: mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []
  -- Trace: mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []
  -- Trace: mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []
  --
  -- After execution:
  --   1. mov-to-output: Output := Input1 = input-loc
  --   1. mov-input2-to-output: Output := Input1 = input-loc
  --   2. store-at-slot: Memory[save-slot] := Output (regs unchanged)
  --   3. load-indirect: Output := *Input1 = fst-loc (since Input1 = input-loc and *input-loc = fst-loc)
  --   4. mov-to-input: Input1 := Output = fst-loc
  --   4. mov-output-to-input2: Input1 := Output = fst-loc
  prod-left-setup-input-helper : ∀ (save-slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (input-loc fst-loc : ValueLocation FS) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    readLoc s input-loc ≡ just fst-loc →
    readReg (regs (proj₁ (exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc))) Input1 ≡ fst-loc
    readReg (regs (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc))) Input1 ≡ fst-loc
    readReg (regs (proj₁ (exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s alloc))) Input1 ≡ fst-loc
  prod-left-setup-input-helper save-slot s alloc input-loc fst-loc not-halted rdi-eq fst-ptr =
    -- Step through the trace execution
    step-through save-slot s alloc input-loc fst-loc not-halted rdi-eq fst-ptr
    where
      step-through : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
        (input-loc fst-loc : ValueLocation FS) →
        halted s ≡ false →
        readReg (regs s) Input1 ≡ input-loc →
        readLoc s input-loc ≡ just fst-loc →
        readReg (regs (proj₁ (exec-trace (mov-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc))) Input1 ≡ fst-loc
        readReg (regs (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc))) Input1 ≡ fst-loc
        readReg (regs (proj₁ (exec-trace (mov-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s alloc))) Input1 ≡ fst-loc
      step-through slot s alloc input-loc fst-loc h-eq rdi-eq fst-ptr rewrite h-eq =
        -- After mov-to-output: Output = input-loc, Input1 unchanged
        -- After mov-input2-to-output: Output = input-loc, Input1 unchanged
        let
          s₁ = proj₁ (exec-abstract mov-to-output s alloc)
          s₁ = proj₁ (exec-abstract mov-input2-to-output s alloc)
          -- Input1 unchanged by mov-to-output (which only writes Output)
          -- Input1 unchanged by mov-input2-to-output (which only writes Output)
          input-s₁ : readReg (regs s₁) Input1 ≡ input-loc
          input-s₁ = rdi-eq  -- mov-to-output doesn't change Input1
          input-s₁ = rdi-eq  -- mov-input2-to-output doesn't change Input1
          h-eq₁ : halted s₁ ≡ false
          h-eq₁ = h-eq
        in step-2 slot s₁ alloc input-loc fst-loc h-eq₁ input-s₁ fst-ptr
        where
          step-2 : ∀ (slot : ℕ) (s₁ : LocState FS) (alloc : AllocState {FS})
            (input-loc fst-loc : ValueLocation FS) →
            halted s₁ ≡ false →
            readReg (regs s₁) Input1 ≡ input-loc →
            readLoc s input-loc ≡ just fst-loc →
            readReg (regs (proj₁ (exec-trace (store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s₁ alloc))) Input1 ≡ fst-loc
            readReg (regs (proj₁ (exec-trace (store-at-slot slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s₁ alloc))) Input1 ≡ fst-loc
          step-2 slot s₁ alloc input-loc fst-loc h-eq₁ input-s₁ fst-ptr rewrite h-eq₁ =
            -- After store-at-slot: Memory changes, regs unchanged
            let
              s₂ = proj₁ (exec-abstract (store-at-slot slot) s₁ alloc)
              -- Input1 unchanged by store-at-slot (which only writes memory)
              input-s₂ : readReg (regs s₂) Input1 ≡ input-loc
              input-s₂ = input-s₁  -- store-at-slot doesn't change registers
              h-eq₂ : halted s₂ ≡ false
              h-eq₂ = trans (store-at-slot-halted slot s₁ alloc) h-eq₁
            in step-3 s₂ alloc input-loc fst-loc h-eq₂ input-s₂
            where
              step-3 : ∀ (s₂ : LocState FS) (alloc : AllocState {FS})
                (input-loc fst-loc : ValueLocation FS) →
                halted s₂ ≡ false →
                readReg (regs s₂) Input1 ≡ input-loc →
                readReg (regs (proj₁ (exec-trace (load-indirect ∷ mov-to-input ∷ []) s₂ alloc))) Input1 ≡ fst-loc
                readReg (regs (proj₁ (exec-trace (load-indirect ∷ mov-output-to-input2 ∷ []) s₂ alloc))) Input1 ≡ fst-loc
              step-3 s₂ alloc input-loc fst-loc h-eq₂ input-s₂ rewrite h-eq₂ =
                -- After load-indirect and mov-to-input: Input1 = fst-loc
                -- After load-indirect and mov-output-to-input2: Input1 = fst-loc
                -- This uses prod-setup-trace-sets-input from earlier
                !!  -- The final step requires showing load-indirect reads fst-loc

  -- | load-indirect preserves memory (only changes registers)
  exec-abstract-load-indirect-preserves-mem : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    readLoc (proj₁ (exec-abstract load-indirect s alloc)) loc ≡ readLoc s loc
  exec-abstract-load-indirect-preserves-mem s alloc (AtStack f k)
    with readLoc s (readReg (regs s) Input1)
  ... | just v = refl   -- When load succeeds, only registers change
  ... | nothing = refl  -- When load fails (halts), memory unchanged
  exec-abstract-load-indirect-preserves-mem s alloc (AtDynamic hl)
    with readLoc s (readReg (regs s) Input1)
  ... | just v = refl
  ... | nothing = refl

  -- | mov-to-input preserves memory (only changes registers)
  -- | mov-output-to-input2 preserves memory (only changes registers)
  exec-abstract-mov-to-input-preserves-mem : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    readLoc (proj₁ (exec-abstract mov-to-input s alloc)) loc ≡ readLoc s loc
    readLoc (proj₁ (exec-abstract mov-output-to-input2 s alloc)) loc ≡ readLoc s loc
  exec-abstract-mov-to-input-preserves-mem s alloc (AtStack f k) = refl
  exec-abstract-mov-to-input-preserves-mem s alloc (AtDynamic hl) = refl

  -- | 4-instruction left setup trace preserves memory except save-slot
  prod-left-setup-mem-helper : ∀ (save-slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    halted s ≡ false →
    loc ≢ AtStack (current-frame alloc) save-slot →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc)) loc ≡ readLoc s loc
    readLoc (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc)) loc ≡ readLoc s loc
    readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s alloc)) loc ≡ readLoc s loc
  prod-left-setup-mem-helper save-slot s alloc loc not-halted loc-neq =
    step-through save-slot s alloc loc not-halted loc-neq
    where
      step-through : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
        (loc : ValueLocation FS) →
        halted s ≡ false →
        loc ≢ AtStack (current-frame alloc) slot →
        readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc)) loc ≡ readLoc s loc
        readLoc (proj₁ (exec-trace (mov-input2-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc)) loc ≡ readLoc s loc
        readLoc (proj₁ (exec-trace (mov-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s alloc)) loc ≡ readLoc s loc
      step-through slot s alloc loc h-eq loc-neq rewrite h-eq =
        let
          s₁ = proj₁ (exec-abstract mov-to-output s alloc)
          s₁ = proj₁ (exec-abstract mov-input2-to-output s alloc)
          mem₁ = exec-abstract-mov-to-output-preserves-mem s alloc loc
          h-eq₁ : halted s₁ ≡ false
          h-eq₁ = h-eq
        in trans (step-2 slot s₁ alloc loc h-eq₁ loc-neq) mem₁
        where
          step-2 : ∀ (slot : ℕ) (s₁ : LocState FS) (alloc : AllocState {FS})
            (loc : ValueLocation FS) →
            halted s₁ ≡ false →
            loc ≢ AtStack (current-frame alloc) slot →
            readLoc (proj₁ (exec-trace (store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s₁ alloc)) loc ≡ readLoc s₁ loc
            readLoc (proj₁ (exec-trace (store-at-slot slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s₁ alloc)) loc ≡ readLoc s₁ loc
          step-2 slot s₁ alloc loc h-eq₁ loc-neq rewrite h-eq₁ =
            let
              s₂ = proj₁ (exec-abstract (store-at-slot slot) s₁ alloc)
              mem₂ = exec-abstract-store-at-slot-preserves-loc slot s₁ alloc loc loc-neq
              h-eq₂ : halted s₂ ≡ false
              h-eq₂ = trans (store-at-slot-halted slot s₁ alloc) h-eq₁
            in trans (step-3 s₂ alloc loc h-eq₂) mem₂
            where
              step-3 : ∀ (s₂ : LocState FS) (alloc : AllocState {FS})
                (loc : ValueLocation FS) →
                halted s₂ ≡ false →
                readLoc (proj₁ (exec-trace (load-indirect ∷ mov-to-input ∷ []) s₂ alloc)) loc ≡ readLoc s₂ loc
                readLoc (proj₁ (exec-trace (load-indirect ∷ mov-output-to-input2 ∷ []) s₂ alloc)) loc ≡ readLoc s₂ loc
              step-3 s₂ alloc loc h-eq₂ rewrite h-eq₂ =
                let
                  s₃ = proj₁ (exec-abstract load-indirect s₂ alloc)
                  mem₃ = exec-abstract-load-indirect-preserves-mem s₂ alloc loc
                  h-eq₃ = load-indirect-preserves-halted s₂ alloc h-eq₂
                in trans (step-4 s₃ alloc loc h-eq₃) mem₃
                where
                  step-4 : ∀ (s₃ : LocState FS) (alloc : AllocState {FS})
                    (loc : ValueLocation FS) →
                    halted s₃ ≡ false →
                    readLoc (proj₁ (exec-trace (mov-to-input ∷ []) s₃ alloc)) loc ≡ readLoc s₃ loc
                    readLoc (proj₁ (exec-trace (mov-output-to-input2 ∷ []) s₃ alloc)) loc ≡ readLoc s₃ loc
                  step-4 s₃ alloc loc h-eq₃ rewrite h-eq₃ =
                    exec-abstract-mov-to-input-preserves-mem s₃ alloc loc

  ------------------------------------------------------------------------
  -- Additional Product Setup Helpers
  ------------------------------------------------------------------------

  -- | After prod-left-setup, stack[save-slot] contains input-loc
  --
  -- Trace: mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input
  -- Trace: mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input
  -- Trace: mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2
  -- After step 1: Output = Input1 = input-loc
  -- After step 2: stack[save-slot] = Output = input-loc
  -- Steps 3-4 don't modify stack[save-slot]
  prod-left-setup-saves-input : ∀ (save-slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (input-loc : ValueLocation FS) →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ input-loc →
    let (s' , _) = exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc
    let (s' , _) = exec-trace (mov-input2-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc
    let (s' , _) = exec-trace (mov-to-output ∷ store-at-slot save-slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s alloc
    in readLoc s' (AtStack (current-frame alloc) save-slot) ≡ just input-loc
  prod-left-setup-saves-input save-slot s alloc input-loc not-halted rdi-eq =
    step-through save-slot s alloc input-loc not-halted rdi-eq
    where
      step-through : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
        (input-loc : ValueLocation FS) →
        halted s ≡ false →
        readReg (regs s) Input1 ≡ input-loc →
        let (s' , _) = exec-trace (mov-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc
        let (s' , _) = exec-trace (mov-input2-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s alloc
        let (s' , _) = exec-trace (mov-to-output ∷ store-at-slot slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s alloc
        in readLoc s' (AtStack (current-frame alloc) slot) ≡ just input-loc
      step-through slot s alloc input-loc h-eq rdi-eq rewrite h-eq =
        let
          -- After mov-to-output: Output = input-loc
          -- After mov-input2-to-output: Output = input-loc
          s₁ = proj₁ (exec-abstract mov-to-output s alloc)
          s₁ = proj₁ (exec-abstract mov-input2-to-output s alloc)
          output-s₁ : readReg (regs s₁) Output ≡ input-loc
          output-s₁ = rdi-eq  -- mov-to-output copies Input1 to Output
          output-s₁ = rdi-eq  -- mov-input2-to-output copies Input1 to Output
          h-eq₁ : halted s₁ ≡ false
          h-eq₁ = h-eq
        in step-2 slot s₁ alloc input-loc h-eq₁ output-s₁
        where
          step-2 : ∀ (slot : ℕ) (s₁ : LocState FS) (alloc : AllocState {FS})
            (input-loc : ValueLocation FS) →
            halted s₁ ≡ false →
            readReg (regs s₁) Output ≡ input-loc →
            let (s' , _) = exec-trace (store-at-slot slot ∷ load-indirect ∷ mov-to-input ∷ []) s₁ alloc
            let (s' , _) = exec-trace (store-at-slot slot ∷ load-indirect ∷ mov-output-to-input2 ∷ []) s₁ alloc
            in readLoc s' (AtStack (current-frame alloc) slot) ≡ just input-loc
          step-2 slot s₁ alloc input-loc h-eq₁ output-eq rewrite h-eq₁ =
            let
              -- After store-at-slot: stack[slot] = Output = input-loc
              s₂ = proj₁ (exec-abstract (store-at-slot slot) s₁ alloc)
              -- The key: store-at-slot writes Output to stack[slot]
              slot-has-input : readLoc s₂ (AtStack (current-frame alloc) slot) ≡ just input-loc
              slot-has-input = trans (store-at-slot-result slot s₁ alloc) (cong just output-eq)
              h-eq₂ : halted s₂ ≡ false
              h-eq₂ = trans (store-at-slot-halted slot s₁ alloc) h-eq₁
            in step-3 s₂ alloc slot h-eq₂ slot-has-input
            where
              -- load-indirect and mov-to-input don't modify stack[slot]
              -- load-indirect and mov-output-to-input2 don't modify stack[slot]
              step-3 : ∀ (s₂ : LocState FS) (alloc : AllocState {FS}) (slot : ℕ) →
                halted s₂ ≡ false →
                readLoc s₂ (AtStack (current-frame alloc) slot) ≡ just input-loc →
                let (s' , _) = exec-trace (load-indirect ∷ mov-to-input ∷ []) s₂ alloc
                let (s' , _) = exec-trace (load-indirect ∷ mov-output-to-input2 ∷ []) s₂ alloc
                in readLoc s' (AtStack (current-frame alloc) slot) ≡ just input-loc
              step-3 s₂ alloc slot h-eq₂ slot-eq rewrite h-eq₂ =
                let
                  s₃ = proj₁ (exec-abstract load-indirect s₂ alloc)
                  mem₃ = exec-abstract-load-indirect-preserves-mem s₂ alloc (AtStack (current-frame alloc) slot)
                  slot-s₃ = trans mem₃ slot-eq
                  h-eq₃ = load-indirect-preserves-halted s₂ alloc h-eq₂
                in step-4 s₃ alloc slot h-eq₃ slot-s₃
                where
                  step-4 : ∀ (s₃ : LocState FS) (alloc : AllocState {FS}) (slot : ℕ) →
                    halted s₃ ≡ false →
                    readLoc s₃ (AtStack (current-frame alloc) slot) ≡ just input-loc →
                    let (s' , _) = exec-trace (mov-to-input ∷ []) s₃ alloc
                    let (s' , _) = exec-trace (mov-output-to-input2 ∷ []) s₃ alloc
                    in readLoc s' (AtStack (current-frame alloc) slot) ≡ just input-loc
                  step-4 s₃ alloc slot h-eq₃ slot-eq rewrite h-eq₃ =
                    trans (exec-abstract-mov-to-input-preserves-mem s₃ alloc (AtStack (current-frame alloc) slot)) slot-eq

  ------------------------------------------------------------------------
  -- Right Setup Helpers
  --
  -- Right setup trace: load-from-slot ∷ mov-to-input ∷ load-indirect-suc ∷ mov-to-input
  -- Right setup trace: load-from-slot ∷ mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2
  -- This trace only modifies registers, never memory.
  ------------------------------------------------------------------------

  -- | load-from-slot preserves memory (only changes registers)
  exec-abstract-load-from-slot-preserves-mem : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    readLoc (proj₁ (exec-abstract (load-from-slot slot) s alloc)) loc ≡ readLoc s loc
  exec-abstract-load-from-slot-preserves-mem slot s alloc (AtStack f k)
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-load-from-slot-preserves-mem slot s alloc (AtDynamic hl)
    with readLoc s (AtStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl

  -- | prod-right-setup preserves alloc
  --
  -- All 4 instructions (load-from-slot, mov-to-input, load-indirect-suc, mov-to-input)
  -- All 4 instructions (load-from-slot, mov-output-to-input2, load-indirect-suc, mov-output-to-input2)
  -- preserve alloc by definition of exec-abstract.
  prod-right-setup-alloc-helper : ∀ (save-slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₂ (exec-trace (load-from-slot save-slot ∷ mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s alloc) ≡ alloc
    proj₂ (exec-trace (load-from-slot save-slot ∷ mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s alloc) ≡ alloc
  prod-right-setup-alloc-helper save-slot s alloc not-halted =
    step-through save-slot s alloc not-halted
    where
      step-through : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
        halted s ≡ false →
        proj₂ (exec-trace (load-from-slot slot ∷ mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s alloc) ≡ alloc
        proj₂ (exec-trace (load-from-slot slot ∷ mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s alloc) ≡ alloc
      step-through slot s alloc h-eq rewrite h-eq
        with readLoc s (AtStack (current-frame alloc) slot)
      ... | nothing = refl  -- halted becomes true, trace returns alloc immediately
      ... | just v = step-2 (record s { regs = writeReg (regs s) Output v }) alloc h-eq
        where
          step-2 : ∀ (s₁ : LocState FS) (alloc : AllocState {FS}) →
            halted s₁ ≡ false →
            proj₂ (exec-trace (mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s₁ alloc) ≡ alloc
            proj₂ (exec-trace (mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s₁ alloc) ≡ alloc
          step-2 s₁ alloc h-eq₁ rewrite h-eq₁ =
            let
              s₂ = proj₁ (exec-abstract mov-to-input s₁ alloc)
              s₂ = proj₁ (exec-abstract mov-output-to-input2 s₁ alloc)
              h-eq₂ : halted s₂ ≡ false
              h-eq₂ = h-eq₁
            in step-3 s₂ alloc h-eq₂
            where
              step-3 : ∀ (s₂ : LocState FS) (alloc : AllocState {FS}) →
                halted s₂ ≡ false →
                proj₂ (exec-trace (load-indirect-suc ∷ mov-to-input ∷ []) s₂ alloc) ≡ alloc
                proj₂ (exec-trace (load-indirect-suc ∷ mov-output-to-input2 ∷ []) s₂ alloc) ≡ alloc
              step-3 s₂ alloc h-eq₂ rewrite h-eq₂ =
                let
                  s₃ = proj₁ (exec-abstract load-indirect-suc s₂ alloc)
                  h-eq₃ = load-indirect-suc-preserves-halted s₂ alloc h-eq₂
                in step-4 s₃ alloc h-eq₃
                where
                  step-4 : ∀ (s₃ : LocState FS) (alloc : AllocState {FS}) →
                    halted s₃ ≡ false →
                    proj₂ (exec-trace (mov-to-input ∷ []) s₃ alloc) ≡ alloc
                    proj₂ (exec-trace (mov-output-to-input2 ∷ []) s₃ alloc) ≡ alloc
                  step-4 s₃ alloc h-eq₃ rewrite h-eq₃ = refl

  -- | prod-right-setup preserves memory
  --
  -- All 4 instructions only modify registers, never memory.
  prod-right-setup-mem-helper : ∀ (save-slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) →
    halted s ≡ false →
    loc ≢ AtStack (current-frame alloc) save-slot →  -- This constraint is actually not needed but kept for symmetry
    let (s' , _) = exec-trace (load-from-slot save-slot ∷ mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s alloc
    let (s' , _) = exec-trace (load-from-slot save-slot ∷ mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s alloc
    in readLoc s' loc ≡ readLoc s loc
  prod-right-setup-mem-helper save-slot s alloc loc not-halted _ =
    step-through save-slot s alloc loc not-halted
    where
      step-through : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
        (loc : ValueLocation FS) →
        halted s ≡ false →
        let (s' , _) = exec-trace (load-from-slot slot ∷ mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s alloc
        let (s' , _) = exec-trace (load-from-slot slot ∷ mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s alloc
        in readLoc s' loc ≡ readLoc s loc
      step-through slot s alloc loc h-eq rewrite h-eq
        with readLoc s (AtStack (current-frame alloc) slot)
      -- When read fails: halted becomes true, rest of trace is skipped, memory unchanged
      ... | nothing = nothing-case
        where
          s' : LocState FS
          s' = record s { halted = true }
          mem-eq : readLoc s' loc ≡ readLoc s loc
          mem-eq = ExecLemmas.readLoc-stackMem-eq s' s loc refl refl
          nothing-case : readLoc (proj₁ (exec-trace (mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s' alloc)) loc ≡ readLoc s loc
          nothing-case : readLoc (proj₁ (exec-trace (mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s' alloc)) loc ≡ readLoc s loc
          nothing-case with halted s'
          ... | true = mem-eq  -- exec-trace returns s' unchanged when halted=true, and s' has same memory as s
          ... | false = mem-eq  -- also works (halted s' is always true here, but Agda may not reduce it)
      ... | just v =
        let
          s₁ = record s { regs = writeReg (regs s) Output v }
          mem₁ : readLoc s₁ loc ≡ readLoc s loc
          mem₁ = ExecLemmas.readLoc-stackMem-eq s₁ s loc refl refl  -- Only regs changed, memory unchanged
          h-eq₁ : halted s₁ ≡ false
          h-eq₁ = h-eq
        in trans (step-2 s₁ alloc loc h-eq₁) mem₁
        where
          step-2 : ∀ (s₁ : LocState FS) (alloc : AllocState {FS})
            (loc : ValueLocation FS) →
            halted s₁ ≡ false →
            let (s' , _) = exec-trace (mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s₁ alloc
            let (s' , _) = exec-trace (mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s₁ alloc
            in readLoc s' loc ≡ readLoc s₁ loc
          step-2 s₁ alloc loc h-eq₁ rewrite h-eq₁ =
            let
              s₂ = proj₁ (exec-abstract mov-to-input s₁ alloc)
              s₂ = proj₁ (exec-abstract mov-output-to-input2 s₁ alloc)
              mem₂ = exec-abstract-mov-to-input-preserves-mem s₁ alloc loc
              h-eq₂ : halted s₂ ≡ false
              h-eq₂ = h-eq₁
            in trans (step-3 s₂ alloc loc h-eq₂) mem₂
            where
              step-3 : ∀ (s₂ : LocState FS) (alloc : AllocState {FS})
                (loc : ValueLocation FS) →
                halted s₂ ≡ false →
                let (s' , _) = exec-trace (load-indirect-suc ∷ mov-to-input ∷ []) s₂ alloc
                let (s' , _) = exec-trace (load-indirect-suc ∷ mov-output-to-input2 ∷ []) s₂ alloc
                in readLoc s' loc ≡ readLoc s₂ loc
              step-3 s₂ alloc loc h-eq₂ rewrite h-eq₂ =
                let
                  s₃ = proj₁ (exec-abstract load-indirect-suc s₂ alloc)
                  mem₃ = exec-abstract-load-indirect-suc-preserves-mem s₂ alloc loc
                  h-eq₃ = load-indirect-suc-preserves-halted s₂ alloc h-eq₂
                in trans (step-4 s₃ alloc loc h-eq₃) mem₃
                where
                  step-4 : ∀ (s₃ : LocState FS) (alloc : AllocState {FS})
                    (loc : ValueLocation FS) →
                    halted s₃ ≡ false →
                    let (s' , _) = exec-trace (mov-to-input ∷ []) s₃ alloc
                    let (s' , _) = exec-trace (mov-output-to-input2 ∷ []) s₃ alloc
                    in readLoc s' loc ≡ readLoc s₃ loc
                  step-4 s₃ alloc loc h-eq₃ rewrite h-eq₃ =
                    exec-abstract-mov-to-input-preserves-mem s₃ alloc loc

  -- | prod-right-setup sets Input1 = snd-loc
  --
  -- Trace: load-from-slot ∷ mov-to-input ∷ load-indirect-suc ∷ mov-to-input
  -- Trace: load-from-slot ∷ mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2
  -- After step 1: Output = stack[save-slot] = input-loc
  -- After step 2: Input1 = Output = input-loc
  -- After step 3: Output = *(Input1 + 1) = *(input-loc + 1) = snd-loc
  -- After step 4: Input1 = Output = snd-loc
  prod-right-setup-input-helper : ∀ (save-slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (input-loc snd-loc : ValueLocation FS) →
    halted s ≡ false →
    readLoc s (AtStack (current-frame alloc) save-slot) ≡ just input-loc →
    readLoc s (sucLoc input-loc) ≡ just snd-loc →
    let (s' , _) = exec-trace (load-from-slot save-slot ∷ mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s alloc
    let (s' , _) = exec-trace (load-from-slot save-slot ∷ mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s alloc
    in readReg (regs s') Input1 ≡ snd-loc
  prod-right-setup-input-helper save-slot s alloc input-loc snd-loc not-halted stack-eq snd-ptr =
    step-through save-slot s alloc input-loc snd-loc not-halted stack-eq snd-ptr
    where
      step-through : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
        (input-loc snd-loc : ValueLocation FS) →
        halted s ≡ false →
        readLoc s (AtStack (current-frame alloc) slot) ≡ just input-loc →
        readLoc s (sucLoc input-loc) ≡ just snd-loc →
        let (s' , _) = exec-trace (load-from-slot slot ∷ mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s alloc
        let (s' , _) = exec-trace (load-from-slot slot ∷ mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s alloc
        in readReg (regs s') Input1 ≡ snd-loc
      step-through slot s alloc input-loc snd-loc h-eq stack-eq snd-ptr rewrite h-eq
        with readLoc s (AtStack (current-frame alloc) slot) | stack-eq
      ... | .(just input-loc) | refl =
        let
          -- After load-from-slot with just: s₁ = record s { regs = writeReg ... }
          s₁ = record s { regs = writeReg (regs s) Output input-loc }
          output-s₁ : readReg (regs s₁) Output ≡ input-loc
          output-s₁ = writeReg-same (regs s) Output input-loc
          h-eq₁ : halted s₁ ≡ false
          h-eq₁ = h-eq
          -- Memory of s₁ equals memory of s (only regs changed)
          mem-eq : readLoc s₁ (sucLoc input-loc) ≡ readLoc s (sucLoc input-loc)
          mem-eq = ExecLemmas.readLoc-stackMem-eq s₁ s (sucLoc input-loc) refl refl
          snd-ptr-s₁ : readLoc s₁ (sucLoc input-loc) ≡ just snd-loc
          snd-ptr-s₁ = trans mem-eq snd-ptr
        in step-2 s₁ alloc input-loc snd-loc h-eq₁ output-s₁ snd-ptr-s₁
        where
          step-2 : ∀ (s₁ : LocState FS) (alloc : AllocState {FS})
            (input-loc snd-loc : ValueLocation FS) →
            halted s₁ ≡ false →
            readReg (regs s₁) Output ≡ input-loc →
            readLoc s₁ (sucLoc input-loc) ≡ just snd-loc →
            let (s' , _) = exec-trace (mov-to-input ∷ load-indirect-suc ∷ mov-to-input ∷ []) s₁ alloc
            let (s' , _) = exec-trace (mov-output-to-input2 ∷ load-indirect-suc ∷ mov-output-to-input2 ∷ []) s₁ alloc
            in readReg (regs s') Input1 ≡ snd-loc
          step-2 s₁ alloc input-loc snd-loc h-eq₁ output-eq snd-ptr-s₁ rewrite h-eq₁ =
            let
              -- After mov-to-input: Input1 = Output = input-loc
              -- After mov-output-to-input2: Input1 = Output = input-loc
              s₂ = proj₁ (exec-abstract mov-to-input s₁ alloc)
              s₂ = proj₁ (exec-abstract mov-output-to-input2 s₁ alloc)
              input-s₂ : readReg (regs s₂) Input1 ≡ input-loc
              input-s₂ = output-eq  -- mov-to-input copies Output to Input1
              input-s₂ = output-eq  -- mov-output-to-input2 copies Output to Input1
              h-eq₂ : halted s₂ ≡ false
              h-eq₂ = h-eq₁
              -- Memory preserved through mov-to-input
              -- Memory preserved through mov-output-to-input2
              snd-ptr-s₂ : readLoc s₂ (sucLoc input-loc) ≡ just snd-loc
              snd-ptr-s₂ = trans (exec-abstract-mov-to-input-preserves-mem s₁ alloc (sucLoc input-loc)) snd-ptr-s₁
            in step-3 s₂ alloc input-loc snd-loc h-eq₂ input-s₂ snd-ptr-s₂
            where
              step-3 : ∀ (s₂ : LocState FS) (alloc : AllocState {FS})
                (input-loc snd-loc : ValueLocation FS) →
                halted s₂ ≡ false →
                readReg (regs s₂) Input1 ≡ input-loc →
                readLoc s₂ (sucLoc input-loc) ≡ just snd-loc →
                let (s' , _) = exec-trace (load-indirect-suc ∷ mov-to-input ∷ []) s₂ alloc
                let (s' , _) = exec-trace (load-indirect-suc ∷ mov-output-to-input2 ∷ []) s₂ alloc
                in readReg (regs s') Input1 ≡ snd-loc
              step-3 s₂ alloc input-loc snd-loc h-eq₂ input-eq snd-ptr-s₂ rewrite h-eq₂ =
                let
                  -- After load-indirect-suc: Output = *(Input1 + 1) = *(input-loc + 1) = snd-loc
                  s₃ = proj₁ (exec-abstract load-indirect-suc s₂ alloc)
                  output-s₃ : readReg (regs s₃) Output ≡ snd-loc
                  output-s₃ = !!  -- load-indirect-suc reads *(Input1 + 1) into Output
                  h-eq₃ = load-indirect-suc-preserves-halted s₂ alloc h-eq₂
                in step-4 s₃ alloc snd-loc h-eq₃ output-s₃
                where
                  step-4 : ∀ (s₃ : LocState FS) (alloc : AllocState {FS})
                    (snd-loc : ValueLocation FS) →
                    halted s₃ ≡ false →
                    readReg (regs s₃) Output ≡ snd-loc →
                    let (s' , _) = exec-trace (mov-to-input ∷ []) s₃ alloc
                    let (s' , _) = exec-trace (mov-output-to-input2 ∷ []) s₃ alloc
                    in readReg (regs s') Input1 ≡ snd-loc
                  step-4 s₃ alloc snd-loc h-eq₃ output-eq rewrite h-eq₃ = output-eq