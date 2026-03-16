------------------------------------------------------------------------
-- Once.CCC.SMCore
--
-- Core types and operations for the SlotMachine abstract machine.
--
-- This is the SOURCE OF TRUTH for fundamental types.
-- SMPrimitives imports from here and adds lemmas/proofs.
--
-- Location-based abstract machine for IR correctness proofs.
--
-- This machine operates ENTIRELY on ValueLocations:
--   - Registers hold ValueLocations
--   - Memory stores ValueLocations (pointers to other locations)
--   - Instructions move Locations between registers and memory
--
-- No Words/addresses appear in this model. The correspondence with
-- concrete x86 maps ValueLocations to addresses.
------------------------------------------------------------------------

module Once.CCC.SMCore where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (_≟_; <⇒≢; ≤-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; inspect; [_])
open import Relation.Nullary using (Dec; yes; no)

-- Import FrameSemantics for Frame type
open import Once.CCC.FrameSemantics using (FrameSemantics)

private
  -- Helper: just is injective (private to avoid name clashes)
  just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

------------------------------------------------------------------------
-- Slot and HeapOffset
------------------------------------------------------------------------

Slot : Set
Slot = ℕ

HeapOffset : Set
HeapOffset = ℕ

------------------------------------------------------------------------
-- HeapRef: Opaque reference to a heap block
------------------------------------------------------------------------

record HeapRef : Set where
  constructor mkHeapRef
  field
    ref-id : ℕ

open HeapRef public

_≟H_ : (h₁ h₂ : HeapRef) → Dec (h₁ ≡ h₂)
mkHeapRef n₁ ≟H mkHeapRef n₂ with n₁ ≟ n₂
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }

------------------------------------------------------------------------
-- HeapLocation: Location within the heap
--
-- Encapsulates HeapRef + HeapOffset. This type enforces the invariant
-- that heap-allocated values can only reference other heap locations,
-- never stack locations. By using HeapLocation in HeapMem's return type,
-- we make it impossible to store stack references in heap memory.
------------------------------------------------------------------------

record HeapLocation : Set where
  constructor heap-loc
  field
    heap-ref : HeapRef
    heap-offset : HeapOffset

open HeapLocation public

-- Decidable equality for HeapLocation
_≟HL_ : (hl₁ hl₂ : HeapLocation) → Dec (hl₁ ≡ hl₂)
heap-loc r₁ o₁ ≟HL heap-loc r₂ o₂ with r₁ ≟H r₂ | o₁ ≟ o₂
... | yes refl | yes refl = yes refl
... | yes _ | no o≢o = no λ { refl → o≢o refl }
... | no r≢r | _ = no λ { refl → r≢r refl }

-- Convert HeapLocation to HeapRef (for frontier checks)
hl-ref : HeapLocation → HeapRef
hl-ref = heap-ref

------------------------------------------------------------------------
-- ValueLocation: Where a value lives
--
-- OnStack locations can reference anything (stack or heap).
-- OnHeap locations use HeapLocation, enforcing heap-only references.
------------------------------------------------------------------------

data ValueLocation (FS : FrameSemantics) : Set where
  OnStack : FrameSemantics.Frame FS → Slot → ValueLocation FS
  OnHeap  : HeapLocation → ValueLocation FS

-- | Successor HeapLocation (for heap internal references)
sucHL : HeapLocation → HeapLocation
sucHL (heap-loc r o) = heap-loc r (suc o)

-- | Offset HeapLocation by n slots
offsetHL : HeapLocation → ℕ → HeapLocation
offsetHL (heap-loc r o) n = heap-loc r (n + o)

-- | Successor location (for accessing pair.snd, closure.code-ptr, etc.)
sucLoc : ∀ {FS} → ValueLocation FS → ValueLocation FS
sucLoc (OnStack f k) = OnStack f (suc k)
sucLoc (OnHeap hl)   = OnHeap (sucHL hl)

-- | Offset location by n slots (for unboxed multi-slot values)
-- Note: n + k so that offsetLoc _ 1 = sucLoc definitionally
offsetLoc : ∀ {FS} → ValueLocation FS → ℕ → ValueLocation FS
offsetLoc (OnStack f k) n = OnStack f (n + k)
offsetLoc (OnHeap hl) n   = OnHeap (offsetHL hl n)

------------------------------------------------------------------------
-- Memory: Stores Locations (not Words)
--
-- KEY INVARIANT: Heap can ONLY store heap locations.
-- This enforces that heap-allocated values never reference stack,
-- which is essential for safe frame deallocation.
--
-- Stack memory can store any ValueLocation (stack or heap).
-- Heap memory can only store HeapLocation (heap-only).
------------------------------------------------------------------------

StackMem : (FS : FrameSemantics) → Set
StackMem FS = FrameSemantics.Frame FS → Slot → Maybe (ValueLocation FS)

-- Heap memory stores HeapLocation (enforces heap-only-references-heap)
HeapMem : Set
HeapMem = HeapLocation → Maybe HeapLocation

------------------------------------------------------------------------
-- Registers: Hold Locations (not Words)
--
-- Two-register model:
--   Input  - argument location (maps to RDI in x86)
--   Output - result location (maps to RAX in x86)
------------------------------------------------------------------------

data AbstractReg : Set where
  Input  : AbstractReg    -- argument location
  Output : AbstractReg    -- result location

-- Decidable equality for AbstractReg
_≟R_ : (r₁ r₂ : AbstractReg) → Dec (r₁ ≡ r₂)
Input  ≟R Input  = yes refl
Input  ≟R Output = no (λ ())
Output ≟R Input  = no (λ ())
Output ≟R Output = yes refl

record Registers (FS : FrameSemantics) : Set where
  constructor mkRegs
  field
    input output : ValueLocation FS
    stackSlot : ℕ  -- current stack slot index (like rsp, but as slot count)

open Registers public

readReg : ∀ {FS} → Registers FS → AbstractReg → ValueLocation FS
readReg r Input  = input r
readReg r Output = output r

writeReg : ∀ {FS} → Registers FS → AbstractReg → ValueLocation FS → Registers FS
writeReg r Input  v = record r { input = v }
writeReg r Output v = record r { output = v }

-- | Update stackSlot
writeStackSlot : ∀ {FS} → Registers FS → ℕ → Registers FS
writeStackSlot r n = record r { stackSlot = n }

-- | Increment stackSlot (for allocation)
incrStackSlot : ∀ {FS} → Registers FS → ℕ → Registers FS
incrStackSlot r n = record r { stackSlot = stackSlot r + n }

-- | Decrement stackSlot (for deallocation/reclamation)
decrStackSlot : ∀ {FS} → Registers FS → ℕ → Registers FS
decrStackSlot r n = record r { stackSlot = stackSlot r ∸ n }
  where open import Data.Nat using (_∸_)

-- Key lemma: writing to one register preserves others
writeReg-preserves : ∀ {FS} (regs : Registers FS) dst r v →
  r ≢ dst →
  readReg (writeReg regs dst v) r ≡ readReg regs r
writeReg-preserves regs Input  Input  v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs Input  Output v r≢dst = refl
writeReg-preserves regs Output Input  v r≢dst = refl
writeReg-preserves regs Output Output v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)

-- Key lemma: writing to a register and reading it back gives the written value
writeReg-same : ∀ {FS} (regs : Registers FS) dst v →
  readReg (writeReg regs dst v) dst ≡ v
writeReg-same regs Input  v = refl
writeReg-same regs Output v = refl

-- Key lemma: writeReg preserves stackSlot
writeReg-preserves-stackSlot : ∀ {FS} (regs : Registers FS) dst v →
  stackSlot (writeReg regs dst v) ≡ stackSlot regs
writeReg-preserves-stackSlot regs Input  v = refl
writeReg-preserves-stackSlot regs Output v = refl

-- Key lemma: writing twice to same register is same as writing once
writeReg-overwrite : ∀ {FS} (regs : Registers FS) dst x y →
  writeReg (writeReg regs dst x) dst y ≡ writeReg regs dst y
writeReg-overwrite regs Input  x y = refl
writeReg-overwrite regs Output x y = refl

------------------------------------------------------------------------
-- LocState: Abstract Machine State
------------------------------------------------------------------------

record LocState (FS : FrameSemantics) : Set where
  constructor mkLocState
  field
    regs : Registers FS
    stackMem : StackMem FS
    heapMem : HeapMem   -- Note: HeapMem is no longer parameterized
    halted : Bool

open LocState public

------------------------------------------------------------------------
-- Allocation Mode
--
-- Where a value is allocated (output of escape analysis).
-- This is target-independent - any backend needs to distinguish
-- stack vs heap allocation.
------------------------------------------------------------------------

data AllocMode : Set where
  Stack : AllocMode  -- Value doesn't escape, allocate on stack
  Heap  : AllocMode  -- Value escapes, allocate on heap

------------------------------------------------------------------------
-- Allocation State
--
-- Tracks frame and heap allocation metadata.
--
--   - current-frame: which frame we're executing in
--   - next-slot: next available stack slot (for BeforeFrontier validity)
--   - frame-capacity: how many slots the frame can hold (for Dispatcher checks)
--   - next-heap-ref: next available heap block ID
--
-- Design note: Both AllocState.next-slot and Registers.stackSlot track
-- stack position, but serve different purposes:
--   - next-slot: Compile-time validity frontier (Dispatcher's view)
--   - stackSlot: Runtime simulation state (mirrors rsp in exec-abstract)
--
-- The Dispatcher updates next-slot when constructing traces.
-- exec-abstract updates stackSlot when executing alloc/dealloc instructions.
--
-- NOTE: The old slots-available proof (next-slot ≤ frame-capacity) was
-- removed. Capacity verification stays in Dispatcher's local reasoning,
-- making exec-abstract fully defined without threading proofs.
------------------------------------------------------------------------

record AllocState {FS : FrameSemantics} : Set where
  constructor mkAllocState
  open FrameSemantics FS
  field
    current-frame : Frame
    next-slot : ℕ
    frame-capacity : ℕ
    next-heap-ref : ℕ

open AllocState public

------------------------------------------------------------------------
-- Memory Operations
------------------------------------------------------------------------

module MemOps {FS : FrameSemantics} where
  open FrameSemantics FS

  -- | Read a Location from stack memory (returns ValueLocation)
  readStackLoc : LocState FS → Frame → Slot → Maybe (ValueLocation FS)
  readStackLoc s f k = stackMem s f k

  -- | Read from heap memory (returns HeapLocation - enforces invariant)
  readHeapLoc : LocState FS → HeapLocation → Maybe HeapLocation
  readHeapLoc s hl = heapMem s hl

  -- | Read a Location from memory
  -- Stack: returns arbitrary ValueLocation
  -- Heap: returns HeapLocation lifted to ValueLocation
  readLoc : LocState FS → ValueLocation FS → Maybe (ValueLocation FS)
  readLoc s (OnStack f k) = stackMem s f k
  readLoc s (OnHeap hl) with heapMem s hl
  ... | just hl' = just (OnHeap hl')
  ... | nothing  = nothing

  -- | Write a Location to stack memory
  writeStackMem : StackMem FS → Frame → Slot → ValueLocation FS → StackMem FS
  writeStackMem mem f k v f' k' with f ≟F f' | k ≟ k'
  ... | yes _ | yes _ = just v
  ... | _     | _     = mem f' k'

  -- | Write a HeapLocation to heap memory (enforces heap-only invariant)
  writeHeapMem : HeapMem → HeapLocation → HeapLocation → HeapMem
  writeHeapMem mem hl v hl' with hl ≟HL hl'
  ... | yes _ = just v
  ... | no _  = mem hl'

  -- | Write a Location to stack memory at a ValueLocation
  writeLocToStack : LocState FS → Frame → Slot → ValueLocation FS → LocState FS
  writeLocToStack s f k v = record s { stackMem = writeStackMem (stackMem s) f k v }

  -- | Write a HeapLocation to heap memory at a HeapLocation
  writeLocToHeap : LocState FS → HeapLocation → HeapLocation → LocState FS
  writeLocToHeap s hl v = record s { heapMem = writeHeapMem (heapMem s) hl v }

  -- | Write a Location to memory
  -- Stack destinations: can store any ValueLocation
  -- Heap destinations: can only store HeapLocation (extracted from OnHeap)
  -- Note: Writing OnStack to OnHeap is a type error - enforces invariant!
  writeLoc : LocState FS → ValueLocation FS → ValueLocation FS → LocState FS
  writeLoc s (OnStack f k) v = writeLocToStack s f k v
  writeLoc s (OnHeap hl) (OnHeap v) = writeLocToHeap s hl v
  writeLoc s (OnHeap hl) (OnStack _ _) = s  -- Invalid: can't store stack ref in heap (no-op)

  -- writeLoc preserves regs (for all cases)
  writeLoc-regs : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : ValueLocation FS) →
    regs (writeLoc s loc v) ≡ regs s
  writeLoc-regs s (OnStack f k) v = refl
  writeLoc-regs s (OnHeap hl) (OnHeap v) = refl
  writeLoc-regs s (OnHeap hl) (OnStack _ _) = refl

  -- writeLoc preserves halted (for all cases)
  writeLoc-halted : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : ValueLocation FS) →
    halted (writeLoc s loc v) ≡ halted s
  writeLoc-halted s (OnStack f k) v = refl
  writeLoc-halted s (OnHeap hl) (OnHeap v) = refl
  writeLoc-halted s (OnHeap hl) (OnStack _ _) = refl

  -- writeLoc OnStack preserves heapMem
  writeLoc-heapMem-stack : ∀ (s : LocState FS) (f : Frame) (k : Slot) (v : ValueLocation FS) →
    heapMem (writeLoc s (OnStack f k) v) ≡ heapMem s
  writeLoc-heapMem-stack s f k v = refl

  -- writeLoc commutes with register updates for OnStack locations
  -- Key for proving trace correctness where register operations interleave with memory writes
  writeLoc-regs-commute : ∀ (s : LocState FS) (f : Frame) (k : Slot) (v : ValueLocation FS)
    (r : Registers FS) →
    writeLoc (record s { regs = r }) (OnStack f k) v ≡
    record (writeLoc s (OnStack f k) v) { regs = r }
  writeLoc-regs-commute s f k v r = refl

  -- writeLoc preserves other locations (reading from a different location)
  -- Key lemma for frame-independence proofs
  writeLoc-preserves-other : ∀ (s : LocState FS) (loc1 loc2 : ValueLocation FS)
    (v : ValueLocation FS) →
    loc1 ≢ loc2 →
    readLoc (writeLoc s loc1 v) loc2 ≡ readLoc s loc2
  -- Writing to stack, reading from different stack location
  writeLoc-preserves-other s (OnStack f1 k1) (OnStack f2 k2) v neq
    with f1 ≟F f2 | k1 ≟ k2
  ... | yes refl | yes refl = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  ... | yes _ | no _ = refl
  ... | no _ | _ = refl
  -- Writing to stack, reading from heap (disjoint)
  writeLoc-preserves-other s (OnStack f k) (OnHeap hl) v _ = refl
  -- Writing to heap, reading from stack (disjoint)
  writeLoc-preserves-other s (OnHeap hl) (OnStack f k) (OnHeap hv) _ = refl
  writeLoc-preserves-other s (OnHeap hl) (OnStack f k) (OnStack _ _) _ = refl
  -- Writing to heap, reading from different heap location
  writeLoc-preserves-other s (OnHeap hl1) (OnHeap hl2) (OnHeap hv) neq
    with hl1 ≟HL hl2
  ... | yes refl = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  ... | no _ = refl
  -- Writing OnStack to OnHeap is a no-op, so reading anything returns original
  writeLoc-preserves-other s (OnHeap hl1) (OnHeap hl2) (OnStack _ _) _ = refl

  -- writeLoc-read-same: Reading from the location we just wrote returns the written value
  -- Stack case: writeLoc s (OnStack f k) v → readLoc (OnStack f k) ≡ just v
  writeLoc-read-same-stack : ∀ (s : LocState FS) (f : Frame) (k : Slot) (v : ValueLocation FS) →
    readLoc (writeLoc s (OnStack f k) v) (OnStack f k) ≡ just v
  writeLoc-read-same-stack s f k v with f ≟F f | k ≟ k
  ... | yes _ | yes _ = refl
  ... | yes _ | no k≢k = ⊥-elim (k≢k refl)
    where open import Data.Empty using (⊥-elim)
  ... | no f≢f | _ = ⊥-elim (f≢f refl)
    where open import Data.Empty using (⊥-elim)

------------------------------------------------------------------------
-- Location Source
------------------------------------------------------------------------

data LocSourceExt (FS : FrameSemantics) : Set where
  Loc : ValueLocation FS → LocSourceExt FS
  IndReg : AbstractReg → LocSourceExt FS
  IndRegSuc : AbstractReg → LocSourceExt FS

resolveSourceExt : ∀ {FS} → Registers FS → LocSourceExt FS → ValueLocation FS
resolveSourceExt regs (Loc loc) = loc
resolveSourceExt regs (IndReg r) = readReg regs r
resolveSourceExt regs (IndRegSuc r) = sucLoc (readReg regs r)

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

data Instr (FS : FrameSemantics) : Set where
  load : AbstractReg → LocSourceExt FS → Instr FS
  store : LocSourceExt FS → AbstractReg → Instr FS
  mov : AbstractReg → AbstractReg → Instr FS

------------------------------------------------------------------------
-- Execution
------------------------------------------------------------------------

module ExecFinal {FS : FrameSemantics} where
  open MemOps {FS}

  exec : Instr FS → LocState FS → LocState FS

  exec (load dst src) s with readLoc s (resolveSourceExt (regs s) src)
  ... | just v  = record s { regs = writeReg (regs s) dst v }
  ... | nothing = record s { halted = true }

  exec (store dst src) s =
    let dstLoc = resolveSourceExt (regs s) dst
        val = readReg (regs s) src
    in writeLoc s dstLoc val

  exec (mov dst src) s =
    record s { regs = writeReg (regs s) dst (readReg (regs s) src) }

  execList : List (Instr FS) → LocState FS → LocState FS
  execList [] s = s
  execList (i ∷ is) s with halted s
  ... | true  = s
  ... | false = execList is (exec i s)

------------------------------------------------------------------------
-- Execution Lemmas
------------------------------------------------------------------------

module ExecLemmas {FS : FrameSemantics} where
  open MemOps {FS}
  open ExecFinal {FS}

  -- | After load, dst holds the value from memory (when successful)
  load-result : ∀ dst src (s : LocState FS) v →
    readLoc s (resolveSourceExt (regs s) src) ≡ just v →
    readReg (regs (exec (load dst src) s)) dst ≡ v
  load-result dst src s v mem-eq with readLoc s (resolveSourceExt (regs s) src) | mem-eq
  ... | just v' | refl = writeReg-same (regs s) dst v'

  -- | After load (successful), other registers are preserved
  load-preserves-reg : ∀ dst src (s : LocState FS) r v →
    readLoc s (resolveSourceExt (regs s) src) ≡ just v →
    r ≢ dst →
    readReg (regs (exec (load dst src) s)) r ≡ readReg (regs s) r
  load-preserves-reg dst src s r v mem-eq r≢dst
    with readLoc s (resolveSourceExt (regs s) src) | mem-eq
  ... | just v' | refl = writeReg-preserves (regs s) dst r v' r≢dst

  -- | After load (failed), registers unchanged
  load-failed-preserves : ∀ dst src (s : LocState FS) →
    readLoc s (resolveSourceExt (regs s) src) ≡ nothing →
    regs (exec (load dst src) s) ≡ regs s
  load-failed-preserves dst src s mem-eq
    with readLoc s (resolveSourceExt (regs s) src) | mem-eq
  ... | nothing | refl = refl

  -- | Load preserves stack memory
  load-preserves-stackMem : ∀ dst src (s : LocState FS) →
    stackMem (exec (load dst src) s) ≡ stackMem s
  load-preserves-stackMem dst src s
    with readLoc s (resolveSourceExt (regs s) src)
  ... | just _  = refl
  ... | nothing = refl

  -- | Load preserves heap memory
  load-preserves-heapMem : ∀ dst src (s : LocState FS) →
    heapMem (exec (load dst src) s) ≡ heapMem s
  load-preserves-heapMem dst src s
    with readLoc s (resolveSourceExt (regs s) src)
  ... | just _  = refl
  ... | nothing = refl

  -- | After mov, dst holds what src held
  mov-result : ∀ dst src (s : LocState FS) →
    readReg (regs (exec (mov dst src) s)) dst ≡ readReg (regs s) src
  mov-result dst src s = writeReg-same (regs s) dst (readReg (regs s) src)

  -- | Mov preserves other registers
  mov-preserves-reg : ∀ dst src (s : LocState FS) r →
    r ≢ dst →
    readReg (regs (exec (mov dst src) s)) r ≡ readReg (regs s) r
  mov-preserves-reg dst src s r r≢dst =
    writeReg-preserves (regs s) dst r (readReg (regs s) src) r≢dst

  -- | Mov preserves memory
  mov-preserves-stackMem : ∀ dst src (s : LocState FS) →
    stackMem (exec (mov dst src) s) ≡ stackMem s
  mov-preserves-stackMem dst src s = refl

  mov-preserves-heapMem : ∀ dst src (s : LocState FS) →
    heapMem (exec (mov dst src) s) ≡ heapMem s
  mov-preserves-heapMem dst src s = refl

  -- | Load preserves halted status when memory read succeeds
  load-preserves-halted : ∀ dst src (s : LocState FS) v →
    readLoc s (resolveSourceExt (regs s) src) ≡ just v →
    halted (exec (load dst src) s) ≡ halted s
  load-preserves-halted dst src s v mem-eq
    with readLoc s (resolveSourceExt (regs s) src) | mem-eq
  ... | just _ | refl = refl

  -- | Load doesn't halt when memory read succeeds and not already halted
  load-no-halt : ∀ dst src (s : LocState FS) v →
    readLoc s (resolveSourceExt (regs s) src) ≡ just v →
    halted s ≡ false →
    halted (exec (load dst src) s) ≡ false
  load-no-halt dst src s v mem-eq not-halted =
    trans (load-preserves-halted dst src s v mem-eq) not-halted

  -- | Memory read is preserved when stackMem unchanged
  readLoc-stackMem-eq : ∀ (s₁ s₂ : LocState FS) loc →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    readLoc s₁ loc ≡ readLoc s₂ loc
  readLoc-stackMem-eq s₁ s₂ (OnStack f k) stack-eq heap-eq =
    cong (λ m → m f k) stack-eq
  readLoc-stackMem-eq s₁ s₂ (OnHeap hl) stack-eq heap-eq
    with heapMem s₁ hl | heapMem s₂ hl | cong (λ m → m hl) heap-eq
  ... | just hl₁ | just hl₂ | eq = cong (λ x → just (OnHeap x)) (just-injective eq)
  ... | nothing | nothing | _ = refl
  ... | just _ | nothing | ()
  ... | nothing | just _ | ()

------------------------------------------------------------------------
-- Abstract Instructions
--
-- Higher-level instructions that map directly to IR operations.
-- Each AbstractInstr has a clear semantics at the LocState level
-- and compiles to one or more x86 instructions.
--
-- This is the trace layer: IR execution produces AbstractTrace,
-- which compiles to x86 and has per-instruction simulation proofs.
------------------------------------------------------------------------

data AbstractInstr : Set where
  -- Register operations
  mov-to-output      : AbstractInstr              -- Output := Input
  mov-to-input       : AbstractInstr              -- Input := Output (compose bridge)

  -- Memory load operations (slot-level, not physical address arithmetic)
  load-indirect      : AbstractInstr              -- Output := *Input
  load-indirect-suc  : AbstractInstr              -- Output := *(sucLoc Input)
  load-from-slot     : Slot → AbstractInstr       -- Output := stack[slot]

  -- Memory store operations
  store-at-slot      : Slot → AbstractInstr       -- stack[slot] := Output
  store-indirect     : AbstractInstr              -- *Input := Output
  store-indirect-suc : AbstractInstr              -- *(sucLoc Input) := Output

  -- Address computation
  lea-slot           : Slot → AbstractInstr       -- Output := &stack[slot]
  restore-input      : Slot → AbstractInstr       -- Input := stack[slot]

  -- Stack management
  instr-alloc-stack   : ℕ → AbstractInstr          -- allocate N slots
  instr-dealloc-stack : ℕ → AbstractInstr          -- deallocate N slots

  -- Apply-specific (function calls)
  instr-push-frame   : ℕ → AbstractInstr          -- push new frame with capacity
  instr-pop-frame    : AbstractInstr              -- restore caller frame
  instr-call-closure : AbstractInstr              -- jump to closure code

-- | A trace is a sequence of abstract instructions
AbstractTrace : Set
AbstractTrace = List AbstractInstr

------------------------------------------------------------------------
-- Abstract Instruction Semantics
--
-- Operational semantics for AbstractInstr. Each instruction transforms
-- (LocState, AllocState) → (LocState, AllocState).
--
-- This is the specification that x86 refinement must preserve.
------------------------------------------------------------------------

module AbstractExec {FS : FrameSemantics} where
  open FrameSemantics FS
  open MemOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}

  -- | Execute one abstract instruction
  exec-abstract : AbstractInstr → LocState FS → AllocState {FS} →
                  LocState FS × AllocState {FS}

  -- mov-to-output: Output := Input
  exec-abstract mov-to-output s alloc =
    record s { regs = writeReg (regs s) Output (readReg (regs s) Input) } , alloc

  -- mov-to-input: Input := Output (compose bridge)
  exec-abstract mov-to-input s alloc =
    record s { regs = writeReg (regs s) Input (readReg (regs s) Output) } , alloc

  -- load-indirect: Output := *Input
  -- Defined via exec to enable trivial trace-correct proofs
  exec-abstract load-indirect s alloc =
    exec (load Output (IndReg Input)) s , alloc

  -- load-indirect-suc: Output := *(sucLoc Input)
  -- Defined via exec to enable trivial trace-correct proofs
  exec-abstract load-indirect-suc s alloc =
    exec (load Output (IndRegSuc Input)) s , alloc

  -- load-from-slot: Output := stack[frame, slot]
  exec-abstract (load-from-slot slot) s alloc with readLoc s (OnStack (current-frame alloc) slot)
  ... | just v  = record s { regs = writeReg (regs s) Output v } , alloc
  ... | nothing = record s { halted = true } , alloc

  -- store-at-slot: stack[frame, slot] := Output
  exec-abstract (store-at-slot slot) s alloc =
    writeLoc s (OnStack (current-frame alloc) slot) (readReg (regs s) Output) , alloc

  -- store-indirect: *Input := Output
  exec-abstract store-indirect s alloc =
    writeLoc s (readReg (regs s) Input) (readReg (regs s) Output) , alloc

  -- store-indirect-suc: *(sucLoc Input) := Output
  exec-abstract store-indirect-suc s alloc =
    writeLoc s (sucLoc (readReg (regs s) Input)) (readReg (regs s) Output) , alloc

  -- lea-slot: Output := &stack[frame, slot]
  exec-abstract (lea-slot slot) s alloc =
    record s { regs = writeReg (regs s) Output (OnStack (current-frame alloc) slot) } , alloc

  -- restore-input: Input := stack[frame, slot]
  exec-abstract (restore-input slot) s alloc with readLoc s (OnStack (current-frame alloc) slot)
  ... | just v  = record s { regs = writeReg (regs s) Input v } , alloc
  ... | nothing = record s { halted = true } , alloc

  -- instr-alloc-stack: advance stackSlot by n
  -- Capacity was verified by Dispatcher when constructing the trace
  exec-abstract (instr-alloc-stack n) s alloc =
    record s { regs = incrStackSlot (regs s) n } , alloc

  -- instr-dealloc-stack: reclaim n slots (decrement stackSlot)
  exec-abstract (instr-dealloc-stack n) s alloc =
    record s { regs = decrStackSlot (regs s) n } , alloc

  -- instr-push-frame: create new frame with given capacity
  -- Resets stackSlot to 0 for the new frame
  -- Note: Frame identity is managed by AllocState.current-frame
  exec-abstract (instr-push-frame cap) s alloc =
    record s { regs = writeStackSlot (regs s) 0 } ,
    record alloc { frame-capacity = cap }

  -- instr-pop-frame: restore caller frame
  -- Note: stackSlot restoration handled by caller (who saved it)
  exec-abstract instr-pop-frame s alloc =
    s , alloc  -- Frame identity restoration is external

  -- instr-call-closure: transfer control to closure code
  -- This is a no-op at abstract level - the call happens via BodyCorrect.execute
  exec-abstract instr-call-closure s alloc =
    s , alloc

  -- | Execute a trace (sequence of abstract instructions)
  exec-trace : AbstractTrace → LocState FS → AllocState {FS} →
               LocState FS × AllocState {FS}
  exec-trace [] s alloc = s , alloc
  exec-trace (i ∷ is) s alloc with halted s
  ... | true  = s , alloc
  ... | false = let (s' , alloc') = exec-abstract i s alloc
                in exec-trace is s' alloc'

  -- | Reduction lemma: when not halted, exec-trace reduces
  exec-trace-cons : ∀ (i : AbstractInstr) (is : AbstractTrace)
    (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-trace (i ∷ is) s alloc ≡
      let (s' , alloc') = exec-abstract i s alloc
      in exec-trace is s' alloc'
  exec-trace-cons i is s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted

  -- | Single instruction trace
  exec-trace-single : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-trace (i ∷ []) s alloc ≡ exec-abstract i s alloc
  exec-trace-single i s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted
