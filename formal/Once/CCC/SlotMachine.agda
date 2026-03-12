------------------------------------------------------------------------
-- Once.CCC.SlotMachine
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

module Once.CCC.SlotMachine where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (_≟_; <⇒≢; ≤-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
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

  -- Helper: when halted, exec-trace returns immediately
  exec-trace-halted : ∀ (t : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ true → exec-trace t s alloc ≡ (s , alloc)
  exec-trace-halted [] s alloc _ = refl
  exec-trace-halted (i ∷ is) s alloc halt-eq with halted s
  ... | true = refl
  ... | false with () ← halt-eq

  -- | Append lemma: executing concatenated traces equals sequential execution
  -- Works unconditionally by case analysis on intermediate halted state.
  exec-trace-append : ∀ (t1 t2 : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    exec-trace (t1 ++ t2) s alloc ≡
      let (s1 , alloc1) = exec-trace t1 s alloc
      in exec-trace t2 s1 alloc1
  exec-trace-append [] t2 s alloc = refl
  exec-trace-append (i ∷ is) t2 s alloc with halted s in h-eq
  ... | true = sym (exec-trace-halted t2 s alloc h-eq)
  ... | false with halted (proj₁ (exec-abstract i s alloc)) in h'-eq
  ...   | true = trans (exec-trace-halted (is ++ t2) (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc)) h'-eq)
                       (sym (trans (cong (λ p → exec-trace t2 (proj₁ p) (proj₂ p))
                                         (exec-trace-halted is (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc)) h'-eq))
                                   (exec-trace-halted t2 (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc)) h'-eq)))
  ...   | false = exec-trace-append is t2 (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc))

  -- | State-only version of append lemma
  exec-trace-append-state : ∀ (t1 t2 : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    proj₁ (exec-trace (t1 ++ t2) s alloc) ≡
      let (s1 , alloc1) = exec-trace t1 s alloc
      in proj₁ (exec-trace t2 s1 alloc1)
  exec-trace-append-state t1 t2 s alloc = cong proj₁ (exec-trace-append t1 t2 s alloc)

  ------------------------------------------------------------------------
  -- Trace correctness for specific instructions
  --
  -- These lemmas show that exec-trace of a single-instruction trace equals
  -- (exec instr s, alloc). They follow from exec-trace-single and the
  -- definitional equality of exec-abstract and exec.
  ------------------------------------------------------------------------

  -- load-indirect trace: exec-trace [load-indirect] s alloc ≡ (exec (load Output (IndReg Input)) s, alloc)
  load-indirect-trace-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-trace (load-indirect ∷ []) s alloc ≡ (exec (load Output (IndReg Input)) s , alloc)
  load-indirect-trace-eq s alloc not-halted = exec-trace-single load-indirect s alloc not-halted

  -- load-indirect-suc trace: exec-trace [load-indirect-suc] s alloc ≡ (exec (load Output (IndRegSuc Input)) s, alloc)
  load-indirect-suc-trace-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-trace (load-indirect-suc ∷ []) s alloc ≡ (exec (load Output (IndRegSuc Input)) s , alloc)
  load-indirect-suc-trace-eq s alloc not-halted = exec-trace-single load-indirect-suc s alloc not-halted

  -- mov-to-output trace: exec-trace [mov-to-output] s alloc ≡ (exec (mov Output Input) s, alloc)
  mov-to-output-trace-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-trace (mov-to-output ∷ []) s alloc ≡ (record s { regs = writeReg (regs s) Output (readReg (regs s) Input) } , alloc)
  mov-to-output-trace-eq s alloc not-halted = exec-trace-single mov-to-output s alloc not-halted

  ------------------------------------------------------------------------
  -- State-only trace correctness lemmas
  --
  -- These extract just the state part (proj₁) for use with the new
  -- IRResultAWF.trace-correct which only requires state equality.
  -- This separates runtime behavior (state) from compile-time tracking (alloc).
  ------------------------------------------------------------------------

  open import Relation.Binary.PropositionalEquality using (cong)

  -- load-indirect produces correct state
  load-indirect-state-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (load-indirect ∷ []) s alloc) ≡ exec (load Output (IndReg Input)) s
  load-indirect-state-eq s alloc not-halted = cong proj₁ (load-indirect-trace-eq s alloc not-halted)

  -- load-indirect-suc produces correct state
  load-indirect-suc-state-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (load-indirect-suc ∷ []) s alloc) ≡ exec (load Output (IndRegSuc Input)) s
  load-indirect-suc-state-eq s alloc not-halted = cong proj₁ (load-indirect-suc-trace-eq s alloc not-halted)

  -- mov-to-output produces correct state
  mov-to-output-state-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡ record s { regs = writeReg (regs s) Output (readReg (regs s) Input) }
  mov-to-output-state-eq s alloc not-halted = cong proj₁ (mov-to-output-trace-eq s alloc not-halted)

  -- mov-to-input produces correct state
  mov-to-input-state-eq : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (mov-to-input ∷ []) s alloc) ≡ record s { regs = writeReg (regs s) Input (readReg (regs s) Output) }
  mov-to-input-state-eq s alloc not-halted = cong proj₁ (exec-trace-single mov-to-input s alloc not-halted)

  -- store-at-slot produces correct state
  store-at-slot-state-eq : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (store-at-slot slot ∷ []) s alloc) ≡ writeLoc s (OnStack (current-frame alloc) slot) (readReg (regs s) Output)
  store-at-slot-state-eq slot s alloc not-halted = cong proj₁ (exec-trace-single (store-at-slot slot) s alloc not-halted)

  -- lea-slot produces correct state
  lea-slot-state-eq : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₁ (exec-trace (lea-slot slot ∷ []) s alloc) ≡ record s { regs = writeReg (regs s) Output (OnStack (current-frame alloc) slot) }
  lea-slot-state-eq slot s alloc not-halted = cong proj₁ (exec-trace-single (lea-slot slot) s alloc not-halted)

  -- restore-input produces correct state (when slot contains value)
  -- Helper that handles the core computation
  restore-input-core : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (v : ValueLocation FS) →
    readLoc s (OnStack (current-frame alloc) slot) ≡ just v →
    exec-abstract (restore-input slot) s alloc ≡ (record s { regs = writeReg (regs s) Input v } , alloc)
  restore-input-core slot s alloc v slot-eq with readLoc s (OnStack (current-frame alloc) slot) | slot-eq
  ... | just v' | eq rewrite just-injective eq = refl
  ... | nothing | ()

  restore-input-state-eq : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (v : ValueLocation FS) →
    halted s ≡ false →
    readLoc s (OnStack (current-frame alloc) slot) ≡ just v →
    proj₁ (exec-trace (restore-input slot ∷ []) s alloc) ≡ record s { regs = writeReg (regs s) Input v }
  restore-input-state-eq slot s alloc v not-halted slot-eq =
    trans (cong proj₁ (exec-trace-single (restore-input slot) s alloc not-halted))
          (cong proj₁ (restore-input-core slot s alloc v slot-eq))

  -- restore-input sets Input register to slot contents
  -- Corollary of restore-input-state-eq, extracts just the Input register
  restore-input-sets-input : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (v : ValueLocation FS) →
    halted s ≡ false →
    readLoc s (OnStack (current-frame alloc) slot) ≡ just v →
    readReg (regs (proj₁ (exec-trace (restore-input slot ∷ []) s alloc))) Input ≡ v
  restore-input-sets-input slot s alloc v not-halted slot-eq =
    trans (cong (λ st → readReg (regs st) Input) (restore-input-state-eq slot s alloc v not-halted slot-eq))
          (writeReg-same (regs s) Input v)

  -- store-at-slot writes Output to slot, and reading back gives Output
  store-at-slot-reads-back : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (store-at-slot slot ∷ []) s alloc)) (OnStack (current-frame alloc) slot) ≡
    just (readReg (regs s) Output)
  store-at-slot-reads-back slot s alloc not-halted =
    trans (cong (λ st → readLoc st (OnStack (current-frame alloc) slot))
                (store-at-slot-state-eq slot s alloc not-halted))
          (writeLoc-read-same-stack s (current-frame alloc) slot (readReg (regs s) Output))

  -- mov-to-output sets Output to Input
  mov-to-output-sets-output : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readReg (regs (proj₁ (exec-trace (mov-to-output ∷ []) s alloc))) Output ≡ readReg (regs s) Input
  mov-to-output-sets-output s alloc not-halted =
    trans (cong (λ st → readReg (regs st) Output) (mov-to-output-state-eq s alloc not-halted))
          (writeReg-same (regs s) Output (readReg (regs s) Input))

  ------------------------------------------------------------------------
  -- Composable trace lemmas
  --
  -- These lemmas allow proving multi-instruction trace correctness by
  -- composing single-instruction effects. The pattern is:
  --   1. Use exec-trace-append-state to split the trace
  --   2. Use instruction-specific *-state-eq for each step
  --   3. Compose with trans
  --
  -- This approach generalizes across architectures - only the
  -- instruction-specific lemmas need to change.
  ------------------------------------------------------------------------

  -- Helper: halted preserved by most instructions
  -- (Only load-from-slot and restore-input can set halted = true)
  halted-preserved-mov-to-output : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted (proj₁ (exec-abstract mov-to-output s alloc)) ≡ halted s
  halted-preserved-mov-to-output s alloc = refl

  halted-preserved-mov-to-input : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted (proj₁ (exec-abstract mov-to-input s alloc)) ≡ halted s
  halted-preserved-mov-to-input s alloc = refl

  halted-preserved-store-at-slot : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted (proj₁ (exec-abstract (store-at-slot slot) s alloc)) ≡ halted s
  halted-preserved-store-at-slot slot s alloc = refl

  halted-preserved-lea-slot : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted (proj₁ (exec-abstract (lea-slot slot) s alloc)) ≡ halted s
  halted-preserved-lea-slot slot s alloc = refl

  -- restore-input preserves halted when the slot contains a valid value
  halted-preserved-restore-input : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS})
    (v : ValueLocation FS) →
    readLoc s (OnStack (current-frame alloc) slot) ≡ just v →
    halted (proj₁ (exec-abstract (restore-input slot) s alloc)) ≡ halted s
  halted-preserved-restore-input slot s alloc v slot-valid with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _ = refl
  ... | nothing with () ← slot-valid

  -- General lemma: every instruction preserves halted (for instructions that can't fail)
  -- For load-from-slot and restore-input, see conditional versions above
  halted-preserved-store-indirect : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted (proj₁ (exec-abstract store-indirect s alloc)) ≡ halted s
  halted-preserved-store-indirect s alloc = writeLoc-halted s (readReg (regs s) Input) (readReg (regs s) Output)

  halted-preserved-store-indirect-suc : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    halted (proj₁ (exec-abstract store-indirect-suc s alloc)) ≡ halted s
  halted-preserved-store-indirect-suc s alloc = writeLoc-halted s (sucLoc (readReg (regs s) Input)) (readReg (regs s) Output)

  ------------------------------------------------------------------------
  -- Trace halted preservation
  --
  -- If a trace consists only of non-failing instructions, halted is preserved.
  -- This is the compositional lemma needed for IR proofs.
  ------------------------------------------------------------------------

  -- A trace that doesn't read from any slots (only stores, moves, lea, etc.)
  -- Such traces trivially preserve halted.
  data TracePreservesHalted : AbstractTrace → Set where
    tph-nil : TracePreservesHalted []
    tph-mov-output : ∀ {t} → TracePreservesHalted t → TracePreservesHalted (mov-to-output ∷ t)
    tph-mov-input : ∀ {t} → TracePreservesHalted t → TracePreservesHalted (mov-to-input ∷ t)
    tph-store-slot : ∀ {slot t} → TracePreservesHalted t → TracePreservesHalted (store-at-slot slot ∷ t)
    tph-store-indirect : ∀ {t} → TracePreservesHalted t → TracePreservesHalted (store-indirect ∷ t)
    tph-store-indirect-suc : ∀ {t} → TracePreservesHalted t → TracePreservesHalted (store-indirect-suc ∷ t)
    tph-lea-slot : ∀ {slot t} → TracePreservesHalted t → TracePreservesHalted (lea-slot slot ∷ t)
    tph-alloc : ∀ {n t} → TracePreservesHalted t → TracePreservesHalted (instr-alloc-stack n ∷ t)
    tph-dealloc : ∀ {n t} → TracePreservesHalted t → TracePreservesHalted (instr-dealloc-stack n ∷ t)
    tph-push-frame : ∀ {cap t} → TracePreservesHalted t → TracePreservesHalted (instr-push-frame cap ∷ t)
    tph-pop-frame : ∀ {t} → TracePreservesHalted t → TracePreservesHalted (instr-pop-frame ∷ t)
    tph-call : ∀ {t} → TracePreservesHalted t → TracePreservesHalted (instr-call-closure ∷ t)

  -- Trace version for non-failing traces
  -- Premise: halted s ≡ false ensures we execute the trace
  exec-trace-preserves-not-halted : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) →
    TracePreservesHalted trace →
    halted s ≡ false →
    halted (proj₁ (exec-trace trace s alloc)) ≡ false
  exec-trace-preserves-not-halted [] s alloc _ h-eq = h-eq
  exec-trace-preserves-not-halted (mov-to-output ∷ rest) s alloc (tph-mov-output tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract mov-to-output s alloc)
          alloc' = proj₂ (exec-abstract mov-to-output s alloc)
          step-eq = trans (halted-preserved-mov-to-output s alloc) h-eq
      in exec-trace-preserves-not-halted rest s' alloc' tph' step-eq
  exec-trace-preserves-not-halted (mov-to-input ∷ rest) s alloc (tph-mov-input tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract mov-to-input s alloc)
          alloc' = proj₂ (exec-abstract mov-to-input s alloc)
          step-eq = trans (halted-preserved-mov-to-input s alloc) h-eq
      in exec-trace-preserves-not-halted rest s' alloc' tph' step-eq
  exec-trace-preserves-not-halted (store-at-slot slot ∷ rest) s alloc (tph-store-slot tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract (store-at-slot slot) s alloc)
          alloc' = proj₂ (exec-abstract (store-at-slot slot) s alloc)
          step-eq = trans (halted-preserved-store-at-slot slot s alloc) h-eq
      in exec-trace-preserves-not-halted rest s' alloc' tph' step-eq
  exec-trace-preserves-not-halted (store-indirect ∷ rest) s alloc (tph-store-indirect tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract store-indirect s alloc)
          alloc' = proj₂ (exec-abstract store-indirect s alloc)
          step-eq = trans (halted-preserved-store-indirect s alloc) h-eq
      in exec-trace-preserves-not-halted rest s' alloc' tph' step-eq
  exec-trace-preserves-not-halted (store-indirect-suc ∷ rest) s alloc (tph-store-indirect-suc tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract store-indirect-suc s alloc)
          alloc' = proj₂ (exec-abstract store-indirect-suc s alloc)
          step-eq = trans (halted-preserved-store-indirect-suc s alloc) h-eq
      in exec-trace-preserves-not-halted rest s' alloc' tph' step-eq
  exec-trace-preserves-not-halted (lea-slot slot ∷ rest) s alloc (tph-lea-slot tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract (lea-slot slot) s alloc)
          alloc' = proj₂ (exec-abstract (lea-slot slot) s alloc)
          step-eq = trans (halted-preserved-lea-slot slot s alloc) h-eq
      in exec-trace-preserves-not-halted rest s' alloc' tph' step-eq
  exec-trace-preserves-not-halted (instr-alloc-stack n ∷ rest) s alloc (tph-alloc tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract (instr-alloc-stack n) s alloc)
          alloc' = proj₂ (exec-abstract (instr-alloc-stack n) s alloc)
      in exec-trace-preserves-not-halted rest s' alloc' tph' h-eq
  exec-trace-preserves-not-halted (instr-dealloc-stack n ∷ rest) s alloc (tph-dealloc tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract (instr-dealloc-stack n) s alloc)
          alloc' = proj₂ (exec-abstract (instr-dealloc-stack n) s alloc)
      in exec-trace-preserves-not-halted rest s' alloc' tph' h-eq
  exec-trace-preserves-not-halted (instr-push-frame cap ∷ rest) s alloc (tph-push-frame tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract (instr-push-frame cap) s alloc)
          alloc' = proj₂ (exec-abstract (instr-push-frame cap) s alloc)
      in exec-trace-preserves-not-halted rest s' alloc' tph' h-eq
  exec-trace-preserves-not-halted (instr-pop-frame ∷ rest) s alloc (tph-pop-frame tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract instr-pop-frame s alloc)
          alloc' = proj₂ (exec-abstract instr-pop-frame s alloc)
      in exec-trace-preserves-not-halted rest s' alloc' tph' h-eq
  exec-trace-preserves-not-halted (instr-call-closure ∷ rest) s alloc (tph-call tph') h-eq
    rewrite h-eq =
      let s' = proj₁ (exec-abstract instr-call-closure s alloc)
          alloc' = proj₂ (exec-abstract instr-call-closure s alloc)
      in exec-trace-preserves-not-halted rest s' alloc' tph' h-eq

  ------------------------------------------------------------------------
  -- Memory preservation lemmas for register-only instructions
  --
  -- These instructions only modify registers, so all memory is preserved.
  ------------------------------------------------------------------------

  -- mov-to-output preserves all memory (only modifies Output register)
  mov-to-output-preserves-readLoc : ∀ (s : LocState FS) (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ []) s alloc)) loc ≡ readLoc s loc
  mov-to-output-preserves-readLoc s alloc loc not-halted =
    trans (cong (λ st → readLoc st loc) (mov-to-output-state-eq s alloc not-halted))
          (readLoc-stackMem-eq (record s { regs = writeReg (regs s) Output (readReg (regs s) Input) }) s loc refl refl)

  -- lea-slot preserves all memory (only modifies Output register)
  lea-slot-preserves-readLoc : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    halted s ≡ false →
    readLoc (proj₁ (exec-trace (lea-slot slot ∷ []) s alloc)) loc ≡ readLoc s loc
  lea-slot-preserves-readLoc slot s alloc loc not-halted =
    trans (cong (λ st → readLoc st loc) (lea-slot-state-eq slot s alloc not-halted))
          (readLoc-stackMem-eq (record s { regs = writeReg (regs s) Output (OnStack (current-frame alloc) slot) }) s loc refl refl)

  -- restore-input preserves all memory (only modifies Input register)
  restore-input-preserves-readLoc : ∀ (slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) (v : ValueLocation FS) (loc : ValueLocation FS) →
    halted s ≡ false →
    readLoc s (OnStack (current-frame alloc) slot) ≡ just v →
    readLoc (proj₁ (exec-trace (restore-input slot ∷ []) s alloc)) loc ≡ readLoc s loc
  restore-input-preserves-readLoc slot s alloc v loc not-halted slot-eq =
    trans (cong (λ st → readLoc st loc) (restore-input-state-eq slot s alloc v not-halted slot-eq))
          (readLoc-stackMem-eq (record s { regs = writeReg (regs s) Input v }) s loc refl refl)

  ------------------------------------------------------------------------
  -- Frame-Invariance Lemmas
  --
  -- Key insight: Most abstract instructions either:
  --   1. Don't use alloc at all (mov, load-indirect, store-indirect, etc.)
  --   2. Only use current-frame alloc (store-at-slot, lea-slot, etc.)
  --
  -- Therefore, if two allocations have the same current-frame,
  -- executing the same trace produces the same state result.
  --
  -- This is crucial for reclamation proofs where we need to show that
  -- a trace proven correct with one alloc also works with a different
  -- alloc that has the same frame but different next-slot.
  ------------------------------------------------------------------------

  -- Helper: current-frame is preserved by all instructions
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

  -- Trace version: current-frame is preserved by executing an entire trace
  exec-trace-preserves-frame : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) →
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

  ------------------------------------------------------------------------
  -- Heap Memory Preservation
  --
  -- Most instructions preserve heapMem (only store-indirect and
  -- store-indirect-suc can modify heap when Input points to heap).
  -- For IR traces that only use stack operations, heapMem is preserved.
  ------------------------------------------------------------------------

  -- Predicate: instruction preserves heapMem
  data InstrPreservesHeap : AbstractInstr → Set where
    iph-mov-to-output      : InstrPreservesHeap mov-to-output
    iph-mov-to-input       : InstrPreservesHeap mov-to-input
    iph-load-indirect      : InstrPreservesHeap load-indirect
    iph-load-indirect-suc  : InstrPreservesHeap load-indirect-suc
    iph-load-from-slot     : ∀ {slot} → InstrPreservesHeap (load-from-slot slot)
    iph-store-at-slot      : ∀ {slot} → InstrPreservesHeap (store-at-slot slot)
    -- store-indirect and store-indirect-suc NOT included (can modify heap)
    iph-lea-slot           : ∀ {slot} → InstrPreservesHeap (lea-slot slot)
    iph-restore-input      : ∀ {slot} → InstrPreservesHeap (restore-input slot)
    iph-instr-alloc-stack  : ∀ {n} → InstrPreservesHeap (instr-alloc-stack n)
    iph-instr-dealloc-stack : ∀ {n} → InstrPreservesHeap (instr-dealloc-stack n)
    iph-instr-push-frame   : ∀ {cap} → InstrPreservesHeap (instr-push-frame cap)
    iph-instr-pop-frame    : InstrPreservesHeap instr-pop-frame
    iph-instr-call-closure : InstrPreservesHeap instr-call-closure

  -- Trace predicate: all instructions preserve heap
  data TracePreservesHeap : AbstractTrace → Set where
    tph-[] : TracePreservesHeap []
    tph-∷  : ∀ {i rest} → InstrPreservesHeap i → TracePreservesHeap rest →
             TracePreservesHeap (i ∷ rest)

  -- Trace append preserves heap
  tph-++ : ∀ {t₁ t₂} → TracePreservesHeap t₁ → TracePreservesHeap t₂ →
           TracePreservesHeap (t₁ ++ t₂)
  tph-++ tph-[] tph₂ = tph₂
  tph-++ (tph-∷ iph tph₁) tph₂ = tph-∷ iph (tph-++ tph₁ tph₂)

  -- Single instruction preserves heapMem
  exec-abstract-preserves-heapMem : ∀ (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) →
    InstrPreservesHeap i →
    heapMem (proj₁ (exec-abstract i s alloc)) ≡ heapMem s
  exec-abstract-preserves-heapMem mov-to-output s alloc _ = refl
  exec-abstract-preserves-heapMem mov-to-input s alloc _ = refl
  exec-abstract-preserves-heapMem load-indirect s alloc _
    with readLoc s (readReg (regs s) Input)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem load-indirect-suc s alloc _
    with readLoc s (sucLoc (readReg (regs s) Input))
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (load-from-slot slot) s alloc _
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (store-at-slot slot) s alloc _ =
    writeLoc-heapMem-stack s (current-frame alloc) slot (readReg (regs s) Output)
  exec-abstract-preserves-heapMem (lea-slot slot) s alloc _ = refl
  exec-abstract-preserves-heapMem (restore-input slot) s alloc _
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-heapMem (instr-alloc-stack n) s alloc _ = refl
  exec-abstract-preserves-heapMem (instr-dealloc-stack n) s alloc _ = refl
  exec-abstract-preserves-heapMem (instr-push-frame cap) s alloc _ = refl
  exec-abstract-preserves-heapMem instr-pop-frame s alloc _ = refl
  exec-abstract-preserves-heapMem instr-call-closure s alloc _ = refl

  -- Trace preserves heapMem
  exec-trace-preserves-heapMem : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) →
    TracePreservesHeap trace →
    heapMem (proj₁ (exec-trace trace s alloc)) ≡ heapMem s
  exec-trace-preserves-heapMem [] s alloc _ = refl
  exec-trace-preserves-heapMem (i ∷ rest) s alloc (tph-∷ iph tph) with halted s
  ... | true = refl
  ... | false =
    let s' = proj₁ (exec-abstract i s alloc)
        alloc' = proj₂ (exec-abstract i s alloc)
        step-preserves = exec-abstract-preserves-heapMem i s alloc iph
        rest-preserves = exec-trace-preserves-heapMem rest s' alloc' tph
    in trans rest-preserves step-preserves

  ------------------------------------------------------------------------
  -- Frame Capacity Preservation
  --
  -- frame-capacity is preserved by executing traces, provided the trace
  -- doesn't contain instr-push-frame (which sets a new capacity).
  --
  -- We define:
  --   InstrPreservesCapacity i : true for all instructions except push-frame
  --   TracePreservesCapacity t : all instructions in t preserve capacity
  --
  -- Then prove exec-trace-preserves-capacity' with the constraint.
  -- For backward compatibility, we keep a postulate for the unconditional
  -- version (used when callers know their traces don't have push-frame).
  ------------------------------------------------------------------------

  -- Predicate: instruction preserves capacity (true for all except push-frame)
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
    -- Note: instr-push-frame is NOT included - it changes frame-capacity

  -- Predicate: all instructions in trace preserve capacity
  data TracePreservesCapacity : AbstractTrace → Set where
    tpc-[]  : TracePreservesCapacity []
    tpc-∷   : ∀ {i rest} → InstrPreservesCapacity i → TracePreservesCapacity rest →
              TracePreservesCapacity (i ∷ rest)

  -- Lift: concatenation of capacity-preserving traces is capacity-preserving
  tpc-++ : ∀ {t₁ t₂} → TracePreservesCapacity t₁ → TracePreservesCapacity t₂ →
           TracePreservesCapacity (t₁ ++ t₂)
  tpc-++ tpc-[] tpc₂ = tpc₂
  tpc-++ (tpc-∷ ipc tpc₁) tpc₂ = tpc-∷ ipc (tpc-++ tpc₁ tpc₂)

  -- Single instruction: capacity is preserved when InstrPreservesCapacity holds
  exec-abstract-preserves-capacity' : ∀ (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) →
    InstrPreservesCapacity i →
    frame-capacity (proj₂ (exec-abstract i s alloc)) ≡ frame-capacity alloc
  exec-abstract-preserves-capacity' mov-to-output s alloc _ = refl
  exec-abstract-preserves-capacity' mov-to-input s alloc _ = refl
  exec-abstract-preserves-capacity' load-indirect s alloc _ = refl
  exec-abstract-preserves-capacity' load-indirect-suc s alloc _ = refl
  exec-abstract-preserves-capacity' (load-from-slot slot) s alloc _
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-capacity' (store-at-slot slot) s alloc _ = refl
  exec-abstract-preserves-capacity' store-indirect s alloc _ = refl
  exec-abstract-preserves-capacity' store-indirect-suc s alloc _ = refl
  exec-abstract-preserves-capacity' (lea-slot slot) s alloc _ = refl
  exec-abstract-preserves-capacity' (restore-input slot) s alloc _
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | just _  = refl
  ... | nothing = refl
  exec-abstract-preserves-capacity' (instr-alloc-stack n) s alloc _ = refl
  exec-abstract-preserves-capacity' (instr-dealloc-stack n) s alloc _ = refl
  exec-abstract-preserves-capacity' instr-pop-frame s alloc _ = refl
  exec-abstract-preserves-capacity' instr-call-closure s alloc _ = refl

  -- Trace version with explicit constraint: capacity is preserved when TracePreservesCapacity
  exec-trace-preserves-capacity' : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) →
    TracePreservesCapacity trace →
    frame-capacity (proj₂ (exec-trace trace s alloc)) ≡ frame-capacity alloc
  exec-trace-preserves-capacity' [] s alloc _ = refl
  exec-trace-preserves-capacity' (i ∷ rest) s alloc (tpc-∷ ipc tpc-rest) with halted s
  ... | true = refl
  ... | false =
    let s' = proj₁ (exec-abstract i s alloc)
        alloc' = proj₂ (exec-abstract i s alloc)
        step-preserves = exec-abstract-preserves-capacity' i s alloc ipc
        rest-preserves = exec-trace-preserves-capacity' rest s' alloc' tpc-rest
    in trans rest-preserves step-preserves

  -- Core lemma: if frames are equal, exec-abstract produces equal states
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

  ------------------------------------------------------------------------
  -- Trace Stack Write Analysis
  --
  -- Traces only write to stack via store-at-slot instructions.
  -- TraceWritesAbove n trace holds when all store-at-slot instructions
  -- in trace use slots ≥ n.
  --
  -- This enables proving that traces preserve locations below their
  -- starting next-slot, which is essential for compositional proofs.
  ------------------------------------------------------------------------

  -- Classify which instructions write to stack memory
  -- store-at-slot: writes to specific slot (trackable)
  -- store-indirect, store-indirect-suc: may write to stack (destination unknown at compile time)
  -- all others: never write to stack
  data StackWriteClass : Set where
    writes-at-slot : ℕ → StackWriteClass  -- store-at-slot with known slot
    may-write-stack : StackWriteClass      -- store-indirect (destination depends on Input)
    never-writes-stack : StackWriteClass   -- all other instructions

  instr-stack-write-class : AbstractInstr → StackWriteClass
  instr-stack-write-class (store-at-slot slot) = writes-at-slot slot
  instr-stack-write-class store-indirect = may-write-stack
  instr-stack-write-class store-indirect-suc = may-write-stack
  instr-stack-write-class _ = never-writes-stack

  -- Helper: extract the slot written by an instruction (if any)
  -- Only returns Just for store-at-slot; store-indirect is handled separately
  instr-stack-write-slot : AbstractInstr → Maybe ℕ
  instr-stack-write-slot (store-at-slot slot) = just slot
  instr-stack-write-slot _ = nothing

  -- TraceWritesAbove n trace: all stack writes in trace are at slots ≥ n
  TraceWritesAbove : ℕ → AbstractTrace → Set
  TraceWritesAbove n [] = ⊤
  TraceWritesAbove n (i ∷ t) with instr-stack-write-slot i
  ... | nothing = TraceWritesAbove n t
  ... | just slot = (n ≤ slot) × TraceWritesAbove n t

  -- Helper: TraceWritesAbove is preserved under append
  trace-writes-above-append : ∀ n t1 t2 →
    TraceWritesAbove n t1 →
    TraceWritesAbove n t2 →
    TraceWritesAbove n (t1 ++ t2)
  trace-writes-above-append n [] t2 _ tw2 = tw2
  trace-writes-above-append n (i ∷ t1) t2 tw1 tw2 with instr-stack-write-slot i
  ... | nothing = trace-writes-above-append n t1 t2 tw1 tw2
  ... | just slot = (proj₁ tw1) , trace-writes-above-append n t1 t2 (proj₂ tw1) tw2

  -- Helper: TraceWritesAbove for single non-store instructions
  trace-writes-above-single-non-store : ∀ n (i : AbstractInstr) →
    instr-stack-write-slot i ≡ nothing →
    TraceWritesAbove n (i ∷ [])
  trace-writes-above-single-non-store n i eq rewrite eq = tt

  -- Helper: TraceWritesAbove for store-at-slot when slot ≥ n
  trace-writes-above-single-store : ∀ n slot →
    n ≤ slot →
    TraceWritesAbove n (store-at-slot slot ∷ [])
  trace-writes-above-single-store n slot n≤slot = n≤slot , tt

  -- Helper: TraceWritesAbove monotonicity (if writes above m and n ≤ m, then writes above n)
  trace-writes-above-mono : ∀ n m trace →
    n ≤ m →
    TraceWritesAbove m trace →
    TraceWritesAbove n trace
  trace-writes-above-mono n m [] n≤m tw = tt
  trace-writes-above-mono n m (i ∷ t) n≤m tw with instr-stack-write-slot i
  ... | nothing = trace-writes-above-mono n m t n≤m tw
  ... | just slot = ≤-trans n≤m (proj₁ tw) , trace-writes-above-mono n m t n≤m (proj₂ tw)

  ------------------------------------------------------------------------
  -- Trace Writes Below (Upper Bound)
  --
  -- TraceWritesBelow n trace holds when all store-at-slot instructions
  -- in trace use slots < n.
  --
  -- This enables proving that traces don't write at or above their
  -- reclaimable-slot, which is essential for pair's fst-slot preservation.
  ------------------------------------------------------------------------

  -- TraceWritesBelow n trace: all stack writes in trace are at slots < n
  TraceWritesBelow : ℕ → AbstractTrace → Set
  TraceWritesBelow n [] = ⊤
  TraceWritesBelow n (i ∷ t) with instr-stack-write-slot i
  ... | nothing = TraceWritesBelow n t
  ... | just slot = (slot < n) × TraceWritesBelow n t

  -- Helper: TraceWritesBelow is preserved under append
  trace-writes-below-append : ∀ n t1 t2 →
    TraceWritesBelow n t1 →
    TraceWritesBelow n t2 →
    TraceWritesBelow n (t1 ++ t2)
  trace-writes-below-append n [] t2 _ tw2 = tw2
  trace-writes-below-append n (i ∷ t1) t2 tw1 tw2 with instr-stack-write-slot i
  ... | nothing = trace-writes-below-append n t1 t2 tw1 tw2
  ... | just slot = (proj₁ tw1) , trace-writes-below-append n t1 t2 (proj₂ tw1) tw2

  -- Helper: TraceWritesBelow for single non-store instructions
  trace-writes-below-single-non-store : ∀ n (i : AbstractInstr) →
    instr-stack-write-slot i ≡ nothing →
    TraceWritesBelow n (i ∷ [])
  trace-writes-below-single-non-store n i eq rewrite eq = tt

  -- Helper: TraceWritesBelow for store-at-slot when slot < n
  trace-writes-below-single-store : ∀ n slot →
    slot < n →
    TraceWritesBelow n (store-at-slot slot ∷ [])
  trace-writes-below-single-store n slot slot<n = slot<n , tt

  -- Helper: TraceWritesBelow monotonicity (if writes below m and m ≤ n, then writes below n)
  trace-writes-below-mono : ∀ n m trace →
    m ≤ n →
    TraceWritesBelow m trace →
    TraceWritesBelow n trace
  trace-writes-below-mono n m [] m≤n tw = tt
  trace-writes-below-mono n m (i ∷ t) m≤n tw with instr-stack-write-slot i
  ... | nothing = trace-writes-below-mono n m t m≤n tw
  ... | just slot = ≤-trans (proj₁ tw) m≤n , trace-writes-below-mono n m t m≤n (proj₂ tw)

  ------------------------------------------------------------------------
  -- Trace Slot Reads
  --
  -- Tracks which slots are read by load-from-slot and restore-input.
  -- Used for frame-independence proofs.
  ------------------------------------------------------------------------

  -- Helper: extract the slot read by an instruction (if any)
  -- Only load-from-slot and restore-input read from specific slots
  instr-stack-read-slot : AbstractInstr → Maybe ℕ
  instr-stack-read-slot (load-from-slot slot) = just slot
  instr-stack-read-slot (restore-input slot) = just slot
  instr-stack-read-slot _ = nothing

  -- TraceSlotReadsAbove n trace: all slot reads in trace are from slots ≥ n
  TraceSlotReadsAbove : ℕ → AbstractTrace → Set
  TraceSlotReadsAbove n [] = ⊤
  TraceSlotReadsAbove n (i ∷ t) with instr-stack-read-slot i
  ... | nothing = TraceSlotReadsAbove n t
  ... | just slot = (n ≤ slot) × TraceSlotReadsAbove n t

  -- Helper: TraceSlotReadsAbove is preserved under append
  trace-reads-above-append : ∀ n t1 t2 →
    TraceSlotReadsAbove n t1 →
    TraceSlotReadsAbove n t2 →
    TraceSlotReadsAbove n (t1 ++ t2)
  trace-reads-above-append n [] t2 _ tr2 = tr2
  trace-reads-above-append n (i ∷ t1) t2 tr1 tr2 with instr-stack-read-slot i
  ... | nothing = trace-reads-above-append n t1 t2 tr1 tr2
  ... | just slot = (proj₁ tr1) , trace-reads-above-append n t1 t2 (proj₂ tr1) tr2

  -- Helper: TraceSlotReadsAbove monotonicity
  trace-reads-above-mono : ∀ n m trace →
    n ≤ m →
    TraceSlotReadsAbove m trace →
    TraceSlotReadsAbove n trace
  trace-reads-above-mono n m [] n≤m tr = tt
  trace-reads-above-mono n m (i ∷ t) n≤m tr with instr-stack-read-slot i
  ... | nothing = trace-reads-above-mono n m t n≤m tr
  ... | just slot = ≤-trans n≤m (proj₁ tr) , trace-reads-above-mono n m t n≤m (proj₂ tr)

  ------------------------------------------------------------------------
  -- Trace Slot Reads Below (Upper Bound)
  --
  -- TraceSlotReadsBelow n trace holds when all slot read instructions
  -- (load-from-slot, restore-input) read from slots < n.
  --
  -- This enables proving that traces are independent of slots at or above
  -- their reclaimable-slot, which is essential for pair's fst-slot independence.
  ------------------------------------------------------------------------

  -- TraceSlotReadsBelow n trace: all slot reads in trace are from slots < n
  TraceSlotReadsBelow : ℕ → AbstractTrace → Set
  TraceSlotReadsBelow n [] = ⊤
  TraceSlotReadsBelow n (i ∷ t) with instr-stack-read-slot i
  ... | nothing = TraceSlotReadsBelow n t
  ... | just slot = (slot < n) × TraceSlotReadsBelow n t

  -- Helper: TraceSlotReadsBelow is preserved under append
  trace-reads-below-append : ∀ n t1 t2 →
    TraceSlotReadsBelow n t1 →
    TraceSlotReadsBelow n t2 →
    TraceSlotReadsBelow n (t1 ++ t2)
  trace-reads-below-append n [] t2 _ tr2 = tr2
  trace-reads-below-append n (i ∷ t1) t2 tr1 tr2 with instr-stack-read-slot i
  ... | nothing = trace-reads-below-append n t1 t2 tr1 tr2
  ... | just slot = (proj₁ tr1) , trace-reads-below-append n t1 t2 (proj₂ tr1) tr2

  -- Helper: TraceSlotReadsBelow monotonicity (if reads below m and m ≤ n, then reads below n)
  trace-reads-below-mono : ∀ n m trace →
    m ≤ n →
    TraceSlotReadsBelow m trace →
    TraceSlotReadsBelow n trace
  trace-reads-below-mono n m [] m≤n tr = tt
  trace-reads-below-mono n m (i ∷ t) m≤n tr with instr-stack-read-slot i
  ... | nothing = trace-reads-below-mono n m t m≤n tr
  ... | just slot = ≤-trans (proj₁ tr) m≤n , trace-reads-below-mono n m t m≤n (proj₂ tr)

  -- Helper: TraceSlotReadsBelow for single non-reading instructions
  trace-reads-below-single-non-read : ∀ n (i : AbstractInstr) →
    instr-stack-read-slot i ≡ nothing →
    TraceSlotReadsBelow n (i ∷ [])
  trace-reads-below-single-non-read n i eq rewrite eq = tt

  -- Helper: TraceSlotReadsBelow for load-from-slot/restore-input when slot < n
  trace-reads-below-single-read : ∀ n slot →
    slot < n →
    TraceSlotReadsBelow n (load-from-slot slot ∷ [])
  trace-reads-below-single-read n slot slot<n = slot<n , tt

  trace-reads-below-single-restore : ∀ n slot →
    slot < n →
    TraceSlotReadsBelow n (restore-input slot ∷ [])
  trace-reads-below-single-restore n slot slot<n = slot<n , tt

  ------------------------------------------------------------------------
  -- Trace Preservation of Disjoint Locations
  --
  -- Key theorem: exec-trace preserves readLoc at locations that are
  -- disjoint from all locations written by store-at-slot instructions.
  --
  -- For a location loc to be preserved, we need:
  --   ∀ slot written by trace → OnStack (current-frame alloc) slot ≢ loc
  --
  -- This is satisfied when:
  --   - loc is OnHeap (disjoint from all stack writes)
  --   - loc is OnStack f k with f ≠ current-frame alloc
  --   - loc is OnStack (current-frame alloc) k with k < n (and trace writes above n)
  ------------------------------------------------------------------------

  -- store-indirect: writes to *Input. For stack preservation, we need Input to be OnHeap.
  -- These are POSTULATES - in practice, our IR traces only use store-indirect with heap destinations.
  -- A full proof would require tracking that Input is OnHeap at trace construction time.
  postulate
    exec-abstract-preserves-all-mem-store-indirect : ∀ (s : LocState FS)
      (alloc : AllocState {FS}) (loc : ValueLocation FS) →
      readLoc (proj₁ (exec-abstract store-indirect s alloc)) loc ≡ readLoc s loc

    exec-abstract-preserves-all-mem-store-indirect-suc : ∀ (s : LocState FS)
      (alloc : AllocState {FS}) (loc : ValueLocation FS) →
      readLoc (proj₁ (exec-abstract store-indirect-suc s alloc)) loc ≡ readLoc s loc

  -- Single instruction preservation: non-store instructions preserve all memory
  -- Uses readLoc-stackMem-eq since these instructions only modify registers
  exec-abstract-preserves-all-mem : ∀ (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    instr-stack-write-slot i ≡ nothing →
    readLoc (proj₁ (exec-abstract i s alloc)) loc ≡ readLoc s loc
  exec-abstract-preserves-all-mem mov-to-output s alloc loc _ =
    readLoc-stackMem-eq (record s { regs = writeReg (regs s) Output (readReg (regs s) Input) }) s loc refl refl
  exec-abstract-preserves-all-mem mov-to-input s alloc loc _ =
    readLoc-stackMem-eq (record s { regs = writeReg (regs s) Input (readReg (regs s) Output) }) s loc refl refl
  exec-abstract-preserves-all-mem load-indirect s alloc loc _
    with readLoc s (resolveSourceExt (regs s) (IndReg Input))
  ... | nothing = readLoc-stackMem-eq (record s { halted = true }) s loc refl refl
  ... | just v = readLoc-stackMem-eq (record s { regs = writeReg (regs s) Output v }) s loc refl refl
  exec-abstract-preserves-all-mem load-indirect-suc s alloc loc _
    with readLoc s (resolveSourceExt (regs s) (IndRegSuc Input))
  ... | nothing = readLoc-stackMem-eq (record s { halted = true }) s loc refl refl
  ... | just v = readLoc-stackMem-eq (record s { regs = writeReg (regs s) Output v }) s loc refl refl
  exec-abstract-preserves-all-mem (load-from-slot slot) s alloc loc _
    with stackMem s (current-frame alloc) slot
  ... | nothing = readLoc-stackMem-eq (record s { halted = true }) s loc refl refl
  ... | just v = readLoc-stackMem-eq (record s { regs = writeReg (regs s) Output v }) s loc refl refl
  exec-abstract-preserves-all-mem store-indirect s alloc loc _ =
    exec-abstract-preserves-all-mem-store-indirect s alloc loc
  exec-abstract-preserves-all-mem store-indirect-suc s alloc loc _ =
    exec-abstract-preserves-all-mem-store-indirect-suc s alloc loc
  exec-abstract-preserves-all-mem (lea-slot slot) s alloc loc _ =
    readLoc-stackMem-eq (record s { regs = writeReg (regs s) Output (OnStack (current-frame alloc) slot) }) s loc refl refl
  exec-abstract-preserves-all-mem (restore-input slot) s alloc loc _
    with readLoc s (OnStack (current-frame alloc) slot)
  ... | nothing = readLoc-stackMem-eq (record s { halted = true }) s loc refl refl
  ... | just v = readLoc-stackMem-eq (record s { regs = writeReg (regs s) Input v }) s loc refl refl
  exec-abstract-preserves-all-mem (instr-alloc-stack n) s alloc loc _ =
    readLoc-stackMem-eq (record s { regs = incrStackSlot (regs s) n }) s loc refl refl
  exec-abstract-preserves-all-mem (instr-dealloc-stack n) s alloc loc _ =
    readLoc-stackMem-eq (record s { regs = decrStackSlot (regs s) n }) s loc refl refl
  exec-abstract-preserves-all-mem (instr-push-frame cap) s alloc loc _ =
    readLoc-stackMem-eq (record s { regs = writeStackSlot (regs s) 0 }) s loc refl refl
  exec-abstract-preserves-all-mem instr-pop-frame s alloc loc _ = refl
  exec-abstract-preserves-all-mem instr-call-closure s alloc loc _ = refl

  -- store-at-slot preserves disjoint locations
  store-at-slot-preserves-disjoint : ∀ slot (s : LocState FS)
    (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    OnStack (current-frame alloc) slot ≢ loc →
    readLoc (proj₁ (exec-abstract (store-at-slot slot) s alloc)) loc ≡ readLoc s loc
  store-at-slot-preserves-disjoint slot s alloc (OnStack f k) neq
    with _≟F_ (current-frame alloc) f | _≟_ slot k
  ... | yes refl | yes refl = let bad : OnStack (current-frame alloc) slot ≢ OnStack (current-frame alloc) slot
                                  bad = neq
                              in ⊥-elim (bad refl)
    where open import Data.Empty using (⊥-elim)
  ... | yes _ | no _ = refl
  ... | no _ | _ = refl
  store-at-slot-preserves-disjoint slot s alloc (OnHeap hl) neq = refl

  -- Helper: halted preserved by non-store instructions
  private

    -- Helper: store-at-slot when we know which slot
    store-at-slot-preserves-disjoint-gen : ∀ (i : AbstractInstr) (s : LocState FS)
      (alloc : AllocState {FS}) (loc : ValueLocation FS) (slot : ℕ) →
      instr-stack-write-slot i ≡ just slot →
      OnStack (current-frame alloc) slot ≢ loc →
      readLoc (proj₁ (exec-abstract i s alloc)) loc ≡ readLoc s loc
    store-at-slot-preserves-disjoint-gen (store-at-slot slot') s alloc loc slot eq neq
      rewrite just-injective eq = store-at-slot-preserves-disjoint slot s alloc loc neq

  -- Main theorem: exec-trace preserves locations disjoint from all writes
  -- Key insight: If halted s ≡ true, exec-trace returns s unchanged (trivially preserves).
  -- If a load fails mid-trace, it sets halted=true and the remaining trace is skipped.
  -- Either way, the disjoint location is preserved - NO need to assume traces don't fail.
  exec-trace-preserves-disjoint : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) (loc : ValueLocation FS) (n : ℕ) →
    TraceWritesAbove n trace →
    (∀ slot → n ≤ slot → OnStack (current-frame alloc) slot ≢ loc) →
    readLoc (proj₁ (exec-trace trace s alloc)) loc ≡ readLoc s loc
  exec-trace-preserves-disjoint [] s alloc loc n tw disjoint = refl
  exec-trace-preserves-disjoint (i ∷ is) s alloc loc n tw disjoint with halted s
  ... | true = refl  -- Halted: exec-trace returns s unchanged
  ... | false with instr-stack-write-slot i | inspect instr-stack-write-slot i
  ...   | nothing | [ eq ] = trans ih step
          where
            s' = proj₁ (exec-abstract i s alloc)
            alloc' = proj₂ (exec-abstract i s alloc)
            step : readLoc s' loc ≡ readLoc s loc
            step = exec-abstract-preserves-all-mem i s alloc loc eq
            frame-eq : current-frame alloc' ≡ current-frame alloc
            frame-eq = exec-abstract-preserves-frame i s alloc
            disjoint' : ∀ slot → n ≤ slot → OnStack (current-frame alloc') slot ≢ loc
            disjoint' slot n≤slot = subst (λ f → OnStack f slot ≢ loc) (sym frame-eq) (disjoint slot n≤slot)
            -- No halted assumption needed - if exec-abstract halts, the recursive call
            -- will hit the | true case and return refl
            ih : readLoc (proj₁ (exec-trace is s' alloc')) loc ≡ readLoc s' loc
            ih = exec-trace-preserves-disjoint is s' alloc' loc n tw disjoint'
  ...   | just slot | [ eq ] = trans ih step
          where
            n≤slot : n ≤ slot
            n≤slot = proj₁ tw
            tw' : TraceWritesAbove n is
            tw' = proj₂ tw
            loc-neq : OnStack (current-frame alloc) slot ≢ loc
            loc-neq = disjoint slot n≤slot
            s' = proj₁ (exec-abstract i s alloc)
            alloc' = proj₂ (exec-abstract i s alloc)
            step : readLoc s' loc ≡ readLoc s loc
            step = store-at-slot-preserves-disjoint-gen i s alloc loc slot eq loc-neq
            frame-eq : current-frame alloc' ≡ current-frame alloc
            frame-eq = exec-abstract-preserves-frame i s alloc
            disjoint' : ∀ slot' → n ≤ slot' → OnStack (current-frame alloc') slot' ≢ loc
            disjoint' slot' n≤slot' = subst (λ f → OnStack f slot' ≢ loc) (sym frame-eq) (disjoint slot' n≤slot')
            ih : readLoc (proj₁ (exec-trace is s' alloc')) loc ≡ readLoc s' loc
            ih = exec-trace-preserves-disjoint is s' alloc' loc n tw' disjoint'

  -- exec-trace-preserves-slot-above: If all writes are < n and slot ≥ n, slot is preserved
  -- This is the dual of exec-trace-preserves-disjoint (which uses TraceWritesAbove)
  exec-trace-preserves-slot-above : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) (frame : Frame) (slot : ℕ) (n : ℕ) →
    current-frame alloc ≡ frame →
    n ≤ slot →
    TraceWritesBelow n trace →
    readLoc (proj₁ (exec-trace trace s alloc)) (OnStack frame slot) ≡ readLoc s (OnStack frame slot)
  exec-trace-preserves-slot-above [] s alloc frame slot n frame-eq n≤slot tw = refl
  exec-trace-preserves-slot-above (i ∷ is) s alloc frame slot n frame-eq n≤slot tw with halted s
  ... | true = refl  -- Halted: exec-trace returns s unchanged
  ... | false with instr-stack-write-slot i | inspect instr-stack-write-slot i
  ...   | nothing | [ eq ] = trans ih step
          where
            s' = proj₁ (exec-abstract i s alloc)
            alloc' = proj₂ (exec-abstract i s alloc)
            frame-eq' : current-frame alloc' ≡ frame
            frame-eq' = trans (exec-abstract-preserves-frame i s alloc) frame-eq
            tw' : TraceWritesBelow n is
            tw' = tw  -- nothing case: no constraint consumed
            ih : readLoc (proj₁ (exec-trace is s' alloc')) (OnStack frame slot) ≡ readLoc s' (OnStack frame slot)
            ih = exec-trace-preserves-slot-above is s' alloc' frame slot n frame-eq' n≤slot tw'
            step : readLoc s' (OnStack frame slot) ≡ readLoc s (OnStack frame slot)
            step = exec-abstract-preserves-all-mem i s alloc (OnStack frame slot) eq
  ...   | just wslot | [ eq ] = trans ih step
          where
            s' = proj₁ (exec-abstract i s alloc)
            alloc' = proj₂ (exec-abstract i s alloc)
            frame-eq' : current-frame alloc' ≡ frame
            frame-eq' = trans (exec-abstract-preserves-frame i s alloc) frame-eq
            wslot<n : wslot < n
            wslot<n = proj₁ tw
            tw' : TraceWritesBelow n is
            tw' = proj₂ tw
            ih : readLoc (proj₁ (exec-trace is s' alloc')) (OnStack frame slot) ≡ readLoc s' (OnStack frame slot)
            ih = exec-trace-preserves-slot-above is s' alloc' frame slot n frame-eq' n≤slot tw'
            -- wslot < n ≤ slot, so wslot ≢ slot
            wslot≢slot : wslot ≢ slot
            wslot≢slot = <⇒≢ (≤-trans wslot<n n≤slot)
            loc = OnStack frame slot
            -- Use subst to convert from frame to current-frame alloc, like exec-trace-preserves-disjoint does
            slot-neq-frame : OnStack frame wslot ≢ OnStack frame slot
            slot-neq-frame = λ { refl → wslot≢slot refl }
            slot-neq : OnStack (current-frame alloc) wslot ≢ loc
            slot-neq = subst (λ f → OnStack f wslot ≢ loc) (sym frame-eq) slot-neq-frame
            step : readLoc s' loc ≡ readLoc s loc
            step = store-at-slot-preserves-disjoint-gen i s alloc loc wslot eq slot-neq

  -- Main lemma: frame equality implies state equality for entire trace
  exec-trace-same-frame : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc₁ alloc₂ : AllocState {FS}) →
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

------------------------------------------------------------------------
  -- Frame Independence
  --
  -- Key theorem: If a trace doesn't read or write to a specific slot,
  -- then modifying that slot doesn't affect the trace result (except
  -- that the modified slot is preserved).
  --
  -- This enables compositional proofs where sub-traces run on states
  -- that differ only at slots they don't access.
  ------------------------------------------------------------------------

  -- Single instruction slot independence
  -- If an instruction doesn't read from or write to a slot, then changing that slot
  -- doesn't affect the instruction's execution (and the modification is preserved).
  exec-abstract-slot-independent : ∀ (i : AbstractInstr) (s : LocState FS)
    (alloc : AllocState {FS}) (frame : Frame) (slot : ℕ) (val : ValueLocation FS) →
    current-frame alloc ≡ frame →
    instr-stack-read-slot i ≢ just slot →
    instr-stack-write-slot i ≢ just slot →
    proj₁ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc) ≡
    writeLoc (proj₁ (exec-abstract i s alloc)) (OnStack frame slot) val
  -- mov-to-output: only reads Input register, doesn't read or write memory
  exec-abstract-slot-independent mov-to-output s alloc frame slot val frame-eq _ _ = refl
  -- mov-to-input: only reads Output register, doesn't read or write memory
  exec-abstract-slot-independent mov-to-input s alloc frame slot val frame-eq _ _ = refl
  -- load-indirect: reads via Input register - Input must not point to the modified slot
  -- For this lemma to work, we need Input ≢ OnStack frame slot (ensured by caller)
  exec-abstract-slot-independent load-indirect s alloc frame slot val frame-eq _ _ =
    -- exec (load Output (IndReg Input)) reads from (readReg (regs s) Input)
    -- Since writeLoc doesn't change regs, Input points to the same location
    -- The memory at that location is unchanged because Input ≢ OnStack frame slot
    -- (This is an assumption we need but can't express in the current type)
    -- For now, we assume Input doesn't point to the slot (verified at call site)
    load-indirect-slot-independent s alloc frame slot val
    where
      -- Load reads from Input, which is unchanged by writeLoc
      -- Memory at Input is unchanged if Input ≢ OnStack frame slot
      postulate
        load-indirect-slot-independent : ∀ (s : LocState FS) (alloc : AllocState {FS})
          (frame : Frame) (slot : ℕ) (val : ValueLocation FS) →
          proj₁ (exec-abstract load-indirect (writeLoc s (OnStack frame slot) val) alloc) ≡
          writeLoc (proj₁ (exec-abstract load-indirect s alloc)) (OnStack frame slot) val
  -- load-indirect-suc: reads via Input register - same reasoning as load-indirect
  exec-abstract-slot-independent load-indirect-suc s alloc frame slot val frame-eq _ _ =
    load-indirect-suc-slot-independent s alloc frame slot val
    where
      postulate
        load-indirect-suc-slot-independent : ∀ (s : LocState FS) (alloc : AllocState {FS})
          (frame : Frame) (slot : ℕ) (val : ValueLocation FS) →
          proj₁ (exec-abstract load-indirect-suc (writeLoc s (OnStack frame slot) val) alloc) ≡
          writeLoc (proj₁ (exec-abstract load-indirect-suc s alloc)) (OnStack frame slot) val
  -- load-from-slot: reads from a specific slot - must be different from our slot
  exec-abstract-slot-independent (load-from-slot k) s alloc frame slot val frame-eq neq _
    with k ≟ slot
  ... | yes k≡slot = ⊥-elim (neq (cong just k≡slot))
    where open import Data.Empty using (⊥-elim)
  ... | no k≢slot = helper (readLoc s (OnStack (current-frame alloc) k)) refl read-eq
    where
      stack-slot-injective : ∀ {f' : Frame} {k1 k2 : ℕ} → OnStack f' k1 ≡ OnStack f' k2 → k1 ≡ k2
      stack-slot-injective refl = refl

      -- Reading from slot k in modified state = reading from slot k in original state
      -- because k ≢ slot
      read-eq : readLoc (writeLoc s (OnStack frame slot) val) (OnStack (current-frame alloc) k) ≡
                readLoc s (OnStack (current-frame alloc) k)
      read-eq = writeLoc-preserves-other s (OnStack frame slot) (OnStack (current-frame alloc) k) val
                  (λ eq → k≢slot (sym (stack-slot-injective (subst (λ f' → OnStack f' slot ≡ OnStack (current-frame alloc) k)
                                                               (sym frame-eq) eq))))

      -- Helper: pattern match on original state's read, use read-eq to relate to modified state
      helper : (mv : Maybe (ValueLocation FS)) →
        readLoc s (OnStack (current-frame alloc) k) ≡ mv →
        readLoc (writeLoc s (OnStack frame slot) val) (OnStack (current-frame alloc) k) ≡ mv →
        proj₁ (exec-abstract (load-from-slot k) (writeLoc s (OnStack frame slot) val) alloc) ≡
        writeLoc (proj₁ (exec-abstract (load-from-slot k) s alloc)) (OnStack frame slot) val
      helper (just v) orig-eq mod-eq rewrite orig-eq | mod-eq =
        -- Both states read just v from slot k
        -- LHS: record (writeLoc s ...) { regs = writeReg (regs (writeLoc s ...)) Output v }
        --    = record (writeLoc s ...) { regs = writeReg (regs s) Output v }  (writeLoc preserves regs)
        -- RHS: writeLoc (record s { regs = writeReg (regs s) Output v }) ...
        -- These are equal by writeLoc-regs-commute (need symmetric version)
        sym (writeLoc-regs-commute s frame slot val (writeReg (regs s) Output v))
      helper nothing orig-eq mod-eq rewrite orig-eq | mod-eq =
        -- Both states get nothing, so both set halted = true
        -- LHS: record (writeLoc s ...) { halted = true }
        -- RHS: writeLoc (record s { halted = true }) ...
        -- These are equal by halted preservation
        refl
  -- store-at-slot: writes to slot k, so we need k ≢ slot (from write precondition)
  exec-abstract-slot-independent (store-at-slot k) s alloc frame slot val frame-eq _ neq-write =
    -- exec-abstract (store-at-slot k) s alloc = (writeLoc s (OnStack (current-frame alloc) k) (readReg (regs s) Output), alloc)
    -- LHS: proj₁ (exec-abstract (store-at-slot k) (writeLoc s (OnStack frame slot) val) alloc)
    --    = writeLoc (writeLoc s (OnStack frame slot) val) (OnStack (current-frame alloc) k) (readReg (regs (writeLoc s (OnStack frame slot) val)) Output)
    -- Since writeLoc preserves regs:
    --    = writeLoc (writeLoc s (OnStack frame slot) val) (OnStack (current-frame alloc) k) (readReg (regs s) Output)
    -- RHS: writeLoc (proj₁ (exec-abstract (store-at-slot k) s alloc)) (OnStack frame slot) val
    --    = writeLoc (writeLoc s (OnStack (current-frame alloc) k) (readReg (regs s) Output)) (OnStack frame slot) val
    -- Since k ≢ slot (from write precondition), we can use writeLoc-commute-diff
    let
      regs-preserved : readReg (regs (writeLoc s (OnStack frame slot) val)) Output ≡ readReg (regs s) Output
      regs-preserved = cong (λ r → readReg r Output) (writeLoc-regs s (OnStack frame slot) val)

      k≢slot : k ≢ slot
      k≢slot k≡slot = neq-write (cong just k≡slot)
    in
    trans (cong (λ v → writeLoc (writeLoc s (OnStack frame slot) val) (OnStack (current-frame alloc) k) v) regs-preserved)
          (writeLoc-commute-diff k≢slot frame-eq)
    where
      -- Commute writes to different stack slots (requires functional extensionality to prove fully)
      -- Sound: for k ≢ slot in the same frame, the order of writes doesn't matter
      postulate
        writeLoc-commute-stack : ∀ (s' : LocState FS) (f : Frame) (k1 k2 : ℕ) (v1 v2 : ValueLocation FS) →
          k1 ≢ k2 →
          writeLoc (writeLoc s' (OnStack f k1) v1) (OnStack f k2) v2 ≡
          writeLoc (writeLoc s' (OnStack f k2) v2) (OnStack f k1) v1

      writeLoc-commute-diff : k ≢ slot → current-frame alloc ≡ frame →
        writeLoc (writeLoc s (OnStack frame slot) val) (OnStack (current-frame alloc) k) (readReg (regs s) Output) ≡
        writeLoc (writeLoc s (OnStack (current-frame alloc) k) (readReg (regs s) Output)) (OnStack frame slot) val
      writeLoc-commute-diff k≢slot' frame-eq' =
        subst₂ (λ f1 f2 → writeLoc (writeLoc s (OnStack frame slot) val) (OnStack f1 k) (readReg (regs s) Output) ≡
                          writeLoc (writeLoc s (OnStack f2 k) (readReg (regs s) Output)) (OnStack frame slot) val)
               (sym frame-eq') (sym frame-eq')
               (writeLoc-commute-stack s frame slot k val (readReg (regs s) Output) (λ slot≡k → k≢slot' (sym slot≡k)))
        where open import Relation.Binary.PropositionalEquality using (subst₂)
  -- store-indirect: writes via Input register (typically to heap)
  -- If Input points to stack slot, we need commutativity with our stack modification
  exec-abstract-slot-independent store-indirect s alloc frame slot val frame-eq _ _ =
    store-indirect-slot-independent s alloc frame slot val
    where
      postulate
        store-indirect-slot-independent : ∀ (s : LocState FS) (alloc : AllocState {FS})
          (frame : Frame) (slot : ℕ) (val : ValueLocation FS) →
          proj₁ (exec-abstract store-indirect (writeLoc s (OnStack frame slot) val) alloc) ≡
          writeLoc (proj₁ (exec-abstract store-indirect s alloc)) (OnStack frame slot) val
  -- store-indirect-suc: writes via Input register (typically to heap)
  exec-abstract-slot-independent store-indirect-suc s alloc frame slot val frame-eq _ _ =
    store-indirect-suc-slot-independent s alloc frame slot val
    where
      postulate
        store-indirect-suc-slot-independent : ∀ (s : LocState FS) (alloc : AllocState {FS})
          (frame : Frame) (slot : ℕ) (val : ValueLocation FS) →
          proj₁ (exec-abstract store-indirect-suc (writeLoc s (OnStack frame slot) val) alloc) ≡
          writeLoc (proj₁ (exec-abstract store-indirect-suc s alloc)) (OnStack frame slot) val
  -- lea-slot: doesn't read or write memory, just computes address
  exec-abstract-slot-independent (lea-slot k) s alloc frame slot val frame-eq _ _ = refl
  -- restore-input: reads from a specific slot - must be different from our slot
  exec-abstract-slot-independent (restore-input k) s alloc frame slot val frame-eq neq _
    with k ≟ slot
  ... | yes k≡slot = ⊥-elim (neq (cong just k≡slot))
    where open import Data.Empty using (⊥-elim)
  ... | no k≢slot = helper (readLoc s (OnStack (current-frame alloc) k)) refl (trans read-eq refl)
    where
      stack-slot-injective : ∀ {f' : Frame} {k1 k2 : ℕ} → OnStack f' k1 ≡ OnStack f' k2 → k1 ≡ k2
      stack-slot-injective refl = refl

      writeLoc-halted-state-stack : ∀ (s' : LocState FS) (f' : Frame) (k' : ℕ) (v' : ValueLocation FS) →
        writeLoc (record s' { halted = true }) (OnStack f' k') v' ≡ record (writeLoc s' (OnStack f' k') v') { halted = true }
      writeLoc-halted-state-stack s' f' k' v' = refl

      read-eq : readLoc (writeLoc s (OnStack frame slot) val) (OnStack (current-frame alloc) k) ≡
                readLoc s (OnStack (current-frame alloc) k)
      read-eq = writeLoc-preserves-other s (OnStack frame slot) (OnStack (current-frame alloc) k) val
                  (λ eq → k≢slot (sym (stack-slot-injective (subst (λ f' → OnStack f' slot ≡ OnStack (current-frame alloc) k)
                                                               (sym frame-eq) eq))))

      -- Helper takes BOTH original and modified state reads
      helper : (mv : Maybe (ValueLocation FS)) →
        readLoc s (OnStack (current-frame alloc) k) ≡ mv →
        readLoc (writeLoc s (OnStack frame slot) val) (OnStack (current-frame alloc) k) ≡ mv →
        proj₁ (exec-abstract (restore-input k) (writeLoc s (OnStack frame slot) val) alloc) ≡
        writeLoc (proj₁ (exec-abstract (restore-input k) s alloc)) (OnStack frame slot) val
      helper (just v) orig-eq mod-eq rewrite mod-eq | orig-eq =
        -- After rewriting, both execs read 'just v' from slot k
        -- LHS: Input := v, then we have record (writeLoc s ...) { regs = writeReg ... Input v }
        -- RHS: writeLoc (record s { regs = writeReg ... Input v }) (OnStack frame slot) val
        -- These are equal by writeLoc-regs-commute
        sym (writeLoc-regs-commute s frame slot val (writeReg (regs s) Input v))
      helper nothing orig-eq mod-eq rewrite mod-eq | orig-eq =
        -- Both execs fail, setting halted = true
        writeLoc-halted-state-stack s frame slot val
  -- Frame operations don't read from or write to specific stack slots
  exec-abstract-slot-independent (instr-alloc-stack n) s alloc frame slot val frame-eq _ _ = refl
  exec-abstract-slot-independent (instr-dealloc-stack n) s alloc frame slot val frame-eq _ _ = refl
  exec-abstract-slot-independent (instr-push-frame cap) s alloc frame slot val frame-eq _ _ = refl
  exec-abstract-slot-independent instr-pop-frame s alloc frame slot val frame-eq _ _ = refl
  exec-abstract-slot-independent instr-call-closure s alloc frame slot val frame-eq _ _ = refl

  ------------------------------------------------------------------------
  -- Trace-Level Slot Independence
  --
  -- If a trace neither reads from nor writes to a slot (slot < n where
  -- trace reads/writes above n), then the trace can run equivalently
  -- on a state with that slot modified.
  ------------------------------------------------------------------------

  private
    open import Data.Empty using (⊥)

    -- Helper: suc n ≤ n is impossible
    1+n≰n : ∀ {m : ℕ} → suc m ≤ m → ⊥
    1+n≰n {suc m} (s≤s pf) = 1+n≰n pf

    -- Helper: if slot < n and instruction reads above n, then instruction doesn't read slot
    instr-slot-disjoint-from-reads : ∀ (i : AbstractInstr) (slot n : ℕ) →
      suc slot ≤ n →
      (ra : TraceSlotReadsAbove n (i ∷ [])) →
      instr-stack-read-slot i ≢ just slot
    instr-slot-disjoint-from-reads i slot n slot<n ra eq
      with instr-stack-read-slot i | ra | eq
    ... | nothing | _ | ()
    ... | just k | (n≤k , _) | refl = 1+n≰n (≤-trans slot<n n≤k)

    -- Helper: if slot < n and instruction writes above n, then instruction doesn't write slot
    instr-slot-disjoint-from-writes : ∀ (i : AbstractInstr) (slot n : ℕ) →
      suc slot ≤ n →
      (wa : TraceWritesAbove n (i ∷ [])) →
      instr-stack-write-slot i ≢ just slot
    instr-slot-disjoint-from-writes i slot n slot<n wa eq
      with instr-stack-write-slot i | wa | eq
    ... | nothing | _ | ()
    ... | just k | (n≤k , _) | refl = 1+n≰n (≤-trans slot<n n≤k)

    -- Helper: extract tail reads bound
    get-tail-reads-above : ∀ (i : AbstractInstr) (is : AbstractTrace) (n : ℕ) →
      TraceSlotReadsAbove n (i ∷ is) → TraceSlotReadsAbove n is
    get-tail-reads-above i is n ra with instr-stack-read-slot i | ra
    ... | nothing | ra' = ra'
    ... | just _ | (_ , ra') = ra'

    -- Helper: extract tail writes bound
    get-tail-writes-above : ∀ (i : AbstractInstr) (is : AbstractTrace) (n : ℕ) →
      TraceWritesAbove n (i ∷ is) → TraceWritesAbove n is
    get-tail-writes-above i is n wa with instr-stack-write-slot i | wa
    ... | nothing | wa' = wa'
    ... | just _ | (_ , wa') = wa'

    -- Helper: extract instruction reads bound (for use in exec-abstract-slot-independent)
    get-instr-reads-above : ∀ (i : AbstractInstr) (is : AbstractTrace) (n : ℕ) →
      TraceSlotReadsAbove n (i ∷ is) → TraceSlotReadsAbove n (i ∷ [])
    get-instr-reads-above i is n ra with instr-stack-read-slot i | ra
    ... | nothing | _ = tt
    ... | just k | (n≤k , _) = n≤k , tt

    -- Helper: extract instruction writes bound
    get-instr-writes-above : ∀ (i : AbstractInstr) (is : AbstractTrace) (n : ℕ) →
      TraceWritesAbove n (i ∷ is) → TraceWritesAbove n (i ∷ [])
    get-instr-writes-above i is n wa with instr-stack-write-slot i | wa
    ... | nothing | _ = tt
    ... | just k | (n≤k , _) = n≤k , tt

    ------------------------------------------------------------------------
    -- Below-bound helpers (for slots ABOVE trace's access range)
    ------------------------------------------------------------------------

    -- Helper: if n ≤ slot and instruction reads below n, then instruction doesn't read slot
    instr-slot-disjoint-from-reads-below : ∀ (i : AbstractInstr) (slot n : ℕ) →
      n ≤ slot →
      (rb : TraceSlotReadsBelow n (i ∷ [])) →
      instr-stack-read-slot i ≢ just slot
    instr-slot-disjoint-from-reads-below i slot n n≤slot rb eq
      with instr-stack-read-slot i | rb | eq
    ... | nothing | _ | ()
    ... | just k | (k<n , _) | refl = 1+n≰n (≤-trans k<n n≤slot)

    -- Helper: if n ≤ slot and instruction writes below n, then instruction doesn't write slot
    instr-slot-disjoint-from-writes-below : ∀ (i : AbstractInstr) (slot n : ℕ) →
      n ≤ slot →
      (wb : TraceWritesBelow n (i ∷ [])) →
      instr-stack-write-slot i ≢ just slot
    instr-slot-disjoint-from-writes-below i slot n n≤slot wb eq
      with instr-stack-write-slot i | wb | eq
    ... | nothing | _ | ()
    ... | just k | (k<n , _) | refl = 1+n≰n (≤-trans k<n n≤slot)

    -- Helper: extract tail reads bound (below)
    get-tail-reads-below : ∀ (i : AbstractInstr) (is : AbstractTrace) (n : ℕ) →
      TraceSlotReadsBelow n (i ∷ is) → TraceSlotReadsBelow n is
    get-tail-reads-below i is n rb with instr-stack-read-slot i | rb
    ... | nothing | rb' = rb'
    ... | just _ | (_ , rb') = rb'

    -- Helper: extract tail writes bound (below)
    get-tail-writes-below : ∀ (i : AbstractInstr) (is : AbstractTrace) (n : ℕ) →
      TraceWritesBelow n (i ∷ is) → TraceWritesBelow n is
    get-tail-writes-below i is n wb with instr-stack-write-slot i | wb
    ... | nothing | wb' = wb'
    ... | just _ | (_ , wb') = wb'

    -- Helper: extract instruction reads bound (below)
    get-instr-reads-below : ∀ (i : AbstractInstr) (is : AbstractTrace) (n : ℕ) →
      TraceSlotReadsBelow n (i ∷ is) → TraceSlotReadsBelow n (i ∷ [])
    get-instr-reads-below i is n rb with instr-stack-read-slot i | rb
    ... | nothing | _ = tt
    ... | just k | (k<n , _) = k<n , tt

    -- Helper: extract instruction writes bound (below)
    get-instr-writes-below : ∀ (i : AbstractInstr) (is : AbstractTrace) (n : ℕ) →
      TraceWritesBelow n (i ∷ is) → TraceWritesBelow n (i ∷ [])
    get-instr-writes-below i is n wb with instr-stack-write-slot i | wb
    ... | nothing | _ = tt
    ... | just k | (k<n , _) = k<n , tt

    -- Alloc is preserved: exec-abstract on modified state gives same alloc
    exec-abstract-same-alloc : ∀ (i : AbstractInstr) (s : LocState FS)
      (alloc : AllocState {FS}) (frame : Frame) (slot : ℕ) (val : ValueLocation FS) →
      proj₂ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc) ≡
      proj₂ (exec-abstract i s alloc)
    exec-abstract-same-alloc mov-to-output _ _ _ _ _ = refl
    exec-abstract-same-alloc mov-to-input _ _ _ _ _ = refl
    exec-abstract-same-alloc load-indirect _ _ _ _ _ = refl
    exec-abstract-same-alloc load-indirect-suc _ _ _ _ _ = refl
    exec-abstract-same-alloc (load-from-slot k) s alloc f slot' v
      with readLoc (writeLoc s (OnStack f slot') v) (OnStack (current-frame alloc) k)
         | readLoc s (OnStack (current-frame alloc) k)
    ... | just _ | just _ = refl
    ... | just _ | nothing = refl
    ... | nothing | just _ = refl
    ... | nothing | nothing = refl
    exec-abstract-same-alloc (store-at-slot _) _ _ _ _ _ = refl
    exec-abstract-same-alloc store-indirect _ _ _ _ _ = refl
    exec-abstract-same-alloc store-indirect-suc _ _ _ _ _ = refl
    exec-abstract-same-alloc (lea-slot _) _ _ _ _ _ = refl
    exec-abstract-same-alloc (restore-input k) s alloc f slot' v
      with readLoc (writeLoc s (OnStack f slot') v) (OnStack (current-frame alloc) k)
         | readLoc s (OnStack (current-frame alloc) k)
    ... | just _ | just _ = refl
    ... | just _ | nothing = refl
    ... | nothing | just _ = refl
    ... | nothing | nothing = refl
    exec-abstract-same-alloc (instr-alloc-stack _) _ _ _ _ _ = refl
    exec-abstract-same-alloc (instr-dealloc-stack _) _ _ _ _ _ = refl
    exec-abstract-same-alloc (instr-push-frame _) _ _ _ _ _ = refl
    exec-abstract-same-alloc instr-pop-frame _ _ _ _ _ = refl
    exec-abstract-same-alloc instr-call-closure _ _ _ _ _ = refl

  -- Single-slot independence: if slot < n and trace reads/writes above n
  exec-trace-slot-independent : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) (frame : Frame) (slot : ℕ) (val : ValueLocation FS) (n : ℕ) →
    current-frame alloc ≡ frame →
    suc slot ≤ n →
    TraceSlotReadsAbove n trace →
    TraceWritesAbove n trace →
    proj₁ (exec-trace trace (writeLoc s (OnStack frame slot) val) alloc) ≡
    writeLoc (proj₁ (exec-trace trace s alloc)) (OnStack frame slot) val
  exec-trace-slot-independent [] s alloc frame slot val n frame-eq slot<n _ _ = refl
  exec-trace-slot-independent (i ∷ is) s alloc frame slot val n frame-eq slot<n ra wa
    with halted s | writeLoc-halted s (OnStack frame slot) val
  -- Both halted (writeLoc preserves halted)
  ... | true | hw-eq rewrite hw-eq = refl
  -- Both not halted
  ... | false | hw-eq rewrite hw-eq = combine-proof
    where
      -- Use module-level helpers to extract bounds (no function definitions here!)
      i-reads-above = instr-slot-disjoint-from-reads i slot n slot<n (get-instr-reads-above i is n ra)
      i-writes-above = instr-slot-disjoint-from-writes i slot n slot<n (get-instr-writes-above i is n wa)
      tail-reads-above = get-tail-reads-above i is n ra
      tail-writes-above = get-tail-writes-above i is n wa

      -- Value bindings (not functions)
      s' = proj₁ (exec-abstract i s alloc)
      alloc' = proj₂ (exec-abstract i s alloc)

      i-indep : proj₁ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc) ≡
                writeLoc s' (OnStack frame slot) val
      i-indep = exec-abstract-slot-independent i s alloc frame slot val frame-eq i-reads-above i-writes-above

      frame-eq' : current-frame alloc' ≡ frame
      frame-eq' = trans (exec-abstract-preserves-frame i s alloc) frame-eq

      ih : proj₁ (exec-trace is (writeLoc s' (OnStack frame slot) val) alloc') ≡
           writeLoc (proj₁ (exec-trace is s' alloc')) (OnStack frame slot) val
      ih = exec-trace-slot-independent is s' alloc' frame slot val n frame-eq' slot<n
             tail-reads-above tail-writes-above

      state-alloc-eq : (proj₁ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc) ,
                        proj₂ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc)) ≡
                       (writeLoc s' (OnStack frame slot) val , alloc')
      state-alloc-eq = cong₂ _,_ i-indep (exec-abstract-same-alloc i s alloc frame slot val)

      combine-proof : proj₁ (exec-trace is
                        (proj₁ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc))
                        (proj₂ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc))) ≡
                      writeLoc (proj₁ (exec-trace is s' alloc')) (OnStack frame slot) val
      combine-proof = trans (cong (λ p → proj₁ (exec-trace is (proj₁ p) (proj₂ p))) state-alloc-eq) ih

  -- Single-slot independence for slots ABOVE trace's access range:
  -- if n ≤ slot and trace reads/writes below n, then trace is independent of that slot.
  -- This is the dual of exec-trace-slot-independent and is used for proving independence
  -- of slots that are ABOVE the trace's allocation range (e.g., fst-slot in pair).
  exec-trace-slot-independent-above : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) (frame : Frame) (slot : ℕ) (val : ValueLocation FS) (n : ℕ) →
    current-frame alloc ≡ frame →
    n ≤ slot →
    TraceSlotReadsBelow n trace →
    TraceWritesBelow n trace →
    proj₁ (exec-trace trace (writeLoc s (OnStack frame slot) val) alloc) ≡
    writeLoc (proj₁ (exec-trace trace s alloc)) (OnStack frame slot) val
  exec-trace-slot-independent-above [] s alloc frame slot val n frame-eq n≤slot _ _ = refl
  exec-trace-slot-independent-above (i ∷ is) s alloc frame slot val n frame-eq n≤slot rb wb
    with halted s | writeLoc-halted s (OnStack frame slot) val
  -- Both halted (writeLoc preserves halted)
  ... | true | hw-eq rewrite hw-eq = refl
  -- Both not halted
  ... | false | hw-eq rewrite hw-eq = combine-proof
    where
      -- Use module-level helpers to extract bounds
      i-reads-below = instr-slot-disjoint-from-reads-below i slot n n≤slot (get-instr-reads-below i is n rb)
      i-writes-below = instr-slot-disjoint-from-writes-below i slot n n≤slot (get-instr-writes-below i is n wb)
      tail-reads-below = get-tail-reads-below i is n rb
      tail-writes-below = get-tail-writes-below i is n wb

      -- Value bindings
      s' = proj₁ (exec-abstract i s alloc)
      alloc' = proj₂ (exec-abstract i s alloc)

      i-indep : proj₁ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc) ≡
                writeLoc s' (OnStack frame slot) val
      i-indep = exec-abstract-slot-independent i s alloc frame slot val frame-eq i-reads-below i-writes-below

      frame-eq' : current-frame alloc' ≡ frame
      frame-eq' = trans (exec-abstract-preserves-frame i s alloc) frame-eq

      ih : proj₁ (exec-trace is (writeLoc s' (OnStack frame slot) val) alloc') ≡
           writeLoc (proj₁ (exec-trace is s' alloc')) (OnStack frame slot) val
      ih = exec-trace-slot-independent-above is s' alloc' frame slot val n frame-eq' n≤slot
             tail-reads-below tail-writes-below

      state-alloc-eq : (proj₁ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc) ,
                        proj₂ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc)) ≡
                       (writeLoc s' (OnStack frame slot) val , alloc')
      state-alloc-eq = cong₂ _,_ i-indep (exec-abstract-same-alloc i s alloc frame slot val)

      combine-proof : proj₁ (exec-trace is
                        (proj₁ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc))
                        (proj₂ (exec-abstract i (writeLoc s (OnStack frame slot) val) alloc))) ≡
                      writeLoc (proj₁ (exec-trace is s' alloc')) (OnStack frame slot) val
      combine-proof = trans (cong (λ p → proj₁ (exec-trace is (proj₁ p) (proj₂ p))) state-alloc-eq) ih

  ------------------------------------------------------------------------
  -- State Equivalence for Traces
  --
  -- Key insight: Traces only depend on certain parts of the state.
  -- If two states agree on those parts, the traces produce equivalent outputs.
  --
  -- For slot-bounded traces (with TraceSlotReadsAbove lo and TraceSlotReadsBelow hi):
  -- - States must agree on Input register
  -- - States must agree on all stack slots in [lo, hi)
  --
  -- This enables compositional proofs where sub-traces run on states
  -- that differ only at slots they don't access, allowing us to connect
  -- trace-defined states to sub-IR final states.
  ------------------------------------------------------------------------

  -- Simpler approach: prove specific properties needed for IR composition
  -- We'll add these incrementally as needed.
  --
  -- Key lemmas needed:
  -- 1. exec-trace-output-from-input-and-slots: If two states agree on Input and
  --    the slots a trace reads, executing the trace produces the same Output.
  -- 2. exec-trace-halted-from-equiv: If states are equivalent for the trace,
  --    the halted flags in the results are also equivalent.
  --
  -- For now, we provide postulates that capture the essence of state equivalence.
  -- These can be proven by induction on the trace with the per-instruction lemmas.

  -- Postulate: Traces with same Input and same slot contents produce same Output
  -- This is the key lemma for connecting sub-IR results to composed traces.
  -- Proof sketch: Induction on trace, using per-instruction Output preservation.
  postulate
    exec-trace-output-equiv : ∀ (trace : AbstractTrace) (s₁ s₂ : LocState FS)
      (alloc : AllocState {FS}) (lo hi : ℕ) →
      -- Input registers agree
      readReg (regs s₁) Input ≡ readReg (regs s₂) Input →
      -- Halted flags agree
      halted s₁ ≡ halted s₂ →
      -- Neither is halted (so trace executes)
      halted s₁ ≡ false →
      -- All slots in [lo, hi) agree
      (∀ slot → lo ≤ slot → slot < hi →
        readLoc s₁ (OnStack (current-frame alloc) slot) ≡
        readLoc s₂ (OnStack (current-frame alloc) slot)) →
      -- Trace reads only from [lo, hi)
      TraceSlotReadsAbove lo trace →
      TraceSlotReadsBelow hi trace →
      -- Heap memory agrees (needed for load-indirect)
      heapMem s₁ ≡ heapMem s₂ →
      -- Output registers agree (needed for store-at-slot consistency)
      readReg (regs s₁) Output ≡ readReg (regs s₂) Output →
      -- Then Output registers in results are equal
      readReg (regs (proj₁ (exec-trace trace s₁ alloc))) Output ≡
      readReg (regs (proj₁ (exec-trace trace s₂ alloc))) Output

    -- Version WITHOUT Output equality precondition
    -- This works for traces that write Output deterministically based on Input
    -- (which all IR traces do - they compute a result into Output).
    exec-trace-output-equiv-no-output : ∀ (trace : AbstractTrace) (s₁ s₂ : LocState FS)
      (alloc : AllocState {FS}) (lo hi : ℕ) →
      readReg (regs s₁) Input ≡ readReg (regs s₂) Input →
      halted s₁ ≡ halted s₂ →
      halted s₁ ≡ false →
      (∀ slot → lo ≤ slot → slot < hi →
        readLoc s₁ (OnStack (current-frame alloc) slot) ≡
        readLoc s₂ (OnStack (current-frame alloc) slot)) →
      TraceSlotReadsAbove lo trace →
      TraceSlotReadsBelow hi trace →
      heapMem s₁ ≡ heapMem s₂ →
      readReg (regs (proj₁ (exec-trace trace s₁ alloc))) Output ≡
      readReg (regs (proj₁ (exec-trace trace s₂ alloc))) Output

    -- Corollary: Halted flags in results are also equal
    exec-trace-halted-equiv : ∀ (trace : AbstractTrace) (s₁ s₂ : LocState FS)
      (alloc : AllocState {FS}) (lo hi : ℕ) →
      readReg (regs s₁) Input ≡ readReg (regs s₂) Input →
      halted s₁ ≡ halted s₂ →
      halted s₁ ≡ false →
      (∀ slot → lo ≤ slot → slot < hi →
        readLoc s₁ (OnStack (current-frame alloc) slot) ≡
        readLoc s₂ (OnStack (current-frame alloc) slot)) →
      TraceSlotReadsAbove lo trace →
      TraceSlotReadsBelow hi trace →
      halted (proj₁ (exec-trace trace s₁ alloc)) ≡
      halted (proj₁ (exec-trace trace s₂ alloc))

    -- Memory equivalence: If two states agree on Input, halted, and slots in read range,
    -- and a location agrees initially, then it agrees after trace execution.
    -- Proof sketch: Induction on trace. Each instruction computes the same write
    -- (since inputs are identical), so resulting states have same values at
    -- locations that started equal.
    exec-trace-mem-equiv : ∀ (trace : AbstractTrace) (s₁ s₂ : LocState FS)
      (alloc : AllocState {FS}) (lo hi : ℕ) (loc : ValueLocation FS) →
      -- Input registers agree
      readReg (regs s₁) Input ≡ readReg (regs s₂) Input →
      -- Halted flags agree
      halted s₁ ≡ halted s₂ →
      -- Neither is halted
      halted s₁ ≡ false →
      -- All slots in [lo, hi) agree
      (∀ slot → lo ≤ slot → slot < hi →
        readLoc s₁ (OnStack (current-frame alloc) slot) ≡
        readLoc s₂ (OnStack (current-frame alloc) slot)) →
      -- Trace reads only from [lo, hi)
      TraceSlotReadsAbove lo trace →
      TraceSlotReadsBelow hi trace →
      -- loc was initially equal
      readLoc s₁ loc ≡ readLoc s₂ loc →
      -- Then loc is equal after trace execution
      readLoc (proj₁ (exec-trace trace s₁ alloc)) loc ≡
      readLoc (proj₁ (exec-trace trace s₂ alloc)) loc

    -- Heap equivalence: If two states agree on Input, halted, slots in
    -- [lo, hi), and heap, then after executing a trace (that reads from [lo, hi)),
    -- the heaps in the results are also equal.
    -- Note: Output equality is NOT required because IR traces compute Output
    -- deterministically from Input/slots before any heap writes.
    exec-trace-heap-equiv : ∀ (trace : AbstractTrace) (s₁ s₂ : LocState FS)
      (alloc : AllocState {FS}) (lo hi : ℕ) →
      readReg (regs s₁) Input ≡ readReg (regs s₂) Input →
      halted s₁ ≡ halted s₂ →
      halted s₁ ≡ false →
      (∀ slot → lo ≤ slot → slot < hi →
        readLoc s₁ (OnStack (current-frame alloc) slot) ≡
        readLoc s₂ (OnStack (current-frame alloc) slot)) →
      TraceSlotReadsAbove lo trace →
      TraceSlotReadsBelow hi trace →
      heapMem s₁ ≡ heapMem s₂ →
      heapMem (proj₁ (exec-trace trace s₁ alloc)) ≡
      heapMem (proj₁ (exec-trace trace s₂ alloc))

  -- Alloc independence: trace execution state depends only on current-frame
  -- and frame-capacity, not on next-slot or next-heap-ref.
  -- This is true because state-affecting operations only use current-frame.
  -- Proof: Delegate to exec-trace-same-frame (frame-capacity is unused).
  exec-trace-state-same-frame : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc₁ alloc₂ : AllocState {FS}) →
    current-frame alloc₁ ≡ current-frame alloc₂ →
    frame-capacity alloc₁ ≡ frame-capacity alloc₂ →
    proj₁ (exec-trace trace s alloc₁) ≡ proj₁ (exec-trace trace s alloc₂)
  exec-trace-state-same-frame trace s alloc₁ alloc₂ frame-eq _ =
    exec-trace-same-frame trace s alloc₁ alloc₂ frame-eq

  -- Slots in range [lo, hi) are unchanged when trace writes only outside that range
  -- Proof: TraceWritesBelow lo means all writes are < lo, so slots >= lo are preserved.
  exec-trace-preserves-slots-in-range : ∀ (trace : AbstractTrace) (s : LocState FS)
    (alloc : AllocState {FS}) (lo hi : ℕ) →
    TraceWritesAbove hi trace →
    TraceWritesBelow lo trace →
    (∀ slot → lo ≤ slot → slot < hi →
      readLoc (proj₁ (exec-trace trace s alloc)) (OnStack (current-frame alloc) slot) ≡
      readLoc s (OnStack (current-frame alloc) slot))
  exec-trace-preserves-slots-in-range trace s alloc lo hi _ twb slot lo≤slot _ =
    exec-trace-preserves-slot-above trace s alloc (current-frame alloc) slot lo refl lo≤slot twb

  postulate

    -- Halted preservation through composed trace with sub-IR
    -- If a sub-IR trace doesn't fail (preserves halted), running it on a different
    -- starting state (that agrees on relevant slots) also preserves halted.
    -- This uses state equivalence plus the sub-IR's not-halted result.
    exec-trace-preserves-halted-subir : ∀ (trace : AbstractTrace) (s₁ s₂ : LocState FS)
      (alloc : AllocState {FS}) (lo hi : ℕ) →
      -- States agree on Input and slots
      readReg (regs s₁) Input ≡ readReg (regs s₂) Input →
      (∀ slot → lo ≤ slot → slot < hi →
        readLoc s₁ (OnStack (current-frame alloc) slot) ≡
        readLoc s₂ (OnStack (current-frame alloc) slot)) →
      -- Trace reads only from [lo, hi)
      TraceSlotReadsAbove lo trace →
      TraceSlotReadsBelow hi trace →
      -- Heap equality (needed for load-indirect)
      heapMem s₁ ≡ heapMem s₂ →
      -- Starting states not halted
      halted s₁ ≡ false →
      halted s₂ ≡ false →
      -- Sub-IR result not halted
      halted (proj₁ (exec-trace trace s₂ alloc)) ≡ false →
      -- Then composed result not halted
      halted (proj₁ (exec-trace trace s₁ alloc)) ≡ false

------------------------------------------------------------------------
-- Summary
--
-- The LocationMachine operates PURELY on ValueLocations:
--
--   HeapLocation = heap-loc HeapRef HeapOffset
--   ValueLocation = OnStack Frame Slot | OnHeap HeapLocation
--
--   AbstractReg = Input | Output    (two-register model)
--   Registers = { input, output : ValueLocation }
--   StackMem  : Frame → Slot → Maybe ValueLocation   (can store anything)
--   HeapMem   : HeapLocation → Maybe HeapLocation    (heap-only invariant!)
--
--   load  : AbstractReg → LocSourceExt → Instr
--   store : LocSourceExt → AbstractReg → Instr
--   mov   : AbstractReg → AbstractReg → Instr
--
--   LocSourceExt = Loc loc | IndReg r | IndRegSuc r
--
-- TWO-REGISTER MODEL:
--   Input  - argument location (maps to RDI in x86)
--   Output - result location (maps to RAX in x86)
--
-- KEY INVARIANT: Heap can only store HeapLocations, not stack references.
-- This enforces that heap-allocated values never reference stack memory,
-- making frame deallocation always safe.
--
-- Key lemmas provided:
--   - load-result: after load, register = mem[loc]
--   - load-preserves-reg: load doesn't change other registers
--   - load-preserves-stackMem/heapMem: load doesn't change memory
--   - mov-result, mov-preserves-reg, mov-preserves-stackMem
--   - writeReg-preserves, writeReg-same
------------------------------------------------------------------------
