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

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

-- Import FrameSemantics for Frame type
open import Once.CCC.FrameSemantics using (FrameSemantics)

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
------------------------------------------------------------------------

data RegId : Set where
  RAX RDI RSI R12 R14 R15 : RegId

-- Decidable equality for RegId
_≟R_ : (r₁ r₂ : RegId) → Dec (r₁ ≡ r₂)
RAX ≟R RAX = yes refl
RAX ≟R RDI = no (λ ())
RAX ≟R RSI = no (λ ())
RAX ≟R R12 = no (λ ())
RAX ≟R R14 = no (λ ())
RAX ≟R R15 = no (λ ())
RDI ≟R RAX = no (λ ())
RDI ≟R RDI = yes refl
RDI ≟R RSI = no (λ ())
RDI ≟R R12 = no (λ ())
RDI ≟R R14 = no (λ ())
RDI ≟R R15 = no (λ ())
RSI ≟R RAX = no (λ ())
RSI ≟R RDI = no (λ ())
RSI ≟R RSI = yes refl
RSI ≟R R12 = no (λ ())
RSI ≟R R14 = no (λ ())
RSI ≟R R15 = no (λ ())
R12 ≟R RAX = no (λ ())
R12 ≟R RDI = no (λ ())
R12 ≟R RSI = no (λ ())
R12 ≟R R12 = yes refl
R12 ≟R R14 = no (λ ())
R12 ≟R R15 = no (λ ())
R14 ≟R RAX = no (λ ())
R14 ≟R RDI = no (λ ())
R14 ≟R RSI = no (λ ())
R14 ≟R R12 = no (λ ())
R14 ≟R R14 = yes refl
R14 ≟R R15 = no (λ ())
R15 ≟R RAX = no (λ ())
R15 ≟R RDI = no (λ ())
R15 ≟R RSI = no (λ ())
R15 ≟R R12 = no (λ ())
R15 ≟R R14 = no (λ ())
R15 ≟R R15 = yes refl

record Registers (FS : FrameSemantics) : Set where
  constructor mkRegs
  field
    rax rdi rsi r12 r14 r15 : ValueLocation FS

open Registers public

readReg : ∀ {FS} → Registers FS → RegId → ValueLocation FS
readReg r RAX = rax r
readReg r RDI = rdi r
readReg r RSI = rsi r
readReg r R12 = r12 r
readReg r R14 = r14 r
readReg r R15 = r15 r

writeReg : ∀ {FS} → Registers FS → RegId → ValueLocation FS → Registers FS
writeReg r RAX v = record r { rax = v }
writeReg r RDI v = record r { rdi = v }
writeReg r RSI v = record r { rsi = v }
writeReg r R12 v = record r { r12 = v }
writeReg r R14 v = record r { r14 = v }
writeReg r R15 v = record r { r15 = v }

-- Key lemma: writing to one register preserves others
writeReg-preserves : ∀ {FS} (regs : Registers FS) dst r v →
  r ≢ dst →
  readReg (writeReg regs dst v) r ≡ readReg regs r
writeReg-preserves regs RAX RAX v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs RAX RDI v r≢dst = refl
writeReg-preserves regs RAX RSI v r≢dst = refl
writeReg-preserves regs RAX R12 v r≢dst = refl
writeReg-preserves regs RAX R14 v r≢dst = refl
writeReg-preserves regs RAX R15 v r≢dst = refl
writeReg-preserves regs RDI RAX v r≢dst = refl
writeReg-preserves regs RDI RDI v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs RDI RSI v r≢dst = refl
writeReg-preserves regs RDI R12 v r≢dst = refl
writeReg-preserves regs RDI R14 v r≢dst = refl
writeReg-preserves regs RDI R15 v r≢dst = refl
writeReg-preserves regs RSI RAX v r≢dst = refl
writeReg-preserves regs RSI RDI v r≢dst = refl
writeReg-preserves regs RSI RSI v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs RSI R12 v r≢dst = refl
writeReg-preserves regs RSI R14 v r≢dst = refl
writeReg-preserves regs RSI R15 v r≢dst = refl
writeReg-preserves regs R12 RAX v r≢dst = refl
writeReg-preserves regs R12 RDI v r≢dst = refl
writeReg-preserves regs R12 RSI v r≢dst = refl
writeReg-preserves regs R12 R12 v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs R12 R14 v r≢dst = refl
writeReg-preserves regs R12 R15 v r≢dst = refl
writeReg-preserves regs R14 RAX v r≢dst = refl
writeReg-preserves regs R14 RDI v r≢dst = refl
writeReg-preserves regs R14 RSI v r≢dst = refl
writeReg-preserves regs R14 R12 v r≢dst = refl
writeReg-preserves regs R14 R14 v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs R14 R15 v r≢dst = refl
writeReg-preserves regs R15 RAX v r≢dst = refl
writeReg-preserves regs R15 RDI v r≢dst = refl
writeReg-preserves regs R15 RSI v r≢dst = refl
writeReg-preserves regs R15 R12 v r≢dst = refl
writeReg-preserves regs R15 R14 v r≢dst = refl
writeReg-preserves regs R15 R15 v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)

-- Key lemma: writing to a register and reading it back gives the written value
writeReg-same : ∀ {FS} (regs : Registers FS) dst v →
  readReg (writeReg regs dst v) dst ≡ v
writeReg-same regs RAX v = refl
writeReg-same regs RDI v = refl
writeReg-same regs RSI v = refl
writeReg-same regs R12 v = refl
writeReg-same regs R14 v = refl
writeReg-same regs R15 v = refl

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

------------------------------------------------------------------------
-- Location Source
------------------------------------------------------------------------

data LocSourceExt (FS : FrameSemantics) : Set where
  Loc : ValueLocation FS → LocSourceExt FS
  IndReg : RegId → LocSourceExt FS
  IndRegSuc : RegId → LocSourceExt FS

resolveSourceExt : ∀ {FS} → Registers FS → LocSourceExt FS → ValueLocation FS
resolveSourceExt regs (Loc loc) = loc
resolveSourceExt regs (IndReg r) = readReg regs r
resolveSourceExt regs (IndRegSuc r) = sucLoc (readReg regs r)

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

data Instr (FS : FrameSemantics) : Set where
  load : RegId → LocSourceExt FS → Instr FS
  store : LocSourceExt FS → RegId → Instr FS
  mov : RegId → RegId → Instr FS

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
    where
      just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
      just-injective refl = refl
  ... | nothing | nothing | _ = refl
  ... | just _ | nothing | ()
  ... | nothing | just _ | ()

------------------------------------------------------------------------
-- Summary
--
-- The LocationMachine operates PURELY on ValueLocations:
--
--   HeapLocation = heap-loc HeapRef HeapOffset
--   ValueLocation = OnStack Frame Slot | OnHeap HeapLocation
--
--   Registers : RegId → ValueLocation
--   StackMem  : Frame → Slot → Maybe ValueLocation   (can store anything)
--   HeapMem   : HeapLocation → Maybe HeapLocation    (heap-only invariant!)
--
--   load  : RegId → LocSourceExt → Instr
--   store : LocSourceExt → RegId → Instr
--   mov   : RegId → RegId → Instr
--
--   LocSourceExt = Loc loc | IndReg r | IndRegSuc r
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
