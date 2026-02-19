------------------------------------------------------------------------
-- Once.Backend.Common.SlotMachine
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

module Once.Backend.Common.SlotMachine where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

-- Import FrameSemantics for Frame type
open import Once.Backend.Common.FrameSemantics using (FrameSemantics)

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
-- ValueLocation: Where a value lives
------------------------------------------------------------------------

data ValueLocation (FS : FrameSemantics) : Set where
  OnStack : FrameSemantics.Frame FS → Slot → ValueLocation FS
  OnHeap  : HeapRef → HeapOffset → ValueLocation FS

-- | Successor location (for accessing pair.snd, closure.code-ptr, etc.)
sucLoc : ∀ {FS} → ValueLocation FS → ValueLocation FS
sucLoc (OnStack f k) = OnStack f (suc k)
sucLoc (OnHeap r o)  = OnHeap r (suc o)

-- | Offset location by n slots (for unboxed multi-slot values)
-- Note: n + k so that offsetLoc _ 1 = sucLoc definitionally
offsetLoc : ∀ {FS} → ValueLocation FS → ℕ → ValueLocation FS
offsetLoc (OnStack f k) n = OnStack f (n + k)
offsetLoc (OnHeap r o) n  = OnHeap r (n + o)

------------------------------------------------------------------------
-- Memory: Stores Locations (not Words)
------------------------------------------------------------------------

StackMem : (FS : FrameSemantics) → Set
StackMem FS = FrameSemantics.Frame FS → Slot → Maybe (ValueLocation FS)

HeapMem : (FS : FrameSemantics) → Set
HeapMem FS = HeapRef → HeapOffset → Maybe (ValueLocation FS)

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
    heapMem : HeapMem FS
    halted : Bool

open LocState public

------------------------------------------------------------------------
-- Memory Operations
------------------------------------------------------------------------

module MemOps {FS : FrameSemantics} where
  open FrameSemantics FS

  -- | Read a Location from memory
  readLoc : LocState FS → ValueLocation FS → Maybe (ValueLocation FS)
  readLoc s (OnStack f k) = stackMem s f k
  readLoc s (OnHeap r o)  = heapMem s r o

  -- | Write a Location to stack memory
  writeStackMem : StackMem FS → Frame → Slot → ValueLocation FS → StackMem FS
  writeStackMem mem f k v f' k' with f ≟F f' | k ≟ k'
  ... | yes _ | yes _ = just v
  ... | _     | _     = mem f' k'

  -- | Write a Location to heap memory
  writeHeapMem : HeapMem FS → HeapRef → HeapOffset → ValueLocation FS → HeapMem FS
  writeHeapMem mem r o v r' o' with r ≟H r' | o ≟ o'
  ... | yes _ | yes _ = just v
  ... | _     | _     = mem r' o'

  -- | Write a Location to memory
  writeLoc : LocState FS → ValueLocation FS → ValueLocation FS → LocState FS
  writeLoc s (OnStack f k) v = record s { stackMem = writeStackMem (stackMem s) f k v }
  writeLoc s (OnHeap r o) v = record s { heapMem = writeHeapMem (heapMem s) r o v }

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
  readLoc-stackMem-eq s₁ s₂ (OnHeap r o) stack-eq heap-eq =
    cong (λ m → m r o) heap-eq

------------------------------------------------------------------------
-- Summary
--
-- The LocationMachine operates PURELY on ValueLocations:
--
--   ValueLocation = OnStack Frame Slot | OnHeap HeapRef HeapOffset
--
--   Registers : RegId → ValueLocation
--   Memory    : ValueLocation → Maybe ValueLocation
--
--   load  : RegId → LocSourceExt → Instr
--   store : LocSourceExt → RegId → Instr
--   mov   : RegId → RegId → Instr
--
--   LocSourceExt = Loc loc | IndReg r | IndRegSuc r
--
-- Key lemmas provided:
--   - load-result: after load, register = mem[loc]
--   - load-preserves-reg: load doesn't change other registers
--   - load-preserves-stackMem/heapMem: load doesn't change memory
--   - mov-result, mov-preserves-reg, mov-preserves-stackMem
--   - writeReg-preserves, writeReg-same
------------------------------------------------------------------------
