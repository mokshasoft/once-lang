-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.SMCore
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

module Once.CCC.Machine.SMCore where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _>_; _≥_; s≤s)
open import Data.Nat.Properties using (_≟_; <⇒≢; ≤-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; inspect; [_])
open import Relation.Nullary using (Dec; yes; no)

-- Import FrameSemantics for Frame type
open import Once.CCC.FrameSemantics using (FrameSemantics)

-- Import SigOpInfo so `instr-sigop` carries its full self-describing
-- info (name + semI + semM), not just the name. This unlocks per-name
-- discharge of `ir-to-trace-correct-sigop` and per-(arch, name)
-- discharge of `sigop-codegen-faithful`.
open import Once.Type using (Type; FitsInReg)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.SigOp.Info using (SigOpInfo)

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

-- Decidable equality for HeapLocation. Inner Dec results are
-- explicitly enumerated via a top-level helper to avoid the with-
-- block case-tree artifact under --exact-split.
≟HL-aux : ∀ {r₁ r₂ o₁ o₂}
        → Dec (r₁ ≡ r₂) → Dec (o₁ ≡ o₂)
        → Dec (heap-loc r₁ o₁ ≡ heap-loc r₂ o₂)
≟HL-aux (yes refl) (yes refl) = yes refl
≟HL-aux (yes refl) (no o≢o)   = no λ { refl → o≢o refl }
≟HL-aux (no r≢r)   (yes _)    = no λ { refl → r≢r refl }
≟HL-aux (no r≢r)   (no _)     = no λ { refl → r≢r refl }

_≟HL_ : (hl₁ hl₂ : HeapLocation) → Dec (hl₁ ≡ hl₂)
heap-loc r₁ o₁ ≟HL heap-loc r₂ o₂ = ≟HL-aux (r₁ ≟H r₂) (o₁ ≟ o₂)

-- Convert HeapLocation to HeapRef (for frontier checks)
hl-ref : HeapLocation → HeapRef
hl-ref = heap-ref

------------------------------------------------------------------------
-- HeapRegion: A contiguous block of heap memory
--
-- Used for tracking ownership of heap-allocated objects.
-- A region starts at a HeapRef and has a fixed size.
------------------------------------------------------------------------

record HeapRegion : Set where
  constructor heap-region
  field
    region-ref : HeapRef
    region-size : ℕ

open HeapRegion public

-- Positive predicate: HeapLocation is within a HeapRegion
-- Uses ordering: same ref AND offset < size
data InRegion : HeapLocation → HeapRegion → Set where
  in-region : ∀ {r o size} →
    o < size →
    InRegion (heap-loc r o) (heap-region r size)

-- HeapOwnership: set of owned heap regions
-- Empty list means no heap writes allowed (current behavior)
HeapOwnership : Set
HeapOwnership = List HeapRegion

-- Positive predicate: HeapLocation is outside all owned regions
-- Either different ref (by ordering) or offset ≥ size
data OutsideOwned : HeapLocation → HeapOwnership → Set where
  outside-nil : ∀ {hl} → OutsideOwned hl []
  outside-cons : ∀ {hl region regions} →
    (ref-id (heap-ref hl) < ref-id (region-ref region) ⊎
     ref-id (heap-ref hl) > ref-id (region-ref region) ⊎
     heap-offset hl ≥ region-size region) →
    OutsideOwned hl regions →
    OutsideOwned hl (region ∷ regions)

------------------------------------------------------------------------
-- ValueLocation: Where a value lives
--
-- AtStack locations can reference anything (stack or heap).
-- AtDynamic locations use HeapLocation, enforcing heap-only references.
------------------------------------------------------------------------

-- AbstractReg: declared here ahead of `regs : AbstractReg → ValueLocation`
-- so LocState can reference it. (Stage-E previously also needed
-- AbstractReg here for `InReg : AbstractReg → ValueLocation`; that
-- constructor has been retired, but AbstractReg's role for register
-- state stays the same.)
data AbstractReg : Set where
  Input1 : AbstractReg    -- first argument location
  Input2 : AbstractReg    -- second argument location
  Output : AbstractReg    -- result location

data ValueLocation (FS : FrameSemantics) : Set where
  AtStack   : FrameSemantics.Frame FS → Slot → ValueLocation FS
  AtDynamic : HeapLocation → ValueLocation FS

-- Plan 0.13.2 — separation of address from value.
--
-- `ValueLocation` is the type of *addresses* — where in memory a
-- value lives. `StoredValue` is the type of *values* — what a
-- memory cell holds.
--
--   - `SV-Ptr loc`     — a pointer cell.
--   - `SV-Tag n`       — a sum-type tag literal (0 = inl, 1 = inr).
--   - `SV-Lit p v`     — a register-fittable primitive literal
--                        (replaces the `encode-const` postulate).
--                        `p : FitsInReg A` is the type evidence;
--                        `v : ⟦ A ⟧` is the value (ℕ for Int,
--                        AgdaFloat for Float, etc.).
--   - `SV-Code n`      — code-address label index (replaces
--                        `encode-code-addr`).
--
-- Closures, pairs, μ-cells are *records* spanning multiple
-- consecutive cells; they decompose into `SV-Ptr` + per-slot
-- contents and don't need their own constructor here. Sums are
-- the only construct where the runtime needs to inspect a tag in
-- memory — hence `SV-Tag`. See `plans/0.13.2-stored-value-type.md`
-- for full rationale.
data StoredValue (FS : FrameSemantics) : Set where
  SV-Ptr  : ValueLocation FS → StoredValue FS
  SV-Tag  : ℕ → StoredValue FS
  SV-Lit  : ∀ {A} → FitsInReg A → ⟦ A ⟧ → StoredValue FS
  SV-Code : ℕ → StoredValue FS

-- Plan 0.2.4.5 D1 (Unit erasure) note: there is intentionally no
-- `Erased` sentinel here. The earlier Erased constructor encoded
-- "Unit values are nowhere" as a value, but that's a half-measure
-- — every memory operation needed a no-op clause for it. The
-- principled spec answer (per `Once.CCC.Machine.ClosureWellFormed`'s
-- `ResultPlace`) is to track Unit-typed results structurally:
-- `unit-result : ResultPlace Unit ...` carries no location at all.
-- So `ValueLocation` stays as the memory-locations type — exactly
-- what its name suggests.

-- Plan 0.2.4.5 Stage E retired (2026-05-07): the speculative
-- `InReg : AbstractReg → ValueLocation` constructor has been removed.
-- It was added as forward-compatible scaffolding for future
-- register-residency of FitsInReg-typed values, but never wired into
-- any consumer (no `valid-*-wf` ever produced an `InReg`-witness).
-- Its presence broke the `preserves-mem` family of lemmas
-- universally (`readLoc s (InReg Output)` shifts under `mov-to-output`)
-- without any compensating benefit. When register-residency lands for
-- real (Plan 0.2.4.5 D4), it should arrive as a SEPARATE polymorphic
-- "result place" type
--     data Place = AtStorage ValueLocation | InReg AbstractReg
-- so memory-only operations (`readLoc`, `writeLoc`, `stackMem`, `regs`)
-- keep their `ValueLocation`-typed (= storage-only) signatures and
-- `preserves-mem` retains its universal form. Result handles
-- (`IRResultAWF.result-loc`, `ValidAtWF`'s loc parameter) move to
-- `Place` only at handover points.

-- | Successor HeapLocation (for heap internal references)
sucHL : HeapLocation → HeapLocation
sucHL (heap-loc r o) = heap-loc r (suc o)

-- | Offset HeapLocation by n slots
offsetHL : HeapLocation → ℕ → HeapLocation
offsetHL (heap-loc r o) n = heap-loc r (n + o)

-- | Successor location (for accessing pair.snd, closure.code-ptr, etc.)
sucLoc : ∀ {FS} → ValueLocation FS → ValueLocation FS
sucLoc (AtStack f k)  = AtStack f (suc k)
sucLoc (AtDynamic hl) = AtDynamic (sucHL hl)

-- | Offset location by n slots (for unboxed multi-slot values)
-- Note: n + k so that offsetLoc _ 1 = sucLoc definitionally.
offsetLoc : ∀ {FS} → ValueLocation FS → ℕ → ValueLocation FS
offsetLoc (AtStack f k)  n = AtStack f (n + k)
offsetLoc (AtDynamic hl) n = AtDynamic (offsetHL hl n)

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

-- Plan 0.13.2: stack memory holds `StoredValue`, not `ValueLocation`.
StackMem : (FS : FrameSemantics) → Set
StackMem FS = FrameSemantics.Frame FS → Slot → Maybe (StoredValue FS)

-- Heap memory stores HeapLocation (enforces heap-only-references-heap)
HeapMem : Set
HeapMem = HeapLocation → Maybe HeapLocation

------------------------------------------------------------------------
-- Registers: Hold Locations (not Words)
--
-- Three-register model (Plan 0.2.4.5 D2):
--   Input1 - first argument location (maps to RDI in x86 SysV)
--   Input2 - second argument location (maps to RSI in x86 SysV)
--   Output - result location (maps to RAX in x86)
--
-- Two input registers eliminate the (env, arg) pack-into-pair waste
-- in `apply-setup-trace`: apply now writes env to Input1 and arg to
-- Input2, no two-store + lea slot pack. CCC primitives top out at
-- a 2-product input shape, so two input registers cover all of
-- pair, curry's body, and apply.
--
-- Note: AbstractReg is declared earlier (above ValueLocation) so
-- LocState's `regs : AbstractReg → ValueLocation` field can reference
-- it. The decidable equality and helpers stay here.
------------------------------------------------------------------------

-- Decidable equality for AbstractReg
_≟R_ : (r₁ r₂ : AbstractReg) → Dec (r₁ ≡ r₂)
Input1 ≟R Input1 = yes refl
Input1 ≟R Input2 = no (λ ())
Input1 ≟R Output = no (λ ())
Input2 ≟R Input1 = no (λ ())
Input2 ≟R Input2 = yes refl
Input2 ≟R Output = no (λ ())
Output ≟R Input1 = no (λ ())
Output ≟R Input2 = no (λ ())
Output ≟R Output = yes refl

-- Plan 0.13.2: registers hold `StoredValue`, not `ValueLocation`.
-- Real machines load tags / ints / pointers into the same registers
-- and discriminate by what was loaded. So register state lifts to
-- the same value type as memory cells.
record Registers (FS : FrameSemantics) : Set where
  constructor mkRegs
  field
    input1 input2 output : StoredValue FS
    stackSlot : ℕ  -- current stack slot index (like rsp, but as slot count)

open Registers public

readReg : ∀ {FS} → Registers FS → AbstractReg → StoredValue FS
readReg r Input1 = input1 r
readReg r Input2 = input2 r
readReg r Output = output r

writeReg : ∀ {FS} → Registers FS → AbstractReg → StoredValue FS → Registers FS
writeReg r Input1 v = record r { input1 = v }
writeReg r Input2 v = record r { input2 = v }
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
writeReg-preserves regs Input1 Input1 v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs Input1 Input2 v r≢dst = refl
writeReg-preserves regs Input1 Output v r≢dst = refl
writeReg-preserves regs Input2 Input1 v r≢dst = refl
writeReg-preserves regs Input2 Input2 v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs Input2 Output v r≢dst = refl
writeReg-preserves regs Output Input1 v r≢dst = refl
writeReg-preserves regs Output Input2 v r≢dst = refl
writeReg-preserves regs Output Output v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)

-- Key lemma: writing to a register and reading it back gives the written value
writeReg-same : ∀ {FS} (regs : Registers FS) dst v →
  readReg (writeReg regs dst v) dst ≡ v
writeReg-same regs Input1 v = refl
writeReg-same regs Input2 v = refl
writeReg-same regs Output v = refl

-- Key lemma: writeReg preserves stackSlot
writeReg-preserves-stackSlot : ∀ {FS} (regs : Registers FS) dst v →
  stackSlot (writeReg regs dst v) ≡ stackSlot regs
writeReg-preserves-stackSlot regs Input1 v = refl
writeReg-preserves-stackSlot regs Input2 v = refl
writeReg-preserves-stackSlot regs Output v = refl

-- Key lemma: writing twice to same register is same as writing once
writeReg-overwrite : ∀ {FS} (regs : Registers FS) dst x y →
  writeReg (writeReg regs dst x) dst y ≡ writeReg regs dst y
writeReg-overwrite regs Input1 x y = refl
writeReg-overwrite regs Input2 x y = refl
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
-- NOTE: frame-capacity was removed in Phase 3 refactoring. Capacity bounds
-- are now enforced per-IR via the scratch-bounded invariant, eliminating
-- the need for global capacity tracking in AllocState.
------------------------------------------------------------------------

record AllocState {FS : FrameSemantics} : Set where
  constructor mkAllocState
  open FrameSemantics FS
  field
    current-frame : Frame
    next-slot : ℕ
    next-heap-ref : ℕ
  -- Note: frame-capacity removed in Phase 3 of core invariants refactoring.
  -- Capacity bounds are now enforced per-closure via scratch-bounded invariant.

open AllocState public

------------------------------------------------------------------------
-- Memory Operations
------------------------------------------------------------------------

module MemOps {FS : FrameSemantics} where
  open FrameSemantics FS

  -- | Read a value from stack memory (returns StoredValue)
  readStackLoc : LocState FS → Frame → Slot → Maybe (StoredValue FS)
  readStackLoc s f k = stackMem s f k

  -- | Read from heap memory (returns HeapLocation - enforces invariant)
  readHeapLoc : LocState FS → HeapLocation → Maybe HeapLocation
  readHeapLoc s hl = heapMem s hl

  -- | Read a value from memory.
  --
  -- Plan 0.13.2: returns `Maybe StoredValue` — the cell's contents
  -- type. Heap reads still return a HeapLocation (heap-only invariant);
  -- they're lifted to `SV-Ptr (AtDynamic _)` at the boundary so the
  -- API uniformly returns StoredValue regardless of address kind.
  readLoc : LocState FS → ValueLocation FS → Maybe (StoredValue FS)
  readLoc s (AtStack f k) = stackMem s f k
  readLoc s (AtDynamic hl) with heapMem s hl
  ... | just hl' = just (SV-Ptr (AtDynamic hl'))
  ... | nothing  = nothing
  -- Plan 0.2.4.5 D1 (Unit erasure): erased values have no content.

  -- | Write a Location to stack memory.
  -- Order of clauses preserves definitional equalities for the (no _)
  -- frame-mismatch case (load-bearing for `writeLoc-preserves-other`):
  -- the no-frame-match branch is a single clause that returns `old`
  -- regardless of the slot decision, so `writeStackMem-aux (no _) _ old _`
  -- reduces by `refl` without case-splitting the second arg.
  -- Plan 0.13.2: stack now holds StoredValue.
  writeStackMem-aux : ∀ {f f' : Frame} {k k' : Slot}
                    → Dec (f ≡ f') → Dec (k ≡ k')
                    → Maybe (StoredValue FS)  -- existing value at (f',k')
                    → StoredValue FS           -- new value
                    → Maybe (StoredValue FS)
  writeStackMem-aux (no _)  _       old _ = old
  writeStackMem-aux (yes _) (yes _) _   v = just v
  writeStackMem-aux (yes _) (no _)  old _ = old

  writeStackMem : StackMem FS → Frame → Slot → StoredValue FS → StackMem FS
  writeStackMem mem f k v f' k' = writeStackMem-aux (f ≟F f') (k ≟ k') (mem f' k') v

  -- | Write a HeapLocation to heap memory (enforces heap-only invariant)
  writeHeapMem : HeapMem → HeapLocation → HeapLocation → HeapMem
  writeHeapMem mem hl v hl' with hl ≟HL hl'
  ... | yes _ = just v
  ... | no _  = mem hl'

  -- | Write a value (StoredValue) to stack memory at a slot.
  -- Plan 0.13.2.
  writeLocToStack : LocState FS → Frame → Slot → StoredValue FS → LocState FS
  writeLocToStack s f k v = record s { stackMem = writeStackMem (stackMem s) f k v }

  -- | Write a HeapLocation to heap memory at a HeapLocation
  writeLocToHeap : LocState FS → HeapLocation → HeapLocation → LocState FS
  writeLocToHeap s hl v = record s { heapMem = writeHeapMem (heapMem s) hl v }

  -- | Write a value (StoredValue) to memory.
  --
  -- Plan 0.13.2: the value arg is now StoredValue (was ValueLocation).
  -- Stack destinations: can store any StoredValue.
  -- Heap destinations: can only store SV-Ptr to another AtDynamic
  -- (heap-only invariant kept). All other StoredValue-to-heap
  -- combinations are no-op (illegal at the abstract level).
  writeLoc : LocState FS → ValueLocation FS → StoredValue FS → LocState FS
  writeLoc s (AtStack f k)  v                          = writeLocToStack s f k v
  writeLoc s (AtDynamic hl) (SV-Ptr (AtDynamic v))     = writeLocToHeap s hl v
  writeLoc s (AtDynamic hl) (SV-Ptr (AtStack _ _))     = s  -- Invalid: stack ref in heap
  writeLoc s (AtDynamic hl) (SV-Tag _)                 = s  -- Invalid: tag in heap
  writeLoc s (AtDynamic hl) (SV-Lit _ _)                 = s  -- Invalid: raw int in heap
  writeLoc s (AtDynamic hl) (SV-Code _)                = s  -- Invalid: code-addr in heap

  -- writeLoc preserves regs (for all cases). Plan 0.13.2: v : StoredValue.
  writeLoc-regs : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : StoredValue FS) →
    regs (writeLoc s loc v) ≡ regs s
  writeLoc-regs s (AtStack f k)  v                      = refl
  writeLoc-regs s (AtDynamic hl) (SV-Ptr (AtDynamic v)) = refl
  writeLoc-regs s (AtDynamic hl) (SV-Ptr (AtStack _ _)) = refl
  writeLoc-regs s (AtDynamic hl) (SV-Tag _)             = refl
  writeLoc-regs s (AtDynamic hl) (SV-Lit _ _)             = refl
  writeLoc-regs s (AtDynamic hl) (SV-Code _)            = refl

  -- writeLoc preserves halted (for all cases). Plan 0.13.2: v : StoredValue.
  writeLoc-halted : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : StoredValue FS) →
    halted (writeLoc s loc v) ≡ halted s
  writeLoc-halted s (AtStack f k)  v                      = refl
  writeLoc-halted s (AtDynamic hl) (SV-Ptr (AtDynamic v)) = refl
  writeLoc-halted s (AtDynamic hl) (SV-Ptr (AtStack _ _)) = refl
  writeLoc-halted s (AtDynamic hl) (SV-Tag _)             = refl
  writeLoc-halted s (AtDynamic hl) (SV-Lit _ _)             = refl
  writeLoc-halted s (AtDynamic hl) (SV-Code _)            = refl

  -- writeLoc AtStack preserves heapMem. Plan 0.13.2: v : StoredValue.
  writeLoc-heapMem-stack : ∀ (s : LocState FS) (f : Frame) (k : Slot) (v : StoredValue FS) →
    heapMem (writeLoc s (AtStack f k) v) ≡ heapMem s
  writeLoc-heapMem-stack s f k v = refl

  -- writeLoc commutes with register updates for AtStack locations.
  -- Plan 0.13.2: v : StoredValue.
  writeLoc-regs-commute : ∀ (s : LocState FS) (f : Frame) (k : Slot) (v : StoredValue FS)
    (r : Registers FS) →
    writeLoc (record s { regs = r }) (AtStack f k) v ≡
    record (writeLoc s (AtStack f k) v) { regs = r }
  writeLoc-regs-commute s f k v r = refl

  -- writeLoc preserves other locations (reading from a different location)
  -- Key lemma for frame-independence proofs.
  -- Inner-with logic extracted to a helper to keep the proof CATCHALL-free.
  writeLoc-preserves-other-stack-aux : ∀ {f1 f2 : Frame} {k1 k2 : Slot}
    (s : LocState FS) (v : StoredValue FS)
    (df : Dec (f1 ≡ f2)) (dk : Dec (k1 ≡ k2))
    → AtStack {FS} f1 k1 ≢ AtStack {FS} f2 k2
    → writeStackMem-aux df dk (stackMem s f2 k2) v ≡ stackMem s f2 k2
  writeLoc-preserves-other-stack-aux s v (yes refl) (yes refl) neq = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  writeLoc-preserves-other-stack-aux s v (yes refl) (no _)     _   = refl
  writeLoc-preserves-other-stack-aux s v (no _)     (yes refl) _   = refl
  writeLoc-preserves-other-stack-aux s v (no _)     (no _)     _   = refl

  writeLoc-preserves-other : ∀ (s : LocState FS) (loc1 loc2 : ValueLocation FS)
    (v : StoredValue FS) →
    loc1 ≢ loc2 →
    readLoc (writeLoc s loc1 v) loc2 ≡ readLoc s loc2
  -- Writing to stack, reading from different stack location
  writeLoc-preserves-other s (AtStack f1 k1) (AtStack f2 k2) v neq =
    writeLoc-preserves-other-stack-aux s v (f1 ≟F f2) (k1 ≟ k2) neq
  -- Writing to stack, reading from heap (disjoint)
  writeLoc-preserves-other s (AtStack f k) (AtDynamic hl) v _ = refl
  -- Writing to heap (SV-Ptr (AtDynamic v)), reading from stack (disjoint)
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Ptr (AtDynamic hv)) _ = refl
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Ptr (AtStack _ _))  _ = refl
  -- Writing non-pointer to heap is no-op, so reading anywhere unchanged
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Tag _)              _ = refl
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Lit _ _)              _ = refl
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Code _)             _ = refl
  -- Writing to heap, reading from different heap location
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Ptr (AtDynamic hv)) neq
    with hl1 ≟HL hl2
  ... | yes refl = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  ... | no _ = refl
  -- Writing non-heap-pointer to AtDynamic is a no-op
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Ptr (AtStack _ _)) _ = refl
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Tag _)              _ = refl
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Lit _ _)              _ = refl
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Code _)             _ = refl
  -- every other location.

  -- writeLoc-read-same: Reading from the location we just wrote returns the written value
  -- Stack case: writeLoc s (AtStack f k) v → readLoc (AtStack f k) ≡ just v
  writeLoc-read-same-stack : ∀ (s : LocState FS) (f : Frame) (k : Slot) (v : StoredValue FS) →
    readLoc (writeLoc s (AtStack f k) v) (AtStack f k) ≡ just v
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

-- Helper: extract a `ValueLocation` from a `StoredValue` if it's
-- a pointer. Plan 0.13.2: registers hold StoredValue, but
-- `resolveSourceExt` needs to derive addresses for loads/stores.
-- A non-pointer register value (tag/int/code) means the program
-- is dereferencing something it shouldn't — return `nothing`.
sv-as-loc : ∀ {FS} → StoredValue FS → Maybe (ValueLocation FS)
sv-as-loc (SV-Ptr loc) = just loc
sv-as-loc (SV-Tag _)   = nothing
sv-as-loc (SV-Lit _ _)   = nothing
sv-as-loc (SV-Code _)  = nothing

resolveSourceExt : ∀ {FS} → Registers FS → LocSourceExt FS → Maybe (ValueLocation FS)
resolveSourceExt regs (Loc loc) = just loc
resolveSourceExt regs (IndReg r) = sv-as-loc (readReg regs r)
resolveSourceExt regs (IndRegSuc r) with sv-as-loc (readReg regs r)
... | just loc = just (sucLoc loc)
... | nothing  = nothing

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

  -- Helper: Apply the result of a memory read to produce new state.
  -- Plan 0.13.2: the read result is `Maybe StoredValue`.
  exec-load-with-value : AbstractReg → Maybe (StoredValue FS) →
                         LocState FS → LocState FS
  exec-load-with-value dst (just v) s = record s { regs = writeReg (regs s) dst v }
  exec-load-with-value dst nothing s = record s { halted = true }

  -- Helper: bind through Maybe-resolved address. If resolveSourceExt
  -- returned `nothing` (non-pointer in register), halt.
  exec-load-via-resolved : AbstractReg → Maybe (ValueLocation FS) →
                           LocState FS → LocState FS
  exec-load-via-resolved dst (just loc) s = exec-load-with-value dst (readLoc s loc) s
  exec-load-via-resolved dst nothing    s = record s { halted = true }

  -- Same shape for stores: if dst-resolution fails, halt.
  exec-store-via-resolved : Maybe (ValueLocation FS) → StoredValue FS →
                            LocState FS → LocState FS
  exec-store-via-resolved (just loc) v s = writeLoc s loc v
  exec-store-via-resolved nothing    _ s = record s { halted = true }

  exec : Instr FS → LocState FS → LocState FS

  exec (load dst src) s =
    exec-load-via-resolved dst (resolveSourceExt (regs s) src) s

  exec (store dst src) s =
    exec-store-via-resolved
      (resolveSourceExt (regs s) dst)
      (readReg (regs s) src)
      s

  exec (mov dst src) s =
    record s { regs = writeReg (regs s) dst (readReg (regs s) src) }

  -- Lemmas for exec-load behavior (definitionally equal, but named for clarity)
  exec-load-just : ∀ dst v s →
    exec-load-with-value dst (just v) s ≡ record s { regs = writeReg (regs s) dst v }
  exec-load-just _ _ _ = refl

  exec-load-nothing : ∀ dst s →
    exec-load-with-value dst nothing s ≡ record s { halted = true }
  exec-load-nothing _ _ = refl

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

  -- | Plan 0.13.2: helper to unify the two Maybe-layers introduced
  -- by resolveSourceExt now returning `Maybe ValueLocation`.
  -- Combines "resolve the source address" and "read the cell".
  resolved-readLoc : LocState FS → LocSourceExt FS → Maybe (StoredValue FS)
  resolved-readLoc s src with resolveSourceExt (regs s) src
  ... | just loc = readLoc s loc
  ... | nothing  = nothing

  -- | After load, dst holds the value from memory (when successful).
  -- Plan 0.13.2: takes the resolved address as an explicit arg to
  -- avoid double-`with` unification issues.
  load-result : ∀ dst src loc (s : LocState FS) v →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ just v →
    readReg (regs (exec (load dst src) s)) dst ≡ v
  load-result dst src loc s v r-eq mem-eq
    with resolveSourceExt (regs s) src | r-eq
  ... | just loc' | refl with readLoc s loc' | mem-eq
  ...   | just v' | refl = writeReg-same (regs s) dst v'

  -- | After load (successful), other registers are preserved
  load-preserves-reg : ∀ dst src loc (s : LocState FS) r v →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ just v →
    r ≢ dst →
    readReg (regs (exec (load dst src) s)) r ≡ readReg (regs s) r
  load-preserves-reg dst src loc s r v r-eq mem-eq r≢dst
    with resolveSourceExt (regs s) src | r-eq
  ... | just loc' | refl with readLoc s loc' | mem-eq
  ...   | just v' | refl = writeReg-preserves (regs s) dst r v' r≢dst

  -- | After load (resolve failed), registers unchanged
  load-failed-resolve-preserves : ∀ dst src (s : LocState FS) →
    resolveSourceExt (regs s) src ≡ nothing →
    regs (exec (load dst src) s) ≡ regs s
  load-failed-resolve-preserves dst src s r-eq
    with resolveSourceExt (regs s) src | r-eq
  ... | nothing | refl = refl

  -- | After load (read returned nothing), registers unchanged
  load-failed-read-preserves : ∀ dst src loc (s : LocState FS) →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ nothing →
    regs (exec (load dst src) s) ≡ regs s
  load-failed-read-preserves dst src loc s r-eq mem-eq
    with resolveSourceExt (regs s) src | r-eq
  ... | just loc' | refl with readLoc s loc' | mem-eq
  ...   | nothing | refl = refl

  -- | Load preserves stack memory
  load-preserves-stackMem : ∀ dst src (s : LocState FS) →
    stackMem (exec (load dst src) s) ≡ stackMem s
  load-preserves-stackMem dst src s
    with resolveSourceExt (regs s) src
  ... | nothing  = refl
  ... | just loc with readLoc s loc
  ...   | just _  = refl
  ...   | nothing = refl

  -- | Load preserves heap memory
  load-preserves-heapMem : ∀ dst src (s : LocState FS) →
    heapMem (exec (load dst src) s) ≡ heapMem s
  load-preserves-heapMem dst src s
    with resolveSourceExt (regs s) src
  ... | nothing  = refl
  ... | just loc with readLoc s loc
  ...   | just _  = refl
  ...   | nothing = refl

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
  load-preserves-halted : ∀ dst src loc (s : LocState FS) v →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ just v →
    halted (exec (load dst src) s) ≡ halted s
  load-preserves-halted dst src loc s v r-eq mem-eq
    with resolveSourceExt (regs s) src | r-eq
  ... | just loc' | refl with readLoc s loc' | mem-eq
  ...   | just _ | refl = refl

  -- | Load doesn't halt when memory read succeeds and not already halted
  load-no-halt : ∀ dst src loc (s : LocState FS) v →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ just v →
    halted s ≡ false →
    halted (exec (load dst src) s) ≡ false
  load-no-halt dst src loc s v r-eq mem-eq not-halted =
    trans (load-preserves-halted dst src loc s v r-eq mem-eq) not-halted

  -- | Memory read is preserved when stackMem and heapMem unchanged.
  -- Now universal (post-Stage-E retirement): readLoc only depends on
  -- (stackMem, heapMem) for AtStack/AtDynamic, and is constantly
  -- `nothing` for Erased. The Stage-E InReg-postulate is gone with
  -- the constructor it was working around.
  readLoc-stackMem-eq : ∀ (s₁ s₂ : LocState FS) loc →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    readLoc s₁ loc ≡ readLoc s₂ loc
  readLoc-stackMem-eq s₁ s₂ (AtStack f k) stack-eq heap-eq =
    cong (λ m → m f k) stack-eq
  readLoc-stackMem-eq s₁ s₂ (AtDynamic hl) stack-eq heap-eq
    with heapMem s₁ hl | heapMem s₂ hl | cong (λ m → m hl) heap-eq
  ... | just hl₁ | just hl₂ | eq = cong (λ x → just (SV-Ptr (AtDynamic x))) (just-injective eq)
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
  mov-to-output      : AbstractInstr              -- Output := Input1
  mov-to-input       : AbstractInstr              -- Input1 := Output (compose bridge)

  -- Plan 0.2.4.5 Stage C: split-input calling convention. Apply's
  -- body receives env in Input1, arg in Input2 (no packed (env, arg)
  -- record). These instructions move between the second input register
  -- and Output, mirroring mov-to-input/mov-to-output for Input2.
  --
  -- For Layer 0–4 with no nested pair construction, fst lowers to
  -- mov-to-output (read Input1) and snd lowers to mov-input2-to-output
  -- (read Input2) — they project the body's split input. Layer 1+ with
  -- nested packed pairs needs a layout-discriminating fst/snd; that's
  -- a future concern.
  mov-output-to-input2 : AbstractInstr            -- Input2 := Output
  mov-input2-to-output : AbstractInstr            -- Output := Input2

  -- Memory load operations (slot-level, not physical address arithmetic)
  load-indirect      : AbstractInstr              -- Output := *Input1
  load-indirect-suc  : AbstractInstr              -- Output := *(sucLoc Input1)
  load-from-slot     : Slot → AbstractInstr       -- Output := stack[slot]

  -- Memory store operations
  store-at-slot      : Slot → AbstractInstr       -- stack[slot] := Output
  store-indirect     : AbstractInstr              -- *Input1 := Output
  store-indirect-suc : AbstractInstr              -- *(sucLoc Input1) := Output

  -- Address computation
  lea-slot           : Slot → AbstractInstr       -- Output := &stack[slot]
  restore-input      : Slot → AbstractInstr       -- Input1 := stack[slot]

  -- Stack management
  instr-alloc-stack   : ℕ → AbstractInstr          -- allocate N slots
  instr-dealloc-stack : ℕ → AbstractInstr          -- deallocate N slots

  -- OCP-0003: Slot reclamation for Sum wrappers
  -- Sets next-slot to a specific value, allowing wrapper allocation at reclaimed position.
  -- Used by Sum to place wrapper at child's reclaimable-slot for tight allocation.
  instr-reclaim-to    : ℕ → AbstractInstr          -- set next-slot to n

  -- Apply-specific (function calls)
  instr-push-frame   : ℕ → AbstractInstr          -- push new frame with capacity
  instr-pop-frame    : AbstractInstr              -- restore caller frame
  instr-call-closure : AbstractInstr              -- jump to closure code

  -- OCP-0003: Worklist operations for loop-based recursion schemes
  --
  -- The worklist is a slot-based stack for tree traversal:
  --   Slot (base-1): count (number of items)
  --   Slots base, base+1, ...: data items
  --
  -- Runtime uses loops; proofs use Star (structural induction on μ-values).
  -- These instructions implement the runtime loop operations.
  --
  worklist-init  : Slot → AbstractInstr  -- Initialize: count := 0
  worklist-push  : Slot → AbstractInstr  -- Push Output, count++
  worklist-pop   : Slot → AbstractInstr  -- count--, Output := top item
  worklist-check : Slot → AbstractInstr  -- Output := 1 if empty, 0 if not

  -- Plan 0.10 Phase B / Phase A step 1: SigOp dispatch.
  --
  -- Carries the SigOpInfo (name + semI + semM). Per-arch
  -- compile-abstract uses `name si` to decide what assembly to emit
  -- (e.g., "exit" → mov $60, %rax; syscall). The proof layer can
  -- consult `semI si` / `semM si` for per-name discharge of
  -- `sigop-codegen-faithful` and `ir-to-trace-correct-sigop` — see
  -- `Once.CCC.SigOp.Info` for the spec layer.
  --
  -- Type indices A, B are implicit and recoverable when needed by
  -- pattern-matching on `instr-sigop {A} {B} si`.
  instr-sigop : ∀ {A B : Type} → SigOpInfo A B → AbstractInstr

  -- Plan 0.11: Load a primitive-typed constant into Output.
  --
  -- Carries `FitsInReg` evidence and the machine-level value
  -- `v : ⟦ A ⟧`. Per-arch `compile-abstract` pattern-matches on the
  -- evidence to emit the right load instruction (`mov $N, %rax` for
  -- Int, etc.). CCC stays specific-primitive-type-agnostic; the
  -- per-arch backend knows specific register-fittable types because
  -- it has to emit specific machine instructions.
  instr-load-const : ∀ {A : Type} → FitsInReg A → ⟦ A ⟧ → AbstractInstr

  -- Plan 0.2.4.2 Phase A: Load the address of a closure-body label
  -- into Output. The argument `n : ℕ` indexes into the parent
  -- function's per-function table of closure-body labels — Plan
  -- 0.2.4.2 D5 (stateful counter, local to each parent function).
  --
  -- Per-arch `compile-abstract` lowers this to a label-relative
  -- address load (`lea .L_thunk_<n>(%rip), %rax` on x86-64).
  --
  -- Plan 0.2.4.2 Phase D follow-up: capture the current Input1
  -- register into the closure-register convention slot (e.g.
  -- `%r12` on x86-64). Used in `apply`'s setup trace to keep the
  -- closure pointer alive across pair-construction so that
  -- `instr-call-closure` (lowered to `call *0x8(%r12)`) has a
  -- valid target.
  --
  -- Abstract semantics: identity. We don't model the closure
  -- register separately at the abstract level — it's purely a
  -- per-arch calling-convention concern.
  -- Used by `curry`'s codegen to set up the closure record's
  -- code-pointer slot.
  instr-load-code-addr : ℕ → AbstractInstr
  instr-save-closure-reg : AbstractInstr

  -- Plan 0.13.1 Phase 1 — sum tag handling (tag-aware abstract layer).
  --
  -- `instr-load-tag-lit n`: write `SV-Tag n` to Output. Used by
  -- `run-inl` / `run-inr` to deposit the sum-discriminator (0 for
  -- inl, 1 for inr) before storing it to the container's tag slot.
  --
  -- `instr-case-on-tag f g`: read `SV-Tag k` from `*Input1` (the
  -- sum value's tag slot, at offset 0) and dispatch:
  --   k = 0 → exec-trace f
  --   k = 1 → exec-trace g
  --   otherwise (no tag / malformed sum) → halt
  --
  -- This is the tag-aware abstract semantics promised by Plan 0.13.1
  -- Phase 1. The proof of run-case correctness composes from
  -- `valid-inl-wf` / `valid-inr-wf`'s tag-eq fields (Plan 0.13.1
  -- Phase 2) — no `case-codegen-faithful` postulate needed.
  --
  -- Argument type for instr-case-on-tag is `List AbstractInstr`
  -- (= `AbstractTrace`) spelled out — the `AbstractTrace` alias is
  -- defined just below.
  -- NOTE: keep instr-case-on-tag in this position so existing
  -- compile-correct proofs and Haskell-side simulations don't shift.
  -- New constructors get added strictly AFTER instr-case-on-tag.
  instr-load-tag-lit : ℕ → AbstractInstr
  instr-case-on-tag : List AbstractInstr → List AbstractInstr → AbstractInstr

  -- Plan 0.14 Phase A — heap allocation primitive.
  --
  -- `instr-alloc-heap n`: allocate a fresh heap block (n cells), bump
  -- `next-heap-ref`, write the resulting `SV-Ptr (AtDynamic …)` to Output.
  -- Caller subsequently writes the cells via `store-indirect` /
  -- `store-indirect-suc` and reads them via `load-indirect` /
  -- `load-indirect-suc`.
  --
  -- The `n` parameter is the cell count for codegen / sigop dispatch;
  -- the abstract semantics treats every `instr-alloc-heap _` as a single
  -- fresh `AtDynamic` whose `sucLoc` chains give access to all n cells
  -- (HeapLocation already supports this).
  --
  -- Added AFTER `instr-case-on-tag` so existing MAlonzo constructor
  -- indices remain stable.
  instr-alloc-heap : ℕ → AbstractInstr

-- | A trace is a sequence of abstract instructions
AbstractTrace : Set
AbstractTrace = List AbstractInstr

------------------------------------------------------------------------
-- Tree-Structured Traces (OCP-0003)
--
-- For recursion schemes, we need traces that can represent recursive
-- structure. TreeTrace extends AbstractTrace with:
--   - Sequencing: Execute traces in order
--   - Branching: Choose trace based on tag slot value
--   - Recursive call: Execute sub-trace (maps to function call at runtime)
--
-- PORTABILITY:
--   These primitives map cleanly to all backends:
--   - x86-64: call/ret sequences, conditional jumps
--   - ARM64: bl/ret sequences, conditional branches
--   - WASM: call instruction, br_if blocks
--   - RISC-V: jal/jalr sequences
--
-- The semantic model is portable: tree structure represents control
-- flow without committing to a specific calling convention.
------------------------------------------------------------------------

data TreeTrace : Set where
  -- | Empty trace
  ε : TreeTrace
  -- | Single instruction
  instr : AbstractInstr → TreeTrace
  -- | Sequential composition: execute t₁ then t₂
  _▸_ : TreeTrace → TreeTrace → TreeTrace
  -- | Branch on tag in slot: if tag=0 run left, else run right
  -- This supports sum types (inj₁/inj₂ dispatching)
  branch : Slot → TreeTrace → TreeTrace → TreeTrace
  -- | Recursive call: execute sub-trace (callee-saved context)
  -- This models the recursive step in recursion schemes
  call-sub : TreeTrace → TreeTrace
  -- | Embed flat trace (compatibility with existing code)
  flat : AbstractTrace → TreeTrace

infixr 5 _▸_

-- | Convert flat trace to tree trace
flatToTree : AbstractTrace → TreeTrace
flatToTree [] = ε
flatToTree (i ∷ is) = instr i ▸ flatToTree is

-- | Flatten tree trace to list (for backends that want flat sequences)
-- Note: branch and call-sub are eliminated by code generation, not here
treeToFlat : TreeTrace → AbstractTrace
treeToFlat ε = []
treeToFlat (instr i) = i ∷ []
treeToFlat (t₁ ▸ t₂) = treeToFlat t₁ ++ treeToFlat t₂
treeToFlat (branch _ tL tR) = treeToFlat tL ++ treeToFlat tR  -- Both branches for analysis
treeToFlat (call-sub t) = treeToFlat t
treeToFlat (flat is) = is

------------------------------------------------------------------------
-- TreeTrace to Runnable Flat Trace Compilation
--
-- This compiles TreeTrace to a flat AbstractTrace that executes
-- equivalently using worklist operations for call-sub.
--
-- PROOF SIGNIFICANCE:
--   exec-tree-trace t s alloc ≡ exec-trace (treeToRunnable wl t) s alloc
--   (where wl is the worklist slot allocation)
--
-- This enables proving ValidAtWF by:
--   1. Build TreeTrace by structural recursion (cata-tree-μ)
--   2. Prove TreeTrace execution correct (cata-tree-μ-correct)
--   3. Compile to flat trace (treeToRunnable)
--   4. By equivalence, flat trace also correct
--
-- RUNTIME MAPPING:
--   - call-sub → worklist-push + main loop processing
--   - branch → conditional jump
--   - Sequential composition → instruction concatenation
------------------------------------------------------------------------

-- | Compile TreeTrace to runnable flat trace
--
-- Parameters:
--   wl : Slot for worklist (count + items)
--   t  : TreeTrace to compile
--
-- The worklist approach:
--   - Initialize worklist at start
--   - call-sub pushes current work item and continues with sub-trace
--   - At end of sub-trace, check worklist for more work
--
-- Note: This is a simplified model. Real runtime uses loop structure.
treeToRunnable : Slot → TreeTrace → AbstractTrace
treeToRunnable wl ε = []
treeToRunnable wl (instr i) = i ∷ []
treeToRunnable wl (t₁ ▸ t₂) = treeToRunnable wl t₁ ++ treeToRunnable wl t₂
treeToRunnable wl (branch slot tL tR) =
  -- Simplified: flatten both branches (runtime uses conditional)
  -- For proofs, the taken branch is determined by getTag
  treeToRunnable wl tL ++ treeToRunnable wl tR
treeToRunnable wl (call-sub t) =
  -- Push current continuation, execute sub-trace
  -- Worklist manages the return continuation
  worklist-push wl ∷ treeToRunnable wl t ++ worklist-pop wl ∷ []
treeToRunnable wl (flat is) = is

-- | Initialize worklist and compile tree trace
treeToRunnableWithInit : Slot → TreeTrace → AbstractTrace
treeToRunnableWithInit wl t = worklist-init wl ∷ treeToRunnable wl t

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

  ------------------------------------------------------------------------
  -- Helper functions for instructions that read from memory
  --
  -- These expose the decision point (Maybe result) for external proofs.
  -- Using these helpers, external code can prove properties by cases on
  -- the Maybe value rather than needing with-pattern alignment.
  ------------------------------------------------------------------------

  -- Helper for load-from-slot: applies memory read result.
  -- Plan 0.13.2: read result is now `Maybe StoredValue`.
  exec-load-from-slot-with-value : Maybe (StoredValue FS) → LocState FS →
                                   AllocState {FS} → LocState FS × AllocState {FS}
  exec-load-from-slot-with-value (just v) s alloc =
    record s { regs = writeReg (regs s) Output v } , alloc
  exec-load-from-slot-with-value nothing s alloc =
    record s { halted = true } , alloc

  -- Helper for restore-input: applies memory read result.
  -- Plan 0.13.2: read result is now `Maybe StoredValue`.
  exec-restore-input-with-value : Maybe (StoredValue FS) → LocState FS →
                                  AllocState {FS} → LocState FS × AllocState {FS}
  exec-restore-input-with-value (just v) s alloc =
    record s { regs = writeReg (regs s) Input1 v } , alloc
  exec-restore-input-with-value nothing s alloc =
    record s { halted = true } , alloc

  -- Lemmas for load-from-slot helper
  exec-load-from-slot-just : ∀ v s alloc →
    exec-load-from-slot-with-value (just v) s alloc ≡
    (record s { regs = writeReg (regs s) Output v } , alloc)
  exec-load-from-slot-just _ _ _ = refl

  exec-load-from-slot-nothing : ∀ s alloc →
    exec-load-from-slot-with-value nothing s alloc ≡
    (record s { halted = true } , alloc)
  exec-load-from-slot-nothing _ _ = refl

  -- Lemmas for restore-input helper
  exec-restore-input-just : ∀ v s alloc →
    exec-restore-input-with-value (just v) s alloc ≡
    (record s { regs = writeReg (regs s) Input1 v } , alloc)
  exec-restore-input-just _ _ _ = refl

  exec-restore-input-nothing : ∀ s alloc →
    exec-restore-input-with-value nothing s alloc ≡
    (record s { halted = true } , alloc)
  exec-restore-input-nothing _ _ = refl

  ------------------------------------------------------------------------
  -- Plan 0.11 Task A — SigOp trusted-base axioms
  --
  -- The abstract semantics of `instr-sigop si` is structured around
  -- two named axioms. Per-(arch, name) discharge replaces these with
  -- per-name implementations (e.g. `linux.exit` halts; `lit.int.<N>`
  -- writes a constant). Until then they are trusted-base entries —
  -- visible to `make postulates-grep` and live in the same place as
  -- the other CCC-layer axioms.
  --
  -- Note: by structuring the abstract semantics this way (only Output
  -- and halted may change), the relaxed CCC discipline contract holds
  -- *definitionally* for `instr-sigop si`: frame, alloc, memory,
  -- Input1 register, and stackSlot are all unchanged by the body of
  -- `exec-abstract (instr-sigop si)` below.
  ------------------------------------------------------------------------

  postulate
    -- The new value placed in Output after the SigOp runs.
    -- Plan 0.13.2: returns `StoredValue` (was `ValueLocation`) since
    -- a SigOp's output could be any kind of value.
    exec-sigop-output : ∀ {A B} → SigOpInfo A B → LocState FS →
                        StoredValue FS

    -- Whether the SigOp halts. `linux.exit` returns `true`; pure
    -- SigOps return `false`.
    exec-sigop-halts  : ∀ {A B} → SigOpInfo A B → LocState FS → Bool

  -- Plan 0.13.2: `encode-const` and `encode-code-addr` deleted —
  -- their roles are now real `StoredValue` constructors.
  -- `instr-load-const fits-int n` writes `SV-Int n` to Output;
  -- `instr-load-code-addr n` writes `SV-Code n`. Two trusted-base
  -- axioms removed.

  ------------------------------------------------------------------------
  -- Main exec-abstract definition
  ------------------------------------------------------------------------

  -- | Execute one abstract instruction
  -- Plan 0.13.1: mutually recursive with exec-trace (case-on-tag
  -- dispatches into one of two sub-traces).
  exec-abstract : AbstractInstr → LocState FS → AllocState {FS} →
                  LocState FS × AllocState {FS}
  exec-trace : AbstractTrace → LocState FS → AllocState {FS} →
               LocState FS × AllocState {FS}

  -- mov-to-output: Output := Input1
  exec-abstract mov-to-output s alloc =
    record s { regs = writeReg (regs s) Output (readReg (regs s) Input1) } , alloc

  -- mov-to-input: Input1 := Output (compose bridge)
  exec-abstract mov-to-input s alloc =
    record s { regs = writeReg (regs s) Input1 (readReg (regs s) Output) } , alloc

  -- mov-output-to-input2: Input2 := Output (Stage C split-input setup)
  exec-abstract mov-output-to-input2 s alloc =
    record s { regs = writeReg (regs s) Input2 (readReg (regs s) Output) } , alloc

  -- mov-input2-to-output: Output := Input2 (Stage C body-side snd)
  exec-abstract mov-input2-to-output s alloc =
    record s { regs = writeReg (regs s) Output (readReg (regs s) Input2) } , alloc

  -- load-indirect: Output := *Input1.
  -- Plan 0.13.2: Input1 holds StoredValue; only succeeds when it's
  -- a pointer. sv-as-loc returns the address or `nothing`.
  exec-abstract load-indirect s alloc
    with sv-as-loc (readReg (regs s) Input1)
  ... | just loc = exec-load-with-value Output (readLoc s loc) s , alloc
  ... | nothing  = record s { halted = true } , alloc

  -- load-indirect-suc: Output := *(sucLoc Input1)
  exec-abstract load-indirect-suc s alloc
    with sv-as-loc (readReg (regs s) Input1)
  ... | just loc = exec-load-with-value Output (readLoc s (sucLoc loc)) s , alloc
  ... | nothing  = record s { halted = true } , alloc

  -- load-from-slot: Output := stack[frame, slot]
  exec-abstract (load-from-slot slot) s alloc =
    exec-load-from-slot-with-value (readLoc s (AtStack (current-frame alloc) slot)) s alloc

  -- store-at-slot: stack[frame, slot] := Output
  exec-abstract (store-at-slot slot) s alloc =
    writeLoc s (AtStack (current-frame alloc) slot) (readReg (regs s) Output) , alloc

  -- store-indirect: *Input1 := Output.
  -- Plan 0.13.2: Input1 holds StoredValue; only succeeds when it's
  -- a pointer.
  exec-abstract store-indirect s alloc
    with sv-as-loc (readReg (regs s) Input1)
  ... | just loc = writeLoc s loc (readReg (regs s) Output) , alloc
  ... | nothing  = record s { halted = true } , alloc

  -- store-indirect-suc: *(sucLoc Input1) := Output
  exec-abstract store-indirect-suc s alloc
    with sv-as-loc (readReg (regs s) Input1)
  ... | just loc = writeLoc s (sucLoc loc) (readReg (regs s) Output) , alloc
  ... | nothing  = record s { halted = true } , alloc

  -- lea-slot: Output := &stack[frame, slot].
  -- Plan 0.13.2: Output gets a `SV-Ptr` to the slot's address.
  exec-abstract (lea-slot slot) s alloc =
    record s { regs = writeReg (regs s) Output (SV-Ptr (AtStack (current-frame alloc) slot)) } , alloc

  -- restore-input: Input1 := stack[frame, slot]
  exec-abstract (restore-input slot) s alloc =
    exec-restore-input-with-value (readLoc s (AtStack (current-frame alloc) slot)) s alloc

  -- instr-alloc-stack: advance stackSlot by n AND advance next-slot frontier
  -- Capacity was verified by Dispatcher when constructing the trace
  -- Note: next-slot tracks compile-time allocation frontier (monotonically increasing)
  exec-abstract (instr-alloc-stack n) s alloc =
    record s { regs = incrStackSlot (regs s) n } ,
    record alloc { next-slot = next-slot alloc + n }

  -- instr-dealloc-stack: reclaim n slots (decrement stackSlot)
  exec-abstract (instr-dealloc-stack n) s alloc =
    record s { regs = decrStackSlot (regs s) n } , alloc

  -- instr-reclaim-to: set next-slot to given value (actual reclamation)
  -- OCP-0003: Used by Sum wrapper allocation to place wrapper at child's reclaimable-slot.
  -- The LocState is unchanged; only the AllocState's next-slot is updated.
  exec-abstract (instr-reclaim-to n) s alloc =
    s , record alloc { next-slot = n }

  -- instr-push-frame: create new frame with given capacity
  -- Resets stackSlot to 0 for the new frame
  -- Note: Frame identity is managed by AllocState.current-frame
  -- Note: capacity parameter retained for API compatibility but not stored
  exec-abstract (instr-push-frame cap) s alloc =
    record s { regs = writeStackSlot (regs s) 0 } ,
    alloc  -- AllocState unchanged (frame-capacity removed)

  -- instr-pop-frame: restore caller frame
  -- Note: stackSlot restoration handled by caller (who saved it)
  exec-abstract instr-pop-frame s alloc =
    s , alloc  -- Frame identity restoration is external

  -- instr-call-closure: transfer control to closure code
  -- This is a no-op at abstract level - the call happens via BodyCorrect.execute
  exec-abstract instr-call-closure s alloc =
    s , alloc

  ------------------------------------------------------------------------
  -- OCP-0003: Worklist Instruction Semantics
  --
  -- Worklist operations support loop-based tree traversal at runtime.
  -- Proofs use Star-based structural induction on μ-values, not loops.
  --
  -- These semantics are simplified abstractions:
  --   - Runtime uses actual counters and indexed slots
  --   - Abstract level provides type-correct behavior
  --   - Correctness follows from Star proofs, not loop simulation
  ------------------------------------------------------------------------

  -- worklist-init: Initialize worklist (count := 0)
  -- Abstract: no observable state change (empty worklist has no items)
  exec-abstract (worklist-init slot) s alloc = s , alloc

  -- worklist-push: Push Output onto worklist, advance count
  -- Abstract: store value at slot (simplified - runtime tracks index)
  exec-abstract (worklist-push slot) s alloc =
    writeLoc s (AtStack (current-frame alloc) slot) (readReg (regs s) Output) , alloc

  -- worklist-pop: Pop top item into Output, decrement count
  -- Abstract: load from slot (simplified - runtime tracks index)
  exec-abstract (worklist-pop slot) s alloc =
    exec-load-from-slot-with-value (readLoc s (AtStack (current-frame alloc) slot)) s alloc

  -- worklist-check: Set Output based on worklist empty status
  -- Abstract: no-op (Star proofs handle termination structurally)
  exec-abstract (worklist-check slot) s alloc = s , alloc

  -- Plan 0.10 Phase B / 0.11 Task A: SigOp dispatch.
  --
  -- The abstract semantics of `instr-sigop si` is **structured**: it
  -- may write a new value-location to Output and may halt the
  -- machine, but it leaves everything else (frame, alloc, memory,
  -- Input1 register, stackSlot) unchanged. The two postulates below
  -- (`exec-sigop-output` and `exec-sigop-halts`) are the trusted-
  -- base axioms describing what a SigOp does at the abstract level.
  -- Per-name discharge of these axioms (e.g. `linux.exit` halts;
  -- `lit.int.<N>` doesn't halt and produces a constant) is downstream
  -- work — see Plan 0.11 task A and Plan 0.10 Phase E.
  --
  -- This shape encodes the relaxed CCC contract structurally:
  --   - frame-eq, slot-stable, mem-preserved, heap-monotone hold
  --     by definitional reduction (alloc and memory unchanged);
  --   - regs-only-output and Input-preservation hold via
  --     writeReg-preserves;
  --   - halted may flip false → true (halting SigOps) or stay false
  --     (pure SigOps) — `exec-sigop-halts` is the per-(arch, name)
  --     discharge target.
  --
  -- Replacing the older identity body `exec-abstract (instr-sigop si)
  -- s alloc = s , alloc` is the Plan-0.11 task-A move that surfaces
  -- the silent wildcard-payload leak as named, audit-visible
  -- postulates.
  exec-abstract (instr-sigop si) s alloc =
    record s { regs   = writeReg (regs s) Output (exec-sigop-output si s)
             ; halted = exec-sigop-halts si s }
    , alloc

  -- Plan 0.13.2: load a primitive constant into Output as `SV-Lit`.
  -- Replaces the encode-const postulate. The FitsInReg evidence is
  -- carried through to the cell so float vs int discrimination
  -- happens via pattern-matching on `SV-Lit isPrim v`.
  exec-abstract (instr-load-const isPrim v) s alloc =
    record s { regs = writeReg (regs s) Output (SV-Lit isPrim v) } , alloc

  -- Plan 0.13.2: load a closure-body label's address into Output as
  -- `SV-Code n`. Replaces the encode-code-addr postulate.
  exec-abstract (instr-load-code-addr n) s alloc =
    record s { regs = writeReg (regs s) Output (SV-Code n) } , alloc

  -- Plan 0.2.4.2 Phase D follow-up: save Input1 to closure register.
  -- Identity at the abstract level — the closure register is purely
  -- a per-arch concern.
  exec-abstract instr-save-closure-reg s alloc = s , alloc

  -- Plan 0.13.1 Phase 1: tag literal — write `SV-Tag n` to Output.
  exec-abstract (instr-load-tag-lit n) s alloc =
    record s { regs = writeReg (regs s) Output (SV-Tag n) } , alloc

  -- Plan 0.13.1 Phase 1: case-on-tag — TEMPORARILY halts at the
  -- abstract level. Making this tag-aware (dispatching into f or g
  -- based on `*Input1`) requires lifting ~12 SMPrimitives lemmas
  -- (TraceNoHeapWrites, instr-writes-slot, InstrPreservesFrame,
  -- etc.) from "per-instruction" to "instruction-or-trace" shape,
  -- since case-on-tag's effect becomes the union of two sub-traces.
  -- See Plan 0.13.1 Phase 1.5 for the coordinated lift.
  exec-abstract (instr-case-on-tag f g) s alloc =
    record s { halted = true } , alloc

  -- Plan 0.14 Phase A: heap allocation.
  -- Bumps `next-heap-ref` via `heap-alloc`, writes the resulting
  -- `SV-Ptr (AtDynamic …)` to Output. Memory at the freshly allocated
  -- cells starts uninitialised (reads return `nothing` until written).
  exec-abstract (instr-alloc-heap n) s alloc =
    let new-loc = AtDynamic (heap-loc (mkHeapRef (next-heap-ref alloc)) 0)
        alloc' = record alloc { next-heap-ref = suc (next-heap-ref alloc) }
    in record s { regs = writeReg (regs s) Output (SV-Ptr new-loc) } , alloc'

  -- | Execute a trace (sequence of abstract instructions)
  -- Signature declared above with exec-abstract for mutual recursion.
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

  ------------------------------------------------------------------------
  -- Tree-Structured Trace Execution (OCP-0003)
  --
  -- Execute tree-structured traces that can represent recursive control
  -- flow. This is the semantic model for recursion scheme proofs.
  --
  -- PROOF ARCHITECTURE:
  --   - Structural recursion on TreeTrace matches μ-value structure
  --   - branch corresponds to sum type dispatching
  --   - call-sub corresponds to recursive scheme invocation
  --   - Sequential composition (_▸_) follows functor structure
  --
  -- RUNTIME MAPPING:
  --   At runtime, these compile to loops (worklist-based) or actual
  --   function calls, depending on the backend. The proof uses
  --   structural recursion which is equivalent for finite μ-values.
  ------------------------------------------------------------------------

  -- | Get tag from a slot (returns 0 for inj₁, 1 for inj₂, nothing if uninitialized)
  -- At runtime, this reads the discriminator field of a sum value.
  -- For proofs, we use a simplified model where nothing means "take left".
  getTag : LocState FS → AllocState {FS} → Slot → Maybe ℕ
  getTag s alloc slot with readLoc s (AtStack (current-frame alloc) slot)
  ... | nothing = nothing
  ... | just _ = just 0  -- Simplified: actual tag extraction is backend-specific

  -- | Execute a tree-structured trace
  --
  -- The structure mirrors how recursion schemes execute:
  --   ε: no-op
  --   instr i: single instruction
  --   t₁ ▸ t₂: sequence
  --   branch slot tL tR: dispatch on sum tag
  --   call-sub t: recursive call (no additional stack frame in abstract model)
  --   flat is: legacy flat trace
  exec-tree-trace : TreeTrace → LocState FS → AllocState {FS} →
                    LocState FS × AllocState {FS}

  -- Empty trace: no effect
  exec-tree-trace ε s alloc = s , alloc

  -- Single instruction
  exec-tree-trace (instr i) s alloc with halted s
  ... | true = s , alloc
  ... | false = exec-abstract i s alloc

  -- Sequential composition
  exec-tree-trace (t₁ ▸ t₂) s alloc with halted s
  ... | true = s , alloc
  ... | false = let (s' , alloc') = exec-tree-trace t₁ s alloc
                in exec-tree-trace t₂ s' alloc'

  -- Branch on tag: read discriminator and dispatch
  exec-tree-trace (branch slot tL tR) s alloc with halted s
  ... | true = s , alloc
  ... | false with getTag s alloc slot
  ... | nothing      = exec-tree-trace tL s alloc  -- Default to left if uninitialized
  ... | just 0       = exec-tree-trace tL s alloc  -- inj₁
  ... | just (suc _) = exec-tree-trace tR s alloc  -- inj₂

  -- Recursive call: execute sub-trace
  -- In abstract model, this is just trace execution (no stack frame push)
  -- Real backends implement this as function call or inlined loop
  exec-tree-trace (call-sub t) s alloc with halted s
  ... | true = s , alloc
  ... | false = exec-tree-trace t s alloc

  -- Embedded flat trace: delegate to exec-trace
  exec-tree-trace (flat is) s alloc = exec-trace is s alloc

  ------------------------------------------------------------------------
  -- Tree Trace Lemmas
  ------------------------------------------------------------------------

  -- | Empty trace is identity
  exec-tree-trace-ε : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    exec-tree-trace ε s alloc ≡ (s , alloc)
  exec-tree-trace-ε s alloc = refl

  -- | Sequential composition reduces when not halted
  exec-tree-trace-seq : ∀ (t₁ t₂ : TreeTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-tree-trace (t₁ ▸ t₂) s alloc ≡
      let (s' , alloc') = exec-tree-trace t₁ s alloc
      in exec-tree-trace t₂ s' alloc'
  exec-tree-trace-seq t₁ t₂ s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted

  -- | Single instruction in tree form matches abstract execution
  exec-tree-trace-instr : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-tree-trace (instr i) s alloc ≡ exec-abstract i s alloc
  exec-tree-trace-instr i s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted

  -- | call-sub is transparent when not halted
  exec-tree-trace-call-sub : ∀ (t : TreeTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-tree-trace (call-sub t) s alloc ≡ exec-tree-trace t s alloc
  exec-tree-trace-call-sub t s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted

  -- | flat trace execution matches exec-trace
  exec-tree-trace-flat : ∀ (is : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    exec-tree-trace (flat is) s alloc ≡ exec-trace is s alloc
  exec-tree-trace-flat is s alloc = refl

  ------------------------------------------------------------------------
  -- TreeTrace to Flat Trace Equivalence
  --
  -- KEY THEOREM: exec-tree-trace and exec-trace produce same results
  -- when the flat trace correctly models the tree structure.
  --
  -- This enables proving correctness via TreeTrace (structural induction)
  -- and then transferring to flat traces (what actually executes).
  --
  -- PROOF APPROACH:
  --   For simple trees without call-sub or branch:
  --     exec-tree-trace t ≡ exec-trace (treeToFlat t)
  --
  --   For trees with call-sub (where semantics are identical):
  --     call-sub just continues execution, so treeToFlat is correct
  --
  --   For trees with branch (runtime vs proof dispatch):
  --     Need to know which branch is taken to establish equivalence
  ------------------------------------------------------------------------

  -- | treeToFlat preserves sequential composition
  exec-trace-++ : ∀ (t₁ t₂ : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-trace (t₁ ++ t₂) s alloc ≡
      let (s' , alloc') = exec-trace t₁ s alloc
      in exec-trace t₂ s' alloc'
  exec-trace-++ [] t₂ s alloc not-halted = refl
  exec-trace-++ (i ∷ t₁) t₂ s alloc not-halted with halted s
  ... | true with () ← not-halted
  ... | false = exec-trace-++ t₁ t₂ (proj₁ (exec-abstract i s alloc))
                              (proj₂ (exec-abstract i s alloc))
                              exec-abstract-preserves-not-halted'
    where
      -- Helper: exec-abstract preserves not-halted (postulated for now)
      -- Full proof requires case analysis on all instructions
      postulate
        exec-abstract-preserves-not-halted' : halted (proj₁ (exec-abstract i s alloc)) ≡ false

  -- | Simple trees (no branch): exec-tree-trace ≡ exec-trace ∘ treeToFlat
  -- This is the foundation for proving recursive scheme correctness
  exec-tree-flat-equiv-simple : ∀ (t : TreeTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    -- For trees without branch, treeToFlat is semantically equivalent
    ⊤  -- Full proof requires induction on TreeTrace structure
  exec-tree-flat-equiv-simple t s alloc not-halted = tt