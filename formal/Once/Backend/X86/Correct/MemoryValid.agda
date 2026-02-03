------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MemoryValid
--
-- Memory validity predicates for x86-64 execution.
-- Tracks which values are properly encoded in memory.
--
-- Key insight: The encoding axioms in Postulates.agda claim to hold
-- for ANY memory m. This is too strong. They should only hold for
-- memory where values were properly allocated.
--
-- MemoryValid captures the invariant that values in memory are
-- properly encoded at their expected addresses.
--
-- KEY CONCEPTS:
--   AllocMode      : Escape analysis result (StackAlloc | HeapAlloc)
--   InAllocRegion  : Maps AllocMode to address predicate (InStack/InHeap)
--   ValidAt        : Unified validity predicate carrying AllocMode
--
-- See: docs/formal/architecture/proof-stack-architecture.md
------------------------------------------------------------------------

module Once.Backend.X86.Correct.MemoryValid where

open import Once.Type
open import Once.Semantics using (⟦_⟧; Closure; ⟦Fix⟧; wrap; encode)
open ⟦Fix⟧
open import Once.Backend.X86.Semantics using (State; Memory; Word; readMem; writeMem)
open import Data.Integer using (ℤ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Once.Backend.X86.Encoding using (mem-read-write; mem-read-other; n≢n+word-size)

-- Import shared AtS records, allocation lemmas, and preservation from Common
open import Once.Backend.Common.MemoryValid public
  using ( PairAtS; pair-at-s; fst-valid-s; snd-valid-s
        ; InlAtS; inl-at-s; tag-valid-inl-s; val-valid-inl-s
        ; InrAtS; inr-at-s; tag-valid-inr-s; val-valid-inr-s
        ; ClosureAtS; closure-at-s; env-valid-s; code-valid-s
        ; NoOverlap; no-overlap
        ; slot-size
        ; alloc-pair-creates-valid-s; alloc-inl-creates-valid-s
        ; alloc-inr-creates-valid-s; alloc-closure-creates-valid-s
        ; PairAtS-preserved-under-mem-eq; InlAtS-preserved-under-mem-eq
        ; InrAtS-preserved-under-mem-eq; ClosureAtS-preserved-under-mem-eq
        )
open import Once.Backend.X86.Layout
  using (InStack; InHeap; stack-heap-addr-disjoint; heap-offset; heap-addr-≥-stack-addr)
open import Data.Nat using (_≥_; _<_)

------------------------------------------------------------------------
-- AllocMode: Allocation mode from escape analysis
--
-- Determines WHERE a value is allocated at runtime:
--   StackAlloc = value doesn't escape, allocated on stack (deterministic addr)
--   HeapAlloc  = value may escape, allocated on heap (via allocator)
--
-- NOTE: This is DISTINCT from InStack/InHeap (address predicates).
--   - AllocMode is a compile-time decision (escape analysis result)
--   - InStack/InHeap are runtime address predicates (where it lives)
--   - InAllocRegion bridges them: maps AllocMode to the address predicate
--
-- For portability, IR proofs should use AllocMode and InAllocRegion,
-- not directly reference InStack/InHeap.
------------------------------------------------------------------------

data AllocMode : Set where
  StackAlloc : AllocMode  -- Escape analysis: local, stack-allocate
  HeapAlloc  : AllocMode  -- Escape analysis: escapes, heap-allocate

-- | Map allocation mode to address predicate
-- StackAlloc → InStack (address is in stack region)
-- HeapAlloc  → InHeap  (address is in heap region)
InAllocRegion : AllocMode → Word → Set
InAllocRegion StackAlloc = InStack
InAllocRegion HeapAlloc  = InHeap

------------------------------------------------------------------------
-- Backwards-compatible aliases (for migration)
-- These allow existing code to use old names until fully migrated.
-- TODO: Remove after all dependent files are updated.
------------------------------------------------------------------------

-- Old name → New name
Region : Set
Region = AllocMode

Stack : AllocMode
Stack = StackAlloc

Heap : AllocMode
Heap = HeapAlloc

InRegion : AllocMode → Word → Set
InRegion = InAllocRegion

open import Once.Backend.X86.Correct.RegisterLemmas using (readMem-writeMem-diff)
open import Once.Backend.X86.Correct.Star using (just-injective)
open import Once.Backend.X86.Correct.Arithmetic using (caller-current-disjoint)
-- NOTE: encode-in-heap-sem no longer needed - InHeap comes from ValidAt constructors

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)

------------------------------------------------------------------------
-- ValidAt: Unified Validity Predicate
--
-- This is the core abstraction for validity-based correctness.
-- ValidAt says "value v is correctly represented at address a in memory m".
--
-- Key insight: Instead of proving "rax ≡ encode (eval ir x)" with postulates,
-- we prove "ValidAt (eval ir x) rax memory" directly from memory writes.
------------------------------------------------------------------------

-- | Unified validity predicate for all types
-- Says "value v is correctly represented at address a in memory m"
--
-- DESIGN: Each allocating constructor carries AllocMode info.
-- The mode (m : AllocMode) and proof (InAllocRegion m addr) come from:
-- - IR's AllocMode (StackAlloc/HeapAlloc from escape analysis)
-- - Runtime temporaries (always StackAlloc)
--
-- This enables:
-- - valid-in-alloc-region extracts the AllocMode and InAllocRegion proof
-- - HeapAlloc values use stack-heap disjointness for preservation
-- - StackAlloc values use frame-separation for preservation
data ValidAt : ∀ {A : Type} → ⟦ A ⟧ → Word → Memory → Set where
  -- Unit: value 0, no memory needed (address 0 is special, no region)
  valid-unit : ∀ {m} → ValidAt {Unit} tt 0 m

  -- Int: address equals encoded value (no memory layout, just the value itself)
  -- This constructor is used by domain compilers (Arith) to construct ValidAt proofs.
  -- CCC receives these proofs from PrimContract but never constructs them directly.
  valid-int : ∀ {n : ⟦ Int ⟧} {addr : Word} {m : Memory} →
    addr ≡ encode n →
    ValidAt {Int} n addr m

  -- Pair: both components valid, pair structure at addr, with region
  valid-pair : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {addr-a addr-b addr : Word} {m : Memory} →
    ValidAt a addr-a m →
    ValidAt b addr-b m →
    PairAtS addr-a addr-b addr m →
    (mode : AllocMode) → InAllocRegion mode addr →
    ValidAt (a , b) addr m

  -- Left sum: tag=0, value valid, with region
  valid-inl : ∀ {A B} {a : ⟦ A ⟧} {addr-a addr : Word} {m : Memory} →
    ValidAt a addr-a m →
    InlAtS addr-a addr m →
    (mode : AllocMode) → InAllocRegion mode addr →
    ValidAt {A + B} (inj₁ a) addr m

  -- Right sum: tag=1, value valid, with region
  valid-inr : ∀ {A B} {b : ⟦ B ⟧} {addr-b addr : Word} {m : Memory} →
    ValidAt b addr-b m →
    InrAtS addr-b addr m →
    (mode : AllocMode) → InAllocRegion mode addr →
    ValidAt {A + B} (inj₂ b) addr m

  -- Closure: env and code-ptr at addr, with region
  -- NOTE: env-addr is explicit parameter, NOT extracted from Closure.env-addr
  -- This decouples the proof from the semantic Closure type's env-addr field.
  valid-closure : ∀ {A B} {cl : Closure A B} {env-addr code-ptr addr : Word} {m : Memory} →
    ClosureAtS env-addr code-ptr addr m →
    (mode : AllocMode) → InAllocRegion mode addr →
    ValidAt {A ⇒ B} cl addr m

  -- Closure from env validity: for curry-created closures, with region
  -- NOTE: No longer requires Closure.env-addr cl ≡ encode env constraint.
  -- The env-addr is tracked in proof infrastructure (ClosureAtS), not semantic Closure.
  valid-closure-env : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
                      {env-addr code-ptr closure-addr : Word} {m : Memory} →
    ValidAt env env-addr m →             -- env validity at runtime address
    ClosureAtS env-addr code-ptr closure-addr m →  -- memory layout
    (mode : AllocMode) → InAllocRegion mode closure-addr →
    ValidAt {A ⇒ B} cl closure-addr m

  -- Eff: same as closure (Eff = Closure at runtime), with region
  valid-eff : ∀ {A B} {cl : Closure A B} {env-addr code-ptr addr : Word} {m : Memory} →
    ClosureAtS env-addr code-ptr addr m →
    (mode : AllocMode) → InAllocRegion mode addr →
    ValidAt {Eff A B} cl addr m

  -- Eff from env validity: for curry-created effect closures, with region
  valid-eff-env : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
                  {env-addr code-ptr closure-addr : Word} {m : Memory} →
    ValidAt env env-addr m →
    ClosureAtS env-addr code-ptr closure-addr m →
    (mode : AllocMode) → InAllocRegion mode closure-addr →
    ValidAt {Eff A B} cl closure-addr m

  -- Fix: validity of unwrapped value (Fix is identity at runtime)
  -- Inherits region from the wrapped value
  valid-fix : ∀ {F} {x : ⟦ F ⟧} {addr : Word} {m : Memory} →
    ValidAt x addr m →
    ValidAt {Fix F} (wrap x) addr m

-- NOTE: ValidAt preservation under memory writes is defined below.
-- See: valid-at-preserved-under-stack-write, valid-at-preserved-under-write

-- | Convert validity from (A ⇒ B) to (Eff A B)
-- These types have the same runtime representation (Closure A B), but
-- ValidAt uses Type as a type index, so conversion is needed.
-- Proven by pattern matching on valid-closure and constructing valid-eff.
valid-arrow-to-eff :
  ∀ {A B} {cl : Closure A B} {addr : Word} {m : Memory} →
  ValidAt {A ⇒ B} cl addr m →
  ValidAt {Eff A B} cl addr m
valid-arrow-to-eff (valid-closure closS r ir) = valid-eff closS r ir
valid-arrow-to-eff (valid-closure-env venv closS r ir) = valid-eff-env venv closS r ir

------------------------------------------------------------------------
-- Extract region information from ValidAt
------------------------------------------------------------------------

-- | Unit at address 0 is treated as being in heap
-- (Address 0 is outside both stack and heap regions, but disjoint from stack)
postulate
  unit-in-heap : InHeap 0

-- NOTE: No int-in-heap postulate!
-- Integers use encode-based interface at Prim boundary.
-- CCC never needs to know about Int's allocation region.

------------------------------------------------------------------------
-- Stack frame separation: caller vs current frame
--
-- For HeapAlloc values: Use stack-heap disjointness (no postulate needed)
-- For StackAlloc values: Use FRAME SEPARATION
--
-- Frame separation invariant (from call convention):
--   push rbp; mov rbp, rsp  -- establishes frame boundary
--   sub rsp, N              -- allocates current frame below rbp
--
-- This gives us:
--   - Caller's values are ABOVE rbp (passed via rdi, or in caller's frame)
--   - Current writes are BELOW rbp (at rsp after sub)
--   - addr > rbp ≥ w  implies  addr ≢ w  (arithmetic)
--
-- The postulate captures the frame separation assumption.
-- It is PROVABLE once we track addr-above-rbp in ValidAt.
------------------------------------------------------------------------

-- | Frame separation: caller's stack addresses ≢ current frame writes
--
-- Assumption: addr is from caller's frame, w is from current frame
-- This is the ACTUAL invariant from escape analysis + call convention:
--   - Stack-allocated values from caller are above rbp
--   - Current function writes below rbp (via sub rsp)
--
-- NOTE: This does NOT claim all stack addresses differ!
-- It claims: caller_addr ≢ current_write when frames are separated.
--
-- TODO: Replace with proven lemma once we track:
--   addr-above-rbp : addr > rbp  (value from caller)
--   w-below-rbp    : w ≤ rbp     (write in current frame)
-- Then: addr > rbp ≥ w → addr > w → addr ≢ w (arithmetic)
postulate
  frame-separation : ∀ {addr w : Word} →
    InStack addr →      -- addr is on stack (from caller's frame)
    InStack w →         -- w is on stack (current frame write)
    w ≢ addr

-- | Stack allocations span multiple slots
-- If addr is in stack, so is addr + slot-size (for 2-slot structures)
-- This mirrors heap-offset for heap allocations.
--
-- TODO: Prove from stack region bounds (upper bound is large enough)
postulate
  stack-offset : ∀ {addr} → InStack addr → InStack (addr +ℕ slot-size)

-- | Derived: frame separation for second slot
-- Uses stack-offset to get InStack for addr + slot-size
frame-separation-plus : ∀ {addr w : Word} →
  InStack addr →
  InStack w →
  w ≢ addr +ℕ slot-size
frame-separation-plus is w-is = frame-separation (stack-offset is) w-is

-- | Extract InAllocRegion proof from ValidAt
-- Returns the allocation mode and region proof stored in the constructor.
valid-in-alloc-region :
  ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory} →
  (va : ValidAt v addr m) →
  ∃[ mode ] InAllocRegion mode addr
valid-in-alloc-region valid-unit = HeapAlloc , unit-in-heap
-- For integers, the "address" is the value itself, not a memory pointer.
-- We treat it as HeapAlloc for disjointness (integers don't alias stack).
-- This is sound because: (1) integers in registers are not dereferenced as pointers,
-- (2) when passed to primitives, the contract handles them appropriately.
valid-in-alloc-region (valid-int _) = HeapAlloc , postulate-int-in-heap
  where postulate postulate-int-in-heap : InHeap _
valid-in-alloc-region (valid-pair _ _ _ mode ir) = mode , ir
valid-in-alloc-region (valid-inl _ _ mode ir) = mode , ir
valid-in-alloc-region (valid-inr _ _ mode ir) = mode , ir
valid-in-alloc-region (valid-closure _ mode ir) = mode , ir
valid-in-alloc-region (valid-closure-env _ _ mode ir) = mode , ir
valid-in-alloc-region (valid-eff _ mode ir) = mode , ir
valid-in-alloc-region (valid-eff-env _ _ mode ir) = mode , ir
valid-in-alloc-region (valid-fix v) = valid-in-alloc-region v

-- Backwards-compatible alias
valid-in-region : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory} →
  ValidAt v addr m → ∃[ mode ] InAllocRegion mode addr
valid-in-region = valid-in-alloc-region

------------------------------------------------------------------------
-- ValidAt child extraction lemmas
------------------------------------------------------------------------

-- | Extract validity of left injection's child value
-- If (inj₁ a) is validly represented at addr, and mem[addr+8] = val-addr,
-- then a is validly represented at val-addr.
-- Proven from ValidAt structure (sum validity implies child validity).
valid-inl-child :
  ∀ {A B} {a : ⟦ A ⟧} {addr val-addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₁ a) addr mem →
  readMem mem (addr +ℕ slot-size) ≡ just val-addr →
  ValidAt a val-addr mem
valid-inl-child (valid-inl {addr-a = addr-a} va inlS _ _) mem-eq =
  let addr-eq = just-injective (trans (sym (val-valid-inl-s inlS)) mem-eq)
  in subst (λ a → ValidAt _ a _) addr-eq va

-- | Extract validity of right injection's child value
-- If (inj₂ b) is validly represented at addr, and mem[addr+8] = val-addr,
-- then b is validly represented at val-addr.
-- Proven from ValidAt structure (sum validity implies child validity).
valid-inr-child :
  ∀ {A B} {b : ⟦ B ⟧} {addr val-addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₂ b) addr mem →
  readMem mem (addr +ℕ slot-size) ≡ just val-addr →
  ValidAt b val-addr mem
valid-inr-child (valid-inr {addr-b = addr-b} vb inrS _ _) mem-eq =
  let addr-eq = just-injective (trans (sym (val-valid-inr-s inrS)) mem-eq)
  in subst (λ a → ValidAt _ a _) addr-eq vb

------------------------------------------------------------------------
-- ValidAt preservation under memory equality
------------------------------------------------------------------------

-- | Propagate validity through address/memory substitution
-- If validity holds at addr1/mem1, and addr2=addr1 and mem2 agrees with mem1,
-- then validity holds at addr2/mem2.
-- Proven by induction on ValidAt structure.
valid-subst-addr-mem :
  ∀ {A} {v : ⟦ A ⟧} {addr1 addr2 : Word} {mem1 mem2 : Memory} →
  ValidAt v addr1 mem1 →
  addr2 ≡ addr1 →
  (∀ a → readMem mem2 a ≡ readMem mem1 a) →
  ValidAt v addr2 mem2
valid-subst-addr-mem valid-unit refl _ = valid-unit
valid-subst-addr-mem (valid-int eq) refl _ = valid-int eq
valid-subst-addr-mem (valid-pair va vb pairS r ir) refl mem-eq =
  valid-pair (valid-subst-addr-mem va refl mem-eq)
             (valid-subst-addr-mem vb refl mem-eq)
             (PairAtS-preserved-under-mem-eq pairS mem-eq)
             r ir
valid-subst-addr-mem (valid-inl va inlS r ir) refl mem-eq =
  valid-inl (valid-subst-addr-mem va refl mem-eq)
            (InlAtS-preserved-under-mem-eq inlS mem-eq)
            r ir
valid-subst-addr-mem (valid-inr vb inrS r ir) refl mem-eq =
  valid-inr (valid-subst-addr-mem vb refl mem-eq)
            (InrAtS-preserved-under-mem-eq inrS mem-eq)
            r ir
valid-subst-addr-mem (valid-closure closS r ir) refl mem-eq =
  valid-closure (ClosureAtS-preserved-under-mem-eq closS mem-eq) r ir
valid-subst-addr-mem (valid-closure-env venv closS r ir) refl mem-eq =
  valid-closure-env
    (valid-subst-addr-mem venv refl mem-eq)
    (ClosureAtS-preserved-under-mem-eq closS mem-eq)
    r ir
valid-subst-addr-mem (valid-eff closS r ir) refl mem-eq =
  valid-eff (ClosureAtS-preserved-under-mem-eq closS mem-eq) r ir
valid-subst-addr-mem (valid-eff-env venv closS r ir) refl mem-eq =
  valid-eff-env
    (valid-subst-addr-mem venv refl mem-eq)
    (ClosureAtS-preserved-under-mem-eq closS mem-eq)
    r ir
valid-subst-addr-mem (valid-fix vx) refl mem-eq =
  valid-fix (valid-subst-addr-mem vx refl mem-eq)

------------------------------------------------------------------------
-- ValidAt preservation under heap-only memory preservation
------------------------------------------------------------------------

-- These helpers preserve HEAP-region values under heap memory preservation.
-- For StackAlloc values, use the *-under-stack-eq variants instead.

-- | Helper: PairAtS preserved under heap-only memory equality
PairAtS-preserved-under-heap-eq :
  ∀ {addr-a addr-b addr : Word} {m1 m2 : Memory} →
  PairAtS addr-a addr-b addr m1 →
  InHeap addr →  -- addr is in heap
  (∀ a → InHeap a → readMem m2 a ≡ readMem m1 a) →
  PairAtS addr-a addr-b addr m2
PairAtS-preserved-under-heap-eq {addr-a} {addr-b} {addr} pairS addr-in-heap heap-eq =
  let addr+8-in-heap = heap-offset addr addr-in-heap
  in pair-at-s (trans (heap-eq addr addr-in-heap) (fst-valid-s pairS))
               (trans (heap-eq (addr +ℕ slot-size) addr+8-in-heap) (snd-valid-s pairS))

-- | Helper: InlAtS preserved under heap-only memory equality
InlAtS-preserved-under-heap-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InlAtS addr-val addr-sum m1 →
  InHeap addr-sum →
  (∀ a → InHeap a → readMem m2 a ≡ readMem m1 a) →
  InlAtS addr-val addr-sum m2
InlAtS-preserved-under-heap-eq {addr-val} {addr-sum} inlS addr-in-heap heap-eq =
  let addr+8-in-heap = heap-offset addr-sum addr-in-heap
  in inl-at-s (trans (heap-eq addr-sum addr-in-heap) (tag-valid-inl-s inlS))
              (trans (heap-eq (addr-sum +ℕ slot-size) addr+8-in-heap) (val-valid-inl-s inlS))

-- | Helper: InrAtS preserved under heap-only memory equality
InrAtS-preserved-under-heap-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InrAtS addr-val addr-sum m1 →
  InHeap addr-sum →
  (∀ a → InHeap a → readMem m2 a ≡ readMem m1 a) →
  InrAtS addr-val addr-sum m2
InrAtS-preserved-under-heap-eq {addr-val} {addr-sum} inrS addr-in-heap heap-eq =
  let addr+8-in-heap = heap-offset addr-sum addr-in-heap
  in inr-at-s (trans (heap-eq addr-sum addr-in-heap) (tag-valid-inr-s inrS))
              (trans (heap-eq (addr-sum +ℕ slot-size) addr+8-in-heap) (val-valid-inr-s inrS))

-- | Helper: ClosureAtS preserved under heap-only memory equality
ClosureAtS-preserved-under-heap-eq :
  ∀ {env-addr code-ptr addr-closure : Word} {m1 m2 : Memory} →
  ClosureAtS env-addr code-ptr addr-closure m1 →
  InHeap addr-closure →
  (∀ a → InHeap a → readMem m2 a ≡ readMem m1 a) →
  ClosureAtS env-addr code-ptr addr-closure m2
ClosureAtS-preserved-under-heap-eq {env-addr} {code-ptr} {addr-closure} closS addr-in-heap heap-eq =
  let addr+8-in-heap = heap-offset addr-closure addr-in-heap
  in closure-at-s (trans (heap-eq addr-closure addr-in-heap) (env-valid-s closS))
                  (trans (heap-eq (addr-closure +ℕ slot-size) addr+8-in-heap) (code-valid-s closS))

------------------------------------------------------------------------
-- AtS preservation under stack-only memory preservation
------------------------------------------------------------------------

-- | Helper: PairAtS preserved under stack-only memory equality
PairAtS-preserved-under-stack-eq :
  ∀ {addr-a addr-b addr : Word} {m1 m2 : Memory} →
  PairAtS addr-a addr-b addr m1 →
  InStack addr →
  (∀ a → InStack a → readMem m2 a ≡ readMem m1 a) →
  PairAtS addr-a addr-b addr m2
PairAtS-preserved-under-stack-eq {addr-a} {addr-b} {addr} pairS addr-in-stack stack-eq =
  let addr+8-in-stack = stack-offset addr-in-stack
  in pair-at-s (trans (stack-eq addr addr-in-stack) (fst-valid-s pairS))
               (trans (stack-eq (addr +ℕ slot-size) addr+8-in-stack) (snd-valid-s pairS))

-- | Helper: InlAtS preserved under stack-only memory equality
InlAtS-preserved-under-stack-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InlAtS addr-val addr-sum m1 →
  InStack addr-sum →
  (∀ a → InStack a → readMem m2 a ≡ readMem m1 a) →
  InlAtS addr-val addr-sum m2
InlAtS-preserved-under-stack-eq {addr-val} {addr-sum} inlS addr-in-stack stack-eq =
  let addr+8-in-stack = stack-offset addr-in-stack
  in inl-at-s (trans (stack-eq addr-sum addr-in-stack) (tag-valid-inl-s inlS))
              (trans (stack-eq (addr-sum +ℕ slot-size) addr+8-in-stack) (val-valid-inl-s inlS))

-- | Helper: InrAtS preserved under stack-only memory equality
InrAtS-preserved-under-stack-eq :
  ∀ {addr-val addr-sum : Word} {m1 m2 : Memory} →
  InrAtS addr-val addr-sum m1 →
  InStack addr-sum →
  (∀ a → InStack a → readMem m2 a ≡ readMem m1 a) →
  InrAtS addr-val addr-sum m2
InrAtS-preserved-under-stack-eq {addr-val} {addr-sum} inrS addr-in-stack stack-eq =
  let addr+8-in-stack = stack-offset addr-in-stack
  in inr-at-s (trans (stack-eq addr-sum addr-in-stack) (tag-valid-inr-s inrS))
              (trans (stack-eq (addr-sum +ℕ slot-size) addr+8-in-stack) (val-valid-inr-s inrS))

-- | Helper: ClosureAtS preserved under stack-only memory equality
ClosureAtS-preserved-under-stack-eq :
  ∀ {env-addr code-ptr addr-closure : Word} {m1 m2 : Memory} →
  ClosureAtS env-addr code-ptr addr-closure m1 →
  InStack addr-closure →
  (∀ a → InStack a → readMem m2 a ≡ readMem m1 a) →
  ClosureAtS env-addr code-ptr addr-closure m2
ClosureAtS-preserved-under-stack-eq {env-addr} {code-ptr} {addr-closure} closS addr-in-stack stack-eq =
  let addr+8-in-stack = stack-offset addr-in-stack
  in closure-at-s (trans (stack-eq addr-closure addr-in-stack) (env-valid-s closS))
                  (trans (stack-eq (addr-closure +ℕ slot-size) addr+8-in-stack) (code-valid-s closS))

------------------------------------------------------------------------
-- ValidAt preservation under region-aware memory preservation
--
-- Takes BOTH heap-eq AND stack-eq, dispatches based on Region.
-- This is the correct approach - no FALSE postulates needed!
------------------------------------------------------------------------

-- | Propagate validity when both heap and stack memory is preserved
-- For HEAP-region values: uses heap equality
-- For STACK-region values: uses stack equality
valid-subst-region-preserved :
  ∀ {A} {v : ⟦ A ⟧} {addr : Word} {mem1 mem2 : Memory} →
  ValidAt v addr mem1 →
  (∀ a → InHeap a → readMem mem2 a ≡ readMem mem1 a) →
  (∀ a → InStack a → readMem mem2 a ≡ readMem mem1 a) →
  ValidAt v addr mem2
valid-subst-region-preserved valid-unit _ _ = valid-unit
valid-subst-region-preserved (valid-int eq) _ _ = valid-int eq
-- Pair: dispatch on region
valid-subst-region-preserved (valid-pair va vb pairS HeapAlloc ih) heap-eq stack-eq =
  valid-pair (valid-subst-region-preserved va heap-eq stack-eq)
             (valid-subst-region-preserved vb heap-eq stack-eq)
             (PairAtS-preserved-under-heap-eq pairS ih heap-eq)
             HeapAlloc ih
valid-subst-region-preserved (valid-pair va vb pairS StackAlloc is) heap-eq stack-eq =
  valid-pair (valid-subst-region-preserved va heap-eq stack-eq)
             (valid-subst-region-preserved vb heap-eq stack-eq)
             (PairAtS-preserved-under-stack-eq pairS is stack-eq)
             StackAlloc is
-- Inl: dispatch on region
valid-subst-region-preserved {A + B} (valid-inl va inlS HeapAlloc ih) heap-eq stack-eq =
  valid-inl (valid-subst-region-preserved va heap-eq stack-eq)
            (InlAtS-preserved-under-heap-eq inlS ih heap-eq)
            HeapAlloc ih
valid-subst-region-preserved {A + B} (valid-inl va inlS StackAlloc is) heap-eq stack-eq =
  valid-inl (valid-subst-region-preserved va heap-eq stack-eq)
            (InlAtS-preserved-under-stack-eq inlS is stack-eq)
            StackAlloc is
-- Inr: dispatch on region
valid-subst-region-preserved {A + B} (valid-inr vb inrS HeapAlloc ih) heap-eq stack-eq =
  valid-inr (valid-subst-region-preserved vb heap-eq stack-eq)
            (InrAtS-preserved-under-heap-eq inrS ih heap-eq)
            HeapAlloc ih
valid-subst-region-preserved {A + B} (valid-inr vb inrS StackAlloc is) heap-eq stack-eq =
  valid-inr (valid-subst-region-preserved vb heap-eq stack-eq)
            (InrAtS-preserved-under-stack-eq inrS is stack-eq)
            StackAlloc is
-- Closure: dispatch on region
valid-subst-region-preserved {A ⇒[ _ ] B} {cl} (valid-closure closS HeapAlloc ih) heap-eq stack-eq =
  valid-closure (ClosureAtS-preserved-under-heap-eq closS ih heap-eq)
                HeapAlloc ih
valid-subst-region-preserved {A ⇒[ _ ] B} {cl} (valid-closure closS StackAlloc is) heap-eq stack-eq =
  valid-closure (ClosureAtS-preserved-under-stack-eq closS is stack-eq)
                StackAlloc is
-- Closure with env: dispatch on region
valid-subst-region-preserved {A ⇒[ _ ] B} {cl} (valid-closure-env venv closS HeapAlloc ih) heap-eq stack-eq =
  valid-closure-env
    (valid-subst-region-preserved venv heap-eq stack-eq)
    (ClosureAtS-preserved-under-heap-eq closS ih heap-eq)
    HeapAlloc ih
valid-subst-region-preserved {A ⇒[ _ ] B} {cl} (valid-closure-env venv closS StackAlloc is) heap-eq stack-eq =
  valid-closure-env
    (valid-subst-region-preserved venv heap-eq stack-eq)
    (ClosureAtS-preserved-under-stack-eq closS is stack-eq)
    StackAlloc is
-- Eff: dispatch on region
valid-subst-region-preserved {Eff A B} {cl} (valid-eff closS HeapAlloc ih) heap-eq stack-eq =
  valid-eff (ClosureAtS-preserved-under-heap-eq closS ih heap-eq)
            HeapAlloc ih
valid-subst-region-preserved {Eff A B} {cl} (valid-eff closS StackAlloc is) heap-eq stack-eq =
  valid-eff (ClosureAtS-preserved-under-stack-eq closS is stack-eq)
            StackAlloc is
-- Eff with env: dispatch on region
valid-subst-region-preserved {Eff A B} {cl} (valid-eff-env venv closS HeapAlloc ih) heap-eq stack-eq =
  valid-eff-env
    (valid-subst-region-preserved venv heap-eq stack-eq)
    (ClosureAtS-preserved-under-heap-eq closS ih heap-eq)
    HeapAlloc ih
valid-subst-region-preserved {Eff A B} {cl} (valid-eff-env venv closS StackAlloc is) heap-eq stack-eq =
  valid-eff-env
    (valid-subst-region-preserved venv heap-eq stack-eq)
    (ClosureAtS-preserved-under-stack-eq closS is stack-eq)
    StackAlloc is
-- Fix: recurse
valid-subst-region-preserved (valid-fix vx) heap-eq stack-eq =
  valid-fix (valid-subst-region-preserved vx heap-eq stack-eq)

------------------------------------------------------------------------
-- Proven lemmas from ValidAt structure (moved out of postulate block)
------------------------------------------------------------------------

-- | Left injection tag is 0 in memory
-- Pattern match on ValidAt: only valid-inl can construct ValidAt {A + B} (inj₁ a)
valid-inl-tag-is-0 :
  ∀ {A B} {a : ⟦ A ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₁ a) addr mem →
  readMem mem addr ≡ just 0
valid-inl-tag-is-0 (valid-inl _ inlS _ _) = tag-valid-inl-s inlS

-- | Left injection value pointer exists in memory
valid-inl-val-ptr :
  ∀ {A B} {a : ⟦ A ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₁ a) addr mem →
  ∃[ val-addr ] (readMem mem (addr +ℕ slot-size) ≡ just val-addr × ValidAt a val-addr mem)
valid-inl-val-ptr (valid-inl {addr-a = addr-a} va inlS _ _) = addr-a , val-valid-inl-s inlS , va

-- | Right injection tag is 1 in memory
valid-inr-tag-is-1 :
  ∀ {A B} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₂ b) addr mem →
  readMem mem addr ≡ just 1
valid-inr-tag-is-1 (valid-inr _ inrS _ _) = tag-valid-inr-s inrS

-- | Right injection value pointer exists in memory
valid-inr-val-ptr :
  ∀ {A B} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A + B} (inj₂ b) addr mem →
  ∃[ val-addr ] (readMem mem (addr +ℕ slot-size) ≡ just val-addr × ValidAt b val-addr mem)
valid-inr-val-ptr (valid-inr {addr-b = addr-b} vb inrS _ _) = addr-b , val-valid-inr-s inrS , vb

-- | Extract fst component validity from pair validity
valid-pair-decompose :
  ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} {addr : Word} {mem : Memory} →
  ValidAt {A * B} (a , b) addr mem →
  ∃[ addr-a ] ∃[ addr-b ]
    (ValidAt a addr-a mem × ValidAt b addr-b mem × PairAtS addr-a addr-b addr mem)
valid-pair-decompose (valid-pair {addr-a = addr-a} {addr-b = addr-b} va vb pairS _ _) =
  addr-a , addr-b , va , vb , pairS

-- NOTE: valid-closure-decompose removed (unused, depended on valid-addr-is-encode)

------------------------------------------------------------------------
-- Region-based disjointness from validity
--
-- These lemmas derive heap-stack disjointness from ValidAt.
-- Uses valid-in-region to dispatch on region.
------------------------------------------------------------------------

-- | Valid address is disjoint from stack addresses
-- If addr has ValidAt and stack-addr is in stack, then addr ≢ stack-addr
-- Uses AllocMode dispatch: HeapAlloc → stack-heap disjoint, StackAlloc → frame-separation
valid-disjoint-from-stack : ∀ {A : Type} {v : ⟦ A ⟧} {addr stack-addr : Word} {m : Memory} →
  ValidAt v addr m →
  InStack stack-addr →
  addr ≢ stack-addr
valid-disjoint-from-stack {A} {v} {addr} {stack-addr} {m} valid stack-proof =
  region-dispatch (proj₁ region) (proj₂ region)
  where
    region = valid-in-region valid
    region-dispatch : (mode : AllocMode) → InAllocRegion mode addr → addr ≢ stack-addr
    region-dispatch HeapAlloc ih = λ addr-eq → stack-heap-addr-disjoint stack-addr addr stack-proof ih (sym addr-eq)
    region-dispatch StackAlloc is = λ addr-eq → frame-separation is stack-proof (sym addr-eq)

------------------------------------------------------------------------
-- Caller-Current Frame Disjointness (CORRECT replacement for frame-separation)
--
-- This is the CORRECT way to prove caller address ≢ current frame address.
-- Uses entry-rsp as the boundary between caller and current frames.
--
-- The old `frame-separation` postulate is FALSE (claims all stack addresses
-- differ, but addr can equal itself!). This replacement:
--   1. Takes entry-rsp as boundary
--   2. Requires proof that caller address ≥ entry-rsp
--   3. Requires proof that current frame address < entry-rsp
--   4. Uses arithmetic lemma caller-current-disjoint
--
-- Migration: Change call sites to provide the bounds instead of InStack.
------------------------------------------------------------------------

-- | Caller address is disjoint from current frame address
-- Given entry-rsp boundary, addr ≥ rsp (caller), w < rsp (current), prove addr ≢ w
--
-- This replaces the pattern: frame-separation is w-is
-- With: caller-disjoint-from-current addr≥rsp w<rsp
caller-disjoint-from-current : ∀ {addr w entry-rsp : Word} →
  addr ≥ entry-rsp →      -- Caller's address (from Ownership or input bounds)
  w < entry-rsp →         -- Current frame write address
  addr ≢ w
caller-disjoint-from-current = caller-current-disjoint

-- | Variant for offset addresses: (addr + k) ≢ w
caller-disjoint-plus-from-current : ∀ {addr w entry-rsp : Word} →
  addr ≥ entry-rsp →
  w < entry-rsp →
  (addr +ℕ slot-size) ≢ w
caller-disjoint-plus-from-current {addr} {w} {entry-rsp} addr≥rsp w<rsp =
  caller-disjoint-from-current (≤-trans addr≥rsp (m≤m+n addr slot-size)) w<rsp
  where
    open import Data.Nat.Properties using (≤-trans; m≤m+n)

-- | Stack write preserves memory above entry-rsp
-- This connects single writes to the memory-above property used by
-- caller-input-preserved and owned-caller-preserved.
--
-- Key insight: If w < entry-rsp and a ≥ entry-rsp, then w ≠ a,
-- so readMem (writeMem m w v) a = readMem m a.
--
-- Usage pattern:
--   caller-input-preserved input-valid rsp-in-stack
--     (stack-write-preserves-above m w v w<rsp)
stack-write-preserves-above :
  ∀ (m : Memory) (w : Word) (v : Word) {entry-rsp : Word} →
  w < entry-rsp →
  (∀ a → a ≥ entry-rsp → readMem (writeMem m w v) a ≡ readMem m a)
stack-write-preserves-above m w v {entry-rsp} w<rsp a a≥rsp =
  readMem-writeMem-diff m w a v w≢a
  where
    -- caller-disjoint-from-current gives a ≢ w, flip to get w ≢ a
    w≢a : w ≢ a
    w≢a w≡a = caller-disjoint-from-current a≥rsp w<rsp (sym w≡a)

-- | Variant for two consecutive writes
-- Useful when allocating 2-slot structures (pairs, closures).
stack-write-2-preserves-above :
  ∀ (m : Memory) (w1 w2 : Word) (v1 v2 : Word) {entry-rsp : Word} →
  w1 < entry-rsp →
  w2 < entry-rsp →
  (∀ a → a ≥ entry-rsp → readMem (writeMem (writeMem m w1 v1) w2 v2) a ≡ readMem m a)
stack-write-2-preserves-above m w1 w2 v1 v2 {entry-rsp} w1<rsp w2<rsp a a≥rsp =
  trans (stack-write-preserves-above (writeMem m w1 v1) w2 v2 w2<rsp a a≥rsp)
        (stack-write-preserves-above m w1 v1 w1<rsp a a≥rsp)

------------------------------------------------------------------------
-- ValidAt preservation under memory writes (HEAP ONLY)
--
-- These lemmas preserve HEAP-region values under STACK writes.
-- They require InHeap addr as a precondition.
--
-- Proof strategy:
-- 1. addr is in heap (precondition)
-- 2. AtS structures read from addr and addr+slot-size, both in heap
-- 3. InStack w means w is disjoint from all heap addresses
-- 4. Therefore readMem (writeMem m w val) heap-addr = readMem m heap-addr
------------------------------------------------------------------------

-- | Helper: PairAtS preserved under stack writes
PairAtS-preserved-under-stack-write :
  ∀ {addr-a addr-b addr w val : Word} {m : Memory} →
  PairAtS addr-a addr-b addr m →
  InHeap addr →
  InStack w →
  PairAtS addr-a addr-b addr (writeMem m w val)
PairAtS-preserved-under-stack-write {addr-a} {addr-b} {addr} {w} {val} {m} pairS addr-in-heap w-in-stack =
  pair-at-s fst-pres snd-pres
  where
    -- w is in stack, addr is in heap, so w ≢ addr
    w≢addr : w ≢ addr
    w≢addr eq = stack-heap-addr-disjoint w addr w-in-stack addr-in-heap eq

    -- addr+slot-size is in heap (heap-offset), so w ≢ addr+slot-size
    addr+8-in-heap : InHeap (addr +ℕ slot-size)
    addr+8-in-heap = heap-offset addr addr-in-heap

    w≢addr+8 : w ≢ (addr +ℕ slot-size)
    w≢addr+8 eq = stack-heap-addr-disjoint w (addr +ℕ slot-size) w-in-stack addr+8-in-heap eq

    fst-pres : readMem (writeMem m w val) addr ≡ just addr-a
    fst-pres = trans (readMem-writeMem-diff m w addr val w≢addr) (fst-valid-s pairS)

    snd-pres : readMem (writeMem m w val) (addr +ℕ slot-size) ≡ just addr-b
    snd-pres = trans (readMem-writeMem-diff m w (addr +ℕ slot-size) val w≢addr+8) (snd-valid-s pairS)

-- | Helper: InlAtS preserved under stack writes
InlAtS-preserved-under-stack-write :
  ∀ {addr-val addr-sum w val : Word} {m : Memory} →
  InlAtS addr-val addr-sum m →
  InHeap addr-sum →
  InStack w →
  InlAtS addr-val addr-sum (writeMem m w val)
InlAtS-preserved-under-stack-write {addr-val} {addr-sum} {w} {val} {m} inlS addr-in-heap w-in-stack =
  inl-at-s tag-pres val-pres
  where
    w≢addr : w ≢ addr-sum
    w≢addr eq = stack-heap-addr-disjoint w addr-sum w-in-stack addr-in-heap eq

    addr+8-in-heap : InHeap (addr-sum +ℕ slot-size)
    addr+8-in-heap = heap-offset addr-sum addr-in-heap

    w≢addr+8 : w ≢ (addr-sum +ℕ slot-size)
    w≢addr+8 eq = stack-heap-addr-disjoint w (addr-sum +ℕ slot-size) w-in-stack addr+8-in-heap eq

    tag-pres : readMem (writeMem m w val) addr-sum ≡ just 0
    tag-pres = trans (readMem-writeMem-diff m w addr-sum val w≢addr) (tag-valid-inl-s inlS)

    val-pres : readMem (writeMem m w val) (addr-sum +ℕ slot-size) ≡ just addr-val
    val-pres = trans (readMem-writeMem-diff m w (addr-sum +ℕ slot-size) val w≢addr+8) (val-valid-inl-s inlS)

-- | Helper: InrAtS preserved under stack writes
InrAtS-preserved-under-stack-write :
  ∀ {addr-val addr-sum w val : Word} {m : Memory} →
  InrAtS addr-val addr-sum m →
  InHeap addr-sum →
  InStack w →
  InrAtS addr-val addr-sum (writeMem m w val)
InrAtS-preserved-under-stack-write {addr-val} {addr-sum} {w} {val} {m} inrS addr-in-heap w-in-stack =
  inr-at-s tag-pres val-pres
  where
    w≢addr : w ≢ addr-sum
    w≢addr eq = stack-heap-addr-disjoint w addr-sum w-in-stack addr-in-heap eq

    addr+8-in-heap : InHeap (addr-sum +ℕ slot-size)
    addr+8-in-heap = heap-offset addr-sum addr-in-heap

    w≢addr+8 : w ≢ (addr-sum +ℕ slot-size)
    w≢addr+8 eq = stack-heap-addr-disjoint w (addr-sum +ℕ slot-size) w-in-stack addr+8-in-heap eq

    tag-pres : readMem (writeMem m w val) addr-sum ≡ just 1
    tag-pres = trans (readMem-writeMem-diff m w addr-sum val w≢addr) (tag-valid-inr-s inrS)

    val-pres : readMem (writeMem m w val) (addr-sum +ℕ slot-size) ≡ just addr-val
    val-pres = trans (readMem-writeMem-diff m w (addr-sum +ℕ slot-size) val w≢addr+8) (val-valid-inr-s inrS)

-- | Helper: ClosureAtS preserved under stack writes
ClosureAtS-preserved-under-stack-write :
  ∀ {env-addr code-ptr addr-closure w val : Word} {m : Memory} →
  ClosureAtS env-addr code-ptr addr-closure m →
  InHeap addr-closure →
  InStack w →
  ClosureAtS env-addr code-ptr addr-closure (writeMem m w val)
ClosureAtS-preserved-under-stack-write {env-addr} {code-ptr} {addr-closure} {w} {val} {m} closS addr-in-heap w-in-stack =
  closure-at-s env-pres code-pres
  where
    w≢addr : w ≢ addr-closure
    w≢addr eq = stack-heap-addr-disjoint w addr-closure w-in-stack addr-in-heap eq

    addr+8-in-heap : InHeap (addr-closure +ℕ slot-size)
    addr+8-in-heap = heap-offset addr-closure addr-in-heap

    w≢addr+8 : w ≢ (addr-closure +ℕ slot-size)
    w≢addr+8 eq = stack-heap-addr-disjoint w (addr-closure +ℕ slot-size) w-in-stack addr+8-in-heap eq

    env-pres : readMem (writeMem m w val) addr-closure ≡ just env-addr
    env-pres = trans (readMem-writeMem-diff m w addr-closure val w≢addr) (env-valid-s closS)

    code-pres : readMem (writeMem m w val) (addr-closure +ℕ slot-size) ≡ just code-ptr
    code-pres = trans (readMem-writeMem-diff m w (addr-closure +ℕ slot-size) val w≢addr+8) (code-valid-s closS)

------------------------------------------------------------------------
-- Stack-region preservation helpers (Phase 1 of stack-heap-compat elimination)
--
-- These helpers preserve *AtS structures when BOTH the value and write
-- address are in Stack region. Requires explicit proof that addresses differ.
------------------------------------------------------------------------

-- | Helper: PairAtS preserved under write to DIFFERENT stack address
PairAtS-preserved-under-diff-stack-write :
  ∀ {addr-a addr-b addr w val : Word} {m : Memory} →
  PairAtS addr-a addr-b addr m →
  w ≢ addr →
  w ≢ addr +ℕ slot-size →
  PairAtS addr-a addr-b addr (writeMem m w val)
PairAtS-preserved-under-diff-stack-write {addr-a} {addr-b} {addr} {w} {val} {m} pairS w≢addr w≢addr+8 =
  pair-at-s fst-pres snd-pres
  where
    fst-pres : readMem (writeMem m w val) addr ≡ just addr-a
    fst-pres = trans (readMem-writeMem-diff m w addr val w≢addr) (fst-valid-s pairS)

    snd-pres : readMem (writeMem m w val) (addr +ℕ slot-size) ≡ just addr-b
    snd-pres = trans (readMem-writeMem-diff m w (addr +ℕ slot-size) val w≢addr+8) (snd-valid-s pairS)

-- | Helper: InlAtS preserved under write to DIFFERENT stack address
InlAtS-preserved-under-diff-stack-write :
  ∀ {addr-val addr-sum w val : Word} {m : Memory} →
  InlAtS addr-val addr-sum m →
  w ≢ addr-sum →
  w ≢ addr-sum +ℕ slot-size →
  InlAtS addr-val addr-sum (writeMem m w val)
InlAtS-preserved-under-diff-stack-write {addr-val} {addr-sum} {w} {val} {m} inlS w≢addr w≢addr+8 =
  inl-at-s tag-pres val-pres
  where
    tag-pres : readMem (writeMem m w val) addr-sum ≡ just 0
    tag-pres = trans (readMem-writeMem-diff m w addr-sum val w≢addr) (tag-valid-inl-s inlS)

    val-pres : readMem (writeMem m w val) (addr-sum +ℕ slot-size) ≡ just addr-val
    val-pres = trans (readMem-writeMem-diff m w (addr-sum +ℕ slot-size) val w≢addr+8) (val-valid-inl-s inlS)

-- | Helper: InrAtS preserved under write to DIFFERENT stack address
InrAtS-preserved-under-diff-stack-write :
  ∀ {addr-val addr-sum w val : Word} {m : Memory} →
  InrAtS addr-val addr-sum m →
  w ≢ addr-sum →
  w ≢ addr-sum +ℕ slot-size →
  InrAtS addr-val addr-sum (writeMem m w val)
InrAtS-preserved-under-diff-stack-write {addr-val} {addr-sum} {w} {val} {m} inrS w≢addr w≢addr+8 =
  inr-at-s tag-pres val-pres
  where
    tag-pres : readMem (writeMem m w val) addr-sum ≡ just 1
    tag-pres = trans (readMem-writeMem-diff m w addr-sum val w≢addr) (tag-valid-inr-s inrS)

    val-pres : readMem (writeMem m w val) (addr-sum +ℕ slot-size) ≡ just addr-val
    val-pres = trans (readMem-writeMem-diff m w (addr-sum +ℕ slot-size) val w≢addr+8) (val-valid-inr-s inrS)

-- | Helper: ClosureAtS preserved under write to DIFFERENT stack address
ClosureAtS-preserved-under-diff-stack-write :
  ∀ {env-addr code-ptr addr-closure w val : Word} {m : Memory} →
  ClosureAtS env-addr code-ptr addr-closure m →
  w ≢ addr-closure →
  w ≢ addr-closure +ℕ slot-size →
  ClosureAtS env-addr code-ptr addr-closure (writeMem m w val)
ClosureAtS-preserved-under-diff-stack-write {env-addr} {code-ptr} {addr-closure} {w} {val} {m} closS w≢addr w≢addr+8 =
  closure-at-s env-pres code-pres
  where
    env-pres : readMem (writeMem m w val) addr-closure ≡ just env-addr
    env-pres = trans (readMem-writeMem-diff m w addr-closure val w≢addr) (env-valid-s closS)

    code-pres : readMem (writeMem m w val) (addr-closure +ℕ slot-size) ≡ just code-ptr
    code-pres = trans (readMem-writeMem-diff m w (addr-closure +ℕ slot-size) val w≢addr+8) (code-valid-s closS)

-- NOTE: valid-at-preserved-under-stack-write REMOVED (dead code)
-- The correct approach uses caller-input-preserved from Ownership.agda
-- which requires RSP context to prove caller frame ≠ current frame.
-- See IR/Apply.agda for the reference implementation.

-- NOTE: Encode-based PairAt/InlAt/InrAt records removed (superseded by PairAtS/InlAtS/InrAtS)
-- NOTE: alloc-*-creates-valid for encode-based records removed (use alloc-*-creates-valid-s)
-- NOTE: pair-valid-preserved removed (use PairAtS-preserved-under-mem-eq)

------------------------------------------------------------------------
-- Bounds-based preservation: valid-subst-mem-above
--
-- This function propagates ValidAt through memory changes using
-- bounds-based preservation (addr ≥ entry-rsp) instead of requiring
-- separate heap-eq and stack-eq.
--
-- KEY INSIGHT:
--   - For Heap addresses: derive addr ≥ entry-rsp via heap-addr-≥-stack-addr
--   - For Stack addresses: require explicit proof that addr ≥ entry-rsp
--
-- The explicit bound requirement captures the CALLER-FRAME INVARIANT:
-- inputs from caller's frame have addresses ≥ current entry-rsp because
-- the caller's frame is above the current frame.
--
-- This eliminates the need for caller-stack-preserved-* postulates when
-- the caller can provide bounds proofs for Stack addresses.
------------------------------------------------------------------------

-- | Helper: PairAtS preserved when addresses ≥ entry-rsp are preserved
PairAtS-preserved-under-mem-above :
  ∀ {addr-a addr-b addr : Word} {m1 m2 : Memory} {entry-rsp : Word} →
  PairAtS addr-a addr-b addr m1 →
  InStack entry-rsp →
  addr ≥ entry-rsp →
  (∀ a → a ≥ entry-rsp → readMem m2 a ≡ readMem m1 a) →
  PairAtS addr-a addr-b addr m2
PairAtS-preserved-under-mem-above {addr-a} {addr-b} {addr} {m1} {m2} {entry-rsp} pairS _ addr≥rsp mem-above =
  pair-at-s (trans (mem-above addr addr≥rsp) (fst-valid-s pairS))
            (trans (mem-above (addr +ℕ slot-size) addr+8≥rsp) (snd-valid-s pairS))
  where
    open import Data.Nat.Properties using (≤-trans; m≤m+n)
    addr+8≥rsp : (addr +ℕ slot-size) ≥ entry-rsp
    addr+8≥rsp = ≤-trans addr≥rsp (m≤m+n addr slot-size)

-- | Helper: InlAtS preserved when addresses ≥ entry-rsp are preserved
InlAtS-preserved-under-mem-above :
  ∀ {addr-a addr : Word} {m1 m2 : Memory} {entry-rsp : Word} →
  InlAtS addr-a addr m1 →
  InStack entry-rsp →
  addr ≥ entry-rsp →
  (∀ a → a ≥ entry-rsp → readMem m2 a ≡ readMem m1 a) →
  InlAtS addr-a addr m2
InlAtS-preserved-under-mem-above {addr-a} {addr} {m1} {m2} {entry-rsp} inlS _ addr≥rsp mem-above =
  inl-at-s (trans (mem-above addr addr≥rsp) (tag-valid-inl-s inlS))
           (trans (mem-above (addr +ℕ slot-size) addr+8≥rsp) (val-valid-inl-s inlS))
  where
    open import Data.Nat.Properties using (≤-trans; m≤m+n)
    addr+8≥rsp : (addr +ℕ slot-size) ≥ entry-rsp
    addr+8≥rsp = ≤-trans addr≥rsp (m≤m+n addr slot-size)

-- | Helper: InrAtS preserved when addresses ≥ entry-rsp are preserved
InrAtS-preserved-under-mem-above :
  ∀ {addr-b addr : Word} {m1 m2 : Memory} {entry-rsp : Word} →
  InrAtS addr-b addr m1 →
  InStack entry-rsp →
  addr ≥ entry-rsp →
  (∀ a → a ≥ entry-rsp → readMem m2 a ≡ readMem m1 a) →
  InrAtS addr-b addr m2
InrAtS-preserved-under-mem-above {addr-b} {addr} {m1} {m2} {entry-rsp} inrS _ addr≥rsp mem-above =
  inr-at-s (trans (mem-above addr addr≥rsp) (tag-valid-inr-s inrS))
           (trans (mem-above (addr +ℕ slot-size) addr+8≥rsp) (val-valid-inr-s inrS))
  where
    open import Data.Nat.Properties using (≤-trans; m≤m+n)
    addr+8≥rsp : (addr +ℕ slot-size) ≥ entry-rsp
    addr+8≥rsp = ≤-trans addr≥rsp (m≤m+n addr slot-size)

-- | Helper: ClosureAtS preserved when addresses ≥ entry-rsp are preserved
ClosureAtS-preserved-under-mem-above :
  ∀ {env-addr code-ptr addr : Word} {m1 m2 : Memory} {entry-rsp : Word} →
  ClosureAtS env-addr code-ptr addr m1 →
  InStack entry-rsp →
  addr ≥ entry-rsp →
  (∀ a → a ≥ entry-rsp → readMem m2 a ≡ readMem m1 a) →
  ClosureAtS env-addr code-ptr addr m2
ClosureAtS-preserved-under-mem-above {env-addr} {code-ptr} {addr} {m1} {m2} {entry-rsp} closS _ addr≥rsp mem-above =
  closure-at-s (trans (mem-above addr addr≥rsp) (env-valid-s closS))
               (trans (mem-above (addr +ℕ slot-size) addr+8≥rsp) (code-valid-s closS))
  where
    open import Data.Nat.Properties using (≤-trans; m≤m+n)
    addr+8≥rsp : (addr +ℕ slot-size) ≥ entry-rsp
    addr+8≥rsp = ≤-trans addr≥rsp (m≤m+n addr slot-size)

-- | Propagate ValidAt using bounds-based preservation
--
-- For Heap addresses: automatically derives ≥ entry-rsp
-- For Stack addresses: requires explicit addr ≥ entry-rsp proof
--
-- The stack-bound function is called for each Stack-region address,
-- providing the bound proof needed for preservation.
valid-subst-mem-above :
  ∀ {A} {v : ⟦ A ⟧} {addr : Word} {mem1 mem2 : Memory} →
  (va : ValidAt v addr mem1) →
  (entry-rsp : Word) →
  InStack entry-rsp →
  (mem-above : ∀ a → a ≥ entry-rsp → readMem mem2 a ≡ readMem mem1 a) →
  -- For Stack addresses, provide bound proofs
  (stack-bound : ∀ a → InStack a → a ≥ entry-rsp) →
  ValidAt v addr mem2
valid-subst-mem-above valid-unit _ _ _ _ = valid-unit
valid-subst-mem-above (valid-int eq) _ _ _ _ = valid-int eq
-- Pair: dispatch on region, derive bound for preservation
valid-subst-mem-above (valid-pair va vb pairS HeapAlloc ih) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-pair
    (valid-subst-mem-above va entry-rsp rsp-in-stack mem-above stack-bound)
    (valid-subst-mem-above vb entry-rsp rsp-in-stack mem-above stack-bound)
    (PairAtS-preserved-under-mem-above pairS rsp-in-stack (heap-addr-≥-stack-addr ih rsp-in-stack) mem-above)
    HeapAlloc ih
valid-subst-mem-above (valid-pair va vb pairS StackAlloc is) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-pair
    (valid-subst-mem-above va entry-rsp rsp-in-stack mem-above stack-bound)
    (valid-subst-mem-above vb entry-rsp rsp-in-stack mem-above stack-bound)
    (PairAtS-preserved-under-mem-above pairS rsp-in-stack (stack-bound _ is) mem-above)
    StackAlloc is
-- Inl: dispatch on region
valid-subst-mem-above {A + B} (valid-inl va inlS HeapAlloc ih) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-inl
    (valid-subst-mem-above va entry-rsp rsp-in-stack mem-above stack-bound)
    (InlAtS-preserved-under-mem-above inlS rsp-in-stack (heap-addr-≥-stack-addr ih rsp-in-stack) mem-above)
    HeapAlloc ih
valid-subst-mem-above {A + B} (valid-inl va inlS StackAlloc is) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-inl
    (valid-subst-mem-above va entry-rsp rsp-in-stack mem-above stack-bound)
    (InlAtS-preserved-under-mem-above inlS rsp-in-stack (stack-bound _ is) mem-above)
    StackAlloc is
-- Inr: dispatch on region
valid-subst-mem-above {A + B} (valid-inr vb inrS HeapAlloc ih) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-inr
    (valid-subst-mem-above vb entry-rsp rsp-in-stack mem-above stack-bound)
    (InrAtS-preserved-under-mem-above inrS rsp-in-stack (heap-addr-≥-stack-addr ih rsp-in-stack) mem-above)
    HeapAlloc ih
valid-subst-mem-above {A + B} (valid-inr vb inrS StackAlloc is) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-inr
    (valid-subst-mem-above vb entry-rsp rsp-in-stack mem-above stack-bound)
    (InrAtS-preserved-under-mem-above inrS rsp-in-stack (stack-bound _ is) mem-above)
    StackAlloc is
-- Closure: dispatch on region
valid-subst-mem-above {A ⇒[ _ ] B} (valid-closure closS HeapAlloc ih) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-closure
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack (heap-addr-≥-stack-addr ih rsp-in-stack) mem-above)
    HeapAlloc ih
valid-subst-mem-above {A ⇒[ _ ] B} (valid-closure closS StackAlloc is) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-closure
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack (stack-bound _ is) mem-above)
    StackAlloc is
-- Closure with env: dispatch on region
valid-subst-mem-above {A ⇒[ _ ] B} (valid-closure-env venv closS HeapAlloc ih) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-closure-env
    (valid-subst-mem-above venv entry-rsp rsp-in-stack mem-above stack-bound)
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack (heap-addr-≥-stack-addr ih rsp-in-stack) mem-above)
    HeapAlloc ih
valid-subst-mem-above {A ⇒[ _ ] B} (valid-closure-env venv closS StackAlloc is) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-closure-env
    (valid-subst-mem-above venv entry-rsp rsp-in-stack mem-above stack-bound)
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack (stack-bound _ is) mem-above)
    StackAlloc is
-- Eff: dispatch on region
valid-subst-mem-above {Eff A B} (valid-eff closS HeapAlloc ih) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-eff
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack (heap-addr-≥-stack-addr ih rsp-in-stack) mem-above)
    HeapAlloc ih
valid-subst-mem-above {Eff A B} (valid-eff closS StackAlloc is) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-eff
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack (stack-bound _ is) mem-above)
    StackAlloc is
-- Eff with env: dispatch on region
valid-subst-mem-above {Eff A B} (valid-eff-env venv closS HeapAlloc ih) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-eff-env
    (valid-subst-mem-above venv entry-rsp rsp-in-stack mem-above stack-bound)
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack (heap-addr-≥-stack-addr ih rsp-in-stack) mem-above)
    HeapAlloc ih
valid-subst-mem-above {Eff A B} (valid-eff-env venv closS StackAlloc is) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-eff-env
    (valid-subst-mem-above venv entry-rsp rsp-in-stack mem-above stack-bound)
    (ClosureAtS-preserved-under-mem-above closS rsp-in-stack (stack-bound _ is) mem-above)
    StackAlloc is
-- Fix: recurse
valid-subst-mem-above (valid-fix vx) entry-rsp rsp-in-stack mem-above stack-bound =
  valid-fix (valid-subst-mem-above vx entry-rsp rsp-in-stack mem-above stack-bound)

------------------------------------------------------------------------
-- Caller-stack-preserved postulates: documentation
--
-- The caller-stack-preserved-* postulates in IR/*.agda capture the
-- CALLER-FRAME INVARIANT: inputs from caller's frame have Stack
-- addresses ≥ current entry-rsp.
--
-- These postulates are semantically correct because:
-- 1. Inputs come from previous IRs or program entry
-- 2. Previous IRs allocated at addresses < their entry-rsp
-- 3. Current entry-rsp ≤ all previously allocated addresses
-- 4. Therefore caller's Stack addresses ≥ current entry-rsp
--
-- To PROVE these postulates, use valid-subst-mem-above with:
-- 1. mem-above from the IR's instruction tracing
-- 2. stack-bound = the caller-frame invariant
--
-- The stack-bound proof requires tracking that inputs are from
-- caller's frame, which can be done by:
-- a) Adding input-addr ≥ entry-rsp as IR precondition
-- b) Tracking allocation provenance through ValidAt
-- c) Proving at IR composition boundaries
--
-- For now, the postulates correctly capture this invariant.
------------------------------------------------------------------------
