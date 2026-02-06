------------------------------------------------------------------------
-- Once.Backend.X86.Correct.Ownership
--
-- Slot-based ownership model for memory preservation proofs.
--
-- KEY INSIGHT: Ownership is tracked via exact slot positions, not
-- inequalities. If we know caller-provided inputs are at specific
-- slots in the caller's frame, preservation follows from frame-disjoint.
--
-- This module provides:
--   - Owner type (Caller vs Current)
--   - OwnedBy predicate indexed by ValidAt and caller's Frame
--   - Preservation lemmas using frame-disjoint from FrameSemantics
--
-- ARCHITECTURE (Slot-Based Ownership):
--   Stack data: tracked via (frame, slot) pairs with exact addressing
--     addr ≡ slot-addr caller-frame k
--   Heap data: preserved by region separation (InStack vs InHeap)
--
--   Preservation proof:
--     - Callee writes to slot-addr callee-frame j
--     - Caller data at slot-addr caller-frame k
--     - callee-frame ≺ caller-frame (frame ordering)
--     - By frame-disjoint: addresses are different
--
-- TRUST BOUNDARY:
--   - init-input-owned: POSTULATED only for initial program entry
--   - For internal calls (Apply): PROVEN from Apply compilation
--   The goal is to minimize trust to just the initial state setup.
--
-- See: docs/formal/guides/slot-based-ownership-architecture.md
------------------------------------------------------------------------

module Once.Backend.X86.Correct.Ownership where

open import Data.Nat using (ℕ; _+_; _≥_; _<_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Type using (Type; Unit; _+_; _⇒[_]_; Eff; Fix)
open import Once.Platform.X86-64 using (⟦_⟧; Closure; ⟦Fix⟧; wrap)
open ⟦Fix⟧
open import Once.Backend.X86.Semantics using (Memory; Word; readMem)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; heap-addr-≥-stack-addr; stack-heap-disjoint;
         StackPointer; slot-addr; Addr)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr)
open import Data.Empty using (⊥; ⊥-elim)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-unit; valid-pair; valid-inl; valid-inr;
         valid-closure; valid-closure-env; valid-eff; valid-eff-env; valid-fix;
         Region; Stack; Heap; InRegion;
         PairAtS; InlAtS; InrAtS; ClosureAtS;
         unit-in-heap)

-- Import FrameSemantics for slot-based addressing
open import Once.Backend.Common.FrameSemantics using (FrameSemantics; AtSlot)
open import Once.Backend.X86.FrameInstantiation
  using (x86-frame-semantics; X86Frame; _x86-≺_; x86-frame-disjoint)

------------------------------------------------------------------------
-- Frame type alias for clarity
------------------------------------------------------------------------

-- | A Frame is a StackPointer (stack frame identity)
Frame : Set
Frame = StackPointer

------------------------------------------------------------------------
-- Owner: Semantic ownership of data
--
-- Caller  = Data belongs to caller, we must preserve it
-- Current = Data belongs to us, we may modify it
--
-- This is NOT about where data is stored (Region), but about
-- who is responsible for it. Heap data is always Caller-owned
-- because we never write to heap.
------------------------------------------------------------------------

data Owner : Set where
  Caller  : Owner   -- Preserved by callee (in caller's frame or heap)
  Current : Owner   -- May be modified by callee (in callee's frame)

------------------------------------------------------------------------
-- AtFrameSlot: Address is at specific slot in a frame
--
-- This is the key predicate for slot-based ownership.
-- Proves exact position, not just inequality.
------------------------------------------------------------------------

AtFrameSlot : Addr → Frame → ℕ → Set
AtFrameSlot addr frame slot = addr ≡ slot-addr frame slot

------------------------------------------------------------------------
-- OwnedBy: Predicate that a ValidAt value is owned by Owner
--
-- This is indexed by the ValidAt proof and the caller's frame.
-- For stack data: requires exact slot position evidence
-- For heap data: automatically owned (region separation)
--
-- Key property: If OwnedBy Caller va caller-frame, then all Stack
-- addresses in va are at slots in caller-frame, so they're preserved
-- when callee writes to its own frame.
------------------------------------------------------------------------

data OwnedBy : Owner → {A : Type} → {v : ⟦ A ⟧} → {addr : Word} → {m : Memory} →
               ValidAt v addr m → Frame → Set where

  -- Unit is always Caller-owned (address 0 in heap, no frame dependency)
  owned-unit : ∀ {m caller-frame} →
    OwnedBy Caller (valid-unit {m}) caller-frame

  -- Pair in Heap: automatically Caller-owned (heap preserved by stack ops)
  owned-pair-heap : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
    {addr-a addr-b addr : Word} {m : Memory}
    {va : ValidAt a addr-a m} {vb : ValidAt b addr-b m}
    {pairS : PairAtS addr-a addr-b addr m}
    {ih : InHeap addr} {caller-frame : Frame} →
    OwnedBy Caller va caller-frame →
    OwnedBy Caller vb caller-frame →
    OwnedBy Caller (valid-pair va vb pairS Heap ih) caller-frame

  -- Pair in Stack: at exact slot in caller's frame
  owned-pair-caller-stack : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
    {addr-a addr-b addr : Word} {m : Memory}
    {va : ValidAt a addr-a m} {vb : ValidAt b addr-b m}
    {pairS : PairAtS addr-a addr-b addr m}
    {is : InStack addr} {caller-frame : Frame} →
    (slot : ℕ) →
    AtFrameSlot addr caller-frame slot →  -- EXACT slot position
    OwnedBy Caller va caller-frame →
    OwnedBy Caller vb caller-frame →
    OwnedBy Caller (valid-pair va vb pairS Stack is) caller-frame

  -- Inl in Heap: automatically Caller-owned
  owned-inl-heap : ∀ {A B} {a : ⟦ A ⟧}
    {addr-a addr : Word} {m : Memory}
    {va : ValidAt a addr-a m}
    {inlS : InlAtS addr-a addr m}
    {ih : InHeap addr} {caller-frame : Frame} →
    OwnedBy Caller va caller-frame →
    OwnedBy Caller (valid-inl {A} {B} va inlS Heap ih) caller-frame

  -- Inl in Stack: at exact slot in caller's frame
  owned-inl-caller-stack : ∀ {A B} {a : ⟦ A ⟧}
    {addr-a addr : Word} {m : Memory}
    {va : ValidAt a addr-a m}
    {inlS : InlAtS addr-a addr m}
    {is : InStack addr} {caller-frame : Frame} →
    (slot : ℕ) →
    AtFrameSlot addr caller-frame slot →
    OwnedBy Caller va caller-frame →
    OwnedBy Caller (valid-inl {A} {B} va inlS Stack is) caller-frame

  -- Inr in Heap: automatically Caller-owned
  owned-inr-heap : ∀ {A B} {b : ⟦ B ⟧}
    {addr-b addr : Word} {m : Memory}
    {vb : ValidAt b addr-b m}
    {inrS : InrAtS addr-b addr m}
    {ih : InHeap addr} {caller-frame : Frame} →
    OwnedBy Caller vb caller-frame →
    OwnedBy Caller (valid-inr {A} {B} vb inrS Heap ih) caller-frame

  -- Inr in Stack: at exact slot in caller's frame
  owned-inr-caller-stack : ∀ {A B} {b : ⟦ B ⟧}
    {addr-b addr : Word} {m : Memory}
    {vb : ValidAt b addr-b m}
    {inrS : InrAtS addr-b addr m}
    {is : InStack addr} {caller-frame : Frame} →
    (slot : ℕ) →
    AtFrameSlot addr caller-frame slot →
    OwnedBy Caller vb caller-frame →
    OwnedBy Caller (valid-inr {A} {B} vb inrS Stack is) caller-frame

  -- Closure in Heap: automatically Caller-owned
  owned-closure-heap : ∀ {A B} {cl : Closure A B}
    {env-addr code-ptr addr : Word} {m : Memory}
    {closS : ClosureAtS env-addr code-ptr addr m}
    {ih : InHeap addr} {caller-frame : Frame} →
    OwnedBy Caller {A ⇒[ _ ] B} {cl} (valid-closure closS Heap ih) caller-frame

  -- Closure in Stack: at exact slot in caller's frame
  owned-closure-caller-stack : ∀ {A B} {cl : Closure A B}
    {env-addr code-ptr addr : Word} {m : Memory}
    {closS : ClosureAtS env-addr code-ptr addr m}
    {is : InStack addr} {caller-frame : Frame} →
    (slot : ℕ) →
    AtFrameSlot addr caller-frame slot →
    OwnedBy Caller {A ⇒[ _ ] B} {cl} (valid-closure {A} {B} {cl} closS Stack is) caller-frame

  -- Closure-env in Heap: automatically Caller-owned
  owned-closure-env-heap : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
    {env-addr code-ptr closure-addr : Word} {m : Memory}
    {venv : ValidAt env env-addr m}
    {closS : ClosureAtS env-addr code-ptr closure-addr m}
    {ih : InHeap closure-addr} {caller-frame : Frame} →
    OwnedBy Caller venv caller-frame →
    OwnedBy Caller {A ⇒[ _ ] B} {cl} (valid-closure-env venv closS Heap ih) caller-frame

  -- Closure-env in Stack: at exact slot in caller's frame
  owned-closure-env-caller-stack : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
    {env-addr code-ptr closure-addr : Word} {m : Memory}
    {venv : ValidAt env env-addr m}
    {closS : ClosureAtS env-addr code-ptr closure-addr m}
    {is : InStack closure-addr} {caller-frame : Frame} →
    (slot : ℕ) →
    AtFrameSlot closure-addr caller-frame slot →
    OwnedBy Caller venv caller-frame →
    OwnedBy Caller {A ⇒[ _ ] B} {cl} (valid-closure-env {A} {B} {E} {cl} venv closS Stack is) caller-frame

  -- Eff in Heap: automatically Caller-owned
  owned-eff-heap : ∀ {A B} {cl : Closure A B}
    {env-addr code-ptr addr : Word} {m : Memory}
    {closS : ClosureAtS env-addr code-ptr addr m}
    {ih : InHeap addr} {caller-frame : Frame} →
    OwnedBy Caller {Eff A B} {cl} (valid-eff closS Heap ih) caller-frame

  -- Eff in Stack: at exact slot in caller's frame
  owned-eff-caller-stack : ∀ {A B} {cl : Closure A B}
    {env-addr code-ptr addr : Word} {m : Memory}
    {closS : ClosureAtS env-addr code-ptr addr m}
    {is : InStack addr} {caller-frame : Frame} →
    (slot : ℕ) →
    AtFrameSlot addr caller-frame slot →
    OwnedBy Caller {Eff A B} {cl} (valid-eff {A} {B} {cl} closS Stack is) caller-frame

  -- Eff-env in Heap: automatically Caller-owned
  owned-eff-env-heap : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
    {env-addr code-ptr closure-addr : Word} {m : Memory}
    {venv : ValidAt env env-addr m}
    {closS : ClosureAtS env-addr code-ptr closure-addr m}
    {ih : InHeap closure-addr} {caller-frame : Frame} →
    OwnedBy Caller venv caller-frame →
    OwnedBy Caller {Eff A B} {cl} (valid-eff-env venv closS Heap ih) caller-frame

  -- Eff-env in Stack: at exact slot in caller's frame
  owned-eff-env-caller-stack : ∀ {A B E} {cl : Closure A B} {env : ⟦ E ⟧}
    {env-addr code-ptr closure-addr : Word} {m : Memory}
    {venv : ValidAt env env-addr m}
    {closS : ClosureAtS env-addr code-ptr closure-addr m}
    {is : InStack closure-addr} {caller-frame : Frame} →
    (slot : ℕ) →
    AtFrameSlot closure-addr caller-frame slot →
    OwnedBy Caller venv caller-frame →
    OwnedBy Caller {Eff A B} {cl} (valid-eff-env {A} {B} {E} {cl} venv closS Stack is) caller-frame

  -- Fix: inherits ownership from wrapped value
  owned-fix : ∀ {F} {x : ⟦ F ⟧} {addr : Word} {m : Memory}
    {vx : ValidAt x addr m} {caller-frame : Frame} →
    OwnedBy Caller vx caller-frame →
    OwnedBy Caller (valid-fix vx) caller-frame

------------------------------------------------------------------------
-- Key Lemma: Extract slot evidence from OwnedBy
--
-- For stack data, OwnedBy contains exact slot position.
-- For heap data, we get absurdity if asked for stack membership.
------------------------------------------------------------------------

-- | Extract the slot from OwnedBy Caller for stack addresses
owned-implies-at-slot : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory}
  {va : ValidAt v addr m} {caller-frame : Frame} →
  OwnedBy Caller va caller-frame →
  InStack addr →
  ∃ (λ slot → AtFrameSlot addr caller-frame slot)
owned-implies-at-slot owned-unit in-stack =
  ⊥-elim (stack-heap-disjoint 0 in-stack unit-in-heap)
owned-implies-at-slot (owned-pair-heap {ih = ih} _ _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-at-slot (owned-pair-caller-stack slot at-slot _ _) _ =
  slot , at-slot
owned-implies-at-slot (owned-inl-heap {ih = ih} _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-at-slot (owned-inl-caller-stack slot at-slot _) _ =
  slot , at-slot
owned-implies-at-slot (owned-inr-heap {ih = ih} _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-at-slot (owned-inr-caller-stack slot at-slot _) _ =
  slot , at-slot
owned-implies-at-slot (owned-closure-heap {ih = ih}) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-at-slot (owned-closure-caller-stack slot at-slot) _ =
  slot , at-slot
owned-implies-at-slot (owned-closure-env-heap {ih = ih} _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-at-slot (owned-closure-env-caller-stack slot at-slot _) _ =
  slot , at-slot
owned-implies-at-slot (owned-eff-heap {ih = ih}) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-at-slot (owned-eff-caller-stack slot at-slot) _ =
  slot , at-slot
owned-implies-at-slot (owned-eff-env-heap {ih = ih} _) is =
  ⊥-elim (stack-heap-disjoint _ is ih)
owned-implies-at-slot (owned-eff-env-caller-stack slot at-slot _) _ =
  slot , at-slot
owned-implies-at-slot (owned-fix owned) is =
  owned-implies-at-slot owned is

------------------------------------------------------------------------
-- Backward Compatibility: Derive addr ≥ rsp from slot evidence
--
-- On x86-64, slot-addr frame k ≥ sp-addr frame (slots grow upward).
-- And sp-addr caller-frame ≥ entry-rsp when caller-frame is caller's.
--
-- This allows existing code using addr ≥ rsp to work.
------------------------------------------------------------------------

open import Once.Backend.X86.Layout using (slot-addr-≥-base)

-- | Slot address is ≥ frame base
slot-addr-≥-frame-base : ∀ (frame : Frame) (slot : ℕ) →
  slot-addr frame slot ≥ sp-addr frame
slot-addr-≥-frame-base = slot-addr-≥-base

-- | If addr is at slot in frame, then addr ≥ frame base
at-slot-implies-≥-base : ∀ (addr : Addr) (frame : Frame) (slot : ℕ) →
  AtFrameSlot addr frame slot →
  addr ≥ sp-addr frame
at-slot-implies-≥-base addr frame slot at-slot =
  subst (_≥ sp-addr frame) (sym at-slot) (slot-addr-≥-frame-base frame slot)

-- | OwnedBy Caller implies stack addresses are ≥ frame base
-- This is the backward-compatible form for existing preservation proofs
owned-implies-stack-bound : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m : Memory}
  {va : ValidAt v addr m} {caller-frame : Frame} →
  OwnedBy Caller va caller-frame →
  InStack addr →
  addr ≥ sp-addr caller-frame
owned-implies-stack-bound {addr = addr} {caller-frame = caller-frame} owned in-stack
  with owned-implies-at-slot owned in-stack
... | slot , at-slot = at-slot-implies-≥-base addr caller-frame slot at-slot

------------------------------------------------------------------------
-- Preservation: Caller-owned values are preserved by callee writes
--
-- Key insight: callee writes to callee-frame, caller data in caller-frame.
-- If callee-frame ≺ caller-frame, then by frame-disjoint, addresses differ.
--
-- For backward compatibility, we still use the addr ≥ rsp form.
-- Future: use frame-disjoint directly for cleaner proofs.
------------------------------------------------------------------------

-- Import preservation lemmas from MemoryValid
open import Once.Backend.X86.Correct.MemoryValid
  using (PairAtS-preserved-under-mem-above;
         InlAtS-preserved-under-mem-above;
         InrAtS-preserved-under-mem-above;
         ClosureAtS-preserved-under-mem-above)
open import Data.Nat.Properties using (≤-trans; m≤m+n)

private
  slot-size : ℕ
  slot-size = 8  -- Word size

-- | Caller-owned values are preserved when memory above frame base is preserved
-- This uses the backward-compatible addr ≥ rsp form.
owned-caller-preserved : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m1 m2 : Memory}
  {va : ValidAt v addr m1} {caller-frame : Frame} →
  OwnedBy Caller va caller-frame →
  InStack (sp-addr caller-frame) →
  (∀ a → a ≥ sp-addr caller-frame → readMem m2 a ≡ readMem m1 a) →
  ValidAt v addr m2
owned-caller-preserved owned-unit _ _ = valid-unit

owned-caller-preserved {m1 = m1} {m2} {valid-pair va vb pairS Heap ih} {caller-frame}
  (owned-pair-heap oa ob) frame-in-stack mem-pres =
  valid-pair
    (owned-caller-preserved oa frame-in-stack mem-pres)
    (owned-caller-preserved ob frame-in-stack mem-pres)
    (PairAtS-preserved-under-mem-above pairS frame-in-stack
      (heap-addr-≥-stack-addr ih frame-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {addr = addr} {m1 = m1} {m2} {valid-pair va vb pairS Stack is} {caller-frame}
  (owned-pair-caller-stack slot at-slot oa ob) frame-in-stack mem-pres =
  valid-pair
    (owned-caller-preserved oa frame-in-stack mem-pres)
    (owned-caller-preserved ob frame-in-stack mem-pres)
    (PairAtS-preserved-under-mem-above pairS frame-in-stack
      (at-slot-implies-≥-base addr caller-frame slot at-slot) mem-pres)
    Stack is

owned-caller-preserved {m1 = m1} {m2} {valid-inl va inlS Heap ih} {caller-frame}
  (owned-inl-heap oa) frame-in-stack mem-pres =
  valid-inl
    (owned-caller-preserved oa frame-in-stack mem-pres)
    (InlAtS-preserved-under-mem-above inlS frame-in-stack
      (heap-addr-≥-stack-addr ih frame-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {addr = addr} {m1 = m1} {m2} {valid-inl va inlS Stack is} {caller-frame}
  (owned-inl-caller-stack slot at-slot oa) frame-in-stack mem-pres =
  valid-inl
    (owned-caller-preserved oa frame-in-stack mem-pres)
    (InlAtS-preserved-under-mem-above inlS frame-in-stack
      (at-slot-implies-≥-base addr caller-frame slot at-slot) mem-pres)
    Stack is

owned-caller-preserved {m1 = m1} {m2} {valid-inr vb inrS Heap ih} {caller-frame}
  (owned-inr-heap ob) frame-in-stack mem-pres =
  valid-inr
    (owned-caller-preserved ob frame-in-stack mem-pres)
    (InrAtS-preserved-under-mem-above inrS frame-in-stack
      (heap-addr-≥-stack-addr ih frame-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {addr = addr} {m1 = m1} {m2} {valid-inr vb inrS Stack is} {caller-frame}
  (owned-inr-caller-stack slot at-slot ob) frame-in-stack mem-pres =
  valid-inr
    (owned-caller-preserved ob frame-in-stack mem-pres)
    (InrAtS-preserved-under-mem-above inrS frame-in-stack
      (at-slot-implies-≥-base addr caller-frame slot at-slot) mem-pres)
    Stack is

owned-caller-preserved {A ⇒[ _ ] B} {m1 = m1} {m2} {valid-closure closS Heap ih} {caller-frame}
  owned-closure-heap frame-in-stack mem-pres =
  valid-closure
    (ClosureAtS-preserved-under-mem-above closS frame-in-stack
      (heap-addr-≥-stack-addr ih frame-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {A ⇒[ _ ] B} {addr = addr} {m1 = m1} {m2} {valid-closure closS Stack is} {caller-frame}
  (owned-closure-caller-stack slot at-slot) frame-in-stack mem-pres =
  valid-closure
    (ClosureAtS-preserved-under-mem-above closS frame-in-stack
      (at-slot-implies-≥-base addr caller-frame slot at-slot) mem-pres)
    Stack is

owned-caller-preserved {A ⇒[ _ ] B} {m1 = m1} {m2} {valid-closure-env venv closS Heap ih} {caller-frame}
  (owned-closure-env-heap oenv) frame-in-stack mem-pres =
  valid-closure-env
    (owned-caller-preserved oenv frame-in-stack mem-pres)
    (ClosureAtS-preserved-under-mem-above closS frame-in-stack
      (heap-addr-≥-stack-addr ih frame-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {A ⇒[ _ ] B} {addr = addr} {m1 = m1} {m2} {valid-closure-env venv closS Stack is} {caller-frame}
  (owned-closure-env-caller-stack slot at-slot oenv) frame-in-stack mem-pres =
  valid-closure-env
    (owned-caller-preserved oenv frame-in-stack mem-pres)
    (ClosureAtS-preserved-under-mem-above closS frame-in-stack
      (at-slot-implies-≥-base addr caller-frame slot at-slot) mem-pres)
    Stack is

owned-caller-preserved {Eff A B} {m1 = m1} {m2} {valid-eff closS Heap ih} {caller-frame}
  owned-eff-heap frame-in-stack mem-pres =
  valid-eff
    (ClosureAtS-preserved-under-mem-above closS frame-in-stack
      (heap-addr-≥-stack-addr ih frame-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {Eff A B} {addr = addr} {m1 = m1} {m2} {valid-eff closS Stack is} {caller-frame}
  (owned-eff-caller-stack slot at-slot) frame-in-stack mem-pres =
  valid-eff
    (ClosureAtS-preserved-under-mem-above closS frame-in-stack
      (at-slot-implies-≥-base addr caller-frame slot at-slot) mem-pres)
    Stack is

owned-caller-preserved {Eff A B} {m1 = m1} {m2} {valid-eff-env venv closS Heap ih} {caller-frame}
  (owned-eff-env-heap oenv) frame-in-stack mem-pres =
  valid-eff-env
    (owned-caller-preserved oenv frame-in-stack mem-pres)
    (ClosureAtS-preserved-under-mem-above closS frame-in-stack
      (heap-addr-≥-stack-addr ih frame-in-stack) mem-pres)
    Heap ih

owned-caller-preserved {Eff A B} {addr = addr} {m1 = m1} {m2} {valid-eff-env venv closS Stack is} {caller-frame}
  (owned-eff-env-caller-stack slot at-slot oenv) frame-in-stack mem-pres =
  valid-eff-env
    (owned-caller-preserved oenv frame-in-stack mem-pres)
    (ClosureAtS-preserved-under-mem-above closS frame-in-stack
      (at-slot-implies-≥-base addr caller-frame slot at-slot) mem-pres)
    Stack is

owned-caller-preserved {m1 = m1} {m2} {valid-fix vx} {caller-frame}
  (owned-fix ox) frame-in-stack mem-pres =
  valid-fix (owned-caller-preserved ox frame-in-stack mem-pres)

------------------------------------------------------------------------
-- Convenience constructors for creating OwnedBy
------------------------------------------------------------------------

make-owned-pair-heap : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
  {addr-a addr-b addr : Word} {m : Memory} {caller-frame : Frame}
  (va : ValidAt a addr-a m) (vb : ValidAt b addr-b m)
  (pairS : PairAtS addr-a addr-b addr m)
  (ih : InHeap addr) →
  OwnedBy Caller va caller-frame →
  OwnedBy Caller vb caller-frame →
  OwnedBy Caller (valid-pair va vb pairS Heap ih) caller-frame
make-owned-pair-heap _ _ _ _ oa ob = owned-pair-heap oa ob

make-owned-pair-stack : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
  {addr-a addr-b addr : Word} {m : Memory} {caller-frame : Frame}
  (va : ValidAt a addr-a m) (vb : ValidAt b addr-b m)
  (pairS : PairAtS addr-a addr-b addr m)
  (is : InStack addr)
  (slot : ℕ)
  (at-slot : AtFrameSlot addr caller-frame slot) →
  OwnedBy Caller va caller-frame →
  OwnedBy Caller vb caller-frame →
  OwnedBy Caller (valid-pair va vb pairS Stack is) caller-frame
make-owned-pair-stack _ _ _ _ slot at-slot oa ob =
  owned-pair-caller-stack slot at-slot oa ob

------------------------------------------------------------------------
-- Caller Input Ownership
--
-- At function entry, the input is at specific slots in caller's frame.
-- For Apply (internal calls): this is PROVEN from compilation evidence.
-- For InitState (program entry): this is POSTULATED (trust boundary).
------------------------------------------------------------------------

-- SEMANTIC INVARIANT: At function entry, input is in caller's frame.
--
-- The caller allocates input at slot-addr caller-frame k for some k.
-- We receive this evidence from Apply compilation.
--
-- TRUST BOUNDARY:
--   - For INTERNAL calls: Evidence comes from Apply compilation
--   - For INITIAL program entry: Postulated in InitState.agda
--
-- NOTE: init-input-owned is defined in InitState.agda to isolate the
-- trust boundary. Downstream modules should import it from there.

-- | Derive input preservation using ownership model
caller-input-preserved : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m1 m2 : Memory}
  {caller-frame : Frame}
  (va : ValidAt v addr m1) →
  OwnedBy Caller va caller-frame →
  InStack (sp-addr caller-frame) →
  (∀ a → a ≥ sp-addr caller-frame → readMem m2 a ≡ readMem m1 a) →
  ValidAt v addr m2
caller-input-preserved va owned frame-in-stack mem-above =
  owned-caller-preserved owned frame-in-stack mem-above

------------------------------------------------------------------------
-- X86-64 OwnershipSemantics Instantiation
--
-- See: Once.Backend.X86.OwnershipInstantiation for the instantiation
-- of the architecture-independent OwnershipSemantics interface.
-- The instantiation is in a separate module to avoid circular imports
-- (this module is imported by InitState, which provides init-input-owned).
------------------------------------------------------------------------
