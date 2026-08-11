-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.Allocation
--
-- Allocation model for SlotMachine POC.
--
-- Supports both stack and heap allocation:
--   - Stack: slots within current frame (for non-escaping values)
--   - Heap: fresh HeapRefs (for escaping values)
--
-- This models the output of escape analysis - the IR specifies
-- which allocation mode to use for each value.
------------------------------------------------------------------------

module Once.CCC.Machine.Allocation where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.List using (_∷_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <⇒≤; +-monoʳ-≤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore public
open import Once.CCC.Machine.SMPrimitives public

------------------------------------------------------------------------
-- Stack Allocation
--
-- Allocate n consecutive slots in the current frame.
-- Returns the base slot and updated state.
------------------------------------------------------------------------

module StackAllocation {FS : FrameSemantics} where
  open FrameSemantics FS

  -- Allocate n slots, returning base location
  -- Capacity check is the caller's responsibility (Dispatcher verifies this)
  stack-alloc : (as : AllocState {FS}) (n : ℕ) →
    ValueLocation FS × AllocState {FS}
  stack-alloc as n =
    AtStack (current-frame as) (next-slot as) ,
    record as { next-slot = next-slot as +ℕ n }

  -- The allocated location
  -- The allocated location
  stack-alloc-loc : (as : AllocState {FS}) (n : ℕ) → ValueLocation FS
  stack-alloc-loc as n = proj₁ (stack-alloc as n)

  -- The updated state
  stack-alloc-state : (as : AllocState {FS}) (n : ℕ) → AllocState {FS}
  stack-alloc-state as n = proj₂ (stack-alloc as n)

  -- Key property: allocated slots are in the current frame
  stack-alloc-in-frame : (as : AllocState {FS}) (n : ℕ) →
    ∃[ slot ] stack-alloc-loc as n ≡ AtStack (current-frame as) slot
  stack-alloc-in-frame as n = next-slot as , refl

  -- Successive slots are at offset from base
  stack-alloc-offset : (as : AllocState {FS}) (n : ℕ) →
    (k : ℕ) → k < n →
    ValueLocation FS
  stack-alloc-offset as n k k<n =
    AtStack (current-frame as) (next-slot as +ℕ k)

------------------------------------------------------------------------
-- Heap Allocation
--
-- Allocate a fresh heap block of n slots.
-- Returns a fresh HeapRef and updated state.
------------------------------------------------------------------------

module HeapAllocation {FS : FrameSemantics} where

  -- Allocate heap block, returning base location
  -- Uses HeapLocation to enforce heap-only invariant
  heap-alloc : (as : AllocState {FS}) (n : ℕ) →
    ValueLocation FS × AllocState {FS}
  heap-alloc as n =
    AtDynamic (heap-loc (mkHeapRef (next-heap-ref as)) 0) ,
    record as { next-heap-ref = suc (next-heap-ref as) }

  -- The allocated HeapLocation (for heap-internal operations)
  heap-alloc-hl : (as : AllocState {FS}) (n : ℕ) → HeapLocation
  heap-alloc-hl as n = heap-loc (mkHeapRef (next-heap-ref as)) 0

  -- The allocated location (as ValueLocation)
  heap-alloc-loc : (as : AllocState {FS}) (n : ℕ) → ValueLocation FS
  heap-alloc-loc as n = proj₁ (heap-alloc as n)

  -- The updated state
  heap-alloc-state : (as : AllocState {FS}) (n : ℕ) → AllocState {FS}
  heap-alloc-state as n = proj₂ (heap-alloc as n)

------------------------------------------------------------------------
-- Unified Allocation Interface
------------------------------------------------------------------------

module Allocator {FS : FrameSemantics} where
  open StackAllocation {FS}
  open HeapAllocation {FS}

  -- Allocate based on mode
  -- For stack: requires proof that slots fit
  -- For heap: always succeeds

  record AllocResult (as : AllocState {FS}) (n : ℕ) : Set where
    field
      location : ValueLocation FS
      new-state : AllocState {FS}
      -- The location points to n consecutive slots
      -- sucLoc^k location is valid for k < n

  -- Stack allocation
  -- Capacity verification is the caller's responsibility (proof is for documentation)
  alloc-stack : (as : AllocState {FS}) (n : ℕ) → AllocResult as n
  alloc-stack as n = record
    { location = stack-alloc-loc as n
    ; new-state = stack-alloc-state as n
    }

  -- Heap allocation (always succeeds)
  alloc-heap : (as : AllocState {FS}) (n : ℕ) → AllocResult as n
  alloc-heap as n = record
    { location = heap-alloc-loc as n
    ; new-state = heap-alloc-state as n
    }

------------------------------------------------------------------------
-- Extended Machine State (with allocation)
------------------------------------------------------------------------

record LocStateWithAlloc {FS : FrameSemantics} : Set where
  constructor mkLocStateWithAlloc
  field
    machine-state : LocState FS
    alloc-state : AllocState {FS}

open LocStateWithAlloc public

------------------------------------------------------------------------
-- Memory Write Operations
--
-- Write a ValueLocation pointer to memory at a given location.
------------------------------------------------------------------------

module WriteOps {FS : FrameSemantics} where
  open MemOps {FS}
  open FrameSemantics FS

  -- Write to a stack slot.
  -- Plan 0.13.2: stackMem stores StoredValue; lift the parameter type.
  write-stack-slot : LocState FS → Frame → ℕ → StoredValue FS → LocState FS
  write-stack-slot s frame slot val =
    record s { stackMem = writeStackMem (stackMem s) frame slot val }

  -- Write a StoredValue to a heap slot.
  -- Plan 0.14: heap cells hold StoredValue (primitives or heap pointers).
  write-heap-slot : LocState FS → HeapLocation → StoredValue FS → LocState FS
  write-heap-slot s hl val =
    record s { heapMem = writeHeapMem (heapMem s) hl val }

  -- Write a ValueLocation pointer (wrapped as SV-Ptr) to a location.
  -- The cross-region constraint stays: storing a stack pointer into
  -- a heap cell is a no-op (the only forbidden combination).
  write-loc : LocState FS → ValueLocation FS → ValueLocation FS → LocState FS
  write-loc s (AtStack f k) val = write-stack-slot s f k (SV-Ptr val)
  write-loc s (AtDynamic hl) (AtDynamic val) = write-heap-slot s hl (SV-Ptr (AtDynamic val))
  write-loc s (AtDynamic hl) (AtStack _ _) = s  -- Invalid: can't store stack ref in heap

  -- Write preserves reads at different locations (stack)
  write-stack-preserves-diff : ∀ s f₁ k₁ f₂ k₂ val →
    (f₁ ≢ f₂) ⊎ (k₁ ≢ k₂) →
    stackMem (write-stack-slot s f₁ k₁ val) f₂ k₂ ≡ stackMem s f₂ k₂
  write-stack-preserves-diff s f₁ k₁ f₂ k₂ val (inj₁ f≢f)
    with _≟F_ f₁ f₂
  ... | yes refl = ⊥-elim (f≢f refl)
  ... | no _ = refl
  write-stack-preserves-diff s f₁ k₁ f₂ k₂ val (inj₂ k≢k)
    with _≟F_ f₁ f₂ | Data.Nat._≟_ k₁ k₂
  ... | yes _ | yes refl = ⊥-elim (k≢k refl)
  ... | yes _ | no _ = refl
  ... | no _ | _ = refl

  -- Write then read same location
  write-stack-read-same : ∀ s f k val →
    stackMem (write-stack-slot s f k val) f k ≡ just val
  write-stack-read-same s f k val with _≟F_ f f | Data.Nat._≟_ k k
  ... | yes _ | yes _ = refl
  ... | yes _ | no k≢k = ⊥-elim (k≢k refl)
  ... | no f≢f | _ = ⊥-elim (f≢f refl)

  -- Similar for heap (now uses HeapLocation)
  write-heap-read-same : ∀ s hl val →
    heapMem (write-heap-slot s hl val) hl ≡ just val
  write-heap-read-same s hl val with hl ≟HL hl
  ... | yes _ = refl
  ... | no hl≢hl = ⊥-elim (hl≢hl refl)

------------------------------------------------------------------------
-- Allocation Frontier Invariant
--
-- A location is "before" the allocation frontier if:
--   - Stack: slot index < next-slot (for current frame)
--   - Heap: ref-id < next-heap-ref
--
-- All valid locations are before the frontier.
------------------------------------------------------------------------

module FrontierInvariant {FS : FrameSemantics} where
  open FrameSemantics FS
  open MemOps {FS}
  open import Data.Nat.Properties using (≤-trans; m≤m+n; n≤1+n; <⇒≢)

  ------------------------------------------------------------------------
  -- Stack Ancestor Source (Provenance Tracking)
  --
  -- When we have stack-ancestor (current ≺ f), we track where f came from.
  -- This enables clean child-to-parent transfer:
  --
  --   - src-origin: f is the origin frame (e.g., parent frame), with slot bound
  --   - src-above-origin: origin ≺ f (f is above origin in the call stack)
  --
  -- Key insight: parent-before-child only creates these two cases, so when
  -- transferring back from child to parent, we never encounter "intermediate"
  -- frames (frames between child and origin that aren't origin itself).
  --
  -- Design: Both constructors carry slot bounds to enable frame transfer proofs.
  -- The bound is from the origin frame's allocation state when the location
  -- was first transferred from stack-before to stack-ancestor.
  ------------------------------------------------------------------------

  -- The bound is an INDEX (4th parameter) so it's visible in the type.
  -- This enables direct extraction when pattern matching.
  data StackAncestorSource (origin-frame : Frame) : Frame → ℕ → ℕ → Set where
    -- f is the origin frame, with slot bound from when it was stack-before
    src-origin : ∀ {k} →
      (origin-slot-bound : ℕ) →
      k < origin-slot-bound →
      StackAncestorSource origin-frame origin-frame k origin-slot-bound

    -- f is above origin in the call stack (origin ≺ f)
    -- Carries slot bound for transfer back to origin frame
    src-above-origin : ∀ {f k} →
      origin-frame ≺ f →
      (origin-slot-bound : ℕ) →
      k < origin-slot-bound →
      StackAncestorSource origin-frame f k origin-slot-bound

  -- Location is before allocation frontier
  --
  -- Uses frame ORDERING (≺) instead of inequality (≢) for the ancestor case.
  -- This enables clean transfer proofs via transitivity:
  --   - If child ≺ parent and we have stack-ancestor (parent ≺ f),
  --     then by transitivity child ≺ f, so stack-ancestor still holds.
  --
  -- The stack-ancestor case includes provenance tracking via
  -- StackAncestorSource, which records where the ancestor proof came from.
  --
  -- Key insight: current-frame ≺ f means f is an ancestor (caller) of current.
  data BeforeFrontier (alloc : AllocState {FS}) : ValueLocation FS → Set where
    stack-before : ∀ {f k} →
      f ≡ current-frame alloc →
      k < next-slot alloc →
      BeforeFrontier alloc (AtStack f k)

    stack-ancestor : ∀ {f k origin-frame bound} →
      current-frame alloc ≺ f →  -- f is above current (caller or higher)
      StackAncestorSource origin-frame f k bound →
      BeforeFrontier alloc (AtStack f k)

    -- Heap locations are before frontier if their ref-id < next-heap-ref
    heap-before : ∀ {hl : HeapLocation} →
      ref-id (heap-ref hl) < next-heap-ref alloc →
      BeforeFrontier alloc (AtDynamic hl)

  -- Helper: frame ordering implies inequality (via irreflexivity)
  ≺⇒≢ : ∀ {f₁ f₂ : Frame} → f₁ ≺ f₂ → f₁ ≢ f₂
  ≺⇒≢ {f₁} {f₂} f₁≺f₂ refl = ≺-irrefl f₁≺f₂

  -- Fresh allocation is after all existing locations
  fresh-stack-after : ∀ (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    loc ≢ AtStack (current-frame alloc) (next-slot alloc)
  fresh-stack-after alloc (AtStack f k) (stack-before refl k<next) eq
    with eq
  ... | refl = (<⇒≢ k<next) refl
  fresh-stack-after alloc (AtStack f k) (stack-ancestor cf≺f _) eq
    with eq
  ... | refl = ≺⇒≢ cf≺f refl
  fresh-stack-after alloc (AtDynamic hl) (heap-before _) ()

  -- Generalized: any caller-frontier location is disjoint from any
  -- scratch slot at or above the original frontier. The store-at-slot
  -- in scratch space cannot alias with closure-loc / input-loc /
  -- env-loc / etc., regardless of whether they're physical
  -- stack (AtStack ancestor frame OR current-frame below next-slot) or
  -- heap (AtDynamic) locations.
  --
  -- Plan 0.16: closure-loc shape independence. Heap and Stack closures
  -- alike satisfy `BeforeFrontier alloc closure-loc` (from
  -- `decomposeClosureWF.env-before`/`closure-before`), so this lemma
  -- handles both uniformly — no need to expose `closure-loc`'s
  -- constructor.
  before-frontier-stack-disjoint :
    ∀ (alloc : AllocState {FS}) (loc : ValueLocation FS) (k : ℕ) →
    BeforeFrontier alloc loc →
    next-slot alloc ≤ k →
    loc ≢ AtStack (current-frame alloc) k
  before-frontier-stack-disjoint alloc _ k (stack-before refl k'<next) next≤k refl =
    <⇒≢ (<-≤-trans k'<next next≤k) refl
    where open import Data.Nat.Properties using (<-≤-trans)
  before-frontier-stack-disjoint alloc _ k (stack-ancestor cf≺f _) next≤k refl =
    ≺⇒≢ cf≺f refl
  before-frontier-stack-disjoint alloc _ k (heap-before _) next≤k ()

  -- Allocation advances frontier
  stack-alloc-advances : ∀ (alloc : AllocState {FS}) n →
    ∀ loc → BeforeFrontier alloc loc →
    BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ n }) loc
  stack-alloc-advances alloc n (AtStack f k) (stack-before refl k<next) =
    stack-before refl (≤-trans k<next (m≤m+n (next-slot alloc) n))
  stack-alloc-advances alloc n (AtStack f k) (stack-ancestor cf≺f src) =
    stack-ancestor cf≺f src  -- Frame ordering and provenance unchanged (same current-frame)
  stack-alloc-advances alloc n (AtDynamic hl) (heap-before r<next) =
    heap-before r<next

  heap-alloc-advances : ∀ (alloc : AllocState {FS}) →
    ∀ loc → BeforeFrontier alloc loc →
    BeforeFrontier (record alloc { next-heap-ref = suc (next-heap-ref alloc) }) loc
  heap-alloc-advances alloc (AtStack f k) (stack-before eq k<next) =
    stack-before eq k<next
  heap-alloc-advances alloc (AtStack f k) (stack-ancestor cf≺f src) =
    stack-ancestor cf≺f src  -- Frame ordering and provenance unchanged (same current-frame)
  heap-alloc-advances alloc (AtDynamic hl) (heap-before r<next) =
    heap-before (≤-trans r<next (n≤1+n (next-heap-ref alloc)))

  -- General frontier monotonicity: if frontier advances, old locations are still before
  -- This is useful when alloc' is derived from alloc through arbitrary operations
  frontier-monotone : ∀ (alloc alloc' : AllocState {FS}) →
    current-frame alloc ≡ current-frame alloc' →
    next-slot alloc ≤ next-slot alloc' →
    next-heap-ref alloc ≤ next-heap-ref alloc' →
    ∀ loc → BeforeFrontier alloc loc → BeforeFrontier alloc' loc
  frontier-monotone alloc alloc' cf-eq slot-≤ heap-≤ (AtStack f k) (stack-before f-eq k<slot) =
    stack-before (trans f-eq cf-eq) (<-≤-trans k<slot slot-≤)
    where open import Data.Nat.Properties using (<-≤-trans)
  frontier-monotone alloc alloc' cf-eq slot-≤ heap-≤ (AtStack f k) (stack-ancestor cf≺f src) =
    stack-ancestor (subst (_≺ f) cf-eq cf≺f) src  -- Transfer ordering via frame equality, preserve provenance
  frontier-monotone alloc alloc' cf-eq slot-≤ heap-≤ (AtDynamic hl) (heap-before r<heap) =
    heap-before (<-≤-trans r<heap heap-≤)
    where open import Data.Nat.Properties using (<-≤-trans)

  ----------------------------------------------------------------------
  -- Plan 0.17 — Type-level Alloc Effect
  --
  -- An `AllocBump` declares an IR producer's effect on the allocation
  -- state: how many stack slots and how many heap refs it consumes,
  -- relative to the input alloc. Producers declare their bump
  -- explicitly; `IRResultBase.final-alloc` is derived from
  -- `apply-bump bump alloc` rather than being a free field. This makes
  -- inconsistencies (heap-result producer with non-zero next-slot-delta,
  -- trace bumping next-slot while bump says 0, etc.) into type errors.
  --
  -- See `plans/0.17-type-level-alloc-effect.md`.
  ----------------------------------------------------------------------

  record AllocBump : Set where
    constructor mkBump
    field
      next-slot-delta     : ℕ
      next-heap-ref-delta : ℕ

  open AllocBump public

  -- Apply a bump to an alloc state. `current-frame` is preserved
  -- (every instruction preserves current-frame; see
  -- `exec-abstract-preserves-frame`), so the bump only touches
  -- `next-slot` and `next-heap-ref`.
  --
  -- Operand order: `delta + next-slot alloc`. Agda's `_+_` is
  -- left-recursive (`zero + m = m`, `suc n + m = suc (n + m)`), so
  -- concrete deltas reduce definitionally:
  --   bump-0           → alloc unchanged (η of record)
  --   mkBump 0 1       → record alloc { next-heap-ref = suc … }
  --   mkBump 2 0       → record alloc { next-slot = suc (suc …) }
  -- This matches the canonical forms produced by SumInlAllocWF,
  -- CurryAllocWF, etc. Compositional producers (ApplyWF, PairAllocWF,
  -- ComposeWF) restructure alloc-correct around `apply-bump-compose`.
  apply-bump : AllocBump → AllocState {FS} → AllocState {FS}
  apply-bump bump alloc = record alloc
    { next-slot     = next-slot-delta bump     +ℕ next-slot alloc
    ; next-heap-ref = next-heap-ref-delta bump +ℕ next-heap-ref alloc
    }

  -- Zero bump: pure data-flow IR with no allocation effect.
  bump-0 : AllocBump
  bump-0 = mkBump 0 0

  -- Bump composition: f then g consumes f.bumps + g.bumps. Used by
  -- ComposeWF to derive its alloc-correct from sub-IR bumps without
  -- threading exec-trace state.
  bump-+ : AllocBump → AllocBump → AllocBump
  bump-+ b1 b2 = mkBump
    (next-slot-delta b1 +ℕ next-slot-delta b2)
    (next-heap-ref-delta b1 +ℕ next-heap-ref-delta b2)

  -- apply-bump preserves current-frame (record-update touches only
  -- next-slot / next-heap-ref).
  apply-bump-preserves-frame : ∀ (bump : AllocBump) (alloc : AllocState {FS}) →
    current-frame (apply-bump bump alloc) ≡ current-frame alloc
  apply-bump-preserves-frame _ _ = refl

  -- Composition of bumps: applying b1 then b2 equals applying their
  -- sum-bump. Uses commutativity + associativity to align the nested
  -- record-update with the single-bump form.
  --   b2.s + (b1.s + alloc.s) = (b1.s + b2.s) + alloc.s
  -- via assoc-then-comm-on-the-deltas. Same for next-heap-ref.
  apply-bump-compose : ∀ (b1 b2 : AllocBump) (alloc : AllocState {FS}) →
    apply-bump b2 (apply-bump b1 alloc) ≡ apply-bump (bump-+ b1 b2) alloc
  apply-bump-compose b1 b2 alloc = cong₂
    (λ s h → record alloc { next-slot = s ; next-heap-ref = h })
    (compose-eq (next-slot-delta b1) (next-slot-delta b2) (next-slot alloc))
    (compose-eq (next-heap-ref-delta b1) (next-heap-ref-delta b2) (next-heap-ref alloc))
    where
      open import Data.Nat.Properties using (+-assoc; +-comm)
      open import Relation.Binary.PropositionalEquality using (cong₂; cong)
      -- d2 + (d1 + x) ≡ (d1 + d2) + x.
      compose-eq : ∀ d1 d2 x → d2 +ℕ (d1 +ℕ x) ≡ (d1 +ℕ d2) +ℕ x
      compose-eq d1 d2 x =
        trans (sym (+-assoc d2 d1 x))
              (cong (_+ℕ x) (+-comm d2 d1))

  -- apply-bump bump-0 reduces to alloc definitionally:
  -- next-slot-delta bump-0 = 0 and 0 + n = n by Agda's left-recursive
  -- `_+_`; then record { next-slot = next-slot alloc; … } = alloc by η.
  apply-bump-0-eq : ∀ (alloc : AllocState {FS}) →
    apply-bump bump-0 alloc ≡ alloc
  apply-bump-0-eq _ = refl

------------------------------------------------------------------------
-- Frame Push/Pop Operations
--
-- These operations support the hybrid frame approach for Apply:
-- - push-frame: Create child frame state for body execution
-- - pop-frame: Restore parent frame state after body completes
--
-- Key insight: Body executes in a "child frame" with fresh next-slot = 0.
-- After body completes, we "pop" back to parent frame. The parent's
-- slot usage is controlled explicitly, making slot-bounded trivial.
------------------------------------------------------------------------

module FrameOps {FS : FrameSemantics} where
  open FrameSemantics FS
  open FrontierInvariant {FS}

  -- Push a child frame for body execution
  -- Child frame starts at next-slot = 0
  -- Heap state is shared between frames
  -- Note: child-capacity parameter retained for API compatibility but no longer stored
  push-frame : (parent : AllocState {FS})
             → (child-frame : Frame)
             → (child-capacity : ℕ)
             → AllocState {FS}
  push-frame parent cf cap = record
    { current-frame = cf
    -- Plan 0.61: the caller's frame is remembered so the epilogue can restore it.
    -- Plan 0.63: …together with the slot count it reserved.
    ; saved-frames = (current-frame parent , frame-slots parent) ∷ saved-frames parent
    ; frame-slots = cap
    ; next-slot = 0
    ; next-heap-ref = next-heap-ref parent  -- Heap shared
    ; block-size = block-size parent        -- …and so are the block sizes
    }

  -- Pop back to parent frame after body execution
  -- Result slot in parent frame, heap may have advanced
  -- NOTE: result-slot should be next-slot parent + pair-slots for apply
  pop-frame : (child : AllocState {FS})
            → (parent : AllocState {FS})
            → (result-slot : ℕ)
            → AllocState {FS}
  pop-frame child parent rs = record parent
    { next-slot = rs
    ; next-heap-ref = next-heap-ref child  -- Heap may have advanced
    ; block-size = block-size child        -- …with the sizes it recorded
    }

  ------------------------------------------------------------------------
  -- Frame Transition Lemmas (Using Frame Ordering)
  --
  -- These lemmas support proving BeforeFrontier across frame switches.
  -- With frame ORDERING (≺) instead of inequality (≢), transfer becomes
  -- structurally obvious via transitivity:
  --
  -- Key insight: child ≺ parent (child frame is "below" parent in call stack)
  --
  -- Transfer cases:
  -- 1. stack-before in parent (f = parent, k < next-slot):
  --    After push, child is current. Since child ≺ parent, this becomes
  --    stack-ancestor with child ≺ parent.
  --
  -- 2. stack-ancestor in parent (parent ≺ f):
  --    After push, child is current. By transitivity: child ≺ parent ≺ f,
  --    so child ≺ f. Stays stack-ancestor.
  --
  -- 3. heap-before: unchanged across frame switch (heap refs are global).
  ------------------------------------------------------------------------

  -- Locations in parent's current frame are BeforeFrontier in child
  -- (via stack-ancestor since child ≺ parent)
  -- The origin is the parent frame with slot bound from the current next-slot.
  in-parent-frame-before-child : ∀ (parent : AllocState {FS})
    (child-frame : Frame) (child-capacity : ℕ) (k : ℕ) →
    child-frame ≺ current-frame parent →  -- Child is below parent
    k < next-slot parent →
    BeforeFrontier (push-frame parent child-frame child-capacity)
                   (AtStack (current-frame parent) k)
  in-parent-frame-before-child parent cf cc k cf≺pf k<next =
    stack-ancestor cf≺pf (src-origin (next-slot parent) k<next)  -- Parent is origin, k < next-slot parent

  -- Heap locations are BeforeFrontier in child if they were in parent
  heap-before-child : ∀ (parent : AllocState {FS})
    (child-frame : Frame) (child-capacity : ℕ) (hl : HeapLocation) →
    ref-id (heap-ref hl) < next-heap-ref parent →
    BeforeFrontier (push-frame parent child-frame child-capacity) (AtDynamic hl)
  heap-before-child parent cf cc hl r<next = heap-before r<next

  -- Locations in an ancestor frame (above parent) are BeforeFrontier in child
  -- (via stack-ancestor since child ≺ f by transitivity)
  -- The origin is the parent frame, and since parent ≺ f, we use src-above-origin.
  ancestor-frame-before-child : ∀ (parent : AllocState {FS})
    (child-frame : Frame) (child-capacity : ℕ) (f : Frame) (k : ℕ)
    (bound : ℕ) (k<bound : k < bound) →
    child-frame ≺ current-frame parent →  -- Child is below parent
    current-frame parent ≺ f →            -- f is above parent
    BeforeFrontier (push-frame parent child-frame child-capacity) (AtStack f k)
  ancestor-frame-before-child parent cf cc f k bound k<bound cf≺pf pf≺f =
    stack-ancestor (≺-trans cf≺pf pf≺f) (src-above-origin pf≺f bound k<bound)

  -- General lemma: BeforeFrontier parent → BeforeFrontier child
  -- With frame ORDERING and PROVENANCE, this is clean via transitivity!
  --
  -- Key: child ≺ parent, so:
  --   - stack-before (f = parent, k < next-slot): becomes stack-ancestor with src-origin
  --   - stack-ancestor (parent ≺ f): becomes stack-ancestor with src-above-origin
  --   - heap-before: unchanged
  --
  -- The origin for the new stack-ancestor is always the parent frame, with:
  --   - src-origin k<next for locations that were in parent's frame
  --   - src-above-origin pf≺f for locations above parent
  parent-before-child : ∀ (parent : AllocState {FS})
    (child-frame : Frame) (child-capacity : ℕ) (loc : ValueLocation FS) →
    child-frame ≺ current-frame parent →  -- Child is below parent
    BeforeFrontier parent loc →
    BeforeFrontier (push-frame parent child-frame child-capacity) loc
  parent-before-child parent cf cc (AtStack f k) cf≺pf (stack-before refl k<next) =
    stack-ancestor cf≺pf (src-origin (next-slot parent) k<next)  -- f = parent is origin
  parent-before-child parent cf cc (AtStack f k) cf≺pf (stack-ancestor pf≺f (src-origin bound k<bound)) =
    stack-ancestor (≺-trans cf≺pf pf≺f) (src-above-origin pf≺f bound k<bound)
  parent-before-child parent cf cc (AtStack f k) cf≺pf (stack-ancestor pf≺f (src-above-origin _ bound k<bound)) =
    stack-ancestor (≺-trans cf≺pf pf≺f) (src-above-origin pf≺f bound k<bound)
  parent-before-child parent cf cc (AtDynamic hl) cf≺pf (heap-before r<next) =
    heap-before r<next  -- Heap refs unchanged

  ------------------------------------------------------------------------
  -- Pop lemmas: After body completes, restore parent frame state
  ------------------------------------------------------------------------

  -- After pop, parent frame locations at slots < result-slot are BeforeFrontier
  pop-preserves-before : ∀ (child parent : AllocState {FS})
    (result-slot : ℕ) (k : ℕ) →
    k < result-slot →
    BeforeFrontier (pop-frame child parent result-slot)
                   (AtStack (current-frame parent) k)
  pop-preserves-before child parent rs k k<rs = stack-before refl k<rs

  -- Heap locations after pop: if they were valid in child, still valid
  -- (heap might have advanced, so we need child's heap state)
  pop-heap-before : ∀ (child parent : AllocState {FS})
    (result-slot : ℕ) (hl : HeapLocation) →
    ref-id (heap-ref hl) < next-heap-ref child →
    BeforeFrontier (pop-frame child parent result-slot) (AtDynamic hl)
  pop-heap-before child parent rs hl r<child-heap = heap-before r<child-heap

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--
--   AllocMode     : StackAlloc | HeapAlloc
--   AllocState    : tracking available slots/refs
--
--   StackAllocation:
--     stack-alloc      : allocate n stack slots
--     stack-alloc-in-frame : result is in current frame
--
--   HeapAllocation:
--     heap-alloc       : allocate n heap slots
--
--   WriteOps:
--     write-loc              : write pointer to location
--     write-stack-read-same  : read back what we wrote
--     write-heap-read-same   : read back what we wrote
--
--   FrontierInvariant:
--     BeforeFrontier      : location is before allocation frontier
--     fresh-stack-after   : new stack slot ≠ old locations
--     stack-alloc-advances: old locations stay before new frontier
--     heap-alloc-advances : same for heap
--
--   FrameOps:
--     push-frame           : create child frame for body execution
--     pop-frame            : restore parent frame after body completes
--     parent-before-child  : BeforeFrontier transfers via transitivity (child ≺ parent)
--
------------------------------------------------------------------------