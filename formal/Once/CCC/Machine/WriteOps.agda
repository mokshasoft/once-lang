-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.WriteOps
--
-- Write operations with disjointness proofs.
-- Separate module to avoid circular dependencies.
------------------------------------------------------------------------

module Once.CCC.Machine.WriteOps where

open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (<⇒≢; m<n⇒m<1+n)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.SMPrimitives
open import Once.CCC.Machine.Allocation

------------------------------------------------------------------------
-- Write Operations with Disjointness
------------------------------------------------------------------------

module WriteWithDisjoint {FS : FrameSemantics} where
  open MemOps {FS}
  open WriteOps {FS}
  open FrontierInvariant {FS}
  open FrameSemantics FS

  -- Writing to a location preserves reads at disjoint locations
  -- Note: AtDynamic now uses HeapLocation
  write-preserves-disjoint : ∀ (s : LocState FS) dst val src →
    dst ≢ src →
    readLoc (write-loc s dst val) src ≡ readLoc s src
  write-preserves-disjoint s (AtStack f k) val (AtStack f' k') neq
    with _≟F_ f f' | Data.Nat._≟_ k k'
  ... | yes refl | yes refl = ⊥-elim (neq refl)
  ... | yes refl | no _    = refl
  ... | no _    | yes refl = refl
  ... | no _    | no _     = refl
  write-preserves-disjoint s (AtStack _ _) val (AtDynamic _) neq = refl
  write-preserves-disjoint s (AtDynamic _) (AtStack _ _) (AtStack _ _) neq = refl  -- Invalid write (no-op)
  write-preserves-disjoint s (AtDynamic _) (AtStack _ _) (AtDynamic _) neq = refl     -- Invalid write (no-op)
  write-preserves-disjoint s (AtDynamic _) (AtDynamic _) (AtStack _ _) neq = refl
  write-preserves-disjoint s (AtDynamic hl) (AtDynamic v) (AtDynamic hl') neq
    with hl ≟HL hl'
  ... | yes refl = ⊥-elim (neq refl)
  ... | no _ = refl

  -- Reading from the location we just wrote to (stack case).
  -- Plan 0.13.2: write-loc to AtStack wraps val as SV-Ptr.
  write-read-same-stack : ∀ (s : LocState FS) (f : Frame) (k : ℕ) (val : ValueLocation FS) →
    readLoc (write-loc s (AtStack f k) val) (AtStack f k) ≡ just (SV-Ptr val)
  write-read-same-stack s f k val = write-stack-read-same s f k (SV-Ptr val)

  -- Reading from the heap location we just wrote to (heap case - val must be HeapLocation).
  -- Plan 0.13.2: heap reads lift to SV-Ptr at the boundary.
  write-read-same-heap : ∀ (s : LocState FS) (hl : HeapLocation) (v : HeapLocation) →
    readLoc (write-loc s (AtDynamic hl) (AtDynamic v)) (AtDynamic hl) ≡ just (SV-Ptr (AtDynamic v))
  write-read-same-heap s hl v with hl ≟HL hl
  ... | yes _ = refl
  ... | no hl≢hl = ⊥-elim (hl≢hl refl)

  ------------------------------------------------------------------------
  -- ValidWrite: predicate for semantically valid writes
  --
  -- The heap-only invariant means heap locations can only store heap values.
  -- ValidWrite captures this: stack destinations accept any value, but
  -- heap destinations require heap values.
  ------------------------------------------------------------------------

  data ValidWrite : ValueLocation FS → ValueLocation FS → Set where
    stack-valid : ∀ {f k val} → ValidWrite (AtStack f k) val
    heap-valid : ∀ {hl v} → ValidWrite (AtDynamic hl) (AtDynamic v)

  -- General write-read-same: requires ValidWrite proof to ensure semantic validity.
  -- Plan 0.13.2: now produces `≡ just (SV-Ptr val)`, since write-loc wraps the
  -- written ValueLocation as SV-Ptr.
  write-read-same : ∀ (s : LocState FS) (loc val : ValueLocation FS) →
    ValidWrite loc val →
    readLoc (write-loc s loc val) loc ≡ just (SV-Ptr val)
  write-read-same s (AtStack f k) val stack-valid = write-stack-read-same s f k (SV-Ptr val)
  write-read-same s (AtDynamic hl) (AtDynamic v) heap-valid = write-read-same-heap s hl v

  ------------------------------------------------------------------------
  -- Positive write preservation lemmas (using BeforeFrontier)
  --
  -- These lemmas take BeforeFrontier directly, avoiding the intermediate
  -- ≢ step. This is the positive interface for IR proofs.
  ------------------------------------------------------------------------

  -- Writing at frontier preserves all BeforeFrontier locations
  write-at-frontier-preserves-before : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    readLoc (write-loc s (AtStack (current-frame alloc) (next-slot alloc)) val) loc ≡
    readLoc s loc

  -- Case 1: Same frame, slot < next-slot
  write-at-frontier-preserves-before s alloc (AtStack f k) val (stack-before f≡cf k<next)
    with _≟F_ (current-frame alloc) f | Data.Nat._≟_ (next-slot alloc) k
  ... | yes _ | yes ns≡k = ⊥-elim (<⇒≢ k<next (sym ns≡k))
  ... | yes _ | no _ = refl
  ... | no cf≢f | _ = ⊥-elim (cf≢f (sym f≡cf))

  -- Case 2: Ancestor frame (current-frame ≺ f)
  write-at-frontier-preserves-before s alloc (AtStack f k) val (stack-ancestor cf≺f _)
    with _≟F_ (current-frame alloc) f
  ... | yes cf≡f = ⊥-elim (≺⇒≢ cf≺f cf≡f)
  ... | no _ = refl

  -- Case 3: Heap location (stack write doesn't affect heap)
  write-at-frontier-preserves-before s alloc (AtDynamic hl) val (heap-before _) = refl

  -- Writing at suc frontier preserves all BeforeFrontier locations
  write-at-suc-frontier-preserves-before : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    readLoc (write-loc s (AtStack (current-frame alloc) (suc (next-slot alloc))) val) loc ≡
    readLoc s loc

  -- Case 1: Same frame, slot < next-slot (so slot < suc next-slot too)
  write-at-suc-frontier-preserves-before s alloc (AtStack f k) val (stack-before f≡cf k<next)
    with _≟F_ (current-frame alloc) f | Data.Nat._≟_ (suc (next-slot alloc)) k
  ... | yes _ | yes sns≡k = ⊥-elim (<⇒≢ (m<n⇒m<1+n k<next) (sym sns≡k))
  ... | yes _ | no _ = refl
  ... | no cf≢f | _ = ⊥-elim (cf≢f (sym f≡cf))

  -- Case 2: Ancestor frame
  write-at-suc-frontier-preserves-before s alloc (AtStack f k) val (stack-ancestor cf≺f _)
    with _≟F_ (current-frame alloc) f
  ... | yes cf≡f = ⊥-elim (≺⇒≢ cf≺f cf≡f)
  ... | no _ = refl

  -- Case 3: Heap location
  write-at-suc-frontier-preserves-before s alloc (AtDynamic hl) val (heap-before _) = refl

  -- | The FRONTIER-slot sibling, for an arbitrary `StoredValue`.
  --
  -- D148: `run-inl`/`run-inr` store the sum TAG at the frontier slot before
  -- writing the payload pointer above it. Their models could not carry an
  -- input's validity across that write, because the only lemma available wrote
  -- at `suc (next-slot alloc)` and stored an `SV-Ptr`. Same proof as above: a
  -- `BeforeFrontier` location has `k < next-slot alloc`, so it is never the
  -- frontier slot itself, and the write is disjoint.
  write-sv-at-frontier-preserves-before : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) (sv : StoredValue FS) →
    BeforeFrontier alloc loc →
    readLoc (writeLoc s (AtStack (current-frame alloc) (next-slot alloc)) sv) loc ≡
    readLoc s loc

  -- Case 1: same frame, slot < next-slot — so the slot is NOT the frontier.
  write-sv-at-frontier-preserves-before s alloc (AtStack f k) sv (stack-before f≡cf k<next)
    with _≟F_ (current-frame alloc) f | Data.Nat._≟_ (next-slot alloc) k
  ... | yes _ | yes ns≡k = ⊥-elim (<⇒≢ k<next (sym ns≡k))
  ... | yes _ | no _ = refl
  ... | no cf≢f | _ = ⊥-elim (cf≢f (sym f≡cf))

  -- Case 2: ancestor frame — a different frame entirely.
  write-sv-at-frontier-preserves-before s alloc (AtStack f k) sv (stack-ancestor cf≺f _)
    with _≟F_ (current-frame alloc) f
  ... | yes cf≡f = ⊥-elim (≺⇒≢ cf≺f cf≡f)
  ... | no _ = refl

  -- Case 3: heap location — a stack write cannot touch it.
  write-sv-at-frontier-preserves-before s alloc (AtDynamic hl) sv (heap-before _) = refl

  -- | …and the SUC-frontier sibling, likewise for an arbitrary `StoredValue`.
  --
  -- Stage F: `run-inl`/`run-inr` store into the payload cell whatever `Input1`
  -- holds, which is a pointer only when the input was memory-resident. With a
  -- register-resident or unit input it is some other `StoredValue`, so the
  -- `write-loc` (pointer-only) form no longer covers the write. The proof is
  -- unchanged: `k < next-slot alloc < suc (next-slot alloc)`, so a
  -- `BeforeFrontier` location is never the written slot.
  write-sv-at-suc-frontier-preserves-before : ∀ (s : LocState FS) (alloc : AllocState {FS})
    (loc : ValueLocation FS) (sv : StoredValue FS) →
    BeforeFrontier alloc loc →
    readLoc (writeLoc s (AtStack (current-frame alloc) (suc (next-slot alloc))) sv) loc ≡
    readLoc s loc

  write-sv-at-suc-frontier-preserves-before s alloc (AtStack f k) sv (stack-before f≡cf k<next)
    with _≟F_ (current-frame alloc) f | Data.Nat._≟_ (suc (next-slot alloc)) k
  ... | yes _ | yes sns≡k = ⊥-elim (<⇒≢ (m<n⇒m<1+n k<next) (sym sns≡k))
  ... | yes _ | no _ = refl
  ... | no cf≢f | _ = ⊥-elim (cf≢f (sym f≡cf))

  write-sv-at-suc-frontier-preserves-before s alloc (AtStack f k) sv (stack-ancestor cf≺f _)
    with _≟F_ (current-frame alloc) f
  ... | yes cf≡f = ⊥-elim (≺⇒≢ cf≺f cf≡f)
  ... | no _ = refl

  write-sv-at-suc-frontier-preserves-before s alloc (AtDynamic hl) sv (heap-before _) = refl