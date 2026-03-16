------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.WriteOps
--
-- Write operations with disjointness proofs.
-- Separate module to avoid circular dependencies.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.WriteOps where

open import Data.Nat using (ℕ; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (yes; no)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SMCore
open import Once.CCC.SMPrimitives
open import Once.CCC.Target.X86v3.Dispatcher.Allocation

------------------------------------------------------------------------
-- Write Operations with Disjointness
------------------------------------------------------------------------

module WriteWithDisjoint {FS : FrameSemantics} where
  open MemOps {FS}
  open WriteOps {FS}
  open FrontierInvariant {FS}
  open FrameSemantics FS

  -- Writing to a location preserves reads at disjoint locations
  -- Note: OnHeap now uses HeapLocation
  write-preserves-disjoint : ∀ (s : LocState FS) dst val src →
    dst ≢ src →
    readLoc (write-loc s dst val) src ≡ readLoc s src
  write-preserves-disjoint s (OnStack f k) val (OnStack f' k') neq
    with _≟F_ f f' | Data.Nat._≟_ k k'
  ... | yes refl | yes refl = ⊥-elim (neq refl)
  ... | yes _ | no _ = refl
  ... | no _ | _ = refl
  write-preserves-disjoint s (OnStack _ _) val (OnHeap _) neq = refl
  write-preserves-disjoint s (OnHeap _) (OnStack _ _) (OnStack _ _) neq = refl  -- Invalid write (no-op)
  write-preserves-disjoint s (OnHeap _) (OnStack _ _) (OnHeap _) neq = refl     -- Invalid write (no-op)
  write-preserves-disjoint s (OnHeap _) (OnHeap _) (OnStack _ _) neq = refl
  write-preserves-disjoint s (OnHeap hl) (OnHeap v) (OnHeap hl') neq
    with hl ≟HL hl'
  ... | yes refl = ⊥-elim (neq refl)
  ... | no _ = refl

  -- Reading from the location we just wrote to (stack case)
  write-read-same-stack : ∀ (s : LocState FS) (f : Frame) (k : ℕ) (val : ValueLocation FS) →
    readLoc (write-loc s (OnStack f k) val) (OnStack f k) ≡ just val
  write-read-same-stack s f k val = write-stack-read-same s f k val

  -- Reading from the heap location we just wrote to (heap case - val must be HeapLocation)
  write-read-same-heap : ∀ (s : LocState FS) (hl : HeapLocation) (v : HeapLocation) →
    readLoc (write-loc s (OnHeap hl) (OnHeap v)) (OnHeap hl) ≡ just (OnHeap v)
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
    stack-valid : ∀ {f k val} → ValidWrite (OnStack f k) val
    heap-valid : ∀ {hl v} → ValidWrite (OnHeap hl) (OnHeap v)

  -- General write-read-same: requires ValidWrite proof to ensure semantic validity
  -- ValidWrite evidence provides type-level proof that only well-typed cases are constructed
  write-read-same : ∀ (s : LocState FS) (loc val : ValueLocation FS) →
    ValidWrite loc val →
    readLoc (write-loc s loc val) loc ≡ just val
  write-read-same s (OnStack f k) val stack-valid = write-stack-read-same s f k val
  write-read-same s (OnHeap hl) (OnHeap v) heap-valid = write-read-same-heap s hl v
