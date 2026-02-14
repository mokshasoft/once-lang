------------------------------------------------------------------------
-- Once.Backend.X86v3.WriteOps
--
-- Write operations with disjointness proofs.
-- Separate module to avoid circular dependencies.
------------------------------------------------------------------------

module Once.Backend.X86v3.WriteOps where

open import Data.Nat using (ℕ; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (yes; no)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Allocation

------------------------------------------------------------------------
-- Write Operations with Disjointness
------------------------------------------------------------------------

module WriteWithDisjoint {FS : FrameSemantics} where
  open MemOps {FS}
  open WriteOps {FS}
  open FrontierInvariant {FS}
  open FrameSemantics FS

  -- Writing to a location preserves reads at disjoint locations
  write-preserves-disjoint : ∀ (s : LocState FS) dst val src →
    dst ≢ src →
    readLoc (write-loc s dst val) src ≡ readLoc s src
  write-preserves-disjoint s (OnStack f k) val (OnStack f' k') neq
    with _≟F_ f f' | Data.Nat._≟_ k k'
  ... | yes refl | yes refl = ⊥-elim (neq refl)
  ... | yes _ | no _ = refl
  ... | no _ | _ = refl
  write-preserves-disjoint s (OnStack _ _) val (OnHeap _ _) neq = refl
  write-preserves-disjoint s (OnHeap _ _) val (OnStack _ _) neq = refl
  write-preserves-disjoint s (OnHeap r o) val (OnHeap r' o') neq
    with r ≟H r' | Data.Nat._≟_ o o'
  ... | yes refl | yes refl = ⊥-elim (neq refl)
  ... | yes _ | no _ = refl
  ... | no _ | _ = refl

  -- sucLoc is different from loc
  sucLoc-neq : ∀ (loc : ValueLocation FS) → sucLoc loc ≢ loc
  sucLoc-neq (OnStack f k) ()
  sucLoc-neq (OnHeap r o) ()

  -- Reading from the location we just wrote to
  write-read-same : ∀ (s : LocState FS) (loc : ValueLocation FS) (val : ValueLocation FS) →
    readLoc (write-loc s loc val) loc ≡ just val
  write-read-same s (OnStack f k) val = write-stack-read-same s f k val
  write-read-same s (OnHeap r o) val = write-heap-read-same s r o val

  -- loc ≢ sucLoc loc (inverse direction of sucLoc-neq)
  loc-neq-sucLoc : ∀ (loc : ValueLocation FS) → loc ≢ sucLoc loc
  loc-neq-sucLoc (OnStack f k) ()
  loc-neq-sucLoc (OnHeap r o) ()

  -- Write preserves stackMem equality at all but written location
  write-loc-stackMem : ∀ (s : LocState FS) (loc : ValueLocation FS) (val : ValueLocation FS) →
    ∀ f k → (OnStack f k ≢ loc) →
    stackMem (write-loc s loc val) f k ≡ stackMem s f k
  write-loc-stackMem s (OnStack f' k') val f k neq
    with _≟F_ f' f | Data.Nat._≟_ k' k
  ... | yes refl | yes refl = ⊥-elim (neq refl)
  ... | yes _ | no _ = refl
  ... | no _ | _ = refl
  write-loc-stackMem s (OnHeap _ _) val f k neq = refl

  -- Write to stack preserves heap
  write-loc-heapMem : ∀ (s : LocState FS) (loc : ValueLocation FS) (val : ValueLocation FS) →
    ∀ r o → (OnHeap r o ≢ loc) →
    heapMem (write-loc s loc val) r o ≡ heapMem s r o
  write-loc-heapMem s (OnStack _ _) val r o neq = refl
  write-loc-heapMem s (OnHeap r' o') val r o neq
    with r' ≟H r | Data.Nat._≟_ o' o
  ... | yes refl | yes refl = ⊥-elim (neq refl)
  ... | yes _ | no _ = refl
  ... | no _ | _ = refl
