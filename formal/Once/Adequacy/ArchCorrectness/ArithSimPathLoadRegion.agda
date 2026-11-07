-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion  (Plan 0.54 rung C)
--
-- Arch-generic: the input-pointer chase is INVISIBLE to a stack write. A spill
-- writes a STACK address; `path-load` chases pointers through the HEAP-resident
-- input; the regions are disjoint (the GLOBAL linker/runtime guarantee, supplied
-- here as the `stack-write-preserves-heap` parameter = `FrameOps`). This
-- discharges every arch's `pl-inv-spill`, given the input value is heap-resident
-- (`HeapChase` — the frame's calling-convention contract). No local region proof.
--
-- Parameterised by the arch's region predicates + the FrameOps preservation
-- lemma (all from `Once.Memory.{Regions,FrameOps}` at the arch's MemoryLayout),
-- plus `def`/`side-off`. The concrete `Memory = ℕ → Maybe ℕ` is shared.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _+_)
open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Data.List using ([]; _∷_)
open import Data.Unit using (⊤)

open import Once.Arith.Machine.Shape using (InputPath; flat-addr)
open import Once.Memory.Memory using (Memory; readMem; writeMem)

module Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion
  (InStack InHeap : ℕ → Set)
  (stack-write-preserves-heap :
     ∀ m a v b → InStack a → InHeap b → readMem (writeMem m a v) b ≡ readMem m b)
  (def : Maybe ℕ → ℕ)
  (word : ℕ)
  where

-- D391: the leaf read over a bare memory (= `path-load-go` with `mem s = m`): one
-- read at `flat-addr`.
plg : Memory → ℕ → InputPath → ℕ → ℕ
plg m base []      k = base
plg m base (x ∷ p) k = def (readMem m (flat-addr word base (x ∷ p) k))

-- The address the read touches is in the heap — the input value is heap-resident
-- (the frame's calling-convention contract; NOT proved here).
-- (D396: the empty path reads no memory)
HeapChase : Memory → ℕ → InputPath → ℕ → Set
HeapChase m base []      k = ⊤
HeapChase m base (x ∷ p) k = InHeap (flat-addr word base (x ∷ p) k)

-- THE DISCHARGE (= pl-inv-spill's content): a stack write is invisible to a
-- heap-resident read, via the GLOBAL disjointness.
plg-stack-write-invisible :
    ∀ m sA v base p k → InStack sA → HeapChase m base p k
  → plg (writeMem m sA v) base p k ≡ plg m base p k
plg-stack-write-invisible m sA v base []      k inS inH = refl
plg-stack-write-invisible m sA v base (x ∷ p) k inS inH =
  cong def (stack-write-preserves-heap m sA v (flat-addr word base (x ∷ p) k) inS inH)

-- HeapChase does not depend on the memory.
heapchase-agree :
    ∀ m m' base p k → (∀ a → InHeap a → readMem m' a ≡ readMem m a)
  → HeapChase m base p k → HeapChase m' base p k
heapchase-agree m m' base p k agree inH = inH
