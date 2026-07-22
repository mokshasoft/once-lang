-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; trans; subst)

open import Once.Arith.Machine.Shape using (InputPath; Side)
open import Once.Memory.Memory using (Memory; readMem; writeMem)

module Once.Adequacy.ArchCorrectness.ArithSimPathLoadRegion
  (InStack InHeap : ℕ → Set)
  (stack-write-preserves-heap :
     ∀ m a v b → InStack a → InHeap b → readMem (writeMem m a v) b ≡ readMem m b)
  (def : Maybe ℕ → ℕ)
  (side-off : Side → ℕ)
  where

-- The input-pointer chase over a bare memory (= `path-load-go` with `mem s = m`).
plg : Memory → ℕ → InputPath → ℕ
plg m addr []          = def (readMem m addr)
plg m addr (sd ∷ rest) = plg m (def (readMem m (addr + side-off sd))) rest

-- Every address the chase reads is in the heap — the input value is heap-resident
-- (the frame's calling-convention contract; NOT proved here).
data HeapChase (m : Memory) : ℕ → InputPath → Set where
  hc-[] : ∀ {addr} → InHeap addr → HeapChase m addr []
  hc-∷  : ∀ {addr sd rest}
        → InHeap (addr + side-off sd)
        → HeapChase m (def (readMem m (addr + side-off sd))) rest
        → HeapChase m addr (sd ∷ rest)

-- THE DISCHARGE (= pl-inv-spill's content): a stack write is invisible to a
-- heap-resident chase — by induction on the path, via the GLOBAL disjointness.
plg-stack-write-invisible :
    ∀ m sA v addr p → InStack sA → HeapChase m addr p
  → plg (writeMem m sA v) addr p ≡ plg m addr p
plg-stack-write-invisible m sA v addr [] inS (hc-[] inH) =
  cong def (stack-write-preserves-heap m sA v addr inS inH)
plg-stack-write-invisible m sA v addr (sd ∷ rest) inS (hc-∷ inH hcRest) =
  trans (cong (λ w → plg (writeMem m sA v) (def w) rest)
              (stack-write-preserves-heap m sA v (addr + side-off sd) inS inH))
        (plg-stack-write-invisible m sA v (def (readMem m (addr + side-off sd))) rest inS hcRest)

-- HeapChase itself SURVIVES a stack write (needed to thread the input-heap
-- witness across a spill in wf-e1): the reads it inspects are all in-heap, so a
-- stack write leaves them — hence the same chase witnesses the new memory.
heapchase-stack-write :
    ∀ m sA v addr p → InStack sA → HeapChase m addr p → HeapChase (writeMem m sA v) addr p
heapchase-stack-write m sA v addr [] inS (hc-[] inH) = hc-[] inH
heapchase-stack-write m sA v addr (sd ∷ rest) inS (hc-∷ inH hcRest) =
  hc-∷ inH (subst (λ x → HeapChase (writeMem m sA v) (def x) rest)
                  (sym (stack-write-preserves-heap m sA v (addr + side-off sd) inS inH))
                  (heapchase-stack-write m sA v (def (readMem m (addr + side-off sd))) rest inS hcRest))
