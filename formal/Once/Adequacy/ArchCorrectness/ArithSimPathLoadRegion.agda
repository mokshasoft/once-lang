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

-- HeapChase SURVIVES any memory change that AGREES on in-heap addresses (needed
-- to thread the input-heap witness across each step in wf-e1): the chase inspects
-- only in-heap reads, so the same chase witnesses `m'`. Its `[]` case is
-- memory-independent (just `InHeap addr`). Non-spill: `m' = e1`'s memory,
-- agreement from `mem-keep`. Spill: `m' = writeMem`, agreement from FrameOps.
heapchase-agree :
    ∀ m m' addr p → (∀ a → InHeap a → readMem m' a ≡ readMem m a)
  → HeapChase m addr p → HeapChase m' addr p
heapchase-agree m m' addr []          agree (hc-[] inH) = hc-[] inH
heapchase-agree m m' addr (sd ∷ rest) agree (hc-∷ inH hcRest) =
  hc-∷ inH (subst (λ x → HeapChase m' (def x) rest)
                  (sym (agree (addr + side-off sd) inH))
                  (heapchase-agree m m' (def (readMem m (addr + side-off sd))) rest agree hcRest))
