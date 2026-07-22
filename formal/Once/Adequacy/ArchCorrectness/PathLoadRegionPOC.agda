-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.PathLoadRegionPOC  (Plan 0.54 rung B / B2.x)
--
-- POC: the GLOBAL region model discharges the pointer-chasing `pl-inv-spill`.
-- A spill writes a STACK address; `path-load` chases pointers through the input,
-- which lives in the HEAP; the two regions are disjoint (RuntimeContract's linker
-- guarantee, via FrameOps.stackAddr-write-preserves-heap). So the spill's write
-- leaves every address the chase reads untouched — proved by induction on the
-- path, consuming a per-read `InHeap` witness (`HeapChase`, = the input value is
-- heap-resident, the frame's contract). Nothing is proved locally about regions.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.PathLoadRegionPOC where

open import Data.Nat using (ℕ; _+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Once.Arith.Machine.Shape using (InputPath; Side; Fst; Snd)
open import Once.Memory.Memory using (Memory; readMem; writeMem)
open import Once.CCC.Target.X86-64.Layout using (InStack; InHeap; stackAddr-write-preserves-heap)

def : Maybe ℕ → ℕ
def (just w) = w
def nothing  = 0

side-off : Side → ℕ
side-off Fst = 0
side-off Snd = 8

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

-- THE DISCHARGE: a stack write is invisible to a heap-resident chase. This is
-- exactly `pl-inv-spill`'s content, derived from the GLOBAL region disjointness
-- (FrameOps.stackAddr-write-preserves-heap) — no local region reasoning.
plg-stack-write-invisible :
    ∀ m sA v addr p → InStack sA → HeapChase m addr p
  → plg (writeMem m sA v) addr p ≡ plg m addr p
plg-stack-write-invisible m sA v addr [] inS (hc-[] inH) =
  cong def (stackAddr-write-preserves-heap m sA v addr inS inH)
plg-stack-write-invisible m sA v addr (sd ∷ rest) inS (hc-∷ inH hcRest) =
  trans (cong (λ w → plg (writeMem m sA v) (def w) rest)
              (stackAddr-write-preserves-heap m sA v (addr + side-off sd) inS inH))
        (plg-stack-write-invisible m sA v (def (readMem m (addr + side-off sd))) rest inS hcRest)
