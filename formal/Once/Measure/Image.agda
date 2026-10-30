-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Measure.Image — STATIC COSTS OF A PROGRAM IMAGE
--
-- Counted over the abstract image every arch lowers (`Compile.image-of`), so
-- the numbers are the same on every arch and are about the object the proofs
-- describe. Static: a site counts once however often it runs (run-time counts
-- are plan 0.130). MERGE.md §1 "Emitted code and its cost" reads them through
-- `once stats` (`Once.Measure`).
--
--   instrs      abstract instructions
--   heap-sites  `instr-alloc-heap` sites
--   heap-cells  cells those sites allocate, summed
--   frames      frames reserved (`c-start`, each `c-entry`)
--   frame-max   the largest frame, in slots
--   frame-sum   all frames, in slots
------------------------------------------------------------------------

module Once.Measure.Image where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_)

open import Once.CCC.Machine.SMCore using (AbstractTrace; AbstractInstr; instr-alloc-heap; instr-ctrl; c-start; c-entry)

record ImageStats : Set where
  constructor mk-stats
  field
    instrs heap-sites heap-cells frames frame-max frame-sum : ℕ

private
  empty : ImageStats
  empty = mk-stats 0 0 0 0 0 0

  frame : ℕ → ImageStats → ImageStats
  frame b (mk-stats i hs hc f fm fs) = mk-stats i hs hc (suc f) (b ⊔ fm) (b + fs)

  -- CATCHALL: only allocation and frame reservation are counted.
  step : AbstractInstr → ImageStats → ImageStats
  step (instr-alloc-heap n)    (mk-stats i hs hc f fm fs) = mk-stats i (suc hs) (n + hc) f fm fs
  step (instr-ctrl (c-start b))   s = frame b s
  step (instr-ctrl (c-entry _ b)) s = frame b s
  {-# CATCHALL #-}
  step _                          s = s

  count : ImageStats → AbstractInstr → ImageStats
  count (mk-stats i hs hc f fm fs) x = step x (mk-stats (suc i) hs hc f fm fs)

  go : ImageStats → AbstractTrace → ImageStats
  go s []       = s
  go s (x ∷ xs) = go (count s x) xs

image-stats : AbstractTrace → ImageStats
image-stats = go empty

-- One `key value` line per count, in the header's order.
show-stats : ImageStats → String
show-stats (mk-stats i hs hc f fm fs) =
  "instrs " ++ showℕ i ++ "\nheap-sites " ++ showℕ hs ++ "\nheap-cells " ++ showℕ hc
  ++ "\nframes " ++ showℕ f ++ "\nframe-max " ++ showℕ fm ++ "\nframe-sum " ++ showℕ fs ++ "\n"
