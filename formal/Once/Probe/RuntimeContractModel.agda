-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Probe.RuntimeContractModel — plan 0.100 P0: the runtime contract is
-- SATISFIABLE. Not imported by anything; it exists to say so to the
-- typechecker.
--
-- It was not: the contract placed the stack `[0, stack-upper]` and the code
-- `[0, code-upper]` both at address 0 while postulating their disjointness, and
-- bounded EVERY program length by `code-upper` — so every `RuntimeContract`
-- was empty and each per-arch postulate was a postulate of `⊥`. This probe
-- refuted it (`intervals-disjoint rc 0`; `prog-fits rc (suc code-upper)`).
-- Now the regions are ORDERED and disjointness is a theorem; the probe builds
-- an instance, so the per-arch postulates are of an inhabited type.
------------------------------------------------------------------------

module Once.Probe.RuntimeContractModel where

open import Data.Nat using (s≤s; z≤n)
open import Once.Memory.RuntimeContract using (RuntimeContract)

-- stack [0,9], heap [10,19], code [20,29]
an-instance : RuntimeContract
an-instance = record
  { stack-upper = 9 ; heap-lower = 10 ; heap-upper = 19 ; code-lower = 20 ; code-upper = 29
  ; stack<heap = Data.Nat.Properties.≤-refl ; heap-valid = Data.Nat.Properties.m≤m+n 10 9
  ; heap<code = Data.Nat.Properties.≤-refl ; code-valid = Data.Nat.Properties.m≤m+n 20 9 }
  where import Data.Nat.Properties
