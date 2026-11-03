-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Compiler — ASSEMBLY POINT
--
-- This module wires together the trusted CPU base (`Once.Adequacy.CPU`) and
-- the per-arch backend correctness (`Once.Adequacy.ArchCorrectness`). The
-- correctness theorem built from them (`once-compiler`, over the Spec) is in
-- `Once.Certified`.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.


import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBr
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32

-- Plan 0.107: the entry unit's owner is the EMITTER's (`Once.Compile.entry-owner`),
-- not a parameter — the theorem is about the program actually emitted.
open import Once.Compile using (entry-owner)

module Once.Compiler
  (x86-64-reg-range : ∀ ι → RB.RegRange entry-owner ι)
  (x86-64-addr-no-wrap : ∀ ι → RB.AddrNoWrap entry-owner ι)
  (x86-64-lit-fits : ∀ ι → RB.LitFits entry-owner ι)
  (riscv64-reg-range : ∀ ι → RBr.RegRange entry-owner ι)
  (riscv64-slot-addr-no-wrap : ∀ ι → RBr.SlotAddrNoWrap entry-owner ι)
  (riscv64-addr-no-wrap : ∀ ι → RBr.AddrNoWrap entry-owner ι)
  (riscv64-lit-fits : ∀ ι → RBr.LitFits entry-owner ι)
  -- …and x86-32's three (plan 0.66 X3): the arch had none while its simulation
  -- was a whole-cloth postulate, which is precisely what a deleted apex
  -- postulate makes visible — the resources a running program needs.
  (x86-32-reg-range : ∀ ι → RB32.RegRange entry-owner ι)
  (x86-32-addr-no-wrap : ∀ ι → RB32.AddrNoWrap entry-owner ι)
  (x86-32-lit-fits : ∀ ι → RB32.LitFits entry-owner ι) where

-- The driver is where the per-arch CPU semantics are INJECTED (D054
-- wired-not-imported). Importing `Once.Adequacy.CPU` here pulls in the
-- per-arch instance postulates; that is intentional and confined to
-- this assembly point. `Once.Adequacy.Compile.WithCPU` itself stays
-- free of those imports.
open import Once.Adequacy.CPU using ()
open import Once.Adequacy.ArchCorrectness
       x86-64-reg-range x86-64-addr-no-wrap x86-64-lit-fits
       riscv64-reg-range riscv64-slot-addr-no-wrap
       riscv64-addr-no-wrap riscv64-lit-fits
       x86-32-reg-range x86-32-addr-no-wrap x86-32-lit-fits
       using (arch-correctness)
-- plan 0.92, and an honest note on its cost: `public` here is NOT convenience.
-- `Once.Certified` builds its apex from `arch-correctness`, and to name it one
-- level up it must be re-exported here. That propagation is exactly the
-- property that makes `public` expensive — but the alternative (Certified
-- re-importing `ArchCorrectness` with its full ten-parameter telescope) is
-- worse.
       public
-- The CLI is extracted from `Once.Extract.Root`; the correctness theorem over
-- what it runs is `Once.Certified` (plan 0.121, D332).
