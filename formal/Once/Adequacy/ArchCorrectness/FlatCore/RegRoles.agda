-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
--
-- THE ROLE MAP (Plan 0.65 G1c, 2026-08-11).
--
-- The abstract machine has a fixed set of registers — Output, Input1, Input2,
-- Scratch, Count — plus three the flat machine owns: the stack pointer, the
-- closure pointer and the heap frontier. `FlatCorrespondence` named x86-64's
-- physical registers for these **799 times**, and every one of those mentions
-- is a ROLE, not an x86 fact. This record is that observation, made a type.
--
-- WHY A RECORD OF NAMED ROLES rather than `Reg` + `sp-reg`. A `sp-reg`-only
-- parameterisation was the original guess; measuring showed it would leave 587
-- concrete register mentions behind, i.e. most of the module. The roles are
-- what the correspondence's fields are ABOUT — `rax-eq` is the claim that the
-- Output register agrees — so naming them is what lets the statements survive
-- a change of arch.
--
-- NO LAWS HERE, DELIBERATELY. Role DISTINCTNESS (that a write to Output leaves
-- Input1 alone) is free today: with the roles projected from a concrete record,
-- `X.readReg (X.writeReg rf out-reg v) in1-reg` still reduces exactly as
-- `readReg (writeReg rf rax v) rdi` did. It stops being free at G1c step 2,
-- where the post-state becomes abstract — so the distinctness the proofs
-- actually use gets added there, driven by the obligations rather than
-- guessed at here.
--
-- ONE MEASURED CAVEAT, for whoever instantiates this next (plan 0.66): x86-32
-- CANNOT fill this record injectively. It has eight GPRs, the machine has nine
-- roles counting the frame pointer, and `Input2` and `Scratch` are both `edx`
-- there today. That is a real finding, not a nuisance — see plan 0.65's G1c
-- section for why there is no local fix and what the two real options are.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.FlatCore.RegRoles where

record RegRoles (Reg : Set) : Set where
  field
    -- the flat machine's own three
    sp-reg      : Reg   -- stack pointer: IS the current frame's base (plan 0.61)
    clos-reg    : Reg   -- closure pointer, mirroring the flat `fclosure` (D097)
    heap-reg    : Reg   -- heap frontier, the bump allocator's top
    -- the abstract machine's registers
    out-reg     : Reg   -- Output
    in1-reg     : Reg   -- Input1
    in2-reg     : Reg   -- Input2
    scratch-reg : Reg   -- Scratch
    count-reg   : Reg   -- Count, the cata tally (plan 0.54 D item 4)
