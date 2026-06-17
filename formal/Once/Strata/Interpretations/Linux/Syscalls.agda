-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Strata.Interpretations.Linux.Syscalls — the Linux syscall
-- interpretation's SigOp CONTRACTS (Plan 0.38, Milestone 1).
--
-- A SigOp is a morphism `A → B` that carries a contract its producer
-- discharges (Plan 0.38). This module is the EXTERNAL producer for the
-- Linux platform: it declares the contract (machine semantics `semM` +
-- observable `EffectShape`) of each Linux syscall Once can invoke. It is
-- the honest home of the external axioms — co-located with the platform
-- it describes, NOT hardcoded in the compiler (which is what the retired
-- `classify-name`/`generic-info` catch-all did).
--
-- DISCHARGE IS PER (SigOp × target), proof-OR-postulate — NOT
-- "external ⟹ axiom" (Plan 0.38, 2026-06-17):
--   * The *value* side: `linux.exit` is `Unit`-valued, so its `semM` is
--     the concrete `λ _ → tt` — NO postulate. (Data-returning syscalls
--     like `linux.read` will postulate `semM` here; a verified kernel
--     like seL4 could instead *prove* it against the kernel's spec.)
--   * The `EffectShape` is declared, not guessed: `linux.exit` `Halts`.
--   * The *implementation* side (`once_exit` asm ⊨ this `semM`/effect) is
--     trust-boundary #2 — discharged per target in
--     `…/Syscalls/<target>/Contract.agda` (deferred); for an unverified
--     kernel it is a postulate, for seL4 it can be proven.
--
-- Internal producers (the arith compiler, `Once.Arith.SigOp.Builders`)
-- PROVE their contracts. This module is the external counterpart.
------------------------------------------------------------------------

module Once.Strata.Interpretations.Linux.Syscalls where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Type using (Int; Unit)
open import Once.CCC.SigOp.Info using (SigOpInfo; mk-info; EffectShape; Halts)

------------------------------------------------------------------------
-- `linux.exit : Int → Unit` — terminate the process with an exit code.
--
-- `semM = λ _ → tt`: the result is `Unit` (the syscall does not return a
-- value into Once). The observable is the `Halts` event recording the
-- exit code (its `Int` input). No value postulate is needed; the only
-- trust is the per-target `impl ⊨ semM` contract (that `once_exit` really
-- performs the `exit` syscall), which lives in the per-target module.
------------------------------------------------------------------------

linux-exit-info : SigOpInfo Int Unit
linux-exit-info = mk-info "linux.exit" (λ _ → tt) (Halts refl)
