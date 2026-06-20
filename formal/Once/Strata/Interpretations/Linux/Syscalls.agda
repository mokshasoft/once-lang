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

open import Data.String using (String)
open import Once.Type using (Int; Unit)
open import Once.Word using (Carrier)
import Once.Semantics.Value Carrier as M
open import Once.SigOp.Info using (SigOpInfo; mk-info; EffectShape; Pure; Halts)
open import Once.SigOp.Interpretation using (Interpretation)

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

------------------------------------------------------------------------
-- The Linux `Interpretation` (Plan 0.38 M0) — the per-name resolver the
-- compiler core is parameterized over. `linux.exit` resolves to its
-- declared `linux-exit-info` (`Halts`, concrete `semM`); every other
-- name resolves to a `Pure` value op whose machine value is the
-- genuine external axiom `linux-semM` — POSTULATED HERE, confined to the
-- Linux interpretation, NOT in the compiler core (this is precisely what
-- the retired `classify-name`/`generic-semM` catch-all did wrongly,
-- inside the core). A verified kernel (seL4) could prove `linux-semM`
-- instead; the core is agnostic to which.
------------------------------------------------------------------------

postulate
  linux-semM : ∀ {A B} → String → M.⟦ A ⟧ → M.⟦ B ⟧

info-linux : ∀ {A B} → String → SigOpInfo A B
info-linux {Int} {Unit} "linux.exit" = linux-exit-info
info-linux             name          = mk-info name (linux-semM name) Pure

linux : Interpretation
linux = record { info = info-linux }
