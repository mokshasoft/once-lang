-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Compiler — ASSEMBLY POINT
--
-- This module wires together:
--   - the abstract spec     (`Once.Adequacy`)
--   - the meaning           (`Once.Denotation.Behavior`)
--   - the trusted CPU base  (`Once.Adequacy.CPU`)
--   - the proof + compile   (`Once.Adequacy.Compile`)
--
-- and constructs a single `CorrectCompiler` value the CLI consumes.
-- This file should be one record literal — no logic, no postulates
-- of its own. If the assembly typechecks, the compiler is correct
-- (modulo the postulates listed in the participating modules).
------------------------------------------------------------------------

module Once.Compiler where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Adequacy
open import Once.Denotation.Behavior using (Source; Behavior)
open import Once.Adequacy.SourceTrace using (⟦_⟧)
-- The driver is where the per-arch CPU semantics are INJECTED (D054
-- wired-not-imported). Importing `Once.Adequacy.CPU` here pulls in the
-- per-arch instance postulates; that is intentional and confined to
-- this assembly point. `Once.Adequacy.Compile.WithCPU` itself stays
-- free of those imports.
open import Once.Adequacy.CPU      using (Arch; Byte; arch-semantics)
open import Once.Adequacy.ArchCorrectness using (arch-correctness)
import Once.Adequacy.Compile as VCompile

-- Instantiate the verified pipeline with the concrete per-arch
-- semantics AND the per-arch backend-correctness witnesses. `VC.compile` /
-- `VC.exec` / `VC.correct` are the compiler, the injected execution, and the
-- grand theorem proved against them. `arch-correctness` forces every target
-- to supply its `ArchCorrect` (proof or postulate) — the assembly point for
-- the per-arch trusted base.
module VC = VCompile.WithCPU arch-semantics arch-correctness

once-compiler : CorrectCompiler
once-compiler = record
  { Arch     = Arch
  ; Source   = Source
  ; Bytes    = List Byte
  ; Behavior = Behavior
  ; ⟦_⟧      = ⟦_⟧
  ; exec     = VC.exec
  -- Behavioural equivalence = pointwise / up-to-`n` SigOp-trace prefix
  -- equality (Plan 0.44). `VC.correct` is already this `∀ n → … n ≡ … n`,
  -- so `correct` slots in with no funext.
  ; _≈_      = λ b₁ b₂ → ∀ (n : ℕ) → b₁ n ≡ b₂ n
  ; compile  = VC.compile
  ; correct  = VC.correct
  }
