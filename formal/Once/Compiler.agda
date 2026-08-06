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

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

open import Data.Nat using (ℕ)

import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB

module Once.Compiler
  (o : CanonicalName) (program-bound : ℕ)
  (x86-64-heap-room : RB.HeapRoom o) (x86-64-stack-room : RB.StackRoom o)
  (x86-64-call-room : RB.CallRoom o) where

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
open import Once.Adequacy.ArchCorrectness o program-bound x86-64-heap-room x86-64-stack-room x86-64-call-room using (arch-correctness)
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
  -- Plan 0.49: the INDEPENDENT meaning is RELATIONAL. `Typed` = an executable
  -- declaratively-well-typed module; `_⊢_` links a source to it by PARSE (not
  -- the elaborator); `⟦_⟧ˢ` is the surface denotation `SD.⟦_⟧ˢ` of `main` (so
  -- `faithful` is load-bearing — typecheck + elaborate + codegen are forced).
  ; Typed    = VC.Typed
  ; _⊢_      = VC._⊢R_
  -- Plan 0.58 (OCP-0006): the reference meaning is now the DIRECT, IR-free
  -- derivation denotation `VC.⟦_⟧ᵈ` (was `VC.⟦_⟧ˢ` = SD∘realize); `correctᵈ`
  -- re-composes the grand theorem with the observational bridge.
  ; ⟦_⟧ˢ     = VC.⟦_⟧ᵈ
  ; exec     = VC.exec
  -- Behavioural equivalence = pointwise / up-to-`n` SigOp-trace prefix
  -- equality (Plan 0.44).
  ; _≈_      = λ b₁ b₂ → ∀ (n : ℕ) → b₁ n ≡ b₂ n
  -- Plan 0.48: `compile` carries the optimizer flag.
  ; compile  = VC.compile
  -- Plan 0.49: the two-conjunct (sound+trace / complete) relational claim.
  ; correct  = VC.correctᵈ
  }
