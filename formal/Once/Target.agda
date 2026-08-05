-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Target
--
-- Target interface for code generation.
-- Each target (x86-64, x86-32, RISC-V, etc.) implements this interface.
------------------------------------------------------------------------

module Once.Target where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Once.IR using (IR)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.CanonicalName using (CanonicalName)
open import Once.Target.RegConvention using (RegConvention)

------------------------------------------------------------------------
-- Target Record
------------------------------------------------------------------------

-- | A target provides architecture-specific code generation.
-- `Set₁` because `regConvention : RegConvention` carries the arch's `Reg : Set`.
record Target : Set₁ where
  field
    -- | Compile IR to assembly text (function body only).
    -- Plan 0.12 Layer 1: takes a starting thunk-label counter and
    -- returns the next-available counter so that thunk labels stay
    -- globally unique across multiple top-level functions in the
    -- same module. `compileAllWithTarget` left-folds the counter.
    -- Plan 0.63 (D089): the DEFINITION'S identity, so its labels carry it.
    irToAsm : CanonicalName → ℕ → ∀ {A B} → IR A B → ℕ × String
    -- | Plan 0.2.4.2 Phase B: assembly text for closure-body labels
    -- (`.L_thunk_<n>:` blocks) emitted AFTER the parent's `ret`.
    -- Empty string for IRs containing no `curry` (most non-effectful
    -- code). Two-pass codegen separates this from `irToAsm` so the
    -- parent's ret comes between them. Plan 0.12 Layer 1: takes the
    -- same starting label counter `irToAsm` was called with, so that
    -- the body-emission's labels match the trace's call sites.
    irToBodies : CanonicalName → ℕ → ∀ {A B} → IR A B → ℕ × String
    -- | Assembly file header (e.g., ".section .text")
    asmHeader : String
    -- | Generate function prologue (label, .globl directive).
    -- Plan 0.50 (def-side CanonicalName): keyed on the definition's
    -- CanonicalName, mangled by `once-symbol-path` — the same identity the
    -- caller resolves to, so def/call symbols agree by construction.
    functionPrologue : CanonicalName → String
    -- | Generate function epilogue (ret instruction)
    functionEpilogue : String
    -- | Plan 0.20 Phase G: emit per-arith-block subroutines as a
    -- flat sequence of assembly definitions, concatenated after
    -- the program's normal text. One block becomes one subroutine
    -- named `once_arith.block.<digest>` matching the call-site
    -- symbol from `compile-sigOp`. Targets that don't yet ship a
    -- block emitter return `""`.
    emitArithBlocks : List ArithBlock → String
    -- | Plan 0.55/0.56: the arch's physical-register convention — its register
    -- partition (`owner`) + arith budget. Making it a Target field FORCES every
    -- arch to declare (and prove valid, via `budget-owned`) how it lends
    -- registers to the arith block; consumed by the PreservesCCC / budget work.
    regConvention : RegConvention

open Target public
