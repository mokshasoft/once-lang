-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CPU.Interface — the portable per-arch interface.
--
-- Extracted from `Once.Adequacy.CPU` so per-arch instance modules
-- can import this without cycling through the dispatcher.
------------------------------------------------------------------------

module Once.Adequacy.CPU.Interface where

open import Data.Fin using (Fin)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe)
open import Data.String using (String)

open import Once.Denotation.Behavior using (Behavior)

-- Bytes
Byte : Set
Byte = Fin 256

-- Supported architectures — the single shared enum (re-exported).
open import Once.Target.Arch public

-- The portable per-arch interface.
record ArchSemantics : Set₁ where
  field
    Program      : Set
    State        : Set
    initialState : State
    run          : Program → State → Maybe State
    -- The OBSERVABLE: the step-indexed SigOp trace produced by executing
    -- `prog` from `state` (Plan 0.44). `run-trace prog st n` is the trace
    -- of SigOp invocations within `n` steps. This replaces the old
    -- value-shaped `observe : Maybe State → Behavior` (a final-state →
    -- exit-code projection, which structurally cannot yield a trace).
    -- It will be DERIVED from `run`'s step semantics once the model
    -- records SigOp invocations and continues (the emit-and-continue
    -- machine); per-arch instances postulate it until then — a named gap
    -- alongside `decode`/`assemble`.
    run-trace    : Program → State → Behavior
    decode       : List Byte → Maybe Program
    -- Assembler: asm text → bytes. The per-arch GNU `as` trust point
    -- (D054 wired-not-imported), confined to this injected bundle.
    -- Removed when the in-Agda assembler (B1) lands.
    assemble     : String → List Byte

  exec-bytes : List Byte → Behavior
  exec-bytes bytes with decode bytes
  ... | Maybe.nothing  = λ _ → []
  ... | Maybe.just prog = run-trace prog initialState
