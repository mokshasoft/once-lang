-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.CPU.Interface — the portable per-arch interface.
--
-- Extracted from `Once.Verified.CPU` so per-arch instance modules
-- can import this without cycling through the dispatcher.
------------------------------------------------------------------------

module Once.Verified.CPU.Interface where

open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Maybe using (Maybe)

open import Once.Verified.Behavior using (Behavior)

-- Bytes
Byte : Set
Byte = Fin 256

-- Supported architectures
data Arch : Set where
  x86-64  : Arch
  x86-32  : Arch
  riscv64 : Arch

-- The portable per-arch interface.
record ArchSemantics : Set₁ where
  field
    Program      : Set
    State        : Set
    initialState : State
    run          : Program → State → Maybe State
    observe      : Maybe State → Behavior
    decode       : List Byte → Maybe Program

  exec-bytes : List Byte → Behavior
  exec-bytes bytes with decode bytes
  ... | Maybe.nothing  = observe Maybe.nothing
  ... | Maybe.just prog = observe (run prog initialState)
