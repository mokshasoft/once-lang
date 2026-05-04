-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.CPU — TRUSTED BASE: per-arch CPU semantics
--
-- This module defines the supported architectures and their byte-level
-- execution semantics. Each `exec-<arch>` is a concrete state-machine
-- definition (currently postulated stub). The TRUST point per arch is
-- the BODY of `exec-<arch>`: a reviewer compares it clause-by-clause
-- against the vendor ISA spec (Intel SDM, RISC-V manual, etc.).
-- There is no separate "matches-spec" axiom — same convention as
-- CompCert's `Asm.v`.
--
-- Bytes are typed `List (Fin 256)` — fully primitive, fully
-- inspectable, no opaque wrapper.
--
-- The result type `Behavior` is imported from `Once.Verified.Behavior`
-- so the per-arch CPU model produces values of the same observable
-- type the source semantics produces. Equality between them is what
-- compiler correctness reduces to.
------------------------------------------------------------------------

module Once.Verified.CPU where

open import Data.Fin using (Fin)
open import Data.List using (List)

open import Once.Verified.Behavior using (Behavior)

------------------------------------------------------------------------
-- Bytes
------------------------------------------------------------------------

Byte : Set
Byte = Fin 256

------------------------------------------------------------------------
-- Supported architectures
------------------------------------------------------------------------

data Arch : Set where
  x86-64  : Arch
  x86-32  : Arch
  riscv64 : Arch

------------------------------------------------------------------------
-- Per-arch CPU semantics (the trusted bodies)
--
-- Each `exec-<arch>` will become a concrete state machine. Postulated
-- stub today; discharge maps to Plan 0.11 (parameterised trusted
-- base). The trust is in each function's body once written, not in
-- a separate axiom.
------------------------------------------------------------------------

postulate
  exec-x86-64  : List Byte → Behavior
  exec-x86-32  : List Byte → Behavior
  exec-riscv64 : List Byte → Behavior

------------------------------------------------------------------------
-- Dispatcher
------------------------------------------------------------------------

exec : Arch → List Byte → Behavior
exec x86-64  = exec-x86-64
exec x86-32  = exec-x86-32
exec riscv64 = exec-riscv64
