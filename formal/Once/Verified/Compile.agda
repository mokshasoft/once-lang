-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.Compile — THE PROOF (the compile function + correctness)
--
-- Parameterised over `Behavior` and `exec` (i.e. over the meaning
-- module and the per-arch CPU model). The proof body never names a
-- "matches-spec" axiom; trust lives strictly in the bodies of
-- `Once.Verified.Behavior` and `Once.Verified.CPU`. This is Plan
-- 0.11's parameterised-trusted-base pattern.
--
-- Today: `compile` and `correct` are themselves postulated wholesale
-- — pending Plan 0.4.2's connector + Plan 0.10's verified=extracted
-- work. As those plans land, postulates here are replaced with
-- concrete derivations.
--
-- The point of this module is that, when discharged, it contains
-- ZERO postulates. Postulates remain only in the input modules
-- (Behavior, CPU) — exactly where the trust lives.
------------------------------------------------------------------------

module Once.Verified.Compile where

open import Data.List using (List)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Verified.Behavior using (Source; Behavior; ⟦_⟧)
open import Once.Verified.CPU       using (Arch; Byte; exec)

postulate
  -- The compile function. Pure transformation Source → Maybe (List Byte),
  -- per-arch.
  compile : Arch → Source → Maybe (List Byte)

  -- The correctness witness. When `compile` produces bytes, the
  -- bytes' execution behaviour matches the source's denotation.
  correct :
    ∀ (arch : Arch) (src : Source) (bytes : List Byte) →
    compile arch src ≡ just bytes →
    exec arch bytes ≡ ⟦ src ⟧
