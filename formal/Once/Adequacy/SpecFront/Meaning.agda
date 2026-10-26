-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Meaning — the compiler's meaning of a typed module
-- is the Spec's behaviour of the program it denotes (plan 0.121 §3.6, F7).
--
-- The compiler runs its core program (`toProgram₀`, over a signature that
-- declares its FFI words), each definition meaning its instances; the Spec
-- runs the denoted program (`Denote`). Plan 0.122: the compiler's core
-- program IS the Spec's, over the module's own signature `Σₛ` (`view`: each
-- FFI entry is a declaration of `Σₛ`, by `SigFacts.sig-in`); in every
-- Interpretation `J` the two runs have the same trace (`same-trace`:
-- `SpecCore.Sound.core-sound`).
------------------------------------------------------------------------

open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecFront.Meaning (fmt : TargetNum) where

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

import Once.Spec.Core.Program as CoreProgram
open import Once.Spec.Trace using (_≈ᵗ⟨_⟩_)
import Once.Internal.Core.Telescope as TL
open import Once.Module using (ModTele; MainIn; emptyScope)
import Once.Core.Translate as TR
import Once.Adequacy.ModuleProgram as MP
import Once.Adequacy.SpecCore.Program as PG
import Once.Adequacy.SpecCore.Sound as Sound
import Once.Adequacy.CoreBridge as CB
open import Once.Adequacy.SpecFront.SigFacts using (sig-in)
open import Once.Adequacy.SpecFront.Words using (key-word)
open import Once.Adequacy.SpecFront.Denote fmt using (Denoted)

module _ {mm′ ds′ es} {mt : ModTele emptyScope es} {mi : MainIn mt} (D : Denoted mm′ ds′ mt mi) where
  open Denoted D

  -- the Spec program the module denotes
  progS : CoreProgram.Program Σₛ
  progS = PG.programS Σₛ fmt wf (TL.program tele entry isMain)

  -- Σₛ declares the module's FFI words
  view : TR.SigIn Σₛ mt
  view = λ m → sig-in Σₛ (key-word keysW) (subst (_ ∈_) sig-eq m)

  -- The compiler's run of its core program has the Spec's trace.
  same-trace : ∀ J → CB.coreTr fmt Σₛ (MP.toProgram₀ Σₛ mt mi view) J ≈ᵗ⟨ _≡_ ⟩ CoreProgram.behaviour Σₛ fmt progS J
  same-trace J =
    subst (λ P → CB.coreTr fmt Σₛ P J ≈ᵗ⟨ _≡_ ⟩ CoreProgram.behaviour Σₛ fmt progS J)
          (sym built)
          (Sound.core-sound Σₛ wf fmt J (TL.program tele entry isMain))
