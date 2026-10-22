-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Meaning — the compiler's meaning of a typed module
-- is the Spec's behaviour of the program it denotes (plan 0.121 §3.6, F7).
--
-- The compiler runs its core program (`toProgram₀`, over a signature that
-- declares its FFI words) against an implementation of that signature; the
-- Spec runs the denoted program (`Denote`) against an Interpretation `J`.
-- Plan 0.122: the compiler's core program IS the Spec's, over the module's
-- own signature `Σₛ` (`view`: each FFI entry is a declaration of `Σₛ`, by
-- `SigFacts.sig-in`); against the implementation read from `J` (`toImpl`)
-- the two runs have the same trace (`same-trace`: `SpecCore.Sound.core-sound`,
-- and neither reading depends on the well-formedness proof).
------------------------------------------------------------------------

open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecFront.Meaning (fmt : TargetNum) where

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import Once.Spec.Signature using (WellFormed)
import Once.Spec.Core.Program as CoreProgram
open import Once.Spec.Trace using (_≈ᵗ⟨_⟩_)
open import Once.Internal.Trace using (interp)
open import Once.Internal.Core.Decl using (toISig)
open import Once.Denotation.TraceTr using (trT∞)
import Once.Internal.Core.Telescope as TL
open import Once.Internal.Module using (ModTele; MainIn; emptyScope)
import Once.Internal.Core.Translate as TR
open import Once.Adequacy.SpecInterp using (toImpl; toInterp)
import Once.Adequacy.SpecCore.Program as PG
import Once.Adequacy.SpecCore.Sound as Sound
open import Once.Adequacy.SpecFront.ImplWF using (toImpl-wf)
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
  same-trace : ∀ (wf′ : WellFormed Σₛ) J
             → trT∞ (toInterp Σₛ wf′ J) [] (TL.runCore Σₛ fmt (TR.toProgram₀ Σₛ mt mi view) (toImpl Σₛ J wf′))
               ≈ᵗ⟨ _≡_ ⟩ CoreProgram.behaviour Σₛ fmt progS J
  same-trace wf′ J =
    subst (λ P → trT∞ (toInterp Σₛ wf′ J) [] (TL.runCore Σₛ fmt P (toImpl Σₛ J wf′)) ≈ᵗ⟨ _≡_ ⟩ CoreProgram.behaviour Σₛ fmt progS J)
          (sym built)
          (subst (λ X → trT∞ (interp (toISig Σₛ) X) [] (TL.runCore Σₛ fmt (TL.program tele entry isMain) X)
                        ≈ᵗ⟨ _≡_ ⟩ CoreProgram.behaviour Σₛ fmt progS J)
                 (toImpl-wf Σₛ J wf wf′)
                 (Sound.core-sound Σₛ wf J uniq fmt (TL.program tele entry isMain)))
