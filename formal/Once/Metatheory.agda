-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory — what the language promises about itself
-- (`Spec.Metatheory`), proved over the Spec alone (D304).
--
--   types       Once.Metatheory.Types
--   surface     Once.Metatheory.Surface
--   effects     Once.Metatheory.Effects (and Erase, Bisim, Observe)
--   inhabited   Once.Metatheory.Inhabited
--   sameness    Once.Metatheory.Sameness (and Coherence.PER)
--   coherence   Once.Metatheory.Coherence.Fundamental
--   term model  Once.Metatheory.TermModel
--   Freyd       Once.Metatheory.Freyd
--   recursion   Once.Metatheory.Recursion (and Unfold, Lawful)
--   totality    Once.Metatheory.Totality (and Run, RunLaws, Trace)
------------------------------------------------------------------------

module Once.Metatheory where

open import Once.Spec.Metatheory using (Metatheory)
open import Once.Metatheory.Types using (types)
open import Once.Metatheory.Totality using (totality)
import Once.Metatheory.Surface as Surface
import Once.Metatheory.Effects as Effects
import Once.Metatheory.Inhabited as Inhabited
import Once.Metatheory.Sameness as Sameness
-- sameness of streams is the greatest fixed point of its one-layer step
import Once.Metatheory.Coherence.StreamSame
import Once.Metatheory.Coherence.Fundamental as Coherence
import Once.Metatheory.TermModel as TermModel
import Once.Metatheory.Freyd as Freyd
import Once.Metatheory.Recursion as Recursion

metatheory : Metatheory
metatheory = record
  { types      = types
  ; surface    = λ Σ S nm dist → Surface.surface Σ S nm dist
  ; effects    = λ Σ → Effects.effects Σ
  ; inhabited  = λ Σ → Inhabited.inhabited Σ
  ; sameness   = λ Σ → Sameness.sameness Σ
  ; coherence  = λ Σ u fmt S → Coherence.coherence Σ u fmt S
  ; term-model = λ Σ u fmt S → TermModel.termModel Σ u fmt S
  ; freyd      = λ Σ → Freyd.freyd Σ
  ; recursion  = λ Σ → Recursion.recursion Σ
  ; totality   = totality
  }
