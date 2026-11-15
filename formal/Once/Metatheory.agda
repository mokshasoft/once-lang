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
--   laws        Once.Metatheory.Laws (categorical structure, equations)
--   parametricity Once.Metatheory.Parametricity (abstraction, naturality)
--   laws-apply  Once.Metatheory.LawsApply (an instance of every law: none is vacuous)
------------------------------------------------------------------------

module Once.Metatheory where

open import Once.Spec.Metatheory using (Metatheory)
open import Once.Metatheory.Types using (types)
open import Once.Metatheory.Totality using (totality)
import Once.Metatheory.Surface as Surface
import Once.Metatheory.Effects as Effects
import Once.Metatheory.Inhabited as Inhabited
import Once.Metatheory.Sameness as Sameness
import Once.Metatheory.Coherence.Fundamental as Coherence
import Once.Metatheory.TermModel as TermModel
import Once.Metatheory.Freyd as Freyd
import Once.Metatheory.Recursion as Recursion
import Once.Metatheory.Laws as Laws
import Once.Metatheory.Parametricity as Parametricity
import Once.Metatheory.LawsApply as LawsApply
import Once.Metatheory.Numbers as Numbers

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
  ; categorical = λ Σ u fmt S → Laws.categorical Σ u fmt S
  ; equations  = λ Σ u fmt S → Laws.equations Σ u fmt S
  ; parametricity = λ Σ u fmt S → Parametricity.parametricity Σ u fmt S
  ; laws-apply = λ fmt → LawsApply.lawsApply fmt
  ; numbers    = Numbers.numbers
  }
