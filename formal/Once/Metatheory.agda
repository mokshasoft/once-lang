-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory — THE PROOF of `Once.Spec.Metatheory` (D304, D305): what the
-- language promises about itself, assembled from the proofs under
-- `Once/Metatheory`, which import only the Spec side (`make metatheory-gate`).
-- `Once.Certified` carries it as `CertifiedBuild.language`.
------------------------------------------------------------------------

module Once.Metatheory where

open import Once.Spec.Metatheory using (Metatheory; TypeSystem)
open import Once.Metatheory.TermModel using (termModel)
open import Once.Metatheory.Effects using (effects)
open import Once.Metatheory.Recursion using (recursion)
open import Once.Metatheory.Freyd using (freyd)
open import Once.Metatheory.Totality using (totality)
import Once.Metatheory.Coherence as Coh
import Once.Metatheory.SubLaws as SL
import Once.Metatheory.ModeAgreement as MA

typeSystem : TypeSystem
typeSystem = record
  { <:-refl             = SL.<:-refl
  ; <:-trans            = SL.<:-trans
  ; <:-unique           = SL.<:-unique
  ; ⊑π-refl             = SL.⊑π-refl
  ; ⊑π-trans            = SL.⊑π-trans
  ; ⊑π-unique           = SL.⊑π-unique
  ; synth-unique        = MA.agree-ii
  ; check-usage-unique  = MA.agree-cc
  ; check-agrees-synth  = MA.agree-ic
  ; domain-agrees-check = MA.agree-dc
  ; domain-agrees-synth = MA.agree-di
  ; domain-exact        = MA.agree-dd
  }

metatheory : Metatheory
metatheory = record
  { term-model  = termModel
  ; type-system = typeSystem
  ; effects     = effects
  ; coherence   = λ S → Coh.coherence S
  ; freyd       = freyd
  ; recursion   = recursion
  ; totality    = totality
  }
