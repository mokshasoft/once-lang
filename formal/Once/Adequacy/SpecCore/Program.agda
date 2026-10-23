{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Program — the compiler's core program as the
-- Spec's, and their definitions environments related (plan 0.121 §3.5; plan
-- 0.122: the compiler's telescope IS the Spec's).
--
-- A compiler core program (`Core.Telescope`) is a Spec program with a
-- well-formedness proof of its signature (`programS`). The two meanings of its
-- telescope, built definition by definition, are related at every instance
-- (`teleR`): each body by the fundamental lemma, in the related environment
-- of its prefix, both read in one model.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; WellFormed)
open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecCore.Program (Σ : Signature) (fmt : TargetNum) where

open import Data.Unit using (tt)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

import Once.Spec.Type as ST
import Once.Internal.Core.Telescope Σ as TL
import Once.Spec.Core.Syntax as SC
open SC.Schema using (type)
import Once.Spec.Core.Program Σ as SP
import Once.Spec.Domain Σ as SD
import Once.Internal.Core.TySubstZero as TZ
open import Once.Spec.Observation Σ using (Model)
import Once.Spec.Core.Meaning as SM
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
import Once.Adequacy.SpecCore.Cases as Cases

------------------------------------------------------------------------
-- The program
------------------------------------------------------------------------

-- A compiler core program, as the Spec's.
programS : WellFormed Σ → TL.Program → SP.Program
programS wf (TL.program defs d e) = record
  { wf     = wf
  ; defs   = defs
  ; main   = d
  ; isMain = e
  }

------------------------------------------------------------------------
-- The definitions environments
------------------------------------------------------------------------

-- (the Spec's environment keeps the model it is given)
model-tele : ∀ (mo : Model) {s} {S : SC.Defs s} (tl : SP.Tele S) → SM.DefSem.model (SP.teleSem fmt mo tl) ≡ mo
model-tele mo SP.[]                 = refl
model-tele mo (SP.def tl sc body D) = refl

private
  -- a value, retyped on the instance's side
  ValR-substˡ : ∀ {X X′ Y} (e : X ≡ X′) (g : GR X Y) (g′ : GR X′ Y) {x y}
              → ValR g x y → ValR g′ (Relation.Binary.PropositionalEquality.subst SD.⟦_⟧ᵛ e x) y
  ValR-substˡ refl g g′ r = Relation.Binary.PropositionalEquality.subst (λ h → ValR h _ _) (GR-unique g g′) r
    where import Relation.Binary.PropositionalEquality

module _ (mo : Model) where

  teleR : ∀ {s} {S : SC.Defs s} (tl : SP.Tele S)
        → Cases.DefsR Σ S fmt (TL.teleSem fmt mo tl) (SP.teleSem fmt mo tl)
  teleR SP.[] ()
  teleR (SP.def {S = S} tl sc body D) zero τ r =
    ValR-substˡ (TZ.⟨⟩-0 Σ S SP.noVars (type sc ST.⟨ τ ⟩)) (g⟨⟩ SP.noVars _) (gr _)
      (Cases.fundamental Σ S fmt (TL.teleSem fmt mo tl) (SP.teleSem fmt mo tl) (teleR tl)
         (trans (TL.teleSem-model fmt mo tl) (sym (model-tele mo tl)))
         D τ r pr-pure tt)
  teleR (SP.def tl sc body D) (suc d) τ r = teleR tl d τ r
