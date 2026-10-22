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
-- of its prefix — given that the signature's declarations are (`SigG`, the
-- implementation against the Spec's model).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; _∶_; WellFormed; DeclType)
open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecCore.Program (Σ : Signature) (fmt : TargetNum) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Fin using (zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import Once.Spec.Type as ST
open import Once.Spec.Signature using (⌜_⌝ᵈ)
open import Once.Internal.Contract using (Impl)
open import Once.Internal.Core.Decl using (toISig; ∈-toISig; ⌜⌝ᵈ-concrete)
import Once.Internal.Core.Telescope Σ as TL
import Once.Internal.GradedOps as LOps
import Once.Spec.Core.Syntax as SC
import Once.Spec.Core.Program Σ as SP
import Once.Spec.Core.Meaning as SM
open import Once.Spec.Observation Σ using (Model)
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
-- The declarations, related once for every prefix
------------------------------------------------------------------------

-- An implementation and a model agree on every declaration of the signature.
SigG : Impl (toISig Σ) → Model → Set
SigG I mo = ∀ {s₀} (S₀ : SC.Defs s₀) {m} (σ : ST.TySub m 0) {c} {t : DeclType} (mem : (c ∶ t) ∈ Σ)
          → ValR (Cases.gS Σ S₀ fmt σ t)
                 (LOps.sigOpRefᵛ {A = ⌜ t ⌝ᵈ} fmt (toISig Σ) I c (⌜⌝ᵈ-concrete t) (∈-toISig mem))
                 (SM.sigopᵛ Σ fmt S₀ σ c t mem mo)

------------------------------------------------------------------------
-- The definitions environments
------------------------------------------------------------------------

-- (the Spec's environment keeps the model it is given)
model-tele : ∀ (mo : Model) {s} {S : SC.Defs s} (tl : SP.Tele S) → SM.DefSem.model (SP.teleSem fmt mo tl) ≡ mo
model-tele mo SP.[]                 = refl
model-tele mo (SP.def tl sc body D) = refl

module _ (I : Impl (toISig Σ)) (mo : Model) (sg : SigG I mo) where

  teleR : ∀ {s} {S : SC.Defs s} (tl : SP.Tele S)
        → Cases.DefsR Σ S fmt (TL.teleSem fmt I tl) (SP.teleSem fmt mo tl)
  teleR SP.[] ()
  teleR (SP.def {S = S} tl sc body D) zero τ r =
    Cases.fundamental Σ S fmt (TL.teleSem fmt I tl) (SP.teleSem fmt mo tl) (teleR tl)
      (λ σ {c} {t} mem → subst (λ mo′ → ValR (Cases.gS Σ S fmt σ t)
                                              (LOps.sigOpRefᵛ {A = ⌜ t ⌝ᵈ} fmt (toISig Σ) I c (⌜⌝ᵈ-concrete t) (∈-toISig mem))
                                              (SM.sigopᵛ Σ fmt S σ c t mem mo′))
                       (sym (model-tele mo tl)) (sg S σ mem))
      D τ r ur-[] pr-pure tt
  teleR (SP.def tl sc body D) (suc d) τ r = teleR tl d τ r
