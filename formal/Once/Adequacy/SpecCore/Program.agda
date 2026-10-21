{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Program — the compiler's core telescope as the
-- Spec's, and their definitions environments related (plan 0.121 §3.5).
--
-- Each definition of the compiler's telescope (`Lang.Core.Telescope`) becomes
-- the Spec's definition of the translated schema, body and typing (`teleS`).
-- Their meanings, built definition by definition, are related at every pair of
-- related instances (`teleR`): each body by the fundamental lemma, in the
-- related environment of its prefix — given that the signature's declarations
-- are (`SigG`, the implementation against the Spec's model).
------------------------------------------------------------------------

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Internal.Contract using (ISig; Impl)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Signature using (Signature; _∶_; WellFormed)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Adequacy.SpecCore.Poly using (declS)

module Once.Adequacy.SpecCore.Program
  {Fs : ISig} (Σ : Signature)
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
  (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Data.Fin using (zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import Once.Internal.Type.WellFormed as LW
import Once.Internal.Type.Honest as LH
import Once.Spec.Type as ST
import Once.Internal.Core.PolyTy as LP
import Once.Internal.Core.Telescope as TL
import Once.Internal.Core.Meaning as GM
import Once.Internal.GradedOps as LOps
import Once.Spec.Core.Syntax as SC
import Once.Spec.Core.Program Σ as SP
import Once.Spec.Core.Meaning as SM
open import Once.Spec.Observation Σ using (Model)
open import Once.Adequacy.SpecCore.Schema using (schS; defsS)
open import Once.Adequacy.SpecCore.Poly using (module Translate; module SubS)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
import Once.Adequacy.SpecCore.Cases as Cases

------------------------------------------------------------------------
-- The telescope
------------------------------------------------------------------------

teleS : ∀ {s} {S : LP.Sig Fs s} → TL.Tele S → SP.Tele (defsS S)
teleS TL.[]                         = SP.[]
teleS (TL.def {S = S} tl sc body D) =
  SP.def (teleS tl) (schS sc) (Translate.ptmS S Σ sigop-S body) (Translate.trD S Σ sigop-S D)

------------------------------------------------------------------------
-- The program
------------------------------------------------------------------------

-- `main`'s conversion, at the Spec's types.
entryS : ∀ {s} (S : LP.Sig Fs s) d → TL.MainEntry (S LP.!! d) → SP.Entry (defsS S SC.!! d)
entryS (S LP.▷ sc) zero    (TL.entry p) = SP.entry (SubS.subS (S LP.▷ sc) p)
entryS (S LP.▷ sc) (suc d) e            = entryS S d e

-- A compiler core program, as the Spec's.
programS : WellFormed Σ → TL.Program Fs → SP.Program
programS wf (TL.program {sig = S} defs d e) = record
  { wf     = wf
  ; defs   = teleS defs
  ; main   = d
  ; isMain = entryS S d e
  }

------------------------------------------------------------------------
-- The declarations, related once for every prefix
------------------------------------------------------------------------

-- An implementation and a model agree on every declaration of the signature.
SigG : Impl Fs → Model → Set
SigG I mo = ∀ {s₀} (S₀ : SC.Defs s₀) {m} (σ′ : ST.TySub m 0) {c A} (k : LW.IsConcrete A) (h : LH.HonestFFI A) (rf : LW.RigidFree A)
            (wn : WordName c) (mem : (showCanonical c , A) ∈ Fs) (gs : GR A (Once.Spec.Signature.⌜_⌝ᵈ (declS A) ST.⟨ σ′ ⟩))
          → ValR gs (LOps.sigOpRefᵛ fmt Fs I c k mem) (SM.sigopᵛ Σ fmt S₀ σ′ c (declS A) (sigop-S wn mem) mo)

------------------------------------------------------------------------
-- The definitions environments
------------------------------------------------------------------------

-- (the Spec's environment keeps the model it is given)
model-tele : ∀ (mo : Model) {s} {S : SC.Defs s} (tl : SP.Tele S) → SM.DefSem.model (SP.teleSem fmt mo tl) ≡ mo
model-tele mo SP.[]                = refl
model-tele mo (SP.def tl sc body D) = refl

module _ (I : Impl Fs) (mo : Model) (sg : SigG I mo) where

  teleR : ∀ {s} {S : LP.Sig Fs s} (tl : TL.Tele S)
        → Cases.DefsR S Σ sigop-S fmt (TL.teleSem fmt I tl) (SP.teleSem fmt mo (teleS tl))
  teleR TL.[] ()
  teleR (TL.def {S = S} tl sc body D) zero τ r τ′ r′ i =
    Cases.fundamental S Σ sigop-S fmt (TL.teleSem fmt I tl) (SP.teleSem fmt mo (teleS tl)) (teleR tl)
                      (λ σ′ k h rf wn mem gs → subst (λ mo′ → ValR gs _ (SM.sigopᵛ Σ fmt _ σ′ _ (declS _) (sigop-S wn mem) mo′))
                                                  (sym (model-tele mo (teleS tl))) (sg _ σ′ k h rf wn mem gs)) D r r′ i tt
  teleR (TL.def tl sc body D) (suc d) τ r τ′ r′ i = teleR tl d τ r τ′ r′ i
