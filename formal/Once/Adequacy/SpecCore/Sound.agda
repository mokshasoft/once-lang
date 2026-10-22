{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Sound — a compiler core program, as the Spec's,
-- does what the Spec says (plan 0.121 §3.5).
--
-- Over a well-formed Spec signature Σ whose declarations render to distinct
-- names, a compiler core program over Σ (`Core.Telescope`) IS a Spec program
-- (`programS`, plan 0.122). Run against a Spec
-- Interpretation `J` — the compiler's side through `SpecInterp.toImpl` — the
-- two have the same trace (`core-sound`): the definitions are related
-- (`Program.teleR`, given `Sig.sig-G`), the entry's conversion keeps them
-- related (`Conv.conv-R`), and related runs are observed alike
-- (`Observe.observe-R`, given `Sig.agree`).
------------------------------------------------------------------------

open import Data.List using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (_,_)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature; WellFormed; Decl; _∶_)
import Once.Spec.Observation as Obs
open import Once.Internal.Core.Decl using (toISig)
module Once.Adequacy.SpecCore.Sound
  (Σ : Signature) (wf : WellFormed Σ) (J : Obs.Interp Σ)
  (uniq : Unique (map (λ d → showCanonical (Decl.name d)) Σ))
  (fmt : TargetNum) where

open import Data.List using ([])
open import Data.Fin using (zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.Internal.Core.Telescope Σ as TL
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Spec.Core.Program Σ as SP
import Once.Spec.Domain Σ as SD
open import Once.Spec.Trace using (Tr; _≈ᵗ⟨_⟩_)
open import Once.Internal.Trace using (Interp)
open import Once.Denotation.TraceTr using (trT∞)
open import Once.Adequacy.SpecInterp using (toImpl; toInterp)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
import Once.Adequacy.SpecCore.Conv as Conv
import Once.Adequacy.SpecCore.Program as PG
import Once.Adequacy.SpecCore.Cases as Cases
open import Once.Adequacy.SpecCore.Observe Σ using (observe-R)
import Once.Adequacy.SpecCore.Sig Σ wf J uniq fmt as Sg

private
  ι : Interp
  ι = toInterp Σ wf J

------------------------------------------------------------------------
-- The program
------------------------------------------------------------------------

programS : TL.Program → SP.Program
programS = PG.programS Σ fmt wf

------------------------------------------------------------------------
-- The entry: related definitions, converted, run alike
------------------------------------------------------------------------

entry-R : ∀ {s} (S : SC.Defs s) {sc : SC.Schema} (e : SP.Entry sc) (v : TL.EntrySem sc)
          (v′ : (τ : ST.TySub (SC.Schema.arity sc) 0) → ST.Respects (SC.Schema.kinds sc) ST.∅ₖ τ
              → SD.⟦ SC.Schema.type sc ST.⟨ τ ⟩ ⟧ᵛ)
        → (∀ τ r → ValR (gr (SC.Schema.type sc ST.⟨ τ ⟩)) (v τ r) (v′ τ r))
        → T∞R (ValR g-unit) (TL.runEntry e v) (SP.runEntry e v′)
entry-R S (SP.entry p) v v′ rel = Conv.conv-R Σ S SP.noVars p (rel SP.noVars (λ ())) {tt} {tt} tt

------------------------------------------------------------------------
-- The program: the same trace
------------------------------------------------------------------------

core-sound : ∀ (P : TL.Program)
           → trT∞ ι [] (TL.runCore fmt P (toImpl Σ J wf)) ≈ᵗ⟨ _≡_ ⟩ SP.behaviour fmt (programS P) J
core-sound (TL.program {sig = S} defs d e) =
  observe-R ι (Obs.Interp.world J) Sg.agree
    (entry-R S e _ _ (λ τ r → PG.teleR Σ fmt (toImpl Σ J wf) (Obs.Interp.model J) Sg.sig-G defs d τ r))
