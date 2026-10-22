{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Sound — a compiler core program, as the Spec's,
-- does what the Spec says (plan 0.121 §3.5).
--
-- Over a well-formed Spec signature Σ whose declarations render to distinct
-- names, a compiler core program against `toISig Σ` (`Lang.Core.Telescope`)
-- becomes a Spec program (`programS`): its telescope translated (`teleS`),
-- its entry the same conversion (`entryS`). Run against a Spec
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
open import Once.Adequacy.SpecCore.Poly using (declS)

module Once.Adequacy.SpecCore.Sound
  (Σ : Signature) (wf : WellFormed Σ) (J : Obs.Interp Σ)
  (uniq : Unique (map (λ d → showCanonical (Decl.name d)) Σ))
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ toISig Σ → (c ∶ declS A) ∈ Σ)
  (fmt : TargetNum) where

open import Data.List using ([])
open import Data.Fin using (zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.Internal.Core.PolyTy as LP
import Once.Internal.Core.Telescope as TL
import Once.Internal.Core.Meaning as GM
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Spec.Core.Program Σ as SP
import Once.Spec.Core.Meaning as SM
import Once.Spec.Domain Σ as SD
open import Once.Spec.Trace using (Tr; _≈ᵗ⟨_⟩_)
open import Once.Internal.Trace using (Interp)
open import Once.Denotation.TraceTr using (trT∞)
open import Once.Adequacy.SpecInterp using (toImpl; toInterp)
open import Once.Adequacy.SpecCore.Schema using (defsS)
open import Once.Adequacy.SpecCore.Poly using (module SubS)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
import Once.Adequacy.SpecCore.Conv as Conv
import Once.Adequacy.SpecCore.Program as PG
open import Once.Adequacy.SpecCore.Observe Σ using (observe-R)
import Once.Adequacy.SpecCore.Sig Σ wf J uniq fmt as Sg

private
  ι : Interp
  ι = toInterp Σ wf J

------------------------------------------------------------------------
-- The program
------------------------------------------------------------------------

-- `main`'s conversion, at the Spec's types.
open PG Σ sigop-S fmt using (entryS)

programS : TL.Program (toISig Σ) → SP.Program
programS = PG.programS Σ sigop-S fmt wf

------------------------------------------------------------------------
-- The entry: related definitions, converted, run alike
------------------------------------------------------------------------

entry-R : ∀ {s} (S : LP.Sig (toISig Σ) s) d (e : TL.MainEntry (S LP.!! d)) (v : TL.EntrySem (S LP.!! d))
          (v′ : (τ : ST.TySub (SC.Schema.arity (defsS S SC.!! d)) 0) → ST.Respects (SC.Schema.kinds (defsS S SC.!! d)) ST.∅ₖ τ
              → SD.⟦ SC.Schema.type (defsS S SC.!! d) ST.⟨ τ ⟩ ⟧ᵛ)
        → (∀ τ r τ′ r′ (i : InstD S d τ τ′) → ValR (GR-def S d i) (v τ r) (v′ τ′ r′))
        → T∞R (ValR g-unit) (TL.runEntry e v) (SP.runEntry (entryS S d e) v′)
entry-R (S LP.▷ sc) zero (TL.entry p) v v′ rel =
  Conv.conv-R (S LP.▷ sc) Σ p g₀ (rel TL.noVars TL.noResp SP.noVars (λ ()) g₀) {tt} {tt} tt
  where
    g₀ : InstG TL.noVars SP.noVars
    g₀ ()
entry-R (S LP.▷ sc) (suc d) e v v′ rel = entry-R S d e v v′ rel

------------------------------------------------------------------------
-- The program: the same trace
------------------------------------------------------------------------

core-sound : ∀ (P : TL.Program (toISig Σ))
           → trT∞ ι [] (TL.runCore fmt P (toImpl Σ J wf)) ≈ᵗ⟨ _≡_ ⟩ SP.behaviour fmt (programS P) J
core-sound (TL.program {sig = S} defs d e) =
  observe-R ι (Obs.Interp.world J) Sg.agree
    (entry-R S d e _ _ (λ τ r τ′ r′ i →
       PG.teleR Σ sigop-S fmt (toImpl Σ J wf) (Obs.Interp.model J) (Sg.sig-G sigop-S) defs d τ r τ′ r′ i))
