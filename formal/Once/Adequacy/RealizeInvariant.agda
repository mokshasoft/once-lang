-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RealizeInvariant — the `realize-invariant` postulate (A4),
-- factored into its own base module (Plan 0.55) so both `MainRealizeAgrees`
-- (which composes it) and `MtIndep` (`mt-den-indep`, which uses it) can import
-- it WITHOUT an import cycle. The postulate itself is UNCHANGED (moved verbatim
-- from `MainRealizeAgrees`).
--
-- (B) realize denotational-invariance — ANY two `⊢ᶜ` derivations of the SAME
--     judgment realize to denotationally-equal terms.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.RealizeInvariant (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Type)
import Once.Denotation.SourceDenote as SD
open import Once.Surface.Syntax using (Usage; ⟦_⟧ᶜ)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Denotation.Realize using (realize)

postulate
  realize-invariant :
    ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type} {Ψ : Usage (NamedCtx.size ctx)}
      (d₁ d₂ : ctx ⊢ᶜ e ∶ A ⨾ Ψ) (dγ : ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜ ⟧ᴰ) (k : ℕ)
    → SD.⟦ realize d₁ ⟧ˢ fmt dγ k ≡ SD.⟦ realize d₂ ⟧ˢ fmt dγ k
