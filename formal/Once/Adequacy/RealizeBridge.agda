-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.RealizeBridge — the AGREEMENT BRIDGE (Plan 0.49 Phase 2 /
-- route 2). A PROOF (not semantics): the real `checkElab` algorithm agrees,
-- denotationally, with the REFERENCE elaboration `realize` (the spec).
--
-- This is the ONLY module allowed to import BOTH the elaborator (`checkElab`)
-- and the reference (`realize`) — it is where they meet. Discharging
-- `realize-agrees` is what FORCES `checkElab`'s term-choice against the
-- denotation (`SD`), closing the last cancellation (row-3). It is NOT trivial:
-- `realize (check-sound … cc)` is the CANONICAL term read off the term-free
-- derivation (built from the raw program), not a copy of `checkElab`'s `se`.
--
-- Companion to `Once.Adequacy.SourceFaithful.faithful` (which relates the OTHER
-- elaborator stage `elaborate : SExpr → IR` to `SD`). Together they force the
-- whole front-end against the one denotation.
------------------------------------------------------------------------

module Once.Adequacy.RealizeBridge where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.Surface.Syntax using (Expr; Usage; ⟦_⟧ᶜ)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
import Once.Denotation.SourceDenote as SD

-- The two things that meet here (the no-cheat boundary is in `Realize`, not
-- this module — this module is the proof, allowed to see both):
open import Once.Denotation.Realize using (realize)
open import Once.TypeCheck.Elaborate using (checkElab; success)
open import Once.TypeCheck.Soundness using (check-sound)

-- THE agreement (postulated top-down; discharged later by induction on the
-- derivation). `se` = `checkElab`'s term; `realize (check-sound … cc)` = the
-- reference term read off the (term-free, raw-built) derivation. Pointwise in
-- the env `dγ` and depth `k`, like `faithful`.
postulate
  realize-agrees : ∀ (ctx : NamedCtx) (e : RawExpr) (A : Type)
    {Ψ : Usage (NamedCtx.size ctx)}
    {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
    (cc : checkElab ctx e A ≡ success Ψ se d f)
    (dγ : ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜ ⟧ᴰ) (k : ℕ) →
    SD.⟦ se ⟧ˢ dγ k ≡ SD.⟦ realize (check-sound ctx e A cc) ⟧ˢ dγ k
