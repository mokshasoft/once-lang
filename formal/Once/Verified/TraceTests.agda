-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.TraceTests — non-vacuity / regression guards for the
-- trace machinery (Plan 0.24, Phase F).
--
-- These are typechecked `refl` assertions: Agda *computes* `obs` /
-- `exitCodeOf` on a concrete IR and confirms the result. They guard
-- against the trace denotation silently going degenerate (e.g. always
-- producing an empty trace or `nothing`) — something the bridge proofs
-- (`obs ≈ concreteTrace`) do NOT catch, since they prove a *relation*,
-- not that `obs` computes anything in particular. Keep these in the
-- checked set; a regression breaks the `refl`.
--
-- (The full `⟦ src ⟧ ≡ just 13` end-to-end through the front-end
-- `sourceToIR` is left to the extracted Haskell test — normalizing the
-- whole elaborator at typecheck time is impractical. These check the
-- new Phase-A′/B machinery directly.)
------------------------------------------------------------------------

module Once.Verified.TraceTests where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Int; Unit; fits-int)
open import Once.CCC.IR using (IR; _∘_; const; SigOp)
open import Once.CCC.SigOp.Info using (SigOpInfo; mk-info)
open import Once.Verified.Trace using (exitCodeOf)
open import Once.Verified.TraceDenote using (obs)

-- A synthetic `linux.exit : Int → Unit` SigOp (effect ignores its arg).
exitInfo : SigOpInfo Int Unit
exitInfo = mk-info "linux.exit" (λ _ → tt) (λ _ → tt)

-- "exit 13" as a tiny `IR Unit Unit`: feed the constant 13 to linux.exit.
testIR : IR Unit Unit
testIR = SigOp exitInfo ∘ const fits-int (+ 13) 13

-- Non-vacuity: `obs` actually traces the program (a `linux.exit` event
-- carrying 13), and `exitCodeOf` recovers 13.
obs-exit-13 : exitCodeOf (proj₁ (obs 0 testIR tt)) ≡ just 13
obs-exit-13 = refl
