-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CanonPolyTransport — the POLY-CONTEXT transport (Plan 0.51).
--
-- `canonModule` canonicalizes poly-DEF bodies too, so `ModuleTyped mR` lives at
-- the canonExpr'd poly context `canonPolysCtx b p`, not `p`. This module:
--   * foundational commutes (`lookupPoly-canon`, `removePoly-canon`),
--   * `polys-transport-{ᵢ,ᵐ,ᶜ}`: a `⊢ᶜ` derivation at a poly context `p` lifts to
--     the canonExpr'd context `canonPolysCtx b p` (the expression is UNCHANGED;
--     only the t-var-poly-instantiate body and the m-cata sub-context read polys,
--     and they re-derive via `canon-pres-ᶜ` + recursion).
------------------------------------------------------------------------

module Once.Adequacy.CanonPolyTransport where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.String.Properties as StrProp using ()
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Type; PolyType)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Parser.Module.Resolve using (canonExpr; elemStr)
open import Once.TypeCheck.Classify using (PolyCtx; lookupPoly; removePoly)

------------------------------------------------------------------------
-- canonExpr a poly context's bodies.
------------------------------------------------------------------------

canonPolysCtx : List String → PolyCtx → PolyCtx
canonPolysCtx b [] = []
canonPolysCtx b ((n , s , body) ∷ rest) = (n , s , canonExpr b [] [] body) ∷ canonPolysCtx b rest

canon-entry : List String → (PolyType × RawExpr) → (PolyType × RawExpr)
canon-entry b (s , body) = (s , canonExpr b [] [] body)

------------------------------------------------------------------------
-- lookupPoly / removePoly commute with canonPolysCtx.
------------------------------------------------------------------------

lookupPoly-canon : ∀ (b : List String) (p : PolyCtx) (x : String)
  → lookupPoly (canonPolysCtx b p) x ≡ mapMaybe (canon-entry b) (lookupPoly p x)
lookupPoly-canon b [] x = refl
lookupPoly-canon b ((n , s , body) ∷ rest) x with StrProp._≟_ n x
... | yes _ = refl
... | no  _ = lookupPoly-canon b rest x

removePoly-canon : ∀ (b : List String) (x : String) (p : PolyCtx)
  → canonPolysCtx b (removePoly x p) ≡ removePoly x (canonPolysCtx b p)
removePoly-canon b x [] = refl
removePoly-canon b x ((n , s , body) ∷ rest) with StrProp._≟_ n x
... | yes _ = refl
... | no  _ = cong ((n , s , canonExpr b [] [] body) ∷_) (removePoly-canon b x rest)

------------------------------------------------------------------------
-- A poly name found in `p` is found in `canonPolysCtx b p` (names preserved).
------------------------------------------------------------------------

lookupPoly-canon-just : ∀ (b : List String) (p : PolyCtx) (x : String) {s body}
  → lookupPoly p x ≡ just (s , body)
  → lookupPoly (canonPolysCtx b p) x ≡ just (s , canonExpr b [] [] body)
lookupPoly-canon-just b p x {s} {body} lp
  rewrite lookupPoly-canon b p x rewrite lp = refl
