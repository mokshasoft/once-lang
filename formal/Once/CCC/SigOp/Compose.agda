-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.SigOp.Compose
--
-- Provider composition (plan 0.2.4.1 Phase B).
--
-- The `Provider` type in `Once.CCC.SigOp.Contract` is a partial
-- function (returns `Maybe`) from SigOpInfos to contract proofs.
-- Multiple providers (IntLit family, external syscalls, user-imported
-- modules, …) are combined into a single composed provider via the
-- standard first-win monoid on partial functions:
--
--   (p <|> q) si = p si or-else q si
--
-- Composition is associative, so chains like
-- `intLit <|> syscalls <|> math <|> user-provider` make sense without
-- parenthesisation.  The left-most provider that recognizes a
-- given SigOp wins; downstream providers are only consulted on
-- `nothing`.
------------------------------------------------------------------------

module Once.CCC.SigOp.Compose where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SigOp.Contract using (module Def)

------------------------------------------------------------------------
-- Composition operator
------------------------------------------------------------------------

module _ {FS : FrameSemantics} (program-bound : ℕ) where
  open Def {FS} program-bound using (PartialProvider)

  -- | First-win composition over PARTIAL providers (the composable layer):
  -- try `p`; if `nothing`, fall through to `q`.
  infixr 5 _<|>_
  _<|>_ : PartialProvider → PartialProvider → PartialProvider
  (p <|> q) si with p si
  ... | just result = just result
  ... | nothing     = q si

  -- | The empty partial provider — recognises nothing. Identity for `_<|>_`.
  emptyProvider : PartialProvider
  emptyProvider _ = nothing

------------------------------------------------------------------------
-- ClaimedProvider: Provider + phantom prefix-set documenting coverage
--
-- Plan 0.20 Phase E (I-arith-7): wrapper that records *which*
-- SigOp name-prefixes a Provider claims to handle. Documentary
-- (Agda does not check that the inner Provider's `nothing` ↔ name
-- has-none-of-these-prefixes), but the composed type makes the
-- still-postulated coverage gaps visible at the entry point.
--
-- The strong-form refactor — `Provider` indexed by claims with a
-- wellformedness witness "returns `just` exactly when name has a
-- claimed prefix" — is option (a) of the type-level refactor
-- ladder; this lightweight version is its first rung.
--
-- Dispatcher consumes the unwrapped inner `Provider` via
-- `ClaimedProvider.provider`; the index is invisible to it.
------------------------------------------------------------------------

module _ {FS : FrameSemantics} (program-bound : ℕ) where
  open Def {FS} program-bound using (PartialProvider)

  record ClaimedProvider (claims : List String) : Set where
    constructor mk-claimed
    field
      provider : PartialProvider

  open ClaimedProvider public

  -- | The empty claimed provider — claims nothing, recognises nothing.
  empty-claimed : ClaimedProvider []
  empty-claimed = mk-claimed (emptyProvider {FS} program-bound)

  -- | Claimed-composition. The composed provider's claim is the
  -- *concatenation* of its parts' claims. Operationally identical
  -- to `_<|>_` on the inner Providers; only the index changes.
  infixr 5 _<|>'_
  _<|>'_ : ∀ {P Q : List String}
        → ClaimedProvider P → ClaimedProvider Q → ClaimedProvider (P ++ Q)
  p <|>' q =
    mk-claimed (_<|>_ {FS} program-bound (provider p) (provider q))
