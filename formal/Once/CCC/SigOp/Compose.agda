-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.SigOp.Compose
--
-- Provider composition (plan 0.2.4.1 Phase B).
--
-- The `Provider` type in `Once.CCC.SigOp.Contract` is a partial
-- function (returns `Maybe`) from SigOpInfos to contract proofs.
-- Multiple providers (IntLit family, Linux syscalls, user-imported
-- modules, …) are combined into a single composed provider via the
-- standard first-win monoid on partial functions:
--
--   (p <|> q) si = p si or-else q si
--
-- Composition is associative, so chains like
-- `intLit <|> linux <|> math <|> user-provider` make sense without
-- parenthesisation.  The left-most provider that recognizes a
-- given SigOp wins; downstream providers are only consulted on
-- `nothing`.
------------------------------------------------------------------------

module Once.CCC.SigOp.Compose where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SigOp.Contract using (module Def)

------------------------------------------------------------------------
-- Composition operator
------------------------------------------------------------------------

module _ {FS : FrameSemantics} (program-bound : ℕ) where
  open Def {FS} program-bound using (Provider)

  -- | First-win composition: try `p` first; if it returns `nothing`,
  -- fall through to `q`.
  infixr 5 _<|>_
  _<|>_ : Provider → Provider → Provider
  (p <|> q) si with p si
  ... | just result = just result
  ... | nothing     = q si

  -- | The empty provider — recognizes nothing. Identity element for
  -- `_<|>_`: `p <|> emptyProvider ≡ p`.
  emptyProvider : Provider
  emptyProvider _ = nothing
