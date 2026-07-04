-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.SigOp.BuiltinProvider  (Plan 0.58 Phase 0)
--
-- The concrete, TOTAL provider for compiler-owned SigOps.
--
-- "Emitted ≠ owned": the compiler INVENTS (owns) only PURE optimization
-- SigOps — arith blocks and literals, all `Pure`+fits-in-reg. It also emits
-- effectful ops (`exit`, I/O), but those come from INTERPRETATION signatures
-- (Strata) and the interpretation owns their contract — below the trust line.
-- There are NO built-in effectful ops.
--
-- So the built-in provider is simply `close pure-prim-provider residual`:
--   * `pure-prim-provider` is effect-keyed (NOT name-keyed), so it returns
--     `just <real contract>` for EVERY `Pure`+fits-in-reg SigOp — no name gap.
--   * `residual` is the ONE named trust-line postulate for the open
--     `CanonicalName` tail (interpretation-owned + once-programmer ops).
--
-- ANTI-CHEAT (`compiler-owns-covered`): because compiler-owned ops are
-- effect-characterized, `pure-prim-provider` matches them BEFORE the residual —
-- definitionally. So the residual is provably unreachable for compiler output;
-- there is no name enumeration to forget.
------------------------------------------------------------------------

module Once.CCC.SigOp.BuiltinProvider where

open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _,_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; FitsInReg; fits-in-reg?)
open import Once.SigOp.Info using (SigOpInfo; effect; Pure)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SigOp.Contract using (module Def)
open import Once.CCC.SigOp.PureProvider using (module PureProviderDef)

module _ {FS : FrameSemantics} (program-bound : ℕ) where
  open Def {FS} program-bound using (Provider; PartialProvider; close; Contract)
  open PureProviderDef {FS} program-bound using (pure-prim-provider)

  -- The trust line. Reached ONLY by names outside the compiler's owned set:
  -- interpretation-owned effectful ops (`exit`, I/O — offline-proved) and
  -- once-programmer SigOps. Compiler-owned ops never reach here.
  postulate
    residual : Provider

  builtin-provider : Provider
  builtin-provider = close pure-prim-provider residual

  -- ANTI-CHEAT (definitional). A compiler-OWNED SigOp is `Pure`+fits-in-reg
  -- *concretely* (e.g. arith `block-info e` is literally `Pure Int`), so
  -- `fits-in-reg? Int` and `effect (block-info e)` REDUCE — and then
  -- `builtin-provider (block-info e)` reduces PAST the residual to the real
  -- contract by `refl`. So every concrete compiler mint site can assert its
  -- own coverage as a one-line `refl` at that site (where the codomain/effect
  -- are concrete). `exit`/I/O are interpretation-owned (not `Pure`) → correctly
  -- below the residual.
  --
  -- A *general* `compiler-owns-covered : Pure+fits ⇒ Is-just pure-prim-provider`
  -- would turn "a compiler op fell to the residual" into a type error at the
  -- abstract level, but requires exposing `pure-prim-provider`'s `with`-dispatch
  -- as a named helper of `(fits-in-reg? B , effect si)` (Agda won't reduce the
  -- internal `with` from outside). Deferred to the Phase-2/3 wiring, where the
  -- coverage is exercised on concrete ops anyway.
  --
  -- Sanity witness that the reduction works on a concrete shape lives at the
  -- arith mint site (Plan 0.58 Phase 3).
