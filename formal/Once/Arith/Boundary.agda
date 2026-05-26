-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Boundary
--
-- Plan 0.20 Phase E — the `blockProvider`.
--
-- D-arith-5: every arith block surfaces to CCC as a `SigOp` and the
-- corresponding `SigOpContract.Provider` discharges its `Contract`.
-- This is that provider.
--
-- Architecture:
--   1. Block SigOps are recognised by name prefix (`"arith.block."`).
--   2. Their `B` is always `Int`.
--   3. The contract is the same shape as `add-int-proof`
--      (`Once.Arith.SigOp.Proofs.agda:137`) — a pure-primitive proof
--      via `mkPurePrimResult` using `arith-trace-correct` and
--      `arith-frontier-stable`.
--   4. So we factor a `block-int-proof` that works for *any*
--      `SigOpInfo A Int` and let the Provider call it after the
--      name + B = Int dispatch.
--
-- The Provider is parameterised by `FrameSemantics` and
-- `program-bound`, matching the `Once.CCC.Machine.Dispatcher`
-- interface.
------------------------------------------------------------------------

module Once.Arith.Boundary where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; [])
open import Data.String using (String)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Type using (Type; Int; fits-int)
open import Once.CCC.IR using (SigOp; AllocMode; Stack)
open import Once.CCC.SigOp.Info using (SigOpInfo; name)
open import Once.CCC.FrameSemantics using (FrameSemantics)

-- | Decidable equality on `Type`: lifted from `Once.TypeCheck.Elaborate`.
open import Once.TypeCheck.Elaborate using (_≟T_)

-- | The contract module.
open import Once.CCC.SigOp.Contract using (module Def)

-- | The pure-primitive proof template.
open import Once.CCC.SigOp.Helper using (module PrimHelper)

-- | The reusable trace + frontier-stable lemmas.
open import Once.Arith.SigOp.Proofs using (module ArithProofs)

------------------------------------------------------------------------
-- Name-prefix recognition
------------------------------------------------------------------------

-- | Test whether `s` starts with the literal "arith.block.".
--
-- Implementation note: stdlib (2.3) doesn't ship a `String.isPrefixOf`,
-- so we drop through `Data.List.Char` for the comparison.
is-block-name : String → Bool
is-block-name s = prefix-match (Data.String.toList "arith.block.") (Data.String.toList s)
  where
    open import Data.Char using (Char) renaming (_≟_ to _≟c_)
    open import Data.List using (List; []; _∷_)
    open import Data.String
    prefix-match : List Char → List Char → Bool
    prefix-match []       _        = true
    prefix-match (_ ∷ _)  []       = false
    prefix-match (c ∷ cs) (d ∷ ds) with c ≟c d
    ... | yes _ = prefix-match cs ds
    ... | no _  = false

------------------------------------------------------------------------
-- The Provider
------------------------------------------------------------------------

module ArithBlockProvider {FS : FrameSemantics} (program-bound : ℕ) where
  open Def {FS} program-bound using (Contract; Provider)
  open PrimHelper {FS} program-bound using (mkPurePrimResult)
  open ArithProofs {FS} program-bound
    using (arith-trace-correct; arith-frontier-stable)

  ------------------------------------------------------------------------
  -- block-int-proof: the polymorphic-in-A pure-primitive proof
  --
  -- For any SigOp whose return type is `Int`, the contract holds — the
  -- proof doesn't case-split on the body, only on the return-shape
  -- being a register-fittable primitive (`fits-int`).
  ------------------------------------------------------------------------

  block-int-proof : ∀ {A} (si : SigOpInfo A Int)
                  → Contract Stack (SigOp si)
  block-int-proof si mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mkPurePrimResult
      si
      Stack
      fits-int
      x
      input-loc
      s
      alloc
      input-before
      not-halted
      rdi-eq
      (arith-trace-correct input-loc s alloc not-halted rdi-eq)
      (λ s' loc' nh' rdi' slot-eq' →
         inj₂ (inj₁ (arith-frontier-stable s' loc' alloc nh' rdi' slot-eq')))

  ------------------------------------------------------------------------
  -- blockProvider: dispatch on name prefix + return type
  ------------------------------------------------------------------------

  blockProvider : Provider
  blockProvider {A} {B} si with is-block-name (name si) | B ≟T Int
  ... | true  | yes refl = just (Stack , block-int-proof si)
  ... | true  | no _     = nothing  -- block name but wrong return type
  ... | false | _        = nothing  -- not a block SigOp

  ------------------------------------------------------------------------
  -- Claim manifest (Plan 0.20 Phase E, I-arith-7 light)
  --
  -- The phantom prefix-list documents that `blockProvider` covers
  -- all SigOps whose name starts with `"arith.block."`. Visible at
  -- the EntryPointCCC level when composed via `_<|>'_`.
  ------------------------------------------------------------------------

  open import Once.CCC.SigOp.Compose using (ClaimedProvider; mk-claimed)

  blockClaims : List String
  blockClaims = "arith.block." ∷ []

  blockClaimed : ClaimedProvider {FS} program-bound blockClaims
  blockClaimed = mk-claimed blockProvider
