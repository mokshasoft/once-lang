-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.BlockValueSemM  (Plan 0.54 rung B / B2.3)
--
-- The abstract arith machine's value result, RESTATED in `block-semM` form —
-- the shape the concrete simulation (B2.3 pieces 1-4) connects to.
--
-- `block-correct` (Backend.Correct, at bits = 64) gives the abstract machine's
-- output as `eval-arith-W` (the ℤ-input evaluator); `eval≡semM` (BlockSemBridge,
-- piece 5) bridges that to `block-semM` over the Word-input tree (`toWord env`).
-- Composed: the abstract machine computes exactly `block-semM (toWord env)` —
-- which is what rung A's flat machine computes (`pure-sigop-output = semM`) and
-- what the concrete `val` must reproduce. So this is the ABSTRACT-SIDE value
-- target of the concrete↔abstract simulation.
------------------------------------------------------------------------

module Once.Arith.Backend.BlockValueSemM where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong)

open import Once.Arith.Machine.Shape using (InputShape; ⟦_⟧S)
-- PLAN 0.75 F4: the abstract-machine compile path is pinned at `NInt`, and
-- that restriction is STATED rather than assumed. Its instruction set
-- (`add-rrr`, `div-rrr`, …) is integer-register shaped, so a float block has
-- no lowering here yet; saying so in the type means the gate sees the gap
-- instead of a float tree silently taking the integer path.
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Machine.AbsState using (init; output-of)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.Compile using (compile-abs)
import Once.Arith.Backend.Correct as Correct
open import Once.Arith.SigOp.Block using (block-semM)
open import Once.Arith.SigOp.BlockSemBridge using (toWord; eval≡semM)
open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- PLAN 0.74 J5: `open Correct 64` was a THIRD bake of the same 64, and this
-- module is where the abstract machine's output is compared with the block's
-- meaning. Baking the width on both sides made the comparison compare a
-- 64-bit machine with a 64-bit meaning on a 32-bit target.
module _ (tn : TargetNum) where

  open Correct (int-bits tn) (float-format tn) using (exec-xprog; block-correct)

  -- The abstract machine's output = `block-semM` of the Word-image of the input.
  block-value-semM : ∀ {sh} (e : MArithIR sh NInt) (env : ⟦ sh ⟧S)
                   → output-of (exec-xprog (emit-program (compile-abs e)) (init env))
                       ≡ just (block-semM e tn (toWord tn sh env))
  block-value-semM e env = trans (block-correct e env) (cong just (eval≡semM tn e env))
