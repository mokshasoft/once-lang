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
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Machine.AbsState using (init; output-of)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.Compile using (compile-abs)
import Once.Arith.Backend.Correct as Correct
open Correct 64 using (exec-xprog; block-correct)
open import Once.Arith.SigOp.Block using (block-semM)
open import Once.Arith.SigOp.BlockSemBridge using (toWord; eval≡semM)

-- The abstract machine's output = `block-semM` of the Word-image of the input.
block-value-semM : ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S)
                 → output-of (exec-xprog (emit-program (compile-abs e)) (init env))
                     ≡ just (block-semM e (toWord sh env))
block-value-semM e env = trans (block-correct e env) (cong just (eval≡semM e env))
