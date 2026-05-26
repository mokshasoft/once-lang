-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Machine.Compile
--
-- Plan 0.20 Phase C — `compile-abs : MArithIR → [AbstractInstr]`.
--
-- Stack-machine compile: every binary op spills its left child to a
-- fresh scratch slot, computes the right child into reg 0, reloads
-- the left into reg 1, and combines into reg 0. Registers used:
-- reg 0 (accumulator) and reg 1 (reload target); n-regs = 2.
--
-- Scratch growth: `aadd a b` at depth `d` uses scratch slot `d` and
-- recurses into `b` at depth `d+1`. The overall budget `required-
-- scratch e` is bounded by the deepest binary-op nest in `e`.
--
-- Phase F (Sethi–Ullman) replaces the depth-based scratch budget
-- with a smarter allocation that reorders children when possible.
-- That's a pure refactor of `compile-go`'s right-hand sides; nothing
-- downstream depends on the current depth-naive strategy.
------------------------------------------------------------------------

module Once.Arith.Machine.Compile where

open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Arith.Machine.AbsState
  using (ArithAbsState; InputShape; ⟦_⟧S; init; output-of)
open import Once.Arith.Machine.AbsInstr
  using (AbstractInstr; load-input; load-imm; add-rrr; sub-rrr; mul-rrr;
         neg-rr; spill; reload; move-to-out; run-abstract)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; ainput; aadd; asub; amul; aneg; eval-arith)

------------------------------------------------------------------------
-- Register / scratch budget
------------------------------------------------------------------------

-- | Two abstract regs: reg 0 = accumulator, reg 1 = reload target.
n-regs : ℕ
n-regs = 2

-- | Scratch budget = maximum recursion depth of binary nodes.
required-scratch : ∀ {sh} → MArithIR sh → ℕ
required-scratch (alit _)     = 0
required-scratch (ainput _)   = 0
required-scratch (aadd a b)   = required-scratch a ⊔ suc (required-scratch b)
required-scratch (asub a b)   = required-scratch a ⊔ suc (required-scratch b)
required-scratch (amul a b)   = required-scratch a ⊔ suc (required-scratch b)
required-scratch (aneg a)     = required-scratch a

------------------------------------------------------------------------
-- compile-abs (operational)
------------------------------------------------------------------------

-- | Compile `e` at scratch-depth `d`. Postcondition (proved by
-- `Phase C validity`): running the result leaves the value of `e`
-- in reg 0; scratch slots `< d` are preserved; reg 1 may be
-- clobbered.
compile-go : ∀ {sh} → ℕ → MArithIR sh → List AbstractInstr
compile-go d (alit z)     = load-imm z 0 ∷ []
compile-go d (ainput p)   = load-input p 0 ∷ []
compile-go d (aadd a b)   =
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ add-rrr 0 1 0 ∷ [])
compile-go d (asub a b)   =
  -- After: reg 0 = (reg 1) - (reg 0) = a - b
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ sub-rrr 0 1 0 ∷ [])
compile-go d (amul a b)   =
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ mul-rrr 0 1 0 ∷ [])
compile-go d (aneg a)     =
  compile-go d a ++ (neg-rr 0 0 ∷ [])

-- | Top-level compile: walk the tree, then move reg 0 to the output.
compile-abs : ∀ {sh} → MArithIR sh → List AbstractInstr
compile-abs e = compile-go 0 e ++ (move-to-out 0 ∷ [])

------------------------------------------------------------------------
-- Validity (statement; proof postulated for Phase C-discharge follow-up)
------------------------------------------------------------------------

-- The proof is a structural induction on `MArithIR` with the
-- strengthened invariant
--
--   ∀ d e s.
--     let s' = run-abstract (compile-go d e) s
--     in (regs s' [ 0 ]) ≡ just (eval-arith e (input s))
--     ∧ (∀ i < d, scratch s' [ i ] ≡ scratch s [ i ])
--
-- The arith ops in the IH propagate via the `bin-op` Maybe-lift's
-- `just/just` case, since both children's IHs give `just`. The
-- scratch-preservation half is required so that `aadd a b`'s
-- `reload d 1` after compiling `b` actually finds the spilled value
-- of `a` (compile-go d a put the value in reg 0; spill 0 d moved
-- it to scratch[d]; compile-go (suc d) b ran at depth ≥ d+1 so
-- scratch[d] is preserved).
--
-- Discharge ~150 LOC: the binary-op induction step needs the
-- IH for `b` to give a state in which (regs ... [ 0 ]) holds the
-- value of `b`, then chain through `reload d 1` and `add-rrr`.
-- Per [[scaffold-then-discharge]], the postulate ships now and the
-- structural proof lands in a focused follow-up.

postulate
  abs-validity :
    ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) →
    output-of (run-abstract (compile-abs e) (init env)) ≡ just (eval-arith e env)
