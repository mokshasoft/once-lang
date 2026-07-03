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
-- This module is WIDTH-AGNOSTIC (it produces `AbstractInstr`, no word
-- semantics). The width-parametric correctness proof lives in
-- `Once.Arith.Machine.CompileCorrect (bits)`.
------------------------------------------------------------------------

module Once.Arith.Machine.Compile where

open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; +_; -[1+_])

open import Once.Arith.Machine.AbsInstr
  using (AbstractInstr; load-input; load-imm; add-rrr; sub-rrr; mul-rrr;
         div-rrr; rem-rrr; div-safe-rrr; rem-safe-rrr; neg-rr; spill; reload;
         move-to-out)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; ainput; aadd; asub; amul; adiv; amod; aneg)

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
required-scratch (adiv a b)   = required-scratch a ⊔ suc (required-scratch b)
required-scratch (amod a b)   = required-scratch a ⊔ suc (required-scratch b)
required-scratch (aneg a)     = required-scratch a

------------------------------------------------------------------------
-- Division-guard elision (Part B): safe-literal divisor detection
--
-- A literal divisor `k` is "safe" iff it can NEVER trigger x86 `idiv`'s
-- #DE fault — i.e. `k ≠ 0` (div-by-zero) AND `k ≠ −1` (INT_MIN/−1
-- overflow). Both cases are the ONLY inputs on which the guarded emit's
-- test/cmp branches ever fire; for a safe literal they are dead, so the
-- backend may emit a bare `idiv`. This is a purely SYNTACTIC decision on
-- the ℤ literal (`+ 0` and `-[1+ 0 ]` are the excluded canonical forms).
------------------------------------------------------------------------

safe-lit? : ℤ → Bool
safe-lit? (+ 0)          = false   -- 0     : div-by-zero
safe-lit? (+ (suc _))    = true    -- ≥ 1
safe-lit? (-[1+ 0 ])     = false   -- −1    : INT_MIN/−1 overflow
safe-lit? (-[1+ suc _ ]) = true    -- ≤ −2

safe-divisor? : ∀ {sh} → MArithIR sh → Bool
safe-divisor? (alit k) = safe-lit? k
safe-divisor? _        = false     -- non-literal divisor: keep the guard

-- | Final div/rem instruction for divisor `b`: the guard-ELIDED `-safe`
-- variant when `b` is a safe literal, else the guarded form. Both denote
-- `_/ˢ_`/`_%ˢ_` identically (only the emitted asm differs).
--
-- Factored through `div-instr`/`rem-instr` on the DECISION Bool so that a
-- `with safe-divisor? b` in the correctness proofs makes `div-op`/`rem-op`
-- reduce definitionally (the Bool appears syntactically as the argument).
div-instr rem-instr : Bool → AbstractInstr
div-instr true  = div-safe-rrr 0 1 0
div-instr false = div-rrr 0 1 0
rem-instr true  = rem-safe-rrr 0 1 0
rem-instr false = rem-rrr 0 1 0

div-op rem-op : ∀ {sh} → MArithIR sh → AbstractInstr
div-op b = div-instr (safe-divisor? b)
rem-op b = rem-instr (safe-divisor? b)

------------------------------------------------------------------------
-- compile-abs (operational)
------------------------------------------------------------------------

-- | Compile `e` at scratch-depth `d`. Postcondition (proved by
-- `CompileCorrect.compile-go-correct`): running the result leaves the
-- value of `e` in reg 0; scratch slots `< d` are preserved; reg 1 may
-- be clobbered.
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
compile-go d (adiv a b)   =
  -- After: reg 0 = (reg 1) /ˢ (reg 0) = a /ˢ b.  `div-op b` picks the
  -- guard-elided variant when `b` is a safe literal (Part B).
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ div-op b ∷ [])
compile-go d (amod a b)   =
  -- After: reg 0 = (reg 1) %ˢ (reg 0) = a %ˢ b.
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ rem-op b ∷ [])
compile-go d (aneg a)     =
  compile-go d a ++ (neg-rr 0 0 ∷ [])

-- | Top-level compile: walk the tree, then move reg 0 to the output.
compile-abs : ∀ {sh} → MArithIR sh → List AbstractInstr
compile-abs e = compile-go 0 e ++ (move-to-out 0 ∷ [])

------------------------------------------------------------------------
-- Degenerate-divisor folding (Part A): sound source-to-source rewrite
--
-- For a DEGENERATE literal divisor the whole `idiv` collapses to a
-- constant/unary op (D055 semantics), so the guard AND the idiv vanish:
--
--   a / 0  ⟶ −1     (a /ˢ 0 = negOne)         a % 0  ⟶ a   (a %ˢ 0 = a)
--   a / −1 ⟶ −a     (a /ˢ negOne = ⊝ a)       a % −1 ⟶ 0   (a %ˢ negOne = 0)
--
-- `eval-arith-W` is preserved by `Once.Word`'s /ˢ-zero/%ˢ-zero/…/negOne
-- lemmas; the preservation theorem is `CompileCorrect.normalize-preserves`.
-- A safe literal (k ∉ {0,−1}) is left for `compile-go`'s `div-op` (Part B).
------------------------------------------------------------------------

fold-div fold-mod : ∀ {sh} → MArithIR sh → MArithIR sh → MArithIR sh
fold-div a (alit (+ 0))      = alit (-[1+ 0 ])   -- a / 0  = −1
fold-div a (alit (-[1+ 0 ])) = aneg a            -- a / −1 = −a
fold-div a b                 = adiv a b
fold-mod a (alit (+ 0))      = a                 -- a % 0  = a
fold-mod a (alit (-[1+ 0 ])) = alit (+ 0)        -- a % −1 = 0
fold-mod a b                 = amod a b

-- | Recursively fold degenerate literal divisors throughout the tree.
normalize : ∀ {sh} → MArithIR sh → MArithIR sh
normalize (alit z)   = alit z
normalize (ainput p) = ainput p
normalize (aadd a b) = aadd (normalize a) (normalize b)
normalize (asub a b) = asub (normalize a) (normalize b)
normalize (amul a b) = amul (normalize a) (normalize b)
normalize (aneg a)   = aneg (normalize a)
normalize (adiv a b) = fold-div (normalize a) (normalize b)
normalize (amod a b) = fold-mod (normalize a) (normalize b)
