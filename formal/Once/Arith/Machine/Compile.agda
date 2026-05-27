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

open import Data.Nat using (ℕ; zero; suc; _⊔_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (<⇒≢)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

open import Once.Arith.Machine.AbsState
  using (ArithAbsState; InputShape; ⟦_⟧S; init; output-of; InputPath; project;
         Store; empty-store; _[_↦_]; _[_]; store-write-same; store-write-other)
open import Once.Arith.Machine.AbsInstr
  using (AbstractInstr; load-input; load-imm; add-rrr; sub-rrr; mul-rrr;
         neg-rr; spill; reload; move-to-out; run-abstract; step;
         maybe-zero; bin-op; un-op)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; ainput; aadd; asub; amul; aneg; eval-arith)
open ArithAbsState

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
--
-- Structural scaffold (Plan 0.20 follow-up, 2026-05-27): the top-level
-- `abs-validity` case-splits on `MArithIR` and dispatches to per-ctor
-- postulates. Adding a new `MArithIR` constructor breaks coverage of
-- the dispatcher, forcing the proof scaffold to be extended in lock-
-- step with the operational layer. The per-ctor postulates remain the
-- open obligations.

------------------------------------------------------------------------
-- Strong invariant on `compile-go`
--
-- Used by all `abs-validity-*` cases to package the four facts an
-- inductive step needs about the inner `compile-go`:
--   reg0      — output register holds the evaluated subexpression
--   scratch≤  — scratch slots strictly below `d` are untouched
--                (the binary case's right operand runs at depth
--                 `suc d`, so the spilled slot `d` survives across it)
--   input-eq  — input env never changes during `compile-go`
--   output-eq — the output slot is only written by the terminating
--                `move-to-out`; `compile-go` leaves it alone
------------------------------------------------------------------------

record CompileGoInv {sh} (d : ℕ) (e : MArithIR sh) (s : ArithAbsState sh) : Set where
  field
    reg0      : regs (run-abstract (compile-go d e) s) [ 0 ]
                  ≡ just (eval-arith e (input s))
    scratch≤  : ∀ i → i < d →
                scratch (run-abstract (compile-go d e) s) [ i ]
                  ≡ scratch s [ i ]
    input-eq  : input (run-abstract (compile-go d e) s) ≡ input s
    output-eq : output (run-abstract (compile-go d e) s) ≡ output s

open CompileGoInv

-- | `run-abstract` distributes over `_++_` — needed at every binary
-- step in the validity proof to split the concatenated instruction
-- list across the two operand traces.
run-abstract-app : ∀ {sh} (xs ys : List AbstractInstr) (s : ArithAbsState sh) →
  run-abstract (xs ++ ys) s ≡ run-abstract ys (run-abstract xs s)
run-abstract-app []       ys s = refl
run-abstract-app (i ∷ is) ys s = run-abstract-app is ys (step i s)

-- | Lemma: `eval-arith (ainput p) inp ≡ maybe-zero (project sh p inp)`.
-- Both definitions case-split on `project sh p inp` the same way, so
-- a single `with` aligns them.
eval-arith-ainput :
  ∀ {sh} (p : InputPath) (inp : ⟦ sh ⟧S) →
  eval-arith {sh} (ainput p) inp ≡ maybe-zero (project sh p inp)
eval-arith-ainput {sh} p inp with project sh p inp
... | just _  = refl
... | nothing = refl

-- Helper for the `ainput p` case.
compile-go-correct-ainput : ∀ {sh} (d : ℕ) (p : InputPath) (s : ArithAbsState sh) →
  CompileGoInv d (ainput p) s
compile-go-correct-ainput {sh} d p s = record
  { reg0      = cong just (sym (eval-arith-ainput p (input s)))
  ; scratch≤  = λ _ _ → refl
  ; input-eq  = refl
  ; output-eq = refl
  }

-- Per-binary-op cases: still postulated. Each requires a chain of
-- store-update reasoning (run-abstract-app + the IHs + spill-then-
-- reload algebra). The dispatcher below is type-locked: adding a new
-- `MArithIR` ctor breaks coverage in `compile-go-correct`, forcing
-- both a postulate and a dispatch arm.
postulate
  aneg-correct : ∀ {sh} (d : ℕ) (a : MArithIR sh) (s : ArithAbsState sh) →
    CompileGoInv d (aneg a) s
  aadd-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh) (s : ArithAbsState sh) →
    CompileGoInv d (aadd a b) s
  asub-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh) (s : ArithAbsState sh) →
    CompileGoInv d (asub a b) s
  amul-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh) (s : ArithAbsState sh) →
    CompileGoInv d (amul a b) s

-- | The main inductive lemma — dispatcher.
compile-go-correct : ∀ {sh} (d : ℕ) (e : MArithIR sh) (s : ArithAbsState sh) →
  CompileGoInv d e s
compile-go-correct d (alit z) s = record
  { reg0      = refl
  ; scratch≤  = λ _ _ → refl
  ; input-eq  = refl
  ; output-eq = refl
  }
compile-go-correct {sh} d (ainput p) s = compile-go-correct-ainput {sh} d p s
compile-go-correct d (aneg a)   s = aneg-correct d a s
compile-go-correct d (aadd a b) s = aadd-correct d a b s
compile-go-correct d (asub a b) s = asub-correct d a b s
compile-go-correct d (amul a b) s = amul-correct d a b s

------------------------------------------------------------------------
-- Derive `abs-validity` cases from the strong invariant
------------------------------------------------------------------------

-- Common bridge: `compile-abs e = compile-go 0 e ++ move-to-out 0 ∷ []`.
-- After `run-abstract` of the prefix, the state's `regs[0]` holds
-- `just (eval-arith e env)`. The final `move-to-out 0` writes that
-- to `output`. So `output-of (run-abstract (compile-abs e) (init env))`
-- equals `just (eval-arith e env)` — derived from `reg0` of the
-- inductive invariant.

-- | Helper: derive `abs-validity` for any `e` from `compile-go-correct`.
private
  abs-validity-from-inv : ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) →
    output-of (run-abstract (compile-abs e) (init env)) ≡ just (eval-arith e env)
  abs-validity-from-inv {sh} e env =
    trans (cong output-of (run-abstract-app (compile-go 0 e) (move-to-out 0 ∷ []) (init env)))
          (reg0 (compile-go-correct 0 e (init env)))

-- All six per-ctor cases derive from `compile-go-correct` via the
-- shared bridge `abs-validity-from-inv`. The bridge is one line of
-- `trans (cong output-of run-abstract-app) reg0`, so once any
-- per-ctor `compile-go-correct` case is discharged (e.g. the alit
-- and ainput cases above), the corresponding `abs-validity-*`
-- inherits the discharge automatically.

abs-validity-alit : ∀ {sh} (z : ℤ) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs {sh} (alit z)) (init env)) ≡ just (eval-arith {sh} (alit z) env)
abs-validity-alit z env = abs-validity-from-inv (alit z) env

abs-validity-ainput : ∀ {sh} (p : InputPath) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs {sh} (ainput p)) (init env)) ≡ just (eval-arith {sh} (ainput p) env)
abs-validity-ainput p env = abs-validity-from-inv (ainput p) env

abs-validity-aadd : ∀ {sh} (a b : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs (aadd a b)) (init env)) ≡ just (eval-arith (aadd a b) env)
abs-validity-aadd a b env = abs-validity-from-inv (aadd a b) env

abs-validity-asub : ∀ {sh} (a b : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs (asub a b)) (init env)) ≡ just (eval-arith (asub a b) env)
abs-validity-asub a b env = abs-validity-from-inv (asub a b) env

abs-validity-amul : ∀ {sh} (a b : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs (amul a b)) (init env)) ≡ just (eval-arith (amul a b) env)
abs-validity-amul a b env = abs-validity-from-inv (amul a b) env

abs-validity-aneg : ∀ {sh} (a : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs (aneg a)) (init env)) ≡ just (eval-arith (aneg a) env)
abs-validity-aneg a env = abs-validity-from-inv (aneg a) env

abs-validity :
  ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs e) (init env)) ≡ just (eval-arith e env)
abs-validity (alit z)    env = abs-validity-alit z env
abs-validity (ainput p)  env = abs-validity-ainput p env
abs-validity (aadd a b)  env = abs-validity-aadd a b env
abs-validity (asub a b)  env = abs-validity-asub a b env
abs-validity (amul a b)  env = abs-validity-amul a b env
abs-validity (aneg a)    env = abs-validity-aneg a env
