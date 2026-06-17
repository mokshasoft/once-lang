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
open import Data.Nat.Properties using (<⇒≢; ≤-refl; m≤n⇒m≤1+n)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
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
open import Once.Word using (module Word64)
open Word64 using (fromℤ; _⊕_; _⊖_; _⊗_; ⊝_)
-- L1: the modular-`Word` evaluator is now width-parameterised; the arch
-- supplies the width. This validity proof is the 64-bit instantiation
-- site — pinned at 64 (matching `Word64` above) until C+D threads `bits`.
open import Once.Arith.Machine.WordSem using (module Sem)
open Sem 64 using (eval-arith-W)
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
-- Validity
------------------------------------------------------------------------

-- The proof is a structural induction on `MArithIR` with the
-- strengthened invariant
--
--   ∀ d e s.
--     let s' = run-abstract (compile-go d e) s
--     in (regs s' [ 0 ]) ≡ just (eval-arith e (input s))
--     ∧ (∀ i < d, scratch s' [ i ] ≡ scratch s [ i ])
--     ∧ input s' ≡ input s
--     ∧ output s' ≡ output s
--
-- The arith ops in the IH propagate via the `bin-op` Maybe-lift's
-- `just/just` case, since both children's IHs give `just`. The
-- scratch-preservation half is required so that `aadd a b`'s
-- `reload d 1` after compiling `b` actually finds the spilled value
-- of `a` (compile-go d a put the value in reg 0; spill 0 d moved
-- it to scratch[d]; compile-go (suc d) b ran at depth ≥ d+1 so
-- scratch[d] is preserved).
--
-- Structural scaffold (Plan 0.20 follow-up, 2026-05-27): the top-level
-- `abs-validity` case-splits on `MArithIR` and dispatches to per-ctor
-- helpers. Adding a new `MArithIR` constructor breaks coverage of the
-- dispatcher, forcing the proof scaffold to be extended in lock-step
-- with the operational layer.

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
                  ≡ just (eval-arith-W e (input s))
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

-- | Lemma: `eval-arith-W (ainput p) inp ≡ fromℤ (maybe-zero (project sh p inp))`.
-- The abstract machine's `load-input` lands `fromℤ (maybe-zero (project …))`
-- in the register; `eval-arith-W (ainput p)` case-splits on `project`
-- the same way, so a single `with` aligns them.
eval-arith-W-ainput :
  ∀ {sh} (p : InputPath) (inp : ⟦ sh ⟧S) →
  eval-arith-W {sh} (ainput p) inp ≡ fromℤ (maybe-zero (project sh p inp))
eval-arith-W-ainput {sh} p inp with project sh p inp
... | just _  = refl
... | nothing = refl

-- Helper for the `ainput p` case.
compile-go-correct-ainput : ∀ {sh} (d : ℕ) (p : InputPath) (s : ArithAbsState sh) →
  CompileGoInv d (ainput p) s
compile-go-correct-ainput {sh} d p s = record
  { reg0      = cong just (sym (eval-arith-W-ainput p (input s)))
  ; scratch≤  = λ _ _ → refl
  ; input-eq  = refl
  ; output-eq = refl
  }

-- Helpers (private): inequality glue for store-write-other.
private
  d≢i : ∀ {i d : ℕ} → i < d → ¬ (d ≡ i)
  d≢i lt eq = <⇒≢ lt (sym eq)

  <-suc : ∀ {i d : ℕ} → i < d → i < suc d
  <-suc lt = m≤n⇒m≤1+n lt

-- Forward declaration so the per-ctor helpers can recurse via the
-- dispatcher. Termination: each helper structurally decreases on the
-- `MArithIR` argument before calling back into `compile-go-correct`.
compile-go-correct : ∀ {sh} (d : ℕ) (e : MArithIR sh) (s : ArithAbsState sh) →
  CompileGoInv d e s

-- | `aneg a`: compile `a`, then negate reg 0 in place.
aneg-correct : ∀ {sh} (d : ℕ) (a : MArithIR sh) (s : ArithAbsState sh) →
  CompileGoInv d (aneg a) s
aneg-correct {sh} d a s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong (un-op (⊝_)) (reg0 ih))
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                               (scratch≤ ih i lt)
  ; input-eq  = trans (cong input bridge) (input-eq ih)
  ; output-eq = trans (cong output bridge) (output-eq ih)
  }
  where
    ih : CompileGoInv d a s
    ih = compile-go-correct d a s

    bridge : run-abstract (compile-go d (aneg a)) s
           ≡ step (neg-rr 0 0) (run-abstract (compile-go d a) s)
    bridge = run-abstract-app (compile-go d a) (neg-rr 0 0 ∷ []) s

-- | `aadd a b`: compile `a` into reg 0, spill to scratch[d], compile
-- `b` into reg 0 at depth (suc d), reload scratch[d] into reg 1, then
-- `add-rrr 0 1 0` lands `a + b` in reg 0.
aadd-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh) (s : ArithAbsState sh) →
  CompileGoInv d (aadd a b) s
aadd-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op _⊕_)
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (add-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (aadd a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ add-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ add-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

-- | `asub a b`: same skeleton as aadd, with `sub-rrr 0 1 0` so the
-- result is `regs[1] − regs[0]` = `a − b`.
asub-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh) (s : ArithAbsState sh) →
  CompileGoInv d (asub a b) s
asub-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op _⊖_)
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (sub-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (asub a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ sub-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ sub-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

-- | `amul a b`: same skeleton as aadd, with `mul-rrr 0 1 0`.
amul-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh) (s : ArithAbsState sh) →
  CompileGoInv d (amul a b) s
amul-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op _⊗_)
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (mul-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (amul a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ mul-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ mul-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

-- | The main inductive lemma — dispatcher.
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
    output-of (run-abstract (compile-abs e) (init env)) ≡ just (eval-arith-W e env)
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
  output-of (run-abstract (compile-abs {sh} (alit z)) (init env)) ≡ just (eval-arith-W {sh} (alit z) env)
abs-validity-alit z env = abs-validity-from-inv (alit z) env

abs-validity-ainput : ∀ {sh} (p : InputPath) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs {sh} (ainput p)) (init env)) ≡ just (eval-arith-W {sh} (ainput p) env)
abs-validity-ainput p env = abs-validity-from-inv (ainput p) env

abs-validity-aadd : ∀ {sh} (a b : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs (aadd a b)) (init env)) ≡ just (eval-arith-W (aadd a b) env)
abs-validity-aadd a b env = abs-validity-from-inv (aadd a b) env

abs-validity-asub : ∀ {sh} (a b : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs (asub a b)) (init env)) ≡ just (eval-arith-W (asub a b) env)
abs-validity-asub a b env = abs-validity-from-inv (asub a b) env

abs-validity-amul : ∀ {sh} (a b : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs (amul a b)) (init env)) ≡ just (eval-arith-W (amul a b) env)
abs-validity-amul a b env = abs-validity-from-inv (amul a b) env

abs-validity-aneg : ∀ {sh} (a : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs (aneg a)) (init env)) ≡ just (eval-arith-W (aneg a) env)
abs-validity-aneg a env = abs-validity-from-inv (aneg a) env

abs-validity :
  ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs e) (init env)) ≡ just (eval-arith-W e env)
abs-validity (alit z)    env = abs-validity-alit z env
abs-validity (ainput p)  env = abs-validity-ainput p env
abs-validity (aadd a b)  env = abs-validity-aadd a b env
abs-validity (asub a b)  env = abs-validity-asub a b env
abs-validity (amul a b)  env = abs-validity-amul a b env
abs-validity (aneg a)    env = abs-validity-aneg a env
