-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Data.Nat using (ℕ; zero; suc; _⊔_; _^_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Unit using (tt)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Once.Arith.Machine.AbsInstr
  using (load-finput; load-fimm; fadd-rrr; fsub-rrr; fmul-rrr; fdiv-rrr; fneg-rr; i2f-rr; AbstractInstr; load-input; load-imm; add-rrr; sub-rrr; mul-rrr;
         div-rrr; rem-rrr; div-safe-rrr; rem-safe-rrr; shl-rri; sdiv-pow2-rri;
         neg-rr; spill; reload; move-to-out)
-- PLAN 0.75 F4: the abstract-machine compile path is pinned at `NInt`, and
-- that restriction is STATED rather than assumed. Its instruction set
-- (`add-rrr`, `div-rrr`, …) is integer-register shaped, so a float block has
-- no lowering here yet; saying so in the type means the gate sees the gap
-- instead of a float tree silently taking the integer path.
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f)

------------------------------------------------------------------------
-- Register / scratch budget
------------------------------------------------------------------------

-- | Two abstract regs: reg 0 = accumulator, reg 1 = reload target.
n-regs : ℕ
n-regs = 2

-- | Scratch budget = maximum recursion depth of binary nodes.
-- PLAN 0.75 F4: kind-POLYMORPHIC. The scratch budget is the tree's binary
-- nesting depth, which is a fact about its SHAPE — the register discipline is
-- identical at both kinds, so the budget is too.
required-scratch : ∀ {sh n} → MArithIR sh n → ℕ
required-scratch (alit _)     = 0
required-scratch (aflit _)    = 0
required-scratch (ai2f a)     = required-scratch a
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

-- Split on every constructor (not a catch-all) so `safe-divisor? e` reduces
-- definitionally in the correctness proofs.
safe-divisor? : ∀ {sh} → MArithIR sh NInt → Bool
safe-divisor? (alit k)   = safe-lit? k
safe-divisor? (ainput _) = false   -- non-literal divisor: keep the guard
safe-divisor? (aadd _ _) = false
safe-divisor? (asub _ _) = false
safe-divisor? (amul _ _) = false
safe-divisor? (adiv _ _) = false
safe-divisor? (amod _ _) = false
safe-divisor? (aneg _)   = false

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

rem-op : ∀ {sh} → MArithIR sh NInt → AbstractInstr
rem-op b = rem-instr (safe-divisor? b)

------------------------------------------------------------------------
-- Power-of-two strength reduction (multiply / divide by `2^j`)
--
-- A literal multiplier/divisor `k = 2^j` (positive power of two, `j ≥ 1`)
-- is compiled to a SHIFT rather than an `imul`/`idiv`:
--   `amul a (alit 2^j)` → left shift by `j`   (`shl-rri`)
--   `adiv a (alit 2^j)` → sign-corrected arithmetic shift right by `j`
--                         (`sdiv-pow2-rri`; truncated signed div by 2^j).
-- Detection is a bounded search recovering `j`; the `pow2-bound` fuel caps
-- `j ≤ pow2-bound` so `2^j < 2^(bits−1)` even at the smallest supported
-- width (32) — i.e. the hardware shift count is valid and (for divide) the
-- divisor `2^j` is a genuine positive value ∉ {0,−1} on every arch.
------------------------------------------------------------------------

-- | Maximum reduced exponent: `2^30 < 2^31 = 2^(32−1)`, safe at width ≥ 32.
pow2-bound : ℕ
pow2-bound = 30

-- | `pow2-try f j n` : the first `j′ ∈ {j, …, j+f−1}` with `n ≡ 2^j′`, else
-- `nothing`. Started at `j = 1`, `f = pow2-bound` — so `j′ ∈ {1, …, 30}`
-- (excludes `2^0 = 1`, which is not worth a shift).
pow2-try : ℕ → ℕ → ℕ → Maybe ℕ
pow2-try zero    j n = nothing
pow2-try (suc f) j n with n ≡ᵇ (2 ^ j)
... | true  = just j
... | false = pow2-try f (suc j) n

-- | Recover the exponent of a positive power-of-two literal (`j ≥ 1`).
pow2-exp? : ℤ → Maybe ℕ
pow2-exp? (+ n)      = pow2-try pow2-bound 1 n
pow2-exp? (-[1+ _ ]) = nothing

-- | The multiplier/divisor's exponent, when it is such a literal. Split on
-- every constructor (not a catch-all) so `pow2? e` reduces definitionally in
-- the strength-reduction correctness proofs.
pow2? : ∀ {sh} → MArithIR sh NInt → Maybe ℕ
pow2? (alit k)   = pow2-exp? k
pow2? (ainput _) = nothing
pow2? (aadd _ _) = nothing
pow2? (asub _ _) = nothing
pow2? (amul _ _) = nothing
pow2? (adiv _ _) = nothing
pow2? (amod _ _) = nothing
pow2? (aneg _)   = nothing

-- Correctness: a detected exponent `j` really identifies `k = + 2^j`.
pow2-try-correct : ∀ f j n j′ → pow2-try f j n ≡ just j′ → n ≡ 2 ^ j′
pow2-try-correct (suc f) j n j′ with n ≡ᵇ (2 ^ j) in p
... | true  = λ eq → trans (≡ᵇ⇒≡ n (2 ^ j) (subst T (sym p) tt))
                           (cong (2 ^_) (just-injective eq))
... | false = pow2-try-correct f (suc j) n j′

pow2-exp?-correct : ∀ k j → pow2-exp? k ≡ just j → k ≡ + (2 ^ j)
pow2-exp?-correct (+ n) j eq = cong +_ (pow2-try-correct pow2-bound 1 n j eq)

-- | Final multiply instruction for multiplier `b`: a left shift when `b`
-- is a power-of-two literal, else the plain `imul`.
mul-choose : Maybe ℕ → AbstractInstr
mul-choose (just j) = shl-rri 0 1 j
mul-choose nothing  = mul-rrr 0 1 0

mul-op : ∀ {sh} → MArithIR sh NInt → AbstractInstr
mul-op b = mul-choose (pow2? b)

-- | Final divide instruction for divisor `b`: a sign-corrected shift when
-- `b` is a power-of-two literal; else the guard-elided/guarded form.
div-choose : Maybe ℕ → Bool → AbstractInstr
div-choose (just j) _ = sdiv-pow2-rri 0 1 j
div-choose nothing  t = div-instr t

div-op : ∀ {sh} → MArithIR sh NInt → AbstractInstr
div-op b = div-choose (pow2? b) (safe-divisor? b)

------------------------------------------------------------------------
-- compile-abs (operational)
------------------------------------------------------------------------

-- | Compile `e` at scratch-depth `d`. Postcondition (proved by
-- `CompileCorrect.compile-go-correct`): running the result leaves the
-- value of `e` in reg 0; scratch slots `< d` are preserved; reg 1 may
-- be clobbered.
-- PLAN 0.75 F4: KIND-INDEXED. The register discipline is identical for both
-- kinds — evaluate the left operand into reg 0, spill it, evaluate the right,
-- reload and combine — because the abstract register file is untyped and a
-- float value is a pattern in it like any other. Only the OPERATION differs,
-- which is exactly the split `NumType` was introduced for.
--
-- No strength reduction on the float side: `mul-op`'s power-of-two shift is an
-- INTEGER identity (`x ⊗ 2^j = shl x j`) and has no float analogue that is
-- exact for every operand, so `amul` at `NFloat` emits the plain multiply.
compile-go : ∀ {sh n} → ℕ → MArithIR sh n → List AbstractInstr
compile-go d (alit z)     = load-imm z 0 ∷ []
compile-go d (aflit dc)   = load-fimm dc 0 ∷ []
compile-go {n = NInt}   d (ainput p) = load-input p 0 ∷ []
compile-go {n = NFloat} d (ainput p) = load-finput p 0 ∷ []
compile-go {n = NInt} d (aadd a b) =
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ add-rrr 0 1 0 ∷ [])
compile-go {n = NFloat} d (aadd a b) =
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ fadd-rrr 0 1 0 ∷ [])
compile-go {n = NInt} d (asub a b) =
  -- After: reg 0 = (reg 1) - (reg 0) = a - b
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ sub-rrr 0 1 0 ∷ [])
compile-go {n = NFloat} d (asub a b) =
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ fsub-rrr 0 1 0 ∷ [])
compile-go {n = NInt} d (amul a b) =
  -- After: reg 0 = (reg 1) ⊗ (reg 0) = a * b.  `mul-op b` picks a left
  -- shift when `b` is a power-of-two literal (strength reduction).
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ mul-op b ∷ [])
compile-go {n = NFloat} d (amul a b) =
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ fmul-rrr 0 1 0 ∷ [])
compile-go {n = NInt}   d (adiv a b) =
  -- After: reg 0 = (reg 1) /ˢ (reg 0) = a /ˢ b.  `div-op b` picks the
  -- guard-elided variant when `b` is a safe literal (Part B).
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ div-op b ∷ [])
-- The float quotient needs no divisor guard: `x/0` is a signed infinity and
-- `0/0` is the canonical NaN (D055 — total, no traps), so there is nothing to
-- branch on and the instruction stands alone.
compile-go {n = NFloat} d (adiv a b) =
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ fdiv-rrr 0 1 0 ∷ [])
compile-go d (amod a b)   =
  -- After: reg 0 = (reg 1) %ˢ (reg 0) = a %ˢ b.
  compile-go d a ++ (spill 0 d ∷ []) ++
  compile-go (suc d) b ++
  (reload d 1 ∷ rem-op b ∷ [])
compile-go {n = NInt}   d (aneg a) = compile-go d a ++ (neg-rr 0 0 ∷ [])
compile-go {n = NFloat} d (aneg a) = compile-go d a ++ (fneg-rr 0 0 ∷ [])
compile-go d (ai2f a) = compile-go d a ++ (i2f-rr 0 0 ∷ [])

-- | Top-level compile: walk the tree, then move reg 0 to the output.
compile-abs : ∀ {sh n} → MArithIR sh n → List AbstractInstr
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

fold-div fold-mod : ∀ {sh} → MArithIR sh NInt → MArithIR sh NInt → MArithIR sh NInt
fold-div a (alit (+ 0))      = alit (-[1+ 0 ])   -- a / 0  = −1
fold-div a (alit (-[1+ 0 ])) = aneg a            -- a / −1 = −a
fold-div a b                 = adiv a b
fold-mod a (alit (+ 0))      = a                 -- a % 0  = a
fold-mod a (alit (-[1+ 0 ])) = alit (+ 0)        -- a % −1 = 0
fold-mod a b                 = amod a b

-- | Recursively fold degenerate literal divisors throughout the tree.
normalize : ∀ {sh} → MArithIR sh NInt → MArithIR sh NInt
normalize (alit z)   = alit z
normalize (ainput p) = ainput p
normalize (aadd a b) = aadd (normalize a) (normalize b)
normalize (asub a b) = asub (normalize a) (normalize b)
normalize (amul a b) = amul (normalize a) (normalize b)
normalize (aneg a)   = aneg (normalize a)
normalize (adiv a b) = fold-div (normalize a) (normalize b)
normalize (amod a b) = fold-mod (normalize a) (normalize b)
