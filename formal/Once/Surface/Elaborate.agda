-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Surface.Elaborate
--
-- Elaboration from surface syntax to IR.
-- Converts lambda/variable expressions to point-free combinators.
------------------------------------------------------------------------

module Once.Surface.Elaborate where

open import Once.Type
open import Once.Float.Decimal using (Decimal)
open import Once.IR
open import Once.Surface.Syntax
open import Once.IRTy.WF using (wf-⌊⌋)
open import Relation.Binary.PropositionalEquality using (subst)
-- coerceIRArrow eliminated: curry/apply are now quantity-polymorphic

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ; ∣_∣)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.String using (String; _++_)

------------------------------------------------------------------------
-- Arithmetic IR Primitives
------------------------------------------------------------------------
--
-- These primitives are the interface between Surface.Syntax arithmetic
-- and the IR. They use the SigOp constructor for opaque runtime operations.
--
-- Semantics are defined by evalSigOp in Once.Semantics (trust boundary).

-- SigOpInfo builders (plan 0.2.4.1 Phase A):
-- each arithmetic / literal IR morphism now carries its SigOpInfo
-- (name + per-layer semantic function). See
--   `Once.Arith.SigOp.IntLit` — integer-literal family
--   `Once.Arith.SigOp.Builders` — other arithmetic SigOpInfos
open import Once.Arith.SigOp.IntLit using (lit-int-info)
open import Once.Arith.SigOp.Builders
open import Once.CanonicalName using (bare)
  using (str-lit-info; add-info; sub-info; mul-info; div-info; mod-info;
         fadd-info; fsub-info; fmul-info;
         neg-info; lt-info; le-info; gt-info; ge-info; eq-info; ne-info;
         generic-info; value-info; arrow-info)
open import Once.Functor.Translate using (IsConcrete; con-base; con-fun; base-Unit)

-- Literals: constant morphisms that ignore input environment.
--
-- Plan 0.11: integer literals are CCC primitives (global elements
-- 1 → Int), not external function calls. They use the `const`
-- ctor — CCC compiles them inline (`mov $N, %rax` on x86-64) with
-- no runtime symbol or call overhead.
--
-- Once's integers are SIGNED two's-complement machine words (D054), so a
-- literal's machine value is `Once.Word`'s `fromℤ` — the SAME function the
-- blocked arith path already uses (`block-semM (alit z) = W.fromℤ z`).
--
-- It used to be `∣ n ∣`, the ABSOLUTE VALUE, so `-5` would have denoted 5.
-- That was invisible because the DENOTATION took the absolute value too, so
-- the two agreed and every proof went through; and because no negative literal
-- can be written yet (`-5` parses as infix subtraction, never a literal token).
-- Plan 0.73 F3 folds `- <literal>` in the parser and would have armed it.
-- D115 finished the job: the payload is the `ℤ` ITSELF, so the elaborator
-- converts nothing. It cannot: it builds ONE IR for three targets and the
-- width is not its to know. The machine materialises the literal at its own
-- width (`lit-value`), exactly as it does a float literal at its own format.
intLit : ℤ → ∀ {Γ} → IR Γ Int
intLit n = const fits-int n ∘ terminal

strLit : String → ∀ {Γ} → IR Γ Str
strLit s = SigOp (str-lit-info s) ∘ terminal

-- A float literal is an ordinary immediate load, exactly like `intLit` — the
-- DECIMAL is the payload (0.74 K0) and the TARGET turns it into bits at its
-- own format, ROUNDING where it cannot hold the value exactly (D116). No FPU
-- is involved in loading a constant.
--
-- There is no representability witness any more. It existed to keep
-- `encode`'s truncation unreachable; `round` closes that hole by construction
-- instead, so there is nothing left for a witness to rule out.
floatLit : Decimal → ∀ {Γ} → IR Γ Float
floatLit d = const fits-float d ∘ terminal

-- Arithmetic operations (Int * Int → Int)
addIR : IR (Int * Int) Int
addIR = SigOp add-info

subIR : IR (Int * Int) Int
subIR = SigOp sub-info

mulIR : IR (Int * Int) Int
mulIR = SigOp mul-info

divIR : IR (Int * Int) Int
divIR = SigOp div-info

modIR : IR (Int * Int) Int
modIR = SigOp mod-info

-- Float arithmetic (Float * Float → Float), plan 0.75 F4. Same shape, distinct
-- SigOps — `arith.add.float` is a different instruction from `arith.add.int`
-- on every target, so the IR says which one it is rather than leaving the
-- backend to infer it from a type it would have to re-derive.
faddIR : IR (Float * Float) Float
faddIR = SigOp fadd-info

fsubIR : IR (Float * Float) Float
fsubIR = SigOp fsub-info

fmulIR : IR (Float * Float) Float
fmulIR = SigOp fmul-info

-- Unary negation (Int → Int)
negIR : IR Int Int
negIR = SigOp neg-info

-- Comparison operations (Int * Int → Bool, where Bool = Unit + Unit)
ltIR : IR (Int * Int) (Unit + Unit)
ltIR = SigOp lt-info

leIR : IR (Int * Int) (Unit + Unit)
leIR = SigOp le-info

gtIR : IR (Int * Int) (Unit + Unit)
gtIR = SigOp gt-info

geIR : IR (Int * Int) (Unit + Unit)
geIR = SigOp ge-info

eqIR : IR (Int * Int) (Unit + Unit)
eqIR = SigOp eq-info

neIR : IR (Int * Int) (Unit + Unit)
neIR = SigOp ne-info

-- | `⟦_⟧ᶜ` (context → environment product type) moved to `Once.Surface.Syntax`
-- (Plan 0.47): it is pure `Ctx → Type`, so it belongs with `Ctx`, and the
-- denotational meaning can take it without importing this (operational)
-- elaborator. It is in scope here via `open import Once.Surface.Syntax`.

-- | Project variable from environment (de Bruijn index 0 = rightmost)
--
-- Given context (Γ, A), index 0 projects A (using snd),
-- index n+1 projects from Γ (using fst then recursing).
--
proj : ∀ {n} {Γ : Ctx n} (i : Fin n) → IR ⌊ ⟦ Γ ⟧ᶜ ⌋ ⌊ lookup Γ i ⌋
proj {Γ = Γ , A ^ q} Fin.zero    = snd
proj {Γ = Γ , A ^ q} (Fin.suc i) = proj i ∘ fst

-- | Helper: swap product components
-- Plan 0.14 follow-up: parameterized on AllocMode for the pair node.
swap' : ∀ {X Y} → AllocMode → IR (X * Y) (Y * X)
swap' m = ⟨ snd , fst ⟩ m

-- | Distribute environment over sum (distributivity isomorphism)
--
--   Γ * (A + B) → (Γ * A) + (Γ * B)
--
-- Uses curry/apply to thread environment through case:
-- 1. Swap to get (A + B) * Γ
-- 2. Case on sum, currying the injection to capture Γ
-- 3. Apply to reconstruct result
--
distribute : ∀ {Γ A B} → AllocMode → IR (Γ * (A + B)) ((Γ * A) + (Γ * B))
distribute {Γ} {A} {B} m = distrib' ∘ swap' m
  where
    curryInlSwap : IR A (Γ ⇛ ((Γ * A) + (Γ * B)))
    curryInlSwap = curry (inl m ∘ swap' m) m

    curryInrSwap : IR B (Γ ⇛ ((Γ * A) + (Γ * B)))
    curryInrSwap = curry (inr m ∘ swap' m) m

    curryDistrib : IR (A + B) (Γ ⇛ ((Γ * A) + (Γ * B)))
    curryDistrib = case curryInlSwap curryInrSwap

    distrib' : IR ((A + B) * Γ) ((Γ * A) + (Γ * B))
    distrib' = apply ∘ ⟨ curryDistrib ∘ fst , snd ⟩ m

-- | Elaborate surface expression to IR
--
-- elaborate e produces an IR morphism from the environment type to
-- the result type: IR ⟦Γ⟧ᶜ A
--
-- Key insight: lambdas extend the environment (product), variables
-- project from the environment, and applications compose appropriately.
--
-- Plan 0.14 follow-up (2026-05-18): parameterized on the default
-- AllocMode for pair/curry/inl/inr/let/binop constructors. The
-- previously-hardcoded Heap is now `m`, threaded from the CLI's
-- --alloc flag via Once.Compile.compileFunBody. Backwards-compatible
-- alias `elaborate-default = elaborate Heap` preserves the old
-- semantics for any caller that doesn't want to choose.
elaborate : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → AllocMode → Expr Γ Ψ A → IR ⌊ ⟦ Γ ⟧ᶜ ⌋ ⌊ A ⌋

-- Variable: project from environment
elaborate m (var i) = proj i

-- Lambda: λ^q x.e becomes curry of (elaborate e)
-- Context (Γ, A) has type ⟦Γ⟧ᶜ * A = ⟦Γ,A⟧ᶜ
-- IR curry is quantity-polymorphic, so it directly produces (A ⇒[ q ] B)
-- The quantity q is enforced during type checking, not during elaboration
elaborate m (lam q _ e) = curry (elaborate m e) m

-- Application: f x becomes apply ∘ ⟨f, x⟩
-- IR's apply is quantity-polymorphic, no coercion needed
elaborate m (app f x) = apply ∘ ⟨ elaborate m f , elaborate m x ⟩ m

-- Effect application (D018-style lifting): `f x` where `f : Eff A B`
-- becomes the suspended action `λ _ → f x : Eff Unit B`. Built from
-- three existing IR primitives:
--   `applyEff ∘ ⟨f, x⟩`  : IR Γ B                  -- run f on x
--   (…) ∘ fst            : IR (Γ * Unit) B         -- ignore Unit input
--   curry (…) m          : IR Γ (Unit ⇒[Many] B)    -- abstract the Unit
--   curry (…) m          : IR Γ (Unit ⇛ B)          -- Plan 0.52 M2: ungraded
-- Built from the existing IR constructors alone. (`arr` retired: pure and
-- eff arrows are the same ungraded `⇛` object, so no tag needed.)
elaborate m (effApp f x) =
  curry ((apply ∘ ⟨ elaborate m f , elaborate m x ⟩ m) ∘ fst) m

-- Pair: (a, b) becomes ⟨a, b⟩
elaborate m (pair a b) = ⟨ elaborate m a , elaborate m b ⟩ m
elaborate m (arr' f)    = elaborate m f   -- Plan 0.52 M2: arr' is identity (IR.arr retired)

-- Projections: compose with projection
elaborate m (fst' p) = fst ∘ elaborate m p
elaborate m (snd' p) = snd ∘ elaborate m p

-- Sum introduction
elaborate m (inl' a) = inl m ∘ elaborate m a
elaborate m (inr' b) = inr m ∘ elaborate m b

-- Case: distribute environment over sum, then case on result
-- s : Expr Γ (A + B), l : Expr (Γ,A) C, r : Expr (Γ,B) C
-- Result: (case el er) ∘ distribute ∘ ⟨ id , es ⟩
elaborate m (case' s l r) =
  case (elaborate m l) (elaborate m r) ∘ distribute m ∘ ⟨ id , elaborate m s ⟩ m

-- Unit
elaborate m unit = terminal

-- Absurd (void elimination)
elaborate m (absurd v) = initial ∘ elaborate m v

-- Let binding: let x = e1 in e2
-- Pairs current environment with computed value, then evaluates e2
-- ⟨ id , e1 ⟩ : Γ → Γ × A  (extend environment with bound value)
-- elaborate e2 : Γ × A → B  (e2 in extended context)
elaborate m (let' e1 e2) = elaborate m e2 ∘ ⟨ id , elaborate m e1 ⟩ m

-- Integer literal: constant that ignores environment
elaborate m (int n) = intLit n

-- String literal: constant that ignores environment
elaborate m (str s) = strLit s

-- Float literal: same shape; the witness is erased at this boundary.
elaborate m (float d) = floatLit d

-- Arithmetic operations: pair operands, then apply primitive
elaborate m (add e₁ e₂) = addIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (sub e₁ e₂) = subIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (mul e₁ e₂) = mulIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (fadd e₁ e₂) = faddIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (fsub e₁ e₂) = fsubIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (fmul e₁ e₂) = fmulIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (div e₁ e₂) = divIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (mod' e₁ e₂) = modIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m

-- Unary negation
elaborate m (neg e) = negIR ∘ elaborate m e

-- Comparison operations
elaborate m (lt e₁ e₂) = ltIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (le e₁ e₂) = leIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (gt e₁ e₂) = gtIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (ge e₁ e₂) = geIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (eq e₁ e₂) = eqIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m
elaborate m (ne e₁ e₂) = neIR ∘ ⟨ elaborate m e₁ , elaborate m e₂ ⟩ m

-- Effect lifting: arr f lifts pure function to effectful morphism
-- IR arr : (A ⇒ B) → Eff A B

-- OCP-0003: roll'/unroll' removed. Use In/Cata/Out/Ana directly.

-- Imported primitive: call external function by name.
--
-- Plan 0.2.4.2 (Option 3): the elaboration dispatches on the
-- SigOp's type at the use site:
--
--   - **Arrow-typed (Dom ⇒[k] Cod)**: emit a CLOSURE that, when
--     applied, invokes the SigOp with its arg. The IR is `curry
--     (SigOp ∘ snd) Heap`: takes (env, arg), projects the arg
--     via `snd`, applies the SigOp morphism. The closure can be
--     passed around as a first-class value and applied later via
--     `apply`. This is what `effApp (sigOp _) x` requires —
--     without it, `SigOp ∘ terminal` would invoke the SigOp during
--     pair construction (with the env's Unit value) instead of
--     during apply (with the proper arg from `x`).
--
--   - **Non-arrow A**: keep the original elaboration `SigOp ∘
--     terminal`. SigOps with non-arrow type produce a value
--     directly (like `intLit`/`strLit`'s shape — though those use
--     `const` now, not `SigOp`). The terminal discards the env;
--     the SigOp produces the result.
--
-- The arrow case is structurally identical to how a user-defined
-- `λ x → f x` would elaborate, so SigOps and user closures are
-- now value-equivalent under apply.
elaborate m (sigOp {A = (Dom ⇒[ k ] Cod)} name (con-fun bDom cCod)) =
  curry (SigOp (arrow-info k name bDom cCod) ∘ snd) m
elaborate m (sigOp name conc) = SigOp (value-info name base-Unit conc) ∘ terminal
-- Plan 0.19: user-defined closure reference.
--
-- Unlike `sigOp`, `closure name` does NOT curry-wrap at arrow type.
-- The asm-level `once_<name>` returns the function-value (a closure
-- ptr) directly when called with Unit input; `SigOp ∘ terminal`
-- expresses exactly that: invoke `once_<name>` with terminal (empty)
-- input, and the result IS the function value. Use sites desugar
-- `f arg` to `apply (closure "f") arg`, which then invokes the
-- returned closure's body with `arg` — matching the asm contract.
--
-- This is the same shape as `sigOp` at non-arrow type. The split
-- exists so the elaborator never silently wraps a user-defined
-- entry in a curry that mismatches its asm signature.
elaborate m (closure name) = SigOp (internal-info (bare name)) ∘ terminal
-- Unresolved polymorphic placeholder. A well-formed Surface Expr
-- reaching elaborate has been through `resolveExpr`, so `poly` nodes
-- only survive when resolution failed (e.g. cycle). Treat as an
-- external SigOp with the unqualified name — matches evalSurface for
-- the correctness theorem, and codegen will catch it as unresolved.
elaborate m (poly name _) = SigOp (internal-info (bare name)) ∘ terminal

-- Plan 0.2.4.5 D2: morphism realm.
-- A `lift-morphism morph` used as a value (e.g. assigned to a variable
-- or returned from a branch) is curry'd over a discarded environment:
-- `curry (morph ∘ snd) m : IR ⟦Γ⟧ᶜ (A ⇒ B)`. When the typechecker
-- knows it is immediately applied, it emits `morph-app` instead,
-- bypassing this curry/apply round-trip and the closure ABI.
elaborate m (lift-morphism morph) = curry (morph ∘ snd) m

-- Plan 0.2.4.5 D2: morphism-realm application.
-- `morph-app morph x` lowers as the pure CCC compose `morph ∘ elaborate x` —
-- no `apply`, no closure-record allocation, no dangling-pointer
-- apply-chain bug (Plan 0.2.4.5 D1 compose runtime). This is the
-- principled lowering for "categorical-style" code (id chains,
-- compose chains, primitives). See `plans/0.2.4.5-morphism-realm-split.md`.
elaborate m (morph-app morph x) = morph ∘ elaborate m x

-- Plan 0.36 Phase 2a: catamorphism with an ARBITRARY closed algebra.
-- The algebra `alg` lives in the empty context, so `elaborate m alg :
-- IR ⟦ ∅ ⟧ᶜ (⟦F⟧T A ⇒ A) = IR Unit (⟦F⟧T A ⇒ A)`. Extract the closed
-- algebra morphism `IR (⟦F⟧T A) A` by feeding a `terminal` env and
-- applying:  `apply ∘ ⟨ algClosure ∘ terminal , id ⟩`. Then build the
-- closed `Cata`, lifted to the surrounding realm exactly like
-- `lift-morphism` (`curry (· ∘ snd) m`). No morphism vocabulary, no
-- parallel lowering — `elaborate` already handles arith/SigOps inside
-- `alg`. See plans/0.36 "two axes of generality".
elaborate m (cata {F = F} {A = A} wfF alg) =
  curry (Cata (wf-⌊⌋ wfF) (subst (λ o → IR o ⌊ A ⌋) (⌊⟧T-commute F A) (apply ∘ ⟨ elaborate m alg ∘ terminal , id ⟩ m)) ∘ snd) m

-- Anamorphism (dual of cata): a closed `Ana`, lifted to the surrounding realm
-- exactly like `cata`. Coalgebra `A → ⟦F⟧T A` built from the closed `coalg`;
-- `Ana wfF coalgebra : IR A (νF)`; `∘ snd` projects the seed from the curry's
-- `(env, seed)`; `curry … m : IR Γ (A ⇒ νF)`.
elaborate m (ana {F = F} {A = A} wfF coalg) =
  curry (Ana (wf-⌊⌋ wfF) (subst (λ o → IR ⌊ A ⌋ o) (⌊⟧T-commute F A) (apply ∘ ⟨ elaborate m coalg ∘ terminal , id ⟩ m)) ∘ snd) m

-- | Historical default: Heap allocation.
elaborate-default : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ A → IR ⌊ ⟦ Γ ⟧ᶜ ⌋ ⌊ A ⌋
elaborate-default = elaborate Heap

-- | Historical-default distribute (Heap). Used by `Once.Surface.Correct`,
-- which is Heap-specialized until Plan 0.4.2 C0 generalizes the proofs.
distribute-default : ∀ {Γ A B} → IR (Γ * (A + B)) ((Γ * A) + (Γ * B))
distribute-default = distribute Heap