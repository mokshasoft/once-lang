-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Surface.Elaborate
--
-- Elaboration from surface syntax to IR.
-- Converts lambda/variable expressions to point-free combinators.
------------------------------------------------------------------------

module Once.Surface.Elaborate where

open import Once.Type
open import Once.CCC.IR
open import Once.Surface.Syntax
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
  using (str-lit-info; add-info; sub-info; mul-info; div-info; mod-info;
         neg-info; lt-info; le-info; gt-info; ge-info; eq-info; ne-info;
         generic-info)

-- Literals: constant morphisms that ignore input environment.
--
-- Plan 0.11: integer literals are CCC primitives (global elements
-- 1 → Int), not external function calls. They use the `const`
-- ctor — CCC compiles them inline (`mov $N, %rax` on x86-64) with
-- no runtime symbol or call overhead.
--
-- Carries both semantic levels per `const`'s signature:
--   - I.⟦Int⟧ = ℤ (proof level): the integer literal `n` itself.
--   - M.⟦Int⟧ = ℕ (machine level): `∣ n ∣` (absolute value).
-- Negative literals are tracked properly once arithmetic migrates.
intLit : ℤ → ∀ {Γ} → IR Γ Int
intLit n = const is-int n ∣ n ∣ ∘ terminal

strLit : String → ∀ {Γ} → IR Γ Str
strLit s = SigOp (str-lit-info s) ∘ terminal

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

-- | Interpret context as a product type (environment type)
--
-- The context (A₀, A₁, ..., Aₙ₋₁) becomes the nested product
-- (...((Unit * A₀) * A₁) * ... * Aₙ₋₁)
--
-- We use left-nested products so newest binding is easiest to access.
--
⟦_⟧ᶜ : ∀ {n} → Ctx n → Type
⟦ ∅ ⟧ᶜ         = Unit
⟦ Γ , A ^ q ⟧ᶜ = ⟦ Γ ⟧ᶜ * A

-- | Project variable from environment (de Bruijn index 0 = rightmost)
--
-- Given context (Γ, A), index 0 projects A (using snd),
-- index n+1 projects from Γ (using fst then recursing).
--
proj : ∀ {n} {Γ : Ctx n} (i : Fin n) → IR ⟦ Γ ⟧ᶜ (lookup Γ i)
proj {Γ = Γ , A ^ q} Fin.zero    = snd
proj {Γ = Γ , A ^ q} (Fin.suc i) = proj i ∘ fst

-- | Helper: swap product components
swap' : ∀ {X Y} → IR (X * Y) (Y * X)
swap' = ⟨ snd , fst ⟩ Heap

-- | Distribute environment over sum (distributivity isomorphism)
--
--   Γ * (A + B) → (Γ * A) + (Γ * B)
--
-- Uses curry/apply to thread environment through case:
-- 1. Swap to get (A + B) * Γ
-- 2. Case on sum, currying the injection to capture Γ
-- 3. Apply to reconstruct result
--
distribute : ∀ {Γ A B} → IR (Γ * (A + B)) ((Γ * A) + (Γ * B))
distribute {Γ} {A} {B} = distrib' ∘ swap'
  where
    curryInlSwap : IR A (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryInlSwap = curry (inl Heap ∘ swap') Heap

    curryInrSwap : IR B (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryInrSwap = curry (inr Heap ∘ swap') Heap

    curryDistrib : IR (A + B) (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryDistrib = case curryInlSwap curryInrSwap

    distrib' : IR ((A + B) * Γ) ((Γ * A) + (Γ * B))
    distrib' = apply ∘ ⟨ curryDistrib ∘ fst , snd ⟩ Heap

-- | Elaborate surface expression to IR
--
-- elaborate e produces an IR morphism from the environment type to
-- the result type: IR ⟦Γ⟧ᶜ A
--
-- Key insight: lambdas extend the environment (product), variables
-- project from the environment, and applications compose appropriately.
--
elaborate : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ A → IR ⟦ Γ ⟧ᶜ A

-- Variable: project from environment
elaborate (var i) = proj i

-- Lambda: λ^q x.e becomes curry of (elaborate e)
-- Context (Γ, A) has type ⟦Γ⟧ᶜ * A = ⟦Γ,A⟧ᶜ
-- IR curry is quantity-polymorphic, so it directly produces (A ⇒[ q ] B)
-- The quantity q is enforced during type checking, not during elaboration
elaborate (lam q _ e) = curry (elaborate e) Heap

-- Application: f x becomes apply ∘ ⟨f, x⟩
-- IR's apply is quantity-polymorphic, no coercion needed
elaborate (app f x) = apply ∘ ⟨ elaborate f , elaborate x ⟩ Heap

-- Effect application (D018-style lifting): `f x` where `f : Eff A B`
-- becomes the suspended action `λ _ → f x : Eff Unit B`. Built from
-- three existing IR primitives:
--   `applyEff ∘ ⟨f, x⟩`  : IR Γ B                  -- run f on x
--   (…) ∘ fst            : IR (Γ * Unit) B         -- ignore Unit input
--   curry (…) Heap       : IR Γ (Unit ⇒[Many] B)    -- abstract the Unit
--   arr ∘ curry (…) Heap : IR Γ (Unit ⇒[ mk-kind Many eff ] B)        -- tag as Eff
-- No new IR constructors, no coercion, no postulate.
elaborate (effApp f x) =
  arr {q = Many} ∘ curry {k = pureK Many} ((apply {k = effK} ∘ ⟨ elaborate f , elaborate x ⟩ Heap) ∘ fst) Heap

-- Pair: (a, b) becomes ⟨a, b⟩
elaborate (pair a b) = ⟨ elaborate a , elaborate b ⟩ Heap

-- Projections: compose with projection
elaborate (fst' p) = fst ∘ elaborate p
elaborate (snd' p) = snd ∘ elaborate p

-- Sum introduction
elaborate (inl' a) = inl Heap ∘ elaborate a
elaborate (inr' b) = inr Heap ∘ elaborate b

-- Case: distribute environment over sum, then case on result
-- s : Expr Γ (A + B), l : Expr (Γ,A) C, r : Expr (Γ,B) C
-- Result: (case el er) ∘ distribute ∘ ⟨ id , es ⟩
elaborate (case' s l r) =
  case (elaborate l) (elaborate r) ∘ distribute ∘ ⟨ id , elaborate s ⟩ Heap

-- Unit
elaborate unit = terminal

-- Absurd (void elimination)
elaborate (absurd v) = initial ∘ elaborate v

-- Let binding: let x = e1 in e2
-- Pairs current environment with computed value, then evaluates e2
-- ⟨ id , e1 ⟩ : Γ → Γ × A  (extend environment with bound value)
-- elaborate e2 : Γ × A → B  (e2 in extended context)
elaborate (let' e1 e2) = elaborate e2 ∘ ⟨ id , elaborate e1 ⟩ Heap

-- Integer literal: constant that ignores environment
elaborate (int n) = intLit n

-- String literal: constant that ignores environment
elaborate (str s) = strLit s

-- Arithmetic operations: pair operands, then apply primitive
elaborate (add e₁ e₂) = addIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (sub e₁ e₂) = subIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (mul e₁ e₂) = mulIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (div e₁ e₂) = divIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (mod' e₁ e₂) = modIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap

-- Unary negation
elaborate (neg e) = negIR ∘ elaborate e

-- Comparison operations
elaborate (lt e₁ e₂) = ltIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (le e₁ e₂) = leIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (gt e₁ e₂) = gtIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (ge e₁ e₂) = geIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (eq e₁ e₂) = eqIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (ne e₁ e₂) = neIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap

-- Effect lifting: arr f lifts pure function to effectful morphism
-- IR arr : (A ⇒ B) → Eff A B
elaborate (arr' f) = arr ∘ elaborate f

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
elaborate (sigOp {A = (Dom ⇒[ k ] Cod)} name) =
  curry {k = k} (SigOp (generic-info name) ∘ snd) Heap
elaborate (sigOp name) = SigOp (generic-info name) ∘ terminal
-- Unresolved polymorphic placeholder. A well-formed Surface Expr
-- reaching elaborate has been through `resolveExpr`, so `poly` nodes
-- only survive when resolution failed (e.g. cycle). Treat as an
-- external SigOp with the unqualified name — matches evalSurface for
-- the correctness theorem, and codegen will catch it as unresolved.
elaborate (poly name _) = SigOp (generic-info name) ∘ terminal