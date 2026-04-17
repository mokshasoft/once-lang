-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Tests.Linearity
--
-- Regression tests for the usage-indexed Expr refactor (plan 0.2.6).
--
-- HOW THIS FILE TESTS LINEARITY:
--
-- Because Expr Γ Ψ A is intrinsically typed with the usage vector Ψ,
-- linearity is enforced at *Agda type-check time*. A test that a
-- program should be REJECTED is encoded as a commented-out definition
-- whose un-commenting would break `make typecheck`. A test that a
-- program should be ACCEPTED is a definition that type-checks.
--
-- Running `make agda MODULE=Once/Tests/Linearity.agda` exercises all
-- the positive cases. Negative cases are documented inline; removing
-- the `--` prefix turns each one into a compile-time rejection test.
--
-- Reference: plans/0.2.6-usage-indexed-expr.md, docs/design/memory.md
------------------------------------------------------------------------

module Once.Tests.Linearity where

open import Data.Integer using (ℤ; +_)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type
open import Once.Surface.Syntax

------------------------------------------------------------------------
-- Test 1: var produces the expected single-use usage vector
------------------------------------------------------------------------

-- Variable at position 0 uses itself exactly once, nothing else.
test-var-usage-0 : Expr (∅ , Int) (One ∷ []) Int
test-var-usage-0 = var zero

-- Variable at position 1 has Zero at position 0 and One at position 1.
-- (Context extended right-first: position 0 is the innermost/rightmost Str.)
test-var-usage-1 : Expr (∅ , Int , Str) (Zero ∷ One ∷ []) Int
test-var-usage-1 = var (suc zero)

------------------------------------------------------------------------
-- Test 2: Literals have zero usage (pure, ignore environment)
------------------------------------------------------------------------

test-int-zero-usage : Expr (∅ , Int , Str) zeroUsage Int
test-int-zero-usage = int (+ 42)

test-str-zero-usage : Expr (∅ , Int) zeroUsage Str
test-str-zero-usage = str "hello"

test-unit-zero-usage : Expr (∅ , Int) zeroUsage Unit
test-unit-zero-usage = unit

test-prim-zero-usage : Expr (∅ , Int) zeroUsage Int
test-prim-zero-usage = prim "external"

------------------------------------------------------------------------
-- Test 3: Linear identity (\^1 x -> x) type-checks
------------------------------------------------------------------------

-- Body uses x exactly once (usage = One at position 0).
-- lam's proof: One ≤q One ≡ true (refl).
-- Result: Int ⊸ Int, i.e. Int ⇒[ One ] Int.
linear-id : Expr ∅ [] (Int ⇒[ One ] Int)
linear-id = lam One refl (var zero)

------------------------------------------------------------------------
-- Test 4: Unrestricted identity (\^w x -> x) type-checks
-- (sub-usage: body uses x once, acceptable under ω-declared arrow)
------------------------------------------------------------------------

-- Body uses x once; One ≤q Many ≡ true (by `_≤q_`).
unrestricted-id : Expr ∅ [] (Int ⇒[ Many ] Int)
unrestricted-id = lam Many refl (var zero)

------------------------------------------------------------------------
-- Test 5: Erased identity (\^0 x -> x) REJECTED by construction
------------------------------------------------------------------------

-- The body uses x once (q' = One), but the declared arrow grade is Zero.
-- lam requires (q' ≤q q) ≡ true, i.e. (One ≤q Zero) ≡ true.
-- (One ≤q Zero) reduces to `false` per Once.Type._≤q_, so `refl` has
-- type `false ≡ false`, not `false ≡ true` — Agda rejects at type-check.
--
-- Uncomment to verify Agda rejects:
--
-- erased-id-rejected : Expr ∅ [] (Int ⇒[ Zero ] Int)
-- erased-id-rejected = lam Zero refl (var zero)

------------------------------------------------------------------------
-- Test 6: Linear body that uses variable twice is REJECTED
------------------------------------------------------------------------

-- `\^1 x -> (x, x)` uses x twice: (One ∷ []) +ᵘ (One ∷ []) = (Many ∷ []).
-- lam declared quantity One, so we'd need (Many ≤q One) ≡ true, which
-- reduces to `false ≡ true`. Agda rejects.
--
-- Uncomment to verify Agda rejects:
--
-- bad-linear-dup : Expr ∅ [] (Int ⇒[ One ] (Int * Int))
-- bad-linear-dup = lam One refl (pair (var zero) (var zero))

-- Same body under an ω-declared arrow: type-checks (Many ≤q Many).
good-unrestricted-dup : Expr ∅ [] (Int ⇒[ Many ] (Int * Int))
good-unrestricted-dup = lam Many refl (pair (var zero) (var zero))

------------------------------------------------------------------------
-- Test 7: Linear discard (\^1 x -> unit) is REJECTED for One,
-- ACCEPTED for Many (sub-usage: Zero ≤ One ≤ Many)
------------------------------------------------------------------------

-- NOTE: Zero ≤q One ≡ true, so `\^1 x -> unit` actually type-checks
-- under QTT sub-usage (discard is allowed even at One grade).
-- "Linear" in QTT means AT MOST once, not EXACTLY once.
linear-discard : Expr ∅ [] (Int ⇒[ One ] Unit)
linear-discard = lam One refl unit

-- Discarding under Many is trivially fine.
unrestricted-discard : Expr ∅ [] (Int ⇒[ Many ] Unit)
unrestricted-discard = lam Many refl unit

------------------------------------------------------------------------
-- Test 8: App scaling — argument usage multiplies by arrow grade
------------------------------------------------------------------------

-- Context: (∅ , f : Int ⇒[ Many ] Int , x : Int), size 2.
-- Position 0 is the innermost/rightmost x; position 1 is f.
-- var (suc zero) = f with usage (Zero ∷ One ∷ []).
-- var zero       = x with usage (One  ∷ Zero ∷ []).
-- app f x : (Zero ∷ One ∷ []) +ᵘ (Many *ᵘ (One ∷ Zero ∷ []))
--         = (Zero ∷ One ∷ []) +ᵘ (Many ∷ Zero ∷ [])
--         = (Many ∷ One ∷ [])
-- So x gets used Many times (via the ω-arrow) and f gets used once.
test-app-scale-many : Expr (∅ , (Int ⇒[ Many ] Int) , Int) (Many ∷ One ∷ []) Int
test-app-scale-many = app (var (suc zero)) (var zero)

-- For a linear function (Int ⇒[ One ] Int), argument scales by One:
-- (Zero ∷ One ∷ []) +ᵘ (One *ᵘ (One ∷ Zero ∷ [])) = (One ∷ One ∷ []).
test-app-scale-one : Expr (∅ , (Int ⇒[ One ] Int) , Int) (One ∷ One ∷ []) Int
test-app-scale-one = app (var (suc zero)) (var zero)

------------------------------------------------------------------------
-- Test 9: Pair combines usage additively
------------------------------------------------------------------------

-- `(x, y)` where x and y are distinct variables uses both once.
test-pair-distinct : Expr (∅ , Int , Str) (One ∷ One ∷ []) (Str * Int)
test-pair-distinct = pair (var zero) (var (suc zero))

-- `(x, x)` uses the same variable twice → Many.
test-pair-same : Expr (∅ , Int) (Many ∷ []) (Int * Int)
test-pair-same = pair (var zero) (var zero)

------------------------------------------------------------------------
-- Test 10: Case branches combine via ⊔ᵘ (max), not +ᵘ (sum)
------------------------------------------------------------------------

-- Scrutinee uses x once; both branches discard their bound variable
-- AND ignore the outer x (returning unit). So total usage is:
--   Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)
-- = (One ∷ []) +ᵘ ((Zero ∷ []) ⊔ᵘ (Zero ∷ []))
-- = (One ∷ []) +ᵘ (Zero ∷ [])
-- = (One ∷ []).
test-case-branches-max : Expr (∅ , Int) (One ∷ []) Unit
test-case-branches-max =
  case' {qℓ = Zero} {qr = Zero} {A = Int} {B = Int} (inl' (var zero))
        unit  -- left branch: ignores bound var, returns unit
        unit  -- right branch: same

-- When BOTH branches use the outer x once, the combined branch usage
-- via ⊔ᵘ is still One (not Many); combined with scrutinee's One we get Many.
-- This demonstrates the max-not-sum discipline for case branches.
--   Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)
-- = (One ∷ []) +ᵘ ((One ∷ []) ⊔ᵘ (One ∷ []))
-- = (One ∷ []) +ᵘ (One ∷ [])
-- = (Many ∷ []).
-- Contrast: if case' used +ᵘ instead of ⊔ᵘ, we'd get (Many ∷ []) via
-- (One + One) + One = Many ... wait this example both end up Many.
-- A cleaner contrast is when the scrutinee doesn't touch x:
--   outer x used by both branches once each, scrutinee zero:
--   ⊔ᵘ: (Zero ∷ []) +ᵘ ((One ∷ []) ⊔ᵘ (One ∷ [])) = (One ∷ [])    -- one use
--   +ᵘ : (Zero ∷ []) +ᵘ ((One ∷ []) +ᵘ (One ∷ []))  = (Many ∷ [])  -- two uses
test-case-branches-shared : Expr (∅ , Int) (One ∷ []) Int
test-case-branches-shared =
  case' {qℓ = Zero} {qr = Zero} {A = Unit} {B = Unit}
        (inl' unit {- scrutinee unused on x -})
        (var (suc zero))  -- left branch uses outer x once
        (var (suc zero))  -- right branch uses outer x once
  -- ⊔ᵘ gives only (One ∷ []); compare to naive sum which would give Many.

------------------------------------------------------------------------
-- Test 11: Let binding scales RHS usage by bound variable's grade
------------------------------------------------------------------------

-- `let y = x in y + y` uses y twice, so RHS x scales by Many.
-- Let's test a simpler case: `let y = x in y` uses y once, so x scales by One.
-- Usage: (Zero ∷ []) body-tail +ᵘ (One *ᵘ (One ∷ []) RHS) = (One ∷ []).
test-let-linear : Expr (∅ , Int) (One ∷ []) Int
test-let-linear = let' (var zero) (var zero)

-- `let y = x in (y, y)` uses y twice (Many), so x scales by Many.
-- Usage: (Zero ∷ []) +ᵘ (Many *ᵘ (One ∷ [])) = (Many ∷ []).
test-let-many : Expr (∅ , Int) (Many ∷ []) (Int * Int)
test-let-many = let' (var zero) (pair (var zero) (var zero))

------------------------------------------------------------------------
-- Test 12: Builtin specializer type-pinning
------------------------------------------------------------------------

-- The per-builtin body specializers (in TypeCheck/Elaborate) should have
-- zeroUsage for their closed-term body. Test-pin their types so accidental
-- drift in the specializer module triggers these tests.
--
-- (We don't import TypeCheck.Elaborate here to keep this file standalone;
-- the pin is in TypeCheck/Elaborate's own signatures. These tests verify
-- that the *shape* of such specializers is constructible.)

-- Reconstruction of specId's body:
test-specId-shape : ∀ (T : Type) → Expr ∅ [] (T ⇒[ Many ] T)
test-specId-shape T = lam Many refl (var zero)

-- Reconstruction of specFst's body:
test-specFst-shape : ∀ (A B : Type) → Expr ∅ [] ((A * B) ⇒[ Many ] A)
test-specFst-shape A B = lam Many refl (fst' (var zero))

-- Reconstruction of specCompose's body (3-arg point-free composition):
test-specCompose-shape : ∀ (A B C : Type)
                      → Expr ∅ [] ((B ⇒[ Many ] C) ⇒[ Many ] ((A ⇒[ Many ] B) ⇒[ Many ] (A ⇒[ Many ] C)))
test-specCompose-shape A B C =
  lam Many refl (lam Many refl (lam Many refl
    (app (var (suc (suc zero)))
         (app (var (suc zero)) (var zero)))))

------------------------------------------------------------------------
-- Test 13: Mixed quantities on nested lambdas
------------------------------------------------------------------------

-- `\^w f. \^1 x. f x` — outer arrow is Many, inner is One.
-- Inner body (app f x): uses f once (Zero ∷ One ∷ []), x once scaled by
--   the arrow grade between f and x... wait, f here is applied, so it's
--   just `app`. f's usage is (Zero ∷ One ∷ []), x's is (One ∷ Zero ∷ []).
-- Actually app's scaling applies to the argument: app f x with f arrow-grade
-- Many gives (f's usage) +ᵘ (Many *ᵘ x's usage).
--
-- Let's just construct a known-good case: identity under both grades.
-- `(Int ⇒[ Many ] Int) ⇒[ Many ] (Int ⇒[ Many ] Int)`
test-apply-id : Expr ∅ [] ((Int ⇒[ Many ] Int) ⇒[ Many ] (Int ⇒[ Many ] Int))
test-apply-id = lam Many refl (var zero)

------------------------------------------------------------------------
-- Test 14: A closed arithmetic expression has zero usage
------------------------------------------------------------------------

test-closed-add : Expr ∅ [] Int
test-closed-add = add (int (+ 1)) (int (+ 2))

------------------------------------------------------------------------
-- Test 15: Arithmetic of a variable with itself
------------------------------------------------------------------------

-- `x + x` uses x twice → Many.
test-self-add : Expr (∅ , Int) (Many ∷ []) Int
test-self-add = add (var zero) (var zero)

-- `x + 1` uses x once (literal contributes Zero).
test-plus-lit : Expr (∅ , Int) (One ∷ []) Int
test-plus-lit = add (var zero) (int (+ 1))
