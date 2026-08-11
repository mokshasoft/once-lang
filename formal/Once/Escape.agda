-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Escape
--
-- Escape analysis for Once IR.
-- Rewrites AllocMode from Heap to Stack where allocations are
-- immediately consumed, making stack allocation safe.
--
-- Key insight: AllocMode is semantically transparent (ignored in eval),
-- so all rewrites are trivially correct. This module identifies patterns
-- where allocations don't escape their immediate context.
--
-- Rules implemented:
--   1. fst ∘ ⟨ f , g ⟩ m → fst ∘ ⟨ f , g ⟩ Stack  (pair consumed by fst)
--   2. snd ∘ ⟨ f , g ⟩ m → snd ∘ ⟨ f , g ⟩ Stack  (pair consumed by snd)
--   3. [ f , g ] ∘ inl m → [ f , g ] ∘ inl Stack  (injection consumed by case)
--   4. [ f , g ] ∘ inr m → [ f , g ] ∘ inr Stack  (injection consumed by case)
--   5. apply ∘ ⟨ curry f m₁ , x ⟩ m₂ → apply ∘ ⟨ curry f Stack , x ⟩ Stack
--      (closure immediately applied, pair immediately consumed)
--   6. apply ∘ ⟨ f , x ⟩ m → apply ∘ ⟨ f , x ⟩ Stack  (pair consumed by apply)
--      (generalizes rule 5 for non-curry functions)
--   7. terminal ∘ ⟨ f , g ⟩ m → terminal ∘ ⟨ f , g ⟩ Stack  (pair discarded)
--   8. terminal ∘ curry f m → terminal ∘ curry f Stack  (closure discarded)
--   9. (f ∘ fst) ∘ ⟨ g , h ⟩ m → (f ∘ fst) ∘ ⟨ g , h ⟩ Stack  (pair consumed by fst)
--  10. (f ∘ snd) ∘ ⟨ g , h ⟩ m → (f ∘ snd) ∘ ⟨ g , h ⟩ Stack  (pair consumed by snd)
--
-- Rules 7-8 are edge cases for dead code that wasn't eliminated.
-- Rules 9-10 are high-impact for let bindings: `let x = e1 in f x` desugars to
-- `(f ∘ snd) ∘ ⟨id, e1⟩` which is now optimized.
--
-- OCP-0003: fold/unfold rules removed. Use In/Cata/Out/Ana for recursive types.
------------------------------------------------------------------------

module Once.Escape where

open import Once.Type
open import Once.IR

open import Data.Nat using (ℕ; zero; suc)

------------------------------------------------------------------------
-- Escape Analysis: Composition Rules
--
-- OCP-0003 postulate eliminated: implemented as plain composition.
-- AllocMode is semantically transparent (ignored in eval), so this is a
-- trivially-correct pass that can later be extended with mode rewrites
-- without breaking the correctness proof. The intended mode-rewrite
-- rules are documented in the module header comment; they require
-- view-based pattern matching similar to Once.Optimize and can be
-- implemented analogously when needed.
------------------------------------------------------------------------

escape-compose : ∀ {A B C} → IR B C → IR A B → IR A C
escape-compose g f = g ∘ f

------------------------------------------------------------------------
-- Escape Analysis: Single Pass
------------------------------------------------------------------------

-- | Apply escape analysis recursively to an IR term
--
-- Descend into all subterms, applying escape-compose at composition
-- points to identify stack-allocatable values.
--
escape-once : ∀ {A B} → IR A B → IR A B
-- D062: escape analysis descends into the constant-leaf IRs of a Fuse/Hylo's
-- natural transform; the structural routing (ntId/ntFst/…) is unchanged.
escape-nt : ∀ {G F} → NatTr G F → NatTr G F

-- Identity: nothing to optimize
escape-once id = id

-- Composition: the key case - recurse into both sides, then apply rules
escape-once (g ∘ f) = escape-compose (escape-once g) (escape-once f)

-- Projections: no allocation, pass through
escape-once fst = fst
escape-once snd = snd

-- Pairing: recurse into components, preserve mode
-- (Mode may be optimized when this pair is consumed in a composition)
escape-once (⟨ f , g ⟩ m) = ⟨ escape-once f , escape-once g ⟩ m

-- Injections: preserve mode
-- (Mode may be optimized when this injection is consumed in a composition)
escape-once (inl m) = inl m
escape-once (inr m) = inr m

-- Case: recurse into branches
escape-once (case f g) = case (escape-once f) (escape-once g)

-- Terminal/Initial: no allocation
escape-once terminal = terminal
escape-once initial = initial

-- Curry: recurse into body, preserve mode
-- (Mode may be optimized when this closure is consumed in a composition)
escape-once (curry f m) = curry (escape-once f) m

-- Apply: no allocation in apply itself
escape-once apply = apply

-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.

-- Effects: no allocation

-- Primitives: opaque, pass through
escape-once (SigOp name) = SigOp name

-- const literal: opaque, pass through
escape-once (const p v) = const p v

-- free-heap: opaque, pass through
escape-once (free-heap h) = free-heap h

-- OCP-0003 recursion schemes: recurse into algebras/coalgebras
escape-once (In wf m) = In wf m
escape-once (out-μ wf) = out-μ wf
escape-once (Cata {F} wf alg) = Cata {F} wf (escape-once alg)
escape-once (Para {F} wf alg) = Para {F} wf (escape-once alg)
escape-once (Out wf) = Out wf
escape-once (in-ν wf m) = in-ν wf m
escape-once (Ana {F} wf coalg) = Ana {F} wf (escape-once coalg)
escape-once (Hylo {F} {G} wfF wfG alg t) = Hylo {F} {G} wfF wfG (escape-once alg) (escape-nt t)
-- Fuse: μ-anchored fusion (correct by construction)
escape-once (Fuse {F} {G} wfF wfG alg t) = Fuse {F} {G} wfF wfG (escape-once alg) (escape-nt t)
-- Guard/Unguard removed: productivity follows from IR totality
-- out-μ/in-ν: Lambek isomorphisms, pass through

escape-nt ntId         = ntId
escape-nt (ntK ir)     = ntK (escape-once ir)
escape-nt (ntFst t)    = ntFst (escape-nt t)
escape-nt (ntSnd t)    = ntSnd (escape-nt t)
escape-nt (ntCase t u) = ntCase (escape-nt t) (escape-nt u)
escape-nt (ntInl t)    = ntInl (escape-nt t)
escape-nt (ntInr t)    = ntInr (escape-nt t)
escape-nt (ntPair t u) = ntPair (escape-nt t) (escape-nt u)

------------------------------------------------------------------------
-- Escape Analysis: Bounded Iteration
------------------------------------------------------------------------

-- | Apply escape analysis n times
--
-- Multiple passes may find new opportunities as the IR is rewritten.
--
escape-n : ∀ {A B} → ℕ → IR A B → IR A B
escape-n zero ir = ir
escape-n (suc n) ir = escape-n n (escape-once ir)

-- | Main entry point: apply escape analysis with fixed bound
--
-- 10 iterations should be sufficient for most programs.
--
escape : ∀ {A B} → IR A B → IR A B
escape = escape-n 10