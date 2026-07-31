------------------------------------------------------------------------
-- OCP-0009 · W2 (option a) item 1 — DOES THE DERIVED `Hom` RECURSION
--                                    TERMINATE?  Yes, structurally — and the
--                                    check answers a second question too.
--
-- HANDOFF §4.1 tabled `Hom` former-by-former and observed that the table is a
-- definition BY RECURSION ON THE TYPE.  §4.2 item 1: check that recursion
-- terminates, because it gates the whole derived route and it is cheap.
--
-- ★ ANSWER: it terminates STRUCTURALLY — no pragma, no measure, no sized types.
-- Every recursive call is on a strict subterm of the type argument, and the two
-- cases that could have caused trouble do not recurse at all.
--
-- ★★ AND THE CHECK SETTLES "PRIMITIVE vs DERIVED", WHICH §4.1 LEFT OPEN.
-- Writing the clauses out forces the question of what `Hom base x y` IS, and
-- the answer is that it is not expressible: the kernel's `RTy` is
-- `base`/`U`/`Π`/`Σ'`/`El`, with no identity type and no empty type, so
-- "identities only" cannot be written as a type.  Same for `Hom (El n)` at a
-- NEUTRAL code.  So:
--
--     `Hom` is a PRIMITIVE CONSTRUCTOR that COMPUTES — exactly like `El`.
--
-- It unfolds at `U`, `Π` and `Σ'`; it is STUCK at `base`, at `El n`, and at a
-- `Hom` (higher paths).  That is the Tarski pattern the kernel already uses and
-- ARCHITECTURE K2 already names: "codes + `El` decoding BY REDUCTION".  The
-- dichotomy §4.1 posed — primitive OR derived — was a false one: it is BOTH,
-- and the repo has the precedent.
--
-- SCOPE.  A miniature type language of its own (PLAN §1.2 — the POC owns its
-- syntax, and the real `RTy` must not be touched before the cascade is
-- authorised).  TERMS ARE A MODULE PARAMETER: the termination question is about
-- the TYPE argument only, no clause inspects a term, so modelling terms would
-- add noise and hide that fact.  Making them opaque PROVES it.
--
-- `--safe`, zero postulates, zero holes, zero imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeHomTy
  (Tm     : Set)          -- terms, opaque: no clause below looks at one
  (v0     : Tm)           -- the bound variable, for the binder cases
  (wk     : Tm → Tm)      -- weakening under a binder
  (ap     : Tm → Tm → Tm) -- application
  (pr₁ pr₂ : Tm → Tm)     -- the pair projections
  where

------------------------------------------------------------------------
-- 1. THE TYPE LANGUAGE — the kernel's `RTy`, plus `Hom` as a constructor.
--
-- Scoping is left implicit (the codomain of `Π`/`Σ'` is "a type under a
-- binder"): binders do not affect the termination measure, and carrying de
-- Bruijn indices here would triple the module for nothing.
------------------------------------------------------------------------

data HTy : Set where
  base : HTy
  U    : HTy
  Π    : HTy → HTy → HTy
  Σ'   : HTy → HTy → HTy
  El   : Tm → HTy
  Hom  : HTy → Tm → Tm → HTy    -- ★ the new former

------------------------------------------------------------------------
-- 2. ★ THE UNFOLDING, and the termination check.
--
-- `homU A x y` is what `Hom A x y` REDUCES to.  Read the clauses against
-- HANDOFF §4.1's table.
------------------------------------------------------------------------

homU : HTy → Tm → Tm → HTy

-- ★ `U` — DIRECTED UNIVALENCE, as a computation rule.  A path between codes is
-- a MAP between their decodings.  Note it makes NO recursive call: this is the
-- clause that looked like it might not terminate (it jumps to a type built from
-- arbitrary terms) and it simply does not recurse.
homU U        c d = Π (El c) (El (wk d))

-- ★ `Π` — the functor category: a family of homs on the codomain.  Recurses on
-- `B`, a strict subterm.
--
-- ⚠ NATURALITY IS NOT CARRIED HERE — that is §4.2 item 2, still open.  It does
-- not affect this result: any naturality condition is stated USING `Hom` at the
-- codomain, which is already this same smaller call, so it cannot enlarge the
-- measure.  Item 2 can be settled either way without redoing item 1.
homU (Π A B)  f g = Π A (homU B (ap (wk f) v0) (ap (wk g) v0))

-- `Σ'` — pairs of morphisms.  Recurses on `A` and on `B`, both strict subterms.
-- ⚠ The second component's transport along the first is elided; like naturality
-- it is stated using this same call, so the measure is unaffected.
homU (Σ' A B) p q = Σ' (homU A (pr₁ p) (pr₁ q)) (homU B (pr₂ (wk p)) (pr₂ (wk q)))

-- ★ STUCK — and this is the finding, not a gap.  There is no `RTy` that says
-- "identities only": the kernel has no identity type and no empty type.  So
-- `Hom base` cannot be derived and must remain a constructor.
homU base     x y = Hom base x y

-- ★ STUCK — `El c` at a NEUTRAL `c`.  When `c` IS a code the type reduces
-- first (`El ⌜Π⌝ c d ⟶ᵀ Π (El c) (El d)`) and the `Π` clause above fires; when
-- it does not, this is a genuine neutral type.  Exactly how `El` itself
-- behaves, and the logical relation already has the shape for it (`⊩ne`).
homU (El c)   x y = Hom (El c) x y

-- STUCK — higher paths.  A path between paths is not given a computation rule
-- here; §4.1 did not scope it and nothing yet needs it.
homU (Hom A t u) x y = Hom (Hom A t u) x y

------------------------------------------------------------------------
-- 3. THE RESULT, and what it does and does not license.
--
-- ★ `homU` above is accepted with NO `TERMINATING` pragma, NO explicit measure
-- and NO sized types (hard ban, PLAN §1.2).  The measure is the type argument,
-- structurally: `Π` recurses on `B`, `Σ'` on `A` and `B`, and the other four
-- clauses do not recurse.  **§4.2 item 1 is discharged.**
--
-- ★ WHAT ELSE IT ESTABLISHES:
--
--   1. `Hom` MUST be a constructor.  Two clauses are stuck for a structural
--      reason (nothing in `RTy` expresses them), so the "fully derived" reading
--      of §4.1 is not available. `Hom` is primitive-and-computing, like `El`.
--   2. The `U` clause — directed univalence — is where the derived reading pays
--      off, and it is the one that does NOT recurse.  ARCHITECTURE K3's
--      objection to univalence ("as an AXIOM it does not compute ⇒ canonicity
--      dies") does not apply to a clause that IS a computation rule.
--   3. Item 2 (naturality at `Π`) is independent of this result, as noted at
--      that clause.  It can be settled either way without redoing item 1.
--
-- ⚠ WHAT IT DOES **NOT** LICENSE.  This is termination of the UNFOLDING
-- FUNCTION, not normalization of the extended `_⟶ᵀ_`.  Those are different
-- claims: the second has to survive `Hom`'s unfolding INTERLEAVED with term
-- reduction inside `El` — e.g. `Hom (El c)` stuck, `c` reduces to a code, the
-- type reduces, `Hom` unfolds, exposing a fresh `Hom (El b)`.  That chain looks
-- fine (term reduction is normalizing — Phase 1 — and each unfolding strictly
-- shrinks the type) but it is NOT proven here and belongs to the cascade's
-- confluence/SR step, §4.2 item 4.  Do not quote item 1 for it.
------------------------------------------------------------------------
