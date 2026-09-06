------------------------------------------------------------------------
-- Once.Derived.Observation
--
-- Observation primitives for safe ν-type to μ-type boundary crossings.
--
-- OCP-0003 Phase 9: Observation Library
--
-- This module provides primitives that safely convert coinductive types
-- (ν-type) to inductive types (μ-type) by bounding the observation.
--
-- Key insight: All observation primitives are implemented as Hylos —
-- they fuse generation and consumption without building intermediate
-- structures. This gives us totality AND full optimization.
--
-- The naming follows coalgebraic terminology:
--   obs      -- observe n steps (bounded observation)
--   obsWhile -- observe while predicate holds
--   obsUntil -- observe until predicate holds
--   embed    -- canonical embedding (finite into cofinite)
--   periodic -- periodic extension (repeat finite structure)
--   foldObs  -- fold over n observations
--
-- Mathematical foundation:
--   Observing a coalgebra (coinductive structure) means witnessing a
--   bounded number of its unfolding steps, producing an inductive
--   (finite) result. The bound ensures termination.
------------------------------------------------------------------------

module Once.Derived.Observation where

open import Data.Unit using (⊤; tt)

open import Once.Type
open import Once.IR
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; IsBaseType; base-Unit; base-Int)

-- Import coinductive types
open import Once.Derived.Coinitial using (StreamF; CoListF; Stream; CoList; wf-StreamF; wf-CoListF)

------------------------------------------------------------------------
-- Inductive Types (from Once.Type)
--
-- Re-using functor definitions from Once.Type.
------------------------------------------------------------------------

-- | List type
List : Type → Type
List A = μ-type (ListF A)

-- | Well-formedness of ListF
wf-ListF : ∀ {A} → IsBaseType A → WellFormedF (ListF A)
wf-ListF isBase = wf-Sum (wf-K base-Unit) (wf-Prod (wf-K isBase) wf-Id)

-- | Natural number type
Nat : Type
Nat = μ-type NatF

-- | Well-formedness of NatF
wf-NatF : WellFormedF NatF
wf-NatF = wf-Sum (wf-K base-Unit) wf-Id

------------------------------------------------------------------------
-- ν → μ Observation (Bounded Consumption)
--
-- These primitives safely cross from ν-type to μ-type by bounding
-- the number of observations. They use Para for provable termination.
--
-- OCP-0003 Phase 10: Para enables terminating bounded recursion without
-- TERMINATING pragmas. Para is derived from Cata, so it inherits totality.
------------------------------------------------------------------------

-- | obs : Nat → Stream A → List A
--
-- Observe exactly n steps of a coinductive structure, producing
-- an inductive structure of the same shape.
--
-- For streams: obs n s = [s₀, s₁, ..., sₙ₋₁]
--
-- Implementation: Para on NatF with the stream as context.
--
-- The Para algebra receives NatF (Nat × (Stream A ⇒ List A)):
--   - Zero case (inl Unit): return function that produces Nil
--   - Suc case (inr (Nat × (Stream A ⇒ List A))): return function that
--     produces Cons (head, rec tail) where rec is the continuation.
--
-- This is provably terminating: Para recurses on the Nat structure,
-- which is well-founded.
--
obs : ∀ {A}
    → WellFormedF (StreamF A)
    → WellFormedF (ListF A)
    → IR (Nat * Stream A) (List A)
obs {A} wfStream wfList =
  apply ∘ ⟨ Para wf-NatF obsAlg ∘ fst , snd ⟩
  where
    -- Para algebra type: NatF (Nat × (Stream A ⇒ List A)) → (Stream A ⇒ List A)
    -- NatF X = Unit + X, so the algebra input is:
    --   Unit + (Nat × (Stream A ⇒[ Many ] List A))
    --
    -- Zero case: produce Nil (the function ignores its stream argument)
    -- Suc case: (n', rec) where n' is the predecessor Nat (unused) and rec
    --           is the recursive result. Produce Cons (head stream, rec (tail stream))

    obsAlg : IR (⟦ NatF ⟧T (Nat * (Stream A ⇒[ Many ] List A))) (Stream A ⇒[ Many ] List A)
    obsAlg = case zeroCase sucCase
      where
        -- Zero case: Unit → (Stream A ⇒ List A)
        -- Produces a function that returns Nil regardless of stream input
        zeroCase : IR Unit (Stream A ⇒[ Many ] List A)
        zeroCase = curry (In wfList Stack ∘ inl Stack ∘ terminal) Stack

        -- Suc case: (Nat × (Stream A ⇒ List A)) → (Stream A ⇒ List A)
        -- Input1: pair of (predecessor Nat, recursive continuation)
        -- Produces: function that takes stream, returns Cons (head, rec tail)
        -- The predecessor Nat (fst) is unused - we only need the continuation (snd)
        sucCase : IR (Nat * (Stream A ⇒[ Many ] List A)) (Stream A ⇒[ Many ] List A)
        sucCase = curry
          (In wfList Stack ∘ inr Stack ∘
           ⟨ fst ∘ Out wfStream ∘ snd                    -- head of stream
           , apply ∘ ⟨ snd ∘ fst                         -- continuation (rec)
                    , snd ∘ Out wfStream ∘ snd ⟩   -- tail of stream
           ⟩)
          Stack

-- | obsWhile p : (A → Bool) → ν F → μ F
--
-- Observe while predicate holds on elements.
-- Stops when predicate fails or stream ends (for CoList).
--
-- For streams: obsWhile p s = [s₀, s₁, ...] while p holds
--
-- NOTE: This requires a Bool type and conditional. For now we provide
-- the type signature; implementation requires Bool infrastructure.
--
-- obsWhile : ∀ {A} → WellFormedF (StreamF A) → WellFormedF (ListF A)
--          → IR ((A ⇒[ Many ] Bool) * Stream A) (List A)

-- | obsUntil p : (A → Bool) → ν F → μ F
--
-- Observe until predicate holds (complement of obsWhile).
-- Includes the element where predicate first holds.
--
-- obsUntil : ∀ {A} → WellFormedF (StreamF A) → WellFormedF (ListF A)
--          → IR ((A ⇒[ Many ] Bool) * Stream A) (List A)

------------------------------------------------------------------------
-- μ → ν Embedding
--
-- These primitives embed inductive types into coinductive types.
-- They are safe because they don't change the termination behavior
-- of the source — finite lists become finite colists.
--
-- With Para (paramorphism) now available in the IR, these operations
-- can access both the recursive result AND the original substructure.
-- Para is derived from Cata, so it inherits totality.
------------------------------------------------------------------------

-- | embed : μ F → ν F
--
-- Canonical embedding of a finite structure into its cofinite counterpart.
-- For lists: a finite list [a, b, c] becomes a CoList that terminates.
--
-- Semantics:
--   embed [] = CoNil
--   embed (a :: as) = CoCons a (embed as)
--
-- Implementation: Ana with coalgebra that pattern-matches on input list
-- and produces CoListF output. Para not strictly needed here.

-- | periodic : μ F → ν F
--
-- Periodic extension: repeat a finite structure forever.
-- For lists: [a, b, c] becomes the infinite stream a, b, c, a, b, c, ...
--
-- Semantics:
--   periodic xs = xs ++ periodic xs  (infinite repetition)
--
-- Implementation: Ana with state (original_list, current_position).
-- When current position empties, restart from original.
-- Requires non-empty list proof or handling of empty case.

------------------------------------------------------------------------
-- Observation with Fold
--
-- These combine observation with folding in a single pass.
--
-- NOTE: These Hylo-based operations are documented for completeness.
-- The complex state threading makes them verbose in point-free IR.
-- A future surface syntax will make these more ergonomic.
------------------------------------------------------------------------

-- | foldObs n f z s : fold over n observations
--
-- Semantics:
--   foldObs n f z s = foldr f z (obs n s)
--
-- But computed directly without building intermediate list (Hylo fusion).
-- Implementation deferred until surface syntax is available.

------------------------------------------------------------------------
-- Summary
--
-- The observation primitives provide safe ν→μ boundary crossings:
--
-- | Operation | Type | Status |
-- |-----------|------|--------|
-- | obs       | Nat → Stream A → List A | ✓ Implemented |
-- | obsWhile  | (A → Bool) → ν F → μ F | Needs Bool infra |
-- | obsUntil  | (A → Bool) → ν F → μ F | Needs Bool infra |
-- | embed     | μ F → ν F | Implementable with Ana |
-- | periodic  | μ F → ν F | Needs Ana |
-- | foldObs   | Nat → (B → A → B) → B → ν F → B | Needs surface syntax |
--
-- The ν→μ operations (obs, obsWhile, obsUntil) are based on Para over
-- the bounding parameter, ensuring termination by structural recursion.
-- Para is derived from Cata, so termination is Cata's.
--
-- The μ→ν operations (embed, periodic) are Anas, which are always safe
-- (productive by IR totality).
--
-- Key principle: All observation operations that cross from ν to μ
-- use bounded recursion, recovering the fusion benefits that would
-- otherwise require unsafe Cata ∘ Ana composition.
------------------------------------------------------------------------
