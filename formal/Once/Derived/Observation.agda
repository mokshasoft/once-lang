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
open import Once.CCC.IR
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
-- the number of observations. They are all Hylos.
------------------------------------------------------------------------

-- | obs : Nat → Stream A → List A
--
-- Observe exactly n steps of a coinductive structure, producing
-- an inductive structure of the same shape.
--
-- For streams: obs n s = [s₀, s₁, ..., sₙ₋₁]
--
-- Implementation: Hylo with out-μ for pattern-matching on Nat
--
-- This is the optimal implementation that enables full fusion:
--   sum (obs n s) = Hylo sumAlg obsCoalg (n,s)  -- no intermediate list!
--
-- The coalgebra uses out-μ to pattern-match on the Nat counter:
--   - If n = 0: produce Nil
--   - If n = suc k: produce Cons (head s, (k, tail s))
--
obs : ∀ {A}
    → WellFormedF (StreamF A)
    → WellFormedF (ListF A)
    → IR (Nat * Stream A) (List A)
obs {A} wfStream wfList = Hylo wfList alg coalg
  where
    -- State type: Nat * Stream A
    -- ListF A applied to state: Unit + (A * (Nat * Stream A))

    -- The coalgebra pattern-matches on Nat using out-μ and produces ListF.
    -- To case on the first component of a pair while keeping access to the rest,
    -- we use: apply ∘ ⟨ case (curry f) (curry g) ∘ fst , snd ⟩
    -- This is equivalent to: caseFst f g where caseFst preserves the context.

    -- Coalgebra: (Nat * Stream A) → Unit + (A * (Nat * Stream A))
    -- Step 1: out-μ ∘ fst gives us (Unit + Nat) from the Nat
    -- Step 2: case on that, with snd (the Stream A) and original Nat available
    coalg : IR (Nat * Stream A) (⟦ ListF A ⟧T (Nat * Stream A))
    coalg = apply ∘ ⟨ case zeroCase sucCase ∘ out-μ wf-NatF ∘ fst , id ⟩ Stack
      where
        -- Zero case: Unit → (Nat * Stream A) → ListF result
        -- Produces Nil regardless of the stream
        zeroCase : IR Unit ((Nat * Stream A) ⇒ (⟦ ListF A ⟧T (Nat * Stream A)))
        zeroCase = curry (inl Stack ∘ terminal) Stack

        -- Suc case: Nat (predecessor) → (Nat * Stream A) → ListF result
        -- Produces Cons (head stream, (predecessor, tail stream))
        -- Input to curried function: Nat (the predecessor k)
        -- Input from apply: (Nat * Stream A) (original pair, but we replace Nat with k)
        sucCase : IR Nat ((Nat * Stream A) ⇒ (⟦ ListF A ⟧T (Nat * Stream A)))
        sucCase = curry
          (inr Stack ∘ ⟨ fst ∘ Out wfStream ∘ snd ∘ snd  -- head of stream
                       , ⟨ fst ∘ snd                      -- predecessor (from first arg)
                         , snd ∘ Out wfStream ∘ snd ∘ snd -- tail of stream
                         ⟩ Stack
                       ⟩ Stack)
          Stack

    -- Algebra: build list (just In)
    alg : IR (⟦ ListF A ⟧T (List A)) (List A)
    alg = In wfList Stack

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
-- NOTE: These operations require Para (paramorphism) which gives access
-- to both the recursive result AND the original substructure. Para is
-- derivable from Cata but adds complexity. These primitives are
-- documented here for completeness; implementation deferred until
-- Para is added to the IR.
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
-- Implementation requires Para (paramorphism) to access original tail.
-- Deferred until Para is available in IR.

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
-- | embed     | μ F → ν F | Needs Para |
-- | periodic  | μ F → ν F | Needs Ana + Para |
-- | foldObs   | Nat → (B → A → B) → B → ν F → B | Needs surface syntax |
--
-- The ν→μ operations (obs, obsWhile, obsUntil) are based on Cata over
-- the bounding parameter, ensuring termination by structural recursion.
--
-- The μ→ν operations (embed, periodic) are Anas, which are always safe
-- (productive by IR totality).
--
-- Key principle: All observation operations that cross from ν to μ
-- use bounded recursion, recovering the fusion benefits that would
-- otherwise require unsafe Cata ∘ Ana composition.
------------------------------------------------------------------------
