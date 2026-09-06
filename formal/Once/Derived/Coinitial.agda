------------------------------------------------------------------------
-- Once.Derived.Coinitial
--
-- Coinductive types and operations (parallel to Initial library).
--
-- OCP-0003 Phase 9: Coinitial Library
--
-- This module provides coinductive (potentially infinite) types built
-- with ν-type, analogous to how the Initial library provides inductive
-- (finite) types built with μ-type.
--
-- Key types:
--   Stream A  = ν (K A ⊗ Id)                -- Infinite stream
--   CoList A  = ν (K Unit ⊕ (K A ⊗ Id))     -- Possibly-finite stream
--
-- Operations are built from Ana (unfold) and Out (observe).
------------------------------------------------------------------------

module Once.Derived.Coinitial where

open import Data.Unit using (⊤; tt)

open import Once.Type
open import Once.IR
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; IsBaseType; base-Unit)

------------------------------------------------------------------------
-- Functor Codes for Coinductive Types
------------------------------------------------------------------------

-- | Stream functor: Stream A = ν (K A ⊗ Id)
--
-- A stream is an infinite sequence: each observation yields a head
-- element and a tail stream.
--
StreamF : Type → Functor
StreamF A = K A ⊗ Id

-- | CoList functor: CoList A = ν (K Unit ⊕ (K A ⊗ Id))
--
-- A colist is a possibly-finite sequence: each observation yields
-- either termination (Unit) or a head and tail.
--
CoListF : Type → Functor
CoListF A = K Unit ⊕ (K A ⊗ Id)

------------------------------------------------------------------------
-- Type Aliases
------------------------------------------------------------------------

-- | Infinite stream
Stream : Type → Type
Stream A = ν-type (StreamF A)

-- | Possibly-finite stream (may terminate)
CoList : Type → Type
CoList A = ν-type (CoListF A)

------------------------------------------------------------------------
-- Well-Formedness Proofs
--
-- Required for recursion scheme constructors (In, Cata, Out, Ana, Hylo).
-- These prove that K positions only contain base types.
------------------------------------------------------------------------

-- | StreamF is well-formed when A is a base type
wf-StreamF : ∀ {A} → IsBaseType A → WellFormedF (StreamF A)
wf-StreamF isBase = wf-Prod (wf-K isBase) wf-Id

-- | CoListF is well-formed when A is a base type
wf-CoListF : ∀ {A} → IsBaseType A → WellFormedF (CoListF A)
wf-CoListF isBase = wf-Sum (wf-K base-Unit) (wf-Prod (wf-K isBase) wf-Id)

------------------------------------------------------------------------
-- Stream Operations
--
-- All operations on streams are built from Ana and Out.
------------------------------------------------------------------------

-- | Observe one step of a stream: yields (head, tail)
--
-- out-stream : Stream A → A * Stream A
--
out-stream : ∀ {A} → WellFormedF (StreamF A) → IR (Stream A) (A * Stream A)
out-stream wf = Out wf

-- | Head of a stream
--
-- head : Stream A → A
--
head : ∀ {A} → WellFormedF (StreamF A) → IR (Stream A) A
head wf = fst ∘ Out wf

-- | Tail of a stream
--
-- tail : Stream A → Stream A
--
tail : ∀ {A} → WellFormedF (StreamF A) → IR (Stream A) (Stream A)
tail wf = snd ∘ Out wf

-- | Repeat a value forever
--
-- repeat : A → Stream A
-- repeat a = ana (λ _ → (a, ())) unit
--
repeat : ∀ {A} → WellFormedF (StreamF A) → IR A (Stream A)
repeat {A} wf = Ana wf coalg
  where
    -- Coalgebra: ignore state, produce (a, unit)
    -- State is the value itself (A), output is (A * A) interpreted as StreamF
    coalg : IR A (A * A)
    coalg = ⟨ id , id ⟩

-- | Iterate a function
--
-- iterate : (A → A) → A → Stream A
-- iterate f a = ana (λ x → (x, f x)) a
--
iterate : ∀ {A q} → WellFormedF (StreamF A) → IR (A * (A ⇒[ q ] A)) (Stream A)
iterate {A} {q} wf = Ana wf coalg
  where
    -- Coalgebra: state is (current_value, step_function)
    -- Output: (current_value, (step_function current_value, step_function))
    coalg : IR (A * (A ⇒[ q ] A)) (⟦ StreamF A ⟧T (A * (A ⇒[ q ] A)))
    coalg = ⟨ fst , ⟨ apply ∘ ⟨ snd , fst ⟩ , snd ⟩ ⟩

-- | Map a function over a stream
--
-- map : (A → B) → Stream A → Stream B
--
-- This is a hylomorphism that observes the stream and constructs
-- a new stream with transformed elements.
--
stream-map : ∀ {A B q}
           → WellFormedF (StreamF A)
           → WellFormedF (StreamF B)
           → IR ((A ⇒[ q ] B) * Stream A) (Stream B)
stream-map {A} {B} wfA wfB = Ana wfB coalg
  where
    -- State: (function, input_stream)
    -- Output: (f (head input), (function, tail input))
    coalg : IR ((A ⇒[ _ ] B) * Stream A) (B * ((A ⇒[ _ ] B) * Stream A))
    coalg = ⟨ apply ∘ ⟨ fst , head wfA ∘ snd ⟩
            , ⟨ fst , tail wfA ∘ snd ⟩
            ⟩

------------------------------------------------------------------------
-- CoList Operations
------------------------------------------------------------------------

-- | Observe one step of a colist: yields Nothing or Just (head, tail)
--
-- out-colist : CoList A → Unit + (A * CoList A)
--
out-colist : ∀ {A} → WellFormedF (CoListF A) → IR (CoList A) (Unit + (A * CoList A))
out-colist wf = Out wf

------------------------------------------------------------------------
-- Note on Filter
--
-- filter : (A → Bool) → Stream A → CoList A
--
-- Filtering an infinite stream may produce a finite result (if the
-- predicate eventually fails forever), so the result type is CoList,
-- not Stream. This type difference documents the semantic change.
------------------------------------------------------------------------
