------------------------------------------------------------------------
-- Once.Backend.Common.IRDispatcher
--
-- Generic IR dispatcher patterns for architecture correctness proofs.
--
-- This module provides:
-- 1. RecDispatcherType - the generic type for size-bounded recursive dispatch
-- 2. Documentation of the dispatcher pattern for IR proofs
--
-- Each architecture instantiates RecDispatcherType with their specific
-- types and implements the dispatcher following the documented pattern.
--
-- The key insight: by passing `rec` as an explicit function argument
-- instead of using parameterized modules, we can:
-- - Eliminate MutualIR/*.agda wrapper modules entirely
-- - Have cleaner, more direct dispatch logic
-- - Make the Acc-based termination pattern explicit
------------------------------------------------------------------------

open import Once.Type using (Type; _*_; _+_; _⇒_; Fix)
open import Once.Contract using (ContractInterface)

-- | IRDispatcher parameterized by ⟦_⟧ and ContractInterface
-- ⟦_⟧ is the type interpretation provided by each architecture
module Once.Backend.Common.IRDispatcher (⟦_⟧ : Type → Set) (CI : ContractInterface) where

import Once.IR ⟦_⟧ as IR
import Once.Backend.Common.IRSize ⟦_⟧ CI as IRSize

open IR.IRDef CI
open IRSize

open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (∃; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Induction.WellFounded using (Acc; acc)

------------------------------------------------------------------------
-- RecDispatcher Type Pattern
--
-- The core abstraction for well-founded recursive dispatch on IR terms.
-- Each architecture instantiates this with their specific types.
--
-- Parameters:
-- - State: Machine state type
-- - Memory: Memory type (extracted from State)
-- - Program: Executable program type
-- - StackPointer: Stack frame reference type
-- - halted, pc, readInputReg, memory: State inspection functions
-- - ValidAt: Validity predicate for values in memory
-- - StackInvariant, StackCapacity, RbpInvariant: Stack discipline
-- - compile: Code generation function
-- - _++ₚ_, lengthₚ: Program operations
-- - ir-stack-requirement: Stack capacity needed for IR
-- - IRStarResultV: Result record type for IR execution
------------------------------------------------------------------------

module RecDispatcherType
  {State Memory Program StackPointer : Set}
  (halted : State → Bool)
  (pc : State → ℕ)
  (readInputReg : State → ℕ)
  (memory : State → Memory)
  (ValidAt : ∀ {A : Type} → ⟦ A ⟧ → ℕ → Memory → Set)
  (StackInvariant : State → Set)
  (StackCapacity : State → ℕ → Set)
  (RbpInvariant : State → Set)
  (compile : ∀ {A B} → IR A B → Program)
  (_++ₚ_ : Program → Program → Program)
  (lengthₚ : Program → ℕ)
  (ir-stack-requirement : ∀ {A B} → IR A B → ℕ)
  (IRStarResultV : ∀ {A B : Type} → IR A B → Program → State → State → ⟦ A ⟧ → ℕ → Set₁)
  where

  -- | Size-bounded recursive dispatcher type
  --
  -- For any IR smaller than bound, produce an execution result.
  -- This is the type of the `rec` function passed to implementation modules.
  --
  -- Usage in dispatcher:
  --   dispatcher ir ... (acc rs) =
  --     let rec : RecDispatcher (ir-size ir)
  --         rec ir' lt ... = dispatcher ir' ... (rs lt)
  --     in ImplementationModule.run-ir-star-v ... rec ...
  RecDispatcher : ℕ → Set₁
  RecDispatcher bound =
    ∀ {A B} (ir : IR A B) → ir-size ir < bound →
    (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ lengthₚ prefix →
    ValidAt x (readInputReg s) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement ir) →
    RbpInvariant s →
    let prog = prefix ++ₚ (compile ir ++ₚ suffix)
    in ∃[ s' ] IRStarResultV ir prog s s' x (lengthₚ prefix)

------------------------------------------------------------------------
-- Dispatcher Pattern Documentation
--
-- Each architecture implements a dispatcher following this pattern:
--
-- mutual
--   run-ir-star-at-offset-v : ∀ {A B} (ir : IR A B) ... → Acc _<_ (ir-size ir) →
--     ∃[ s' ] IRStarResultV ir prog s s' x offset
--
--   -- Base cases: delegate to StarBase, ignore Acc
--   run-ir-star-at-offset-v id ... _ = run-id-star-vv ...
--   run-ir-star-at-offset-v terminal ... _ = run-terminal-star-vv ...
--   ... (other non-recursive cases)
--
--   -- Recursive cases: construct rec from Acc, delegate to IR modules
--   run-ir-star-at-offset-v (⟨ f , g ⟩) ... (acc rs) =
--     let rec : RecDispatcher (ir-size ⟨ f , g ⟩)
--         rec ir' lt ... = run-ir-star-at-offset-v ir' ... (rs lt)
--     in Pair.run-pair-star-v ... rec ...
--
--   run-ir-star-at-offset-v (g ∘ f) ... (acc rs) =
--     let rec : RecDispatcher (ir-size (g ∘ f))
--         rec ir' lt ... = run-ir-star-at-offset-v ir' ... (rs lt)
--     in Compose.run-compose-star-v ... rec ...
--
--   run-ir-star-at-offset-v ([ f , g ]) ... (acc rs) =
--     let rec : RecDispatcher (ir-size [ f , g ])
--         rec ir' lt ... = run-ir-star-at-offset-v ir' ... (rs lt)
--     in Case.run-case-star-v ... rec ...
--
--   -- curry and apply: may need Acc for thunk/closure body execution
--   run-ir-star-at-offset-v (curry f) ... ac = run-curry-star-v ... ac
--   run-ir-star-at-offset-v apply ... ac = run-apply-star-v ... ac
--
-- -- Public API: provides initial Acc
-- run-ir-star ir ... = run-ir-star-at-offset-v ir ... (<-wellFounded (ir-size ir))
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Implementation Module Pattern
--
-- Each recursive IR case (Pair, Compose, Case) follows this pattern:
--
-- module IR.Pair where
--   open RecDispatcherType {State} {Program} ... using (RecDispatcher)
--
--   run-pair-star-v : ∀ {A B C} (f : IR C A) (g : IR C B) (bound : ℕ) →
--     (rec : RecDispatcher bound) →
--     ir-size f < bound → ir-size g < bound →
--     (prefix suffix : Program) ... →
--     ∃[ s' ] IRStarResultV ⟨ f , g ⟩ prog s s' x offset
--   run-pair-star-v f g bound rec f<bound g<bound ... =
--     ... (execute f using rec f f<bound ...)
--     ... (execute g using rec g g<bound ...)
--     ... (combine results)
--
-- This pattern:
-- 1. Takes RecDispatcher bound as explicit parameter
-- 2. Takes size proofs for sub-terms (f<bound, g<bound)
-- 3. Uses rec for recursive calls on smaller IRs
-- 4. Enables elimination of parameterized module wrappers (MutualIR/*)
------------------------------------------------------------------------
