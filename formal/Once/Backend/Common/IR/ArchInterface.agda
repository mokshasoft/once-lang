------------------------------------------------------------------------
-- Once.Backend.Common.IR.ArchInterface
--
-- Interface that each architecture must implement for IR proofs.
--
-- This defines the "contract" that backends must fulfill:
--   - Machine model (State, step, etc.)
--   - Code generation (compile, compile-length)
--   - Phase lemmas for composite IR (pair, curry, case)
--   - Leaf case proofs (id, inl, inr, etc.)
--
-- By implementing this interface, an architecture gets access to
-- the shared mutual recursion structure for free.
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd; arr; unfold; fold)
open import Once.Type using (Type; _*_; _⇒_; Eff) renaming (_+_ to _⊕_)
open import Once.Semantics using (⟦_⟧; eval; encode)

module Once.Backend.Common.IR.ArchInterface where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Backend.Common.IR.Spec

------------------------------------------------------------------------
-- ArchCorrectness Interface
--
-- The main interface that each architecture must implement.
-- Split into:
--   1. PhaseLemmas - lemmas for each phase of composite IR
--   2. LeafLemmas - proofs for leaf IR constructors
------------------------------------------------------------------------

record ArchCorrectness : Set₁ where
  field
    -- Machine interface
    machine : MachineInterface

    -- Invariant interface
    invariants : InvariantInterface machine

    -- Validity interface
    validity : ValidityInterface machine invariants

    -- Code generation interface
    codegen : CodeGenInterface machine

  -- Open all interfaces
  open MachineInterface machine public
  open InvariantInterface invariants public
  open ValidityInterface validity public
  open CodeGenInterface codegen public
  open IRSpecs machine invariants validity codegen public

  field
    ---------------------------------------------------------
    -- Leaf Case Lemmas
    --
    -- Direct proofs for IR constructors with no sub-IR
    ---------------------------------------------------------

    -- Identity is correct
    id-correct : ∀ {A : Type} (x : ⟦ A ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement (id {A})) →
      ∃[ s' ] IRCorrectness (id {A}) (compile (id {A})) s s' x 0

    -- Left injection is correct
    inl-correct : ∀ {A B : Type} (a : ⟦ A ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement (inl {A} {B})) →
      ∃[ s' ] IRCorrectness (inl {A} {B}) (compile (inl {A} {B})) s s' a 0

    -- Right injection is correct
    inr-correct : ∀ {A B : Type} (b : ⟦ B ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement (inr {A} {B})) →
      ∃[ s' ] IRCorrectness (inr {A} {B}) (compile (inr {A} {B})) s s' b 0

    -- First projection is correct
    fst-correct : ∀ {A B : Type} (p : ⟦ A * B ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement (fst {A} {B})) →
      ∃[ s' ] IRCorrectness (fst {A} {B}) (compile (fst {A} {B})) s s' p 0

    -- Second projection is correct
    snd-correct : ∀ {A B : Type} (p : ⟦ A * B ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement (snd {A} {B})) →
      ∃[ s' ] IRCorrectness (snd {A} {B}) (compile (snd {A} {B})) s s' p 0

    ---------------------------------------------------------
    -- Phase Lemmas for Pair: ⟨ f , g ⟩
    --
    -- Execution: setup → f → middle → g → cleanup
    ---------------------------------------------------------

    -- Setup phase: save registers, allocate pair, prepare input for f
    pair-setup-correct : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement ⟨ f , g ⟩) →
      ∃[ s₁ ] PairSpecs.SetupPost f g s s₁ x

    -- Middle phase: store f's result, restore input for g
    pair-middle-correct : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s s₁ s₂ : State) (fx : ⟦ A ⟧) →
      -- s₂ is state after f executed
      ∃[ s₃ ] PairSpecs.MiddlePost f g s₁ s₂ s₃ x fx

    -- Cleanup phase: construct pair, restore registers
    pair-cleanup-correct : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s s₁ s₃ s₄ : State) (fx : ⟦ A ⟧) (gx : ⟦ B ⟧) →
      -- s₄ is state after g executed
      ∃[ s₅ ] PairSpecs.CleanupPost f g s s₁ s₃ s₄ s₅ x fx gx

    ---------------------------------------------------------
    -- Phase Lemmas for Curry: curry f
    --
    -- Execution: setup (create closure, skip thunk)
    -- Thunk execution happens via apply
    ---------------------------------------------------------

    curry-setup-correct : ∀ {A B C : Type} (f : IR (A * B) C)
      (x : ⟦ A ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement (curry f)) →
      ∃[ s₁ ] CurrySpecs.SetupPost f s s₁ x

    ---------------------------------------------------------
    -- Phase Lemmas for Case: [ f , g ]
    --
    -- Execution: dispatch → (f | g)
    ---------------------------------------------------------

    case-dispatch-left : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (a : ⟦ A ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement [ f , g ]) →
      -- Input is inj₁ a
      ∃[ s₁ ] CaseSpecs.DispatchLeftPost f g s s₁ a

    case-dispatch-right : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (b : ⟦ B ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement [ f , g ]) →
      -- Input is inj₂ b
      ∃[ s₁ ] CaseSpecs.DispatchRightPost f g s s₁ b

    ---------------------------------------------------------
    -- Compose: f ∘ g means "first g, then f"
    --
    -- No special phases needed - just sequential execution
    -- But we need to show that g's postconditions enable f
    ---------------------------------------------------------

    compose-enables-second : ∀ {A B C : Type} (f : IR B C) (g : IR A B)
      (x : ⟦ A ⟧) (s s' : State) →
      IRCorrectness g (compile g) s s' x 0 →
      Preconditions s' (output-value s') (ir-stack-requirement f)

    ---------------------------------------------------------
    -- Apply: special handling
    --
    -- Apply needs the induction hypothesis to prove the thunk correct.
    -- The architecture provides the proof structure, parameterized by IH.
    ---------------------------------------------------------

    apply-correct :
      -- The induction hypothesis: all IR is correct
      (ih : ∀ {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
            Preconditions s (output-value s) (ir-stack-requirement ir) →
            ∃[ s' ] IRCorrectness ir (compile ir) s s' x 0) →
      ∀ {A B : Type} (p : ⟦ (A ⇒ B) * A ⟧) (s : State) →
      Preconditions s (output-value s) (ir-stack-requirement (apply {A} {B})) →
      ∃[ s' ] IRCorrectness (apply {A} {B}) (compile (apply {A} {B})) s s' p 0

------------------------------------------------------------------------
-- Summary
--
-- To add a new architecture:
--   1. Define State, Program, step, etc.
--   2. Define StackInvariant, ValidAt, etc.
--   3. Define compile and compile-length
--   4. Prove leaf lemmas (id, inl, inr, fst, snd)
--   5. Prove phase lemmas (pair-setup/middle/cleanup, curry-setup, case-dispatch)
--   6. Prove compose-enables-second
--   7. Prove apply-correct (using IH for thunk)
--   8. Bundle into ArchCorrectness record
--   9. The MutualRecursion module gives you full IR correctness for free!
------------------------------------------------------------------------
