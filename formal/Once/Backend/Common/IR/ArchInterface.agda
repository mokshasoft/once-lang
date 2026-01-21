------------------------------------------------------------------------
-- Once.Backend.Common.IR.ArchInterface
--
-- Complete interface that each architecture must implement.
--
-- Design principle: All proof obligations in ONE record.
-- This includes both leaf cases AND glue lemmas for combining phases.
-- The mutual recursion structure then becomes trivial.
--
-- This is NOT documentation - Agda's type system enforces that
-- each architecture provides all required proofs.
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd; arr; unfold; fold; terminal; initial; Prim)
open import Once.Type as Type using (Type; _*_; _⇒_; Eff; Fix; Void) renaming (_+_ to _⊕_)
open import Once.Semantics using (⟦_⟧; eval; encode)

module Once.Backend.Common.IR.ArchInterface where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Backend.Common.IR.Spec

------------------------------------------------------------------------
-- ArchCorrectness: Complete Architecture Implementation
--
-- An architecture implements this record to get the mutual recursion
-- structure "for free" from MutualRecursion.agda.
--
-- The record is large because it includes ALL obligations:
--   1. Machine/Invariant/Validity/CodeGen interfaces
--   2. Leaf case proofs (id, inl, inr, fst, snd, etc.)
--   3. Phase lemmas (setup, middle, cleanup for pair; dispatch for case)
--   4. Glue lemmas (how to combine phases into full correctness)
--   5. Capacity threading lemmas
------------------------------------------------------------------------

record ArchCorrectness : Set₂ where
  field
    -- Machine interface
    machine : MachineInterface

    -- Invariant interface
    invariants : InvariantInterface machine

    -- Validity interface
    validity : ValidityInterface machine invariants

    -- Code generation interface
    codegen : CodeGenInterface machine

  -- Open all interfaces for convenience
  open MachineInterface machine public
  open InvariantInterface invariants public
  open ValidityInterface validity public
  open CodeGenInterface codegen public

  -- Open IRSpecs with a placeholder Star (will be refined)
  -- Each architecture provides Star through the star-trans field
  field
    -- Star relation for execution sequences
    Star : Program → State → State → Set

    -- Star transitivity (fundamental for combining proofs)
    star-trans : ∀ {prog : Program} {s₁ s₂ s₃ : State} →
      Star prog s₁ s₂ →
      Star prog s₂ s₃ →
      Star prog s₁ s₃

  -- Now open IRSpecs with the actual Star
  open IRSpecs machine invariants validity codegen Star public

  field
    -----------------------------------------------------------------
    -- Leaf Case Proofs
    --
    -- Direct proofs for IR constructors with no sub-IR
    -----------------------------------------------------------------

    -- Identity
    id-correct : ∀ {A : Type} (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x empty-program (ir-stack-requirement (id {A})) →
      ∃[ s' ] IRCorrectness (id {A}) (compile (id {A})) s s' x 0

    -- Left injection
    inl-correct : ∀ {A B : Type} (a : ⟦ A ⟧) (s : State) →
      Preconditions {A} s a empty-program (ir-stack-requirement (inl {A} {B})) →
      ∃[ s' ] IRCorrectness (inl {A} {B}) (compile (inl {A} {B})) s s' a 0

    -- Right injection
    inr-correct : ∀ {A B : Type} (b : ⟦ B ⟧) (s : State) →
      Preconditions {B} s b empty-program (ir-stack-requirement (inr {A} {B})) →
      ∃[ s' ] IRCorrectness (inr {A} {B}) (compile (inr {A} {B})) s s' b 0

    -- First projection
    fst-correct : ∀ {A B : Type} (p : ⟦ A * B ⟧) (s : State) →
      Preconditions {A * B} s p empty-program (ir-stack-requirement (fst {A} {B})) →
      ∃[ s' ] IRCorrectness (fst {A} {B}) (compile (fst {A} {B})) s s' p 0

    -- Second projection
    snd-correct : ∀ {A B : Type} (p : ⟦ A * B ⟧) (s : State) →
      Preconditions {A * B} s p empty-program (ir-stack-requirement (snd {A} {B})) →
      ∃[ s' ] IRCorrectness (snd {A} {B}) (compile (snd {A} {B})) s s' p 0

    -- Arrow (effect construction)
    arr-correct : ∀ {A B : Type} (f : ⟦ A ⇒ B ⟧) (s : State) →
      Preconditions {A ⇒ B} s f empty-program (ir-stack-requirement (arr {A} {B})) →
      ∃[ s' ] IRCorrectness (arr {A} {B}) (compile (arr {A} {B})) s s' f 0

    -- Unfold (Fix destructor)
    unfold-correct : ∀ {F : Type} (x : ⟦ Fix F ⟧) (s : State) →
      Preconditions {Fix F} s x empty-program (ir-stack-requirement (unfold {F})) →
      ∃[ s' ] IRCorrectness (unfold {F}) (compile (unfold {F})) s s' x 0

    -- Fold (Fix constructor)
    fold-correct : ∀ {F : Type} (x : ⟦ F ⟧) (s : State) →
      Preconditions {F} s x empty-program (ir-stack-requirement (fold {F})) →
      ∃[ s' ] IRCorrectness (fold {F}) (compile (fold {F})) s s' x 0

    -- Terminal (to Unit)
    terminal-correct : ∀ {A : Type} (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x empty-program (ir-stack-requirement (terminal {A})) →
      ∃[ s' ] IRCorrectness (terminal {A}) (compile (terminal {A})) s s' x 0

    -- Initial (from Void - vacuously true)
    initial-correct : ∀ {A : Type} (x : ⟦ Void ⟧) (s : State) →
      Preconditions {Void} s x empty-program (ir-stack-requirement (initial {A})) →
      ∃[ s' ] IRCorrectness (initial {A}) (compile (initial {A})) s s' x 0

    -- Primitive operations
    prim-correct : ∀ {A B : Type} (name : String) (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x empty-program (ir-stack-requirement (Prim {A} {B} name)) →
      ∃[ s' ] IRCorrectness (Prim {A} {B} name) (compile (Prim {A} {B} name)) s s' x 0

    -----------------------------------------------------------------
    -- Compose Glue
    --
    -- (f ∘ g) means "first g, then f"
    -----------------------------------------------------------------

    -- Derive g's preconditions from compose's
    compose-g-preconditions : ∀ {A B C : Type} (f : IR B C) (g : IR A B)
      (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x empty-program (ir-stack-requirement (f ∘ g)) →
      Preconditions {A} s x empty-program (ir-stack-requirement g)

    -- After g, enable f
    compose-enables-f : ∀ {A B C : Type} (f : IR B C) (g : IR A B)
      (x : ⟦ A ⟧) (s s₁ : State) →
      Preconditions {A} s x empty-program (ir-stack-requirement (f ∘ g)) →
      IRCorrectness g (compile g) s s₁ x 0 →
      Preconditions {B} s₁ (eval g x) empty-program (ir-stack-requirement f)

    -- Combine g and f into compose
    compose-combine : ∀ {A B C : Type} (f : IR B C) (g : IR A B)
      (x : ⟦ A ⟧) (s s₁ s₂ : State) →
      IRCorrectness g (compile g) s s₁ x 0 →
      IRCorrectness f (compile f) s₁ s₂ (eval g x) 0 →
      IRCorrectness (f ∘ g) (compile (f ∘ g)) s s₂ x 0

    -----------------------------------------------------------------
    -- Pair Glue: ⟨ f , g ⟩
    --
    -- Execution: setup → f → middle → g → cleanup
    -----------------------------------------------------------------

    -- Setup: prepare for f
    pair-setup : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s : State) →
      Preconditions {C} s x empty-program (ir-stack-requirement ⟨ f , g ⟩) →
      ∃[ s₁ ] PairSpecs.SetupPost f g s s₁ x

    -- Setup enables f
    pair-setup-enables-f : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s s₁ : State) →
      PairSpecs.SetupPost f g s s₁ x →
      Preconditions {C} s₁ x empty-program (ir-stack-requirement f)

    -- Middle: store f's result, restore input for g
    pair-middle : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s₁ s₂ : State) (fx : ⟦ A ⟧) →
      IRCorrectness f (compile f) s₁ s₂ x 0 →
      ∃[ s₃ ] PairSpecs.MiddlePost f g s₁ s₂ s₃ x fx

    -- Middle enables g
    pair-middle-enables-g : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s₁ s₂ s₃ : State) (fx : ⟦ A ⟧) →
      PairSpecs.MiddlePost f g s₁ s₂ s₃ x fx →
      Preconditions {C} s₃ x empty-program (ir-stack-requirement g)

    -- Cleanup: construct pair
    -- Takes: s-orig (original state for SavedRegsPreserved), s₃ (where g started), s₄ (after g)
    pair-cleanup : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s-orig s₃ s₄ : State) (fx : ⟦ A ⟧) (gx : ⟦ B ⟧) →
      IRCorrectness g (compile g) s₃ s₄ x 0 →
      ∃[ s₅ ] PairSpecs.CleanupPost f g s-orig s₅ x fx gx

    -- Combine all pair phases
    pair-combine : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s s₁ s₂ s₃ s₄ s₅ : State) →
      PairSpecs.SetupPost f g s s₁ x →
      IRCorrectness f (compile f) s₁ s₂ x 0 →
      PairSpecs.MiddlePost f g s₁ s₂ s₃ x (eval f x) →
      IRCorrectness g (compile g) s₃ s₄ x 0 →
      PairSpecs.CleanupPost f g s s₅ x (eval f x) (eval g x) →
      IRCorrectness ⟨ f , g ⟩ (compile ⟨ f , g ⟩) s s₅ x 0

    -----------------------------------------------------------------
    -- Curry Glue: curry f
    --
    -- Creates closure, skips thunk. Thunk executed via apply.
    -----------------------------------------------------------------

    curry-setup : ∀ {A B C : Type} (f : IR (A * B) C)
      (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x empty-program (ir-stack-requirement (curry f)) →
      ∃[ s₁ ] CurrySpecs.SetupPost f s s₁ x

    curry-combine : ∀ {A B C : Type} (f : IR (A * B) C)
      (x : ⟦ A ⟧) (s s₁ : State) →
      CurrySpecs.SetupPost f s s₁ x →
      IRCorrectness (curry f) (compile (curry f)) s s₁ x 0

    -----------------------------------------------------------------
    -- Case Glue: [ f , g ]
    --
    -- Dispatch then branch
    -----------------------------------------------------------------

    -- Dispatch left
    case-dispatch-left : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (a : ⟦ A ⟧) (s : State) →
      Preconditions {A ⊕ B} s (inj₁ a) empty-program (ir-stack-requirement [ f , g ]) →
      ∃[ s₁ ] CaseSpecs.DispatchLeftPost f g s s₁ a

    -- Dispatch left enables f
    case-dispatch-enables-f : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (a : ⟦ A ⟧) (s s₁ : State) →
      CaseSpecs.DispatchLeftPost f g s s₁ a →
      Preconditions {A} s₁ a empty-program (ir-stack-requirement f)

    -- Combine dispatch left + f
    case-left-combine : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (a : ⟦ A ⟧) (s s₁ s₂ : State) →
      CaseSpecs.DispatchLeftPost f g s s₁ a →
      IRCorrectness f (compile f) s₁ s₂ a 0 →
      IRCorrectness [ f , g ] (compile [ f , g ]) s s₂ (inj₁ a) 0

    -- Dispatch right
    case-dispatch-right : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (b : ⟦ B ⟧) (s : State) →
      Preconditions {A ⊕ B} s (inj₂ b) empty-program (ir-stack-requirement [ f , g ]) →
      ∃[ s₁ ] CaseSpecs.DispatchRightPost f g s s₁ b

    -- Dispatch right enables g
    case-dispatch-enables-g : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (b : ⟦ B ⟧) (s s₁ : State) →
      CaseSpecs.DispatchRightPost f g s s₁ b →
      Preconditions {B} s₁ b empty-program (ir-stack-requirement g)

    -- Combine dispatch right + g
    case-right-combine : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (b : ⟦ B ⟧) (s s₁ s₂ : State) →
      CaseSpecs.DispatchRightPost f g s s₁ b →
      IRCorrectness g (compile g) s₁ s₂ b 0 →
      IRCorrectness [ f , g ] (compile [ f , g ]) s s₂ (inj₂ b) 0

    -----------------------------------------------------------------
    -- Apply: Uses Induction Hypothesis
    --
    -- Apply needs IH to execute the thunk inside the closure.
    -----------------------------------------------------------------

    apply-correct :
      -- The induction hypothesis
      (ih : ∀ {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
            Preconditions {A} s x empty-program (ir-stack-requirement ir) →
            ∃[ s' ] IRCorrectness ir (compile ir) s s' x 0) →
      ∀ {A B : Type} (p : ⟦ (A ⇒ B) * A ⟧) (s : State) →
      Preconditions {(A ⇒ B) * A} s p empty-program (ir-stack-requirement (apply {A} {B})) →
      ∃[ s' ] IRCorrectness (apply {A} {B}) (compile (apply {A} {B})) s s' p 0

------------------------------------------------------------------------
-- Summary
--
-- ArchCorrectness is the COMPLETE contract for an architecture.
-- By implementing this record, an architecture:
--   1. Provides all leaf case proofs
--   2. Provides all phase lemmas
--   3. Provides all glue lemmas for combining phases
--
-- The MutualRecursion module then simply wires these together
-- into the full ir-correct theorem with NO additional postulates.
------------------------------------------------------------------------
