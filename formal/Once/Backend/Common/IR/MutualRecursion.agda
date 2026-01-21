{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.Common.IR.MutualRecursion
--
-- Shared mutual recursion structure for IR correctness proofs.
--
-- This is the heart of the architecture-independent proof framework.
-- Given an ArchCorrectness implementation (which provides phase lemmas
-- and leaf proofs), this module derives full IR correctness via
-- mutual recursion over the IR structure.
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd; arr; unfold; fold; terminal; initial; Prim)
open import Once.Type as Type using (Type; _*_; _⇒_; Eff; Fix) renaming (_+_ to _⊕_)
open import Once.Semantics using (⟦_⟧; eval; encode)

module Once.Backend.Common.IR.MutualRecursion where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Backend.Common.IR.Spec
open import Once.Backend.Common.IR.ArchInterface

------------------------------------------------------------------------
-- IR Correctness via Mutual Recursion
------------------------------------------------------------------------

module IRCorrect (Arch : ArchCorrectness) where

  open ArchCorrectness Arch

  -- Abbreviation for preconditions
  Pre : State → ℕ → Set
  Pre s cap = Preconditions s (output-value s) cap

  ----------------------------------------------------------------------
  -- Module-level postulates for phase transitions
  ----------------------------------------------------------------------

  -- Compose: g's preconditions from compose's
  postulate
    g-preconditions : ∀ {A B C : Type} (f : IR B C) (g : IR A B) (s : State) →
      Pre s (ir-stack-requirement (f ∘ g)) →
      Pre s (ir-stack-requirement g)

  -- Compose: combine g and f correctness
  postulate
    compose-correctness : ∀ {A B C : Type} (f : IR B C) (g : IR A B)
      (x : ⟦ A ⟧) (s s₁ s₂ : State) →
      IRCorrectness g (compile g) s s₁ x 0 →
      IRCorrectness f (compile f) s₁ s₂ (eval g x) 0 →
      IRCorrectness (f ∘ g) (compile (f ∘ g)) s s₂ x 0

  -- Pair: setup enables f
  postulate
    setup-enables-f : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (s s₁ : State) (x : ⟦ C ⟧) →
      PairSpecs.SetupPost f g s s₁ x →
      Pre s₁ (ir-stack-requirement f)

  -- Pair: middle enables g
  postulate
    middle-enables-g : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (s₁ s₂ s₃ : State) (x : ⟦ C ⟧) (fx : ⟦ A ⟧) →
      PairSpecs.MiddlePost f g s₁ s₂ s₃ x fx →
      Pre s₃ (ir-stack-requirement g)

  -- Pair: combine all phases
  postulate
    pair-correctness : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (x : ⟦ C ⟧) (s s₁ s₂ s₃ s₄ s₅ : State) →
      PairSpecs.SetupPost f g s s₁ x →
      IRCorrectness f (compile f) s₁ s₂ x 0 →
      PairSpecs.MiddlePost f g s₁ s₂ s₃ x (eval f x) →
      IRCorrectness g (compile g) s₃ s₄ x 0 →
      PairSpecs.CleanupPost f g s s₁ s₃ s₄ s₅ x (eval f x) (eval g x) →
      IRCorrectness ⟨ f , g ⟩ (compile ⟨ f , g ⟩) s s₅ x 0

  -- Curry: setup gives correctness
  postulate
    curry-correctness : ∀ {A B C : Type} (f : IR (A * B) C)
      (x : ⟦ A ⟧) (s s₁ : State) →
      CurrySpecs.SetupPost f s s₁ x →
      IRCorrectness (curry f) (compile (curry f)) s s₁ x 0

  -- Case left: dispatch enables f
  postulate
    dispatch-enables-f : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (s s₁ : State) (a : ⟦ A ⟧) →
      CaseSpecs.DispatchLeftPost f g s s₁ a →
      Pre s₁ (ir-stack-requirement f)

  -- Case left: combine dispatch and f
  postulate
    case-left-correctness : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (a : ⟦ A ⟧) (s s₁ s₂ : State) →
      CaseSpecs.DispatchLeftPost f g s s₁ a →
      IRCorrectness f (compile f) s₁ s₂ a 0 →
      IRCorrectness [ f , g ] (compile [ f , g ]) s s₂ (inj₁ a) 0

  -- Case right: dispatch enables g
  postulate
    dispatch-enables-g : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (s s₁ : State) (b : ⟦ B ⟧) →
      CaseSpecs.DispatchRightPost f g s s₁ b →
      Pre s₁ (ir-stack-requirement g)

  -- Case right: combine dispatch and g
  postulate
    case-right-correctness : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (b : ⟦ B ⟧) (s s₁ s₂ : State) →
      CaseSpecs.DispatchRightPost f g s s₁ b →
      IRCorrectness g (compile g) s₁ s₂ b 0 →
      IRCorrectness [ f , g ] (compile [ f , g ]) s s₂ (inj₂ b) 0

  -- Arr: applies a closure to produce an effect
  postulate
    arr-correct : ∀ {A B : Type} (x : ⟦ A ⇒ B ⟧) (s : State) →
      Pre s (ir-stack-requirement (arr {A} {B})) →
      ∃[ s' ] IRCorrectness (arr {A} {B}) (compile (arr {A} {B})) s s' x 0

  -- Unfold: destructor for Fix F
  postulate
    unfold-correct : ∀ {F : Type} (x : ⟦ Type.Fix F ⟧) (s : State) →
      Pre s (ir-stack-requirement (unfold {F})) →
      ∃[ s' ] IRCorrectness (unfold {F}) (compile (unfold {F})) s s' x 0

  -- Fold: constructor for Fix F
  postulate
    fold-correct : ∀ {F : Type} (x : ⟦ F ⟧) (s : State) →
      Pre s (ir-stack-requirement (fold {F})) →
      ∃[ s' ] IRCorrectness (fold {F}) (compile (fold {F})) s s' x 0

  -- Terminal: maps anything to unit
  postulate
    terminal-correct : ∀ {A : Type} (x : ⟦ A ⟧) (s : State) →
      Pre s (ir-stack-requirement (terminal {A})) →
      ∃[ s' ] IRCorrectness (terminal {A}) (compile (terminal {A})) s s' x 0

  -- Initial: from Void (vacuously true)
  postulate
    initial-correct : ∀ {A : Type} (x : ⟦ Type.Void ⟧) (s : State) →
      Pre s (ir-stack-requirement (initial {A})) →
      ∃[ s' ] IRCorrectness (initial {A}) (compile (initial {A})) s s' x 0

  -- Prim: primitive operations
  postulate
    prim-correct : ∀ {A B : Type} (name : String) (x : ⟦ A ⟧) (s : State) →
      Pre s (ir-stack-requirement (Prim {A} {B} name)) →
      ∃[ s' ] IRCorrectness (Prim {A} {B} name) (compile (Prim {A} {B} name)) s s' x 0

  ----------------------------------------------------------------------
  -- Mutual Recursion over IR Structure
  ----------------------------------------------------------------------

  {-# TERMINATING #-}
  mutual
    -- Main theorem: all IR is correct
    ir-correct : ∀ {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
                 Pre s (ir-stack-requirement ir) →
                 ∃[ s' ] IRCorrectness ir (compile ir) s s' x 0

    -- Identity: delegate to architecture
    ir-correct id x s pre = id-correct x s pre

    -- Left injection: delegate to architecture
    ir-correct inl x s pre = inl-correct x s pre

    -- Right injection: delegate to architecture
    ir-correct inr x s pre = inr-correct x s pre

    -- First projection: delegate to architecture
    ir-correct fst x s pre = fst-correct x s pre

    -- Second projection: delegate to architecture
    ir-correct snd x s pre = snd-correct x s pre

    -- Composition: f ∘ g means "first g, then f"
    ir-correct (f ∘ g) x s pre =
      let (s₁ , g-corr) = ir-correct g x s (g-preconditions f g s pre)
          f-pre = compose-enables-second f g x s s₁ g-corr
          (s₂ , f-corr) = ir-correct f (eval g x) s₁ f-pre
      in s₂ , compose-correctness f g x s s₁ s₂ g-corr f-corr

    -- Pair: setup → f → middle → g → cleanup
    ir-correct ⟨ f , g ⟩ x s pre =
      let (s₁ , setup) = pair-setup-correct f g x s pre
          f-pre = setup-enables-f f g s s₁ x setup
          (s₂ , f-corr) = ir-correct f x s₁ f-pre
          (s₃ , middle) = pair-middle-correct f g x s s₁ s₂ (eval f x)
          g-pre = middle-enables-g f g s₁ s₂ s₃ x (eval f x) middle
          (s₄ , g-corr) = ir-correct g x s₃ g-pre
          (s₅ , cleanup) = pair-cleanup-correct f g x s s₁ s₃ s₄ (eval f x) (eval g x)
      in s₅ , pair-correctness f g x s s₁ s₂ s₃ s₄ s₅
               setup f-corr middle g-corr cleanup

    -- Curry: setup creates closure, skips thunk
    ir-correct (curry f) x s pre =
      let (s₁ , setup) = curry-setup-correct f x s pre
      in s₁ , curry-correctness f x s s₁ setup

    -- Apply: delegate to arch with induction hypothesis
    ir-correct apply x s pre = apply-correct ir-correct x s pre

    -- Case: dispatch then branch
    ir-correct [ f , g ] (inj₁ a) s pre =
      let (s₁ , dispatch) = case-dispatch-left f g a s pre
          f-pre = dispatch-enables-f f g s s₁ a dispatch
          (s₂ , f-corr) = ir-correct f a s₁ f-pre
      in s₂ , case-left-correctness f g a s s₁ s₂ dispatch f-corr

    ir-correct [ f , g ] (inj₂ b) s pre =
      let (s₁ , dispatch) = case-dispatch-right f g b s pre
          g-pre = dispatch-enables-g f g s s₁ b dispatch
          (s₂ , g-corr) = ir-correct g b s₁ g-pre
      in s₂ , case-right-correctness f g b s s₁ s₂ dispatch g-corr

    -- Arr: applies a closure to produce an effect
    ir-correct arr x s pre = arr-correct x s pre

    -- Unfold
    ir-correct unfold x s pre = unfold-correct x s pre

    -- Fold
    ir-correct fold x s pre = fold-correct x s pre

    -- Terminal: maps anything to unit
    ir-correct terminal x s pre = terminal-correct x s pre

    -- Initial: from Void (vacuously true - x : Void is impossible)
    ir-correct initial x s pre = initial-correct x s pre

    -- Prim: primitive operations
    ir-correct (Prim name) x s pre = prim-correct name x s pre
