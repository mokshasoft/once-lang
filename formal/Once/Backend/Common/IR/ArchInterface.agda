------------------------------------------------------------------------
-- Once.Backend.Common.IR.ArchInterface
--
-- Complete interface that each architecture must implement.
--
-- Design principle: All proof obligations in ONE record.
-- This includes both leaf cases AND glue lemmas for combining phases.
-- The mutual recursion structure then becomes trivial.
--
-- KEY: Sub-IR always runs within the context of the full program.
-- All functions take prefix/suffix to ensure proper Star proof context.
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd; arr; unfold; fold; terminal; initial; Prim)
open import Once.Type as Type using (Type; _*_; _⇒_; Eff; Fix; Void) renaming (_+_ to _⊕_)
open import Once.Semantics using (⟦_⟧; eval; encode; Closure)

module Once.Backend.Common.IR.ArchInterface where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_; _<_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Backend.Common.IR.Spec

------------------------------------------------------------------------
-- ArchCorrectness: Complete Architecture Implementation
--
-- An architecture implements this record to get the mutual recursion
-- structure "for free" from MutualRecursion.agda.
--
-- KEY DESIGN: Every function takes prefix/suffix parameters.
-- This ensures sub-IR runs in the context of the full program.
-- prog = prefix ++ compile ir ++ suffix
-- offset = length prefix
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
  field
    -- Star relation for execution sequences
    Star : Program → State → State → Set

    -- Star transitivity (fundamental for combining proofs)
    star-trans : ∀ {prog : Program} {s₁ s₂ s₃ : State} →
      Star prog s₁ s₂ →
      Star prog s₂ s₃ →
      Star prog s₁ s₃

    -- Closure well-formedness predicate (architecture-specific)
    ClosureWF : ClosureWFPredicate Program

    -- Extract thunk capacity from a ClosureWF proof
    -- For X86: ClosureWellFormed.thunk-capacity
    wf-thunk-capacity : ∀ {E A B : Type} {prog : Program} {cp : ℕ}
                           {env : ⟦ E ⟧} {sem : ⟦ A ⟧ → ⟦ B ⟧} →
                         ClosureWF {E} {A} {B} prog cp env sem → ℕ

    -- Extract cap-upper-bound from a ClosureWF proof
    -- For X86: ClosureWellFormed.cap-upper-bound
    wf-cap-upper-bound : ∀ {E A B : Type} {prog : Program} {cp : ℕ}
                            {env : ⟦ E ⟧} {sem : ⟦ A ⟧ → ⟦ B ⟧} →
                          ClosureWF {E} {A} {B} prog cp env sem → ℕ

    -- Closure layout predicate: [env-addr, code-ptr] at addr in memory
    -- For X86: Once.Backend.Common.Validity.ClosureAtS
    ClosureAtS : Word → Word → Word → Memory → Set

  -- Now open IRSpecs with the actual Star, ClosureWF, and capacity extractors
  open IRSpecs machine invariants validity codegen Star ClosureWF wf-thunk-capacity wf-cap-upper-bound ClosureAtS public

  field
    -----------------------------------------------------------------
    -- Leaf Case Proofs
    --
    -- Direct proofs for IR constructors with no sub-IR.
    -- prog = prefix ++ compile ir ++ suffix, offset = length prefix
    -----------------------------------------------------------------

    id-correct : ∀ {A : Type} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x prefix (ir-stack-requirement (id {A})) →
      ApplyWFInput (ClosureDom A) (ClosureCod A) (prefix ++ₚ compile (id {A}) ++ₚ suffix) s (closureOf A x) →
      ∃[ s' ] IRCorrectness (id {A}) (prefix ++ₚ compile (id {A}) ++ₚ suffix) s s' x (program-length prefix)

    inl-correct : ∀ {A B : Type} (prefix suffix : Program) (a : ⟦ A ⟧) (s : State) →
      Preconditions {A} s a prefix (ir-stack-requirement (inl {A} {B})) →
      ∃[ s' ] IRCorrectness (inl {A} {B}) (prefix ++ₚ compile (inl {A} {B}) ++ₚ suffix) s s' a (program-length prefix)

    inr-correct : ∀ {A B : Type} (prefix suffix : Program) (b : ⟦ B ⟧) (s : State) →
      Preconditions {B} s b prefix (ir-stack-requirement (inr {A} {B})) →
      ∃[ s' ] IRCorrectness (inr {A} {B}) (prefix ++ₚ compile (inr {A} {B}) ++ₚ suffix) s s' b (program-length prefix)

    fst-correct : ∀ {A B : Type} (prefix suffix : Program) (p : ⟦ A * B ⟧) (s : State) →
      Preconditions {A * B} s p prefix (ir-stack-requirement (fst {A} {B})) →
      ∃[ s' ] IRCorrectness (fst {A} {B}) (prefix ++ₚ compile (fst {A} {B}) ++ₚ suffix) s s' p (program-length prefix)

    snd-correct : ∀ {A B : Type} (prefix suffix : Program) (p : ⟦ A * B ⟧) (s : State) →
      Preconditions {A * B} s p prefix (ir-stack-requirement (snd {A} {B})) →
      ∃[ s' ] IRCorrectness (snd {A} {B}) (prefix ++ₚ compile (snd {A} {B}) ++ₚ suffix) s s' p (program-length prefix)

    arr-correct : ∀ {A B : Type} (prefix suffix : Program) (f : ⟦ A ⇒ B ⟧) (s : State) →
      Preconditions {A ⇒ B} s f prefix (ir-stack-requirement (arr {A} {B})) →
      ∃[ s' ] IRCorrectness (arr {A} {B}) (prefix ++ₚ compile (arr {A} {B}) ++ₚ suffix) s s' f (program-length prefix)

    unfold-correct : ∀ {F : Type} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
      Preconditions {Fix F} s x prefix (ir-stack-requirement (unfold {F})) →
      ∃[ s' ] IRCorrectness (unfold {F}) (prefix ++ₚ compile (unfold {F}) ++ₚ suffix) s s' x (program-length prefix)

    fold-correct : ∀ {F : Type} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
      Preconditions {F} s x prefix (ir-stack-requirement (fold {F})) →
      ∃[ s' ] IRCorrectness (fold {F}) (prefix ++ₚ compile (fold {F}) ++ₚ suffix) s s' x (program-length prefix)

    terminal-correct : ∀ {A : Type} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x prefix (ir-stack-requirement (terminal {A})) →
      ∃[ s' ] IRCorrectness (terminal {A}) (prefix ++ₚ compile (terminal {A}) ++ₚ suffix) s s' x (program-length prefix)

    initial-correct : ∀ {A : Type} (prefix suffix : Program) (x : ⟦ Void ⟧) (s : State) →
      Preconditions {Void} s x prefix (ir-stack-requirement (initial {A})) →
      ∃[ s' ] IRCorrectness (initial {A}) (prefix ++ₚ compile (initial {A}) ++ₚ suffix) s s' x (program-length prefix)

    prim-correct : ∀ {A B : Type} (name : String) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x prefix (ir-stack-requirement (Prim {A} {B} name)) →
      ∃[ s' ] IRCorrectness (Prim {A} {B} name) (prefix ++ₚ compile (Prim {A} {B} name) ++ₚ suffix) s s' x (program-length prefix)

    -----------------------------------------------------------------
    -- Compose Glue: (f ∘ g) means "first g, then f"
    --
    -- compile (f ∘ g) = compile g ++ transfer ++ compile f
    -----------------------------------------------------------------

    -- Transfer instruction(s) between g and f (e.g., mov rdi, rax for X86)
    compose-transfer : ∀ {A B C : Type} (f : IR B C) (g : IR A B) → Program

    -- Derive g's preconditions from compose's (same prefix, different capacity)
    compose-g-preconditions : ∀ {A B C : Type} (f : IR B C) (g : IR A B)
      (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x prefix (ir-stack-requirement (f ∘ g)) →
      Preconditions {A} s x prefix (ir-stack-requirement g)

    -- After g runs, run transfer and derive f's preconditions
    -- g ran in context: prefix ++ₚ compile g ++ₚ (transfer ++ₚ compile f ++ₚ suffix)
    -- Transfer advances PC from end of g to start of f
    -- Returns: s₂ (state after transfer), Star proof for transfer, rsp preservation,
    --          Preconditions for f at s₂, and converted ApplyWFInput for f
    compose-run-transfer : ∀ {A B C : Type} (f : IR B C) (g : IR A B)
      (prefix suffix : Program) (x : ⟦ A ⟧) (s s₁ : State) →
      Preconditions {A} s x prefix (ir-stack-requirement (f ∘ g)) →
      IRCorrectness g (prefix ++ₚ compile g ++ₚ (compose-transfer f g ++ₚ compile f ++ₚ suffix)) s s₁ x (program-length prefix) →
      ∃[ s₂ ] (Star (prefix ++ₚ compile g ++ₚ (compose-transfer f g ++ₚ compile f ++ₚ suffix)) s₁ s₂ ×
               rsp-value s₂ ≡ rsp-value s₁ ×  -- Transfer preserves rsp
               Preconditions {B} s₂ (eval g x) (prefix ++ₚ compile g ++ₚ compose-transfer f g) (ir-stack-requirement f) ×
               ApplyWFInput (ClosureDom B) (ClosureCod B) ((prefix ++ₚ compile g ++ₚ compose-transfer f g) ++ₚ compile f ++ₚ suffix) s₂ (closureOf B (eval g x)))

    -- Combine g, transfer, and f results into compose result
    -- Takes original capacity and rsp preservation for deriving compose output capacity
    compose-combine : ∀ {A B C : Type} (f : IR B C) (g : IR A B)
      (prefix suffix : Program) (x : ⟦ A ⟧) (s s₁ s₂ s₃ : State) →
      StackCapacity s (ir-stack-requirement (f ∘ g)) →  -- Original capacity for output derivation
      rsp-value s₂ ≡ rsp-value s₁ →  -- Transfer preserves rsp (for rsp-compose)
      IRCorrectness g (prefix ++ₚ compile g ++ₚ (compose-transfer f g ++ₚ compile f ++ₚ suffix)) s s₁ x (program-length prefix) →
      Star (prefix ++ₚ compile g ++ₚ (compose-transfer f g ++ₚ compile f ++ₚ suffix)) s₁ s₂ →
      IRCorrectness f ((prefix ++ₚ compile g ++ₚ compose-transfer f g) ++ₚ compile f ++ₚ suffix) s₂ s₃ (eval g x) (program-length (prefix ++ₚ compile g ++ₚ compose-transfer f g)) →
      IRCorrectness (f ∘ g) (prefix ++ₚ compile (f ∘ g) ++ₚ suffix) s s₃ x (program-length prefix)

    -----------------------------------------------------------------
    -- Pair Glue: ⟨ f , g ⟩
    --
    -- Execution: setup → f → middle → g → cleanup
    -----------------------------------------------------------------

    -- Compute prefix/suffix for f and g within pair context
    pair-context : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (prefix suffix : Program) →
      Program × Program × Program × Program  -- (prefix-f, suffix-f, prefix-g, suffix-g)

    pair-setup : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
      Preconditions {C} s x prefix (ir-stack-requirement ⟨ f , g ⟩) →
      let prog = prefix ++ₚ compile ⟨ f , g ⟩ ++ₚ suffix
          offset-f = program-length (proj₁ (pair-context f g prefix suffix))
      in ∃[ s₁ ] PairSpecs.SetupPost f g prog offset-f s s₁ x

    pair-setup-enables-f : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (prefix suffix : Program) (x : ⟦ C ⟧) (s s₁ : State) →
      let prog = prefix ++ₚ compile ⟨ f , g ⟩ ++ₚ suffix
          offset-f = program-length (proj₁ (pair-context f g prefix suffix))
      in PairSpecs.SetupPost f g prog offset-f s s₁ x →
      Preconditions {C} s₁ x (proj₁ (pair-context f g prefix suffix)) (ir-stack-requirement f)

    pair-middle : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (prefix suffix : Program) (x : ⟦ C ⟧) (s s₁ s₂ : State) (fx : ⟦ A ⟧)
      (setup : let prog = prefix ++ₚ compile ⟨ f , g ⟩ ++ₚ suffix
                   offset-f = program-length (proj₁ (pair-context f g prefix suffix))
               in PairSpecs.SetupPost f g prog offset-f s s₁ x)
      (f-corr : IRCorrectness f (proj₁ (pair-context f g prefix suffix) ++ₚ compile f ++ₚ proj₁ (proj₂ (pair-context f g prefix suffix))) s₁ s₂ x (program-length (proj₁ (pair-context f g prefix suffix)))) →
      let prog = prefix ++ₚ compile ⟨ f , g ⟩ ++ₚ suffix
          offset-g = program-length (proj₁ (proj₂ (proj₂ (pair-context f g prefix suffix))))
      in ∃[ s₃ ] PairSpecs.MiddlePost f g prog offset-g s₁ s₂ s₃ x fx

    pair-middle-enables-g : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (prefix suffix : Program) (x : ⟦ C ⟧) (s₁ s₂ s₃ : State) (fx : ⟦ A ⟧) →
      let prog = prefix ++ₚ compile ⟨ f , g ⟩ ++ₚ suffix
          offset-g = program-length (proj₁ (proj₂ (proj₂ (pair-context f g prefix suffix))))
      in PairSpecs.MiddlePost f g prog offset-g s₁ s₂ s₃ x fx →
      Preconditions {C} s₃ x (proj₁ (proj₂ (proj₂ (pair-context f g prefix suffix)))) (ir-stack-requirement g)

    pair-cleanup : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (prefix suffix : Program) (x : ⟦ C ⟧) (s-orig s₁ s₂ s₃ s₄ : State) (fx : ⟦ A ⟧) (gx : ⟦ B ⟧) →
      StackCapacity s-orig (ir-stack-requirement ⟨ f , g ⟩) →  -- Original capacity for output derivation
      FramePtrInvariant s-orig →  -- Original frame invariant for restoration
      StackInvariant s-orig →  -- Original stack invariant for PairFinalPrecond
      result-slot-addr s₄ + slot-size < frame-ptr-addr s₄ →  -- Result slot + word below frame ptr (for frame preservation)
      -- Intermediate results needed for PairFinalPrecond construction
      let prog = prefix ++ₚ compile ⟨ f , g ⟩ ++ₚ suffix
          offset-f = program-length (proj₁ (pair-context f g prefix suffix))
          offset-g = program-length (proj₁ (proj₂ (proj₂ (pair-context f g prefix suffix))))
      in (setup : PairSpecs.SetupPost f g prog offset-f s-orig s₁ x) →
      (f-corr : IRCorrectness f (proj₁ (pair-context f g prefix suffix) ++ₚ compile f ++ₚ proj₁ (proj₂ (pair-context f g prefix suffix))) s₁ s₂ x (program-length (proj₁ (pair-context f g prefix suffix)))) →
      (middle : PairSpecs.MiddlePost f g prog offset-g s₁ s₂ s₃ x fx) →
      (g-corr : IRCorrectness g (proj₁ (proj₂ (proj₂ (pair-context f g prefix suffix))) ++ₚ compile g ++ₚ proj₂ (proj₂ (proj₂ (pair-context f g prefix suffix)))) s₃ s₄ x (program-length (proj₁ (proj₂ (proj₂ (pair-context f g prefix suffix)))))) →
      let offset-end = program-length prefix + compile-length ⟨ f , g ⟩
      in ∃[ s₅ ] PairSpecs.CleanupPost f g prog offset-end s-orig s₄ s₅ x fx gx

    pair-combine : ∀ {A B C : Type} (f : IR C A) (g : IR C B)
      (prefix suffix : Program) (x : ⟦ C ⟧) (s s₁ s₂ s₃ s₄ s₅ : State) →
      let prog = prefix ++ₚ compile ⟨ f , g ⟩ ++ₚ suffix
          offset-f = program-length (proj₁ (pair-context f g prefix suffix))
          offset-g = program-length (proj₁ (proj₂ (proj₂ (pair-context f g prefix suffix))))
          offset-end = program-length prefix + compile-length ⟨ f , g ⟩
      in PairSpecs.SetupPost f g prog offset-f s s₁ x →
      IRCorrectness f (proj₁ (pair-context f g prefix suffix) ++ₚ compile f ++ₚ proj₁ (proj₂ (pair-context f g prefix suffix))) s₁ s₂ x (program-length (proj₁ (pair-context f g prefix suffix))) →
      PairSpecs.MiddlePost f g prog offset-g s₁ s₂ s₃ x (eval f x) →
      IRCorrectness g (proj₁ (proj₂ (proj₂ (pair-context f g prefix suffix))) ++ₚ compile g ++ₚ proj₂ (proj₂ (proj₂ (pair-context f g prefix suffix)))) s₃ s₄ x (program-length (proj₁ (proj₂ (proj₂ (pair-context f g prefix suffix))))) →
      PairSpecs.CleanupPost f g prog offset-end s s₄ s₅ x (eval f x) (eval g x) →
      IRCorrectness ⟨ f , g ⟩ (prefix ++ₚ compile ⟨ f , g ⟩ ++ₚ suffix) s s₅ x (program-length prefix)

    -----------------------------------------------------------------
    -- Curry Glue: curry f
    -----------------------------------------------------------------

    curry-setup : ∀ {A B C : Type} (f : IR (A * B) C)
      (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
      Preconditions {A} s x prefix (ir-stack-requirement (curry f)) →
      let prog = prefix ++ₚ compile (curry f) ++ₚ suffix
          offset = program-length prefix
      in ∃[ s₁ ] CurrySpecs.SetupPost f prog offset s s₁ x

    curry-combine :
      (ih : ∀ {A B : Type} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
            Preconditions {A} s x prefix (ir-stack-requirement ir) →
            ApplyWFInput (ClosureDom A) (ClosureCod A) (prefix ++ₚ compile ir ++ₚ suffix) s (closureOf A x) →
            ∃[ s' ] IRCorrectness ir (prefix ++ₚ compile ir ++ₚ suffix) s s' x (program-length prefix)) →
      ∀ {A B C : Type} (f : IR (A * B) C)
      (prefix suffix : Program) (x : ⟦ A ⟧) (s s₁ : State) →
      let prog = prefix ++ₚ compile (curry f) ++ₚ suffix
          offset = program-length prefix
      in CurrySpecs.SetupPost f prog offset s s₁ x →
      IRCorrectness (curry f) prog s s₁ x offset

    -----------------------------------------------------------------
    -- Case Glue: [ f , g ]
    -----------------------------------------------------------------

    case-left-context : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) → Program × Program

    case-right-context : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) → Program × Program

    case-dispatch-left : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) (a : ⟦ A ⟧) (s : State) →
      Preconditions {A ⊕ B} s (inj₁ a) prefix (ir-stack-requirement [ f , g ]) →
      let prog = prefix ++ₚ compile [ f , g ] ++ₚ suffix
          offset-f = program-length (proj₁ (case-left-context f g prefix suffix))
      in ∃[ s₁ ] CaseSpecs.DispatchLeftPost f g prog offset-f s s₁ a

    case-dispatch-enables-f : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) (a : ⟦ A ⟧) (s s₁ : State) →
      let prog = prefix ++ₚ compile [ f , g ] ++ₚ suffix
          offset-f = program-length (proj₁ (case-left-context f g prefix suffix))
      in CaseSpecs.DispatchLeftPost f g prog offset-f s s₁ a →
      Preconditions {A} s₁ a (proj₁ (case-left-context f g prefix suffix)) (ir-stack-requirement f)

    case-left-cleanup : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) (a : ⟦ A ⟧) (s s₁ s₂ : State) →
      let prog = prefix ++ₚ compile [ f , g ] ++ₚ suffix
          offset-f = program-length (proj₁ (case-left-context f g prefix suffix))
          offset-end = program-length prefix + compile-length [ f , g ]
      -- Original preconditions (needed for capacity/invariant restoration)
      in Preconditions {A ⊕ B} s (inj₁ a) prefix (ir-stack-requirement [ f , g ]) →
      CaseSpecs.DispatchLeftPost f g prog offset-f s s₁ a →
      IRCorrectness f (proj₁ (case-left-context f g prefix suffix) ++ₚ compile f ++ₚ proj₂ (case-left-context f g prefix suffix)) s₁ s₂ a (program-length (proj₁ (case-left-context f g prefix suffix))) →
      ∃[ s₃ ] CaseSpecs.CleanupPost f g prog offset-end s s₂ s₃ (eval f a)

    case-left-combine : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) (a : ⟦ A ⟧) (s s₁ s₂ s₃ : State) →
      let prog = prefix ++ₚ compile [ f , g ] ++ₚ suffix
          offset-f = program-length (proj₁ (case-left-context f g prefix suffix))
          offset-end = program-length prefix + compile-length [ f , g ]
      in CaseSpecs.DispatchLeftPost f g prog offset-f s s₁ a →
      IRCorrectness f (proj₁ (case-left-context f g prefix suffix) ++ₚ compile f ++ₚ proj₂ (case-left-context f g prefix suffix)) s₁ s₂ a (program-length (proj₁ (case-left-context f g prefix suffix))) →
      CaseSpecs.CleanupPost f g prog offset-end s s₂ s₃ (eval f a) →
      IRCorrectness [ f , g ] (prefix ++ₚ compile [ f , g ] ++ₚ suffix) s s₃ (inj₁ a) (program-length prefix)

    case-dispatch-right : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) (b : ⟦ B ⟧) (s : State) →
      Preconditions {A ⊕ B} s (inj₂ b) prefix (ir-stack-requirement [ f , g ]) →
      let prog = prefix ++ₚ compile [ f , g ] ++ₚ suffix
          offset-g = program-length (proj₁ (case-right-context f g prefix suffix))
      in ∃[ s₁ ] CaseSpecs.DispatchRightPost f g prog offset-g s s₁ b

    case-dispatch-enables-g : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) (b : ⟦ B ⟧) (s s₁ : State) →
      let prog = prefix ++ₚ compile [ f , g ] ++ₚ suffix
          offset-g = program-length (proj₁ (case-right-context f g prefix suffix))
      in CaseSpecs.DispatchRightPost f g prog offset-g s s₁ b →
      Preconditions {B} s₁ b (proj₁ (case-right-context f g prefix suffix)) (ir-stack-requirement g)

    case-right-cleanup : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) (b : ⟦ B ⟧) (s s₁ s₂ : State) →
      let prog = prefix ++ₚ compile [ f , g ] ++ₚ suffix
          offset-g = program-length (proj₁ (case-right-context f g prefix suffix))
          offset-end = program-length prefix + compile-length [ f , g ]
      -- Original preconditions (needed for capacity/invariant restoration)
      in Preconditions {A ⊕ B} s (inj₂ b) prefix (ir-stack-requirement [ f , g ]) →
      CaseSpecs.DispatchRightPost f g prog offset-g s s₁ b →
      IRCorrectness g (proj₁ (case-right-context f g prefix suffix) ++ₚ compile g ++ₚ proj₂ (case-right-context f g prefix suffix)) s₁ s₂ b (program-length (proj₁ (case-right-context f g prefix suffix))) →
      ∃[ s₃ ] CaseSpecs.CleanupPost f g prog offset-end s s₂ s₃ (eval g b)

    case-right-combine : ∀ {A B C : Type} (f : IR A C) (g : IR B C)
      (prefix suffix : Program) (b : ⟦ B ⟧) (s s₁ s₂ s₃ : State) →
      let prog = prefix ++ₚ compile [ f , g ] ++ₚ suffix
          offset-g = program-length (proj₁ (case-right-context f g prefix suffix))
          offset-end = program-length prefix + compile-length [ f , g ]
      in CaseSpecs.DispatchRightPost f g prog offset-g s s₁ b →
      IRCorrectness g (proj₁ (case-right-context f g prefix suffix) ++ₚ compile g ++ₚ proj₂ (case-right-context f g prefix suffix)) s₁ s₂ b (program-length (proj₁ (case-right-context f g prefix suffix))) →
      CaseSpecs.CleanupPost f g prog offset-end s s₂ s₃ (eval g b) →
      IRCorrectness [ f , g ] (prefix ++ₚ compile [ f , g ] ++ₚ suffix) s s₃ (inj₂ b) (program-length prefix)

    -----------------------------------------------------------------
    -- Apply: Uses Induction Hypothesis
    -----------------------------------------------------------------

    apply-correct :
      (ih : ∀ {A B : Type} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
            Preconditions {A} s x prefix (ir-stack-requirement ir) →
            ApplyWFInput (ClosureDom A) (ClosureCod A) (prefix ++ₚ compile ir ++ₚ suffix) s (closureOf A x) →
            ∃[ s' ] IRCorrectness ir (prefix ++ₚ compile ir ++ₚ suffix) s s' x (program-length prefix)) →
      ∀ {A B : Type} (prefix suffix : Program) (p : ⟦ (A ⇒ B) * A ⟧) (s : State) →
      Preconditions {(A ⇒ B) * A} s p prefix (ir-stack-requirement (apply {A} {B})) →
      ApplyWFInput A B (prefix ++ₚ compile (apply {A} {B}) ++ₚ suffix) s (closureOf ((A ⇒ B) * A) p) →
      ∃[ s' ] IRCorrectness (apply {A} {B}) (prefix ++ₚ compile (apply {A} {B}) ++ₚ suffix) s s' p (program-length prefix)
