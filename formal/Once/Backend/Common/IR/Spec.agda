------------------------------------------------------------------------
-- Once.Backend.Common.IR.Spec
--
-- Architecture-independent correctness specifications for IR.
--
-- This module defines WHAT correctness means for each IR constructor,
-- parameterized by architecture-specific details.
--
-- DESIGN PRINCIPLE: These types are extracted from X86's working proofs,
-- not invented abstractly. They match what X86 actually provides.
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; curry; apply; [_,_]; inl; inr; fst; snd; arr; unfold; fold)
open import Once.Type using (Type; _*_; _⇒_; _⇒[_]_; Eff; Unit; Void; Int; Float; Str; Buffer; TVar; Fix) renaming (_+_ to _⊕_)
open import Once.Semantics using (⟦_⟧; eval; encode; Closure)

module Once.Backend.Common.IR.Spec where

open import Data.Nat using (ℕ; _+_; _∸_; _>_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Abstract Machine Interface
--
-- Core types and operations each architecture provides.
-- Derived from X86's working implementation, designed to generalize
-- to AArch64 and RISC-V.
------------------------------------------------------------------------

-- | Word type: ℕ, matching the semantic layer (Once.Memory.Word = ℕ)
-- This is fixed rather than parameterized since all architectures and
-- the semantic encode/Closure use ℕ as the word type.
Word : Set
Word = ℕ

record MachineInterface : Set₁ where
  infixr 5 _++ₚ_

  field
    -- Core types
    State : Set
    Program : Set
    Memory : Set

    -- State accessors
    pc : State → ℕ
    halted : State → Bool
    memory : State → Memory

    -- Register accessors (architecture names the registers)
    -- Input register: where function arguments arrive (rdi / x0 / a0)
    input-value : State → Word
    -- Output register: where results are placed (rax / x0 / a0)
    output-value : State → Word

    -- Memory operations
    readMem : Memory → Word → Maybe Word

    -- Program operations
    program-length : Program → ℕ
    empty-program : Program
    empty-program-length : program-length empty-program ≡ 0

    -- Program concatenation (for prefix/suffix patterns)
    _++ₚ_ : Program → Program → Program
    ++ₚ-length : ∀ (p₁ p₂ : Program) → program-length (p₁ ++ₚ p₂) ≡ program-length p₁ + program-length p₂
    ++ₚ-assoc : ∀ (p₁ p₂ p₃ : Program) → (p₁ ++ₚ p₂) ++ₚ p₃ ≡ p₁ ++ₚ (p₂ ++ₚ p₃)
    ++ₚ-empty-left : ∀ (p : Program) → empty-program ++ₚ p ≡ p
    ++ₚ-empty-right : ∀ (p : Program) → p ++ₚ empty-program ≡ p

    -- Execution
    step : Program → State → Maybe State

------------------------------------------------------------------------
-- Invariant Interface
--
-- Architecture-specific invariants that must be maintained.
-- Extracted from X86's StackInvariant, RbpInvariant, etc.
------------------------------------------------------------------------

record InvariantInterface (M : MachineInterface) : Set₁ where
  open MachineInterface M

  field
    -- Stack invariant (frame pointer discipline)
    StackInvariant : State → Set

    -- Stack capacity (enough space for N slots)
    StackCapacity : State → ℕ → Set

    -- Frame pointer invariant (rbp chain valid, etc.)
    FramePtrInvariant : State → Set

    -- Saved registers preserved between states
    SavedRegsPreserved : State → State → Set

    -- RSP/SP delta tracking (for capacity threading)
    -- Returns how much stack pointer changes after executing IR
    rsp-delta-slots : State → State → ℕ → Set

    -- Memory regions
    InStack : Word → Set
    InHeap : Word → Set
    InCode : Word → Set

    -- Memory preservation predicates
    HeapPreserved : State → State → Set
    CodePreserved : State → State → Set
    FramePreserved : State → State → Set

    -- Frame setup information from dispatch (for cleanup derivation)
    -- Records arch-specific facts about how dispatch set up the call frame.
    -- Used by cleanup to derive register/memory state after branch execution.
    FrameSetupInfo : State → State → Set

------------------------------------------------------------------------
-- Validity Interface
--
-- ValidAt predicate: "value v is correctly represented at addr in memory"
------------------------------------------------------------------------

record ValidityInterface (M : MachineInterface) (Inv : InvariantInterface M) : Set₁ where
  open MachineInterface M
  open InvariantInterface Inv

  field
    -- Core validity predicate
    ValidAt : ∀ {A : Type} → ⟦ A ⟧ → Word → Memory → Set

    -- Validity preserved under heap-preserving operations
    valid-preserved-heap : ∀ {A} {v : ⟦ A ⟧} {addr : Word} {m₁ m₂ : Memory} →
      ValidAt v addr m₁ →
      (∀ a → InHeap a → readMem m₂ a ≡ readMem m₁ a) →
      ValidAt v addr m₂

------------------------------------------------------------------------
-- Code Generation Interface
------------------------------------------------------------------------

record CodeGenInterface (M : MachineInterface) : Set₁ where
  open MachineInterface M

  field
    -- Compile IR to program
    compile : ∀ {A B} → IR A B → Program

    -- Length of compiled code
    compile-length : ∀ {A B} → IR A B → ℕ

    -- Stack requirements
    ir-stack-requirement : ∀ {A B} → IR A B → ℕ
    ir-output-capacity : ∀ {A B} → IR A B → ℕ
    ir-rsp-delta : ∀ {A B} → IR A B → ℕ

    -- Apply overhead: stack slots consumed by apply glue code (before thunk)
    apply-overhead : ℕ

------------------------------------------------------------------------
-- ClosureWFOutput: Optional closure well-formedness from curry
--
-- When curry executes, it produces a closure whose code-ptr points to
-- valid thunk code within the program. Apply consumes this proof.
--
-- The structure is universal; the WF predicate is architecture-specific.
------------------------------------------------------------------------

-- | Closure well-formedness predicate type
-- Each architecture provides its own ClosureWF predicate with
-- architecture-specific preconditions and guarantees.
ClosureWFPredicate : Set → Set₁
ClosureWFPredicate Program = ∀ {E A B : Type} →
  Program → ℕ → ⟦ E ⟧ → (⟦ A ⟧ → ⟦ B ⟧) → Set

-- | Output type tracking optional closure well-formedness
-- Most IRs produce no-closure; curry produces has-closure with WF proof.
data ClosureWFOutput {Program : Set}
    (ClosureWF : ClosureWFPredicate Program)
    (prog : Program) : Set₁ where
  no-closure : ClosureWFOutput ClosureWF prog
  has-closure : ∀ {E A B : Type}
    (closure-addr code-ptr : ℕ) (env : ⟦ E ⟧)
    (semantics : ⟦ A ⟧ → ⟦ B ⟧)
    (wf : ClosureWF {E} {A} {B} prog code-ptr env semantics) →
    ClosureWFOutput ClosureWF prog

------------------------------------------------------------------------
-- ClosureTypesOf: Extract closure domain/codomain from a Type
--
-- For apply {A} {B} : IR ((A ⇒ B) * A) B, the input type is (A ⇒ B) * A.
-- ClosureTypesOf extracts (A, B) from this. Similarly for curry's output
-- type (A ⇒ B). This enables type-safe threading through compose:
-- g : IR X Y and f : IR Y Z share type Y, so ClosureTypesOf Y gives
-- the same closure types at both ends.
------------------------------------------------------------------------

ClosureTypesOf : Type → Type × Type
ClosureTypesOf ((A ⇒[ _ ] B) * _) = (A , B)
ClosureTypesOf (A ⇒[ _ ] B) = (A , B)
ClosureTypesOf _ = (Unit , Unit)

-- Projections for readability
ClosureDom : Type → Type
ClosureDom T = proj₁ (ClosureTypesOf T)

ClosureCod : Type → Type
ClosureCod T = proj₂ (ClosureTypesOf T)

-- | Extract the closure value from a typed semantic value
--
-- For (A ⇒ B) * _, returns the first component (the closure in a pair)
-- For A ⇒ B, returns the value itself (it IS a closure)
-- For other types, returns a dummy (only used with no-apply-wf)
private
  dummy-closure : Closure Unit Unit
  dummy-closure = record { env-addr = 0 ; semantics = λ _ → tt }

closureOf : (T : Type) → ⟦ T ⟧ → Closure (ClosureDom T) (ClosureCod T)
closureOf ((A ⇒[ _ ] B) * _) (cl , _) = cl
closureOf (A ⇒[ _ ] B) v = v
-- Pair cases where first component is NOT an arrow (ClosureTypesOf = (Unit,Unit))
closureOf (Unit * _) _ = dummy-closure
closureOf (Void * _) _ = dummy-closure
closureOf ((A * B) * _) _ = dummy-closure
closureOf ((A ⊕ B) * _) _ = dummy-closure
closureOf (Int * _) _ = dummy-closure
closureOf (Float * _) _ = dummy-closure
closureOf (Str * _) _ = dummy-closure
closureOf (Buffer * _) _ = dummy-closure
closureOf ((TVar _) * _) _ = dummy-closure
closureOf ((Eff _ _) * _) _ = dummy-closure
closureOf ((Fix _) * _) _ = dummy-closure
-- Non-pair, non-arrow cases (ClosureTypesOf = (Unit,Unit))
closureOf Unit _ = dummy-closure
closureOf Void _ = dummy-closure
closureOf (_ ⊕ _) _ = dummy-closure
closureOf Int _ = dummy-closure
closureOf Float _ = dummy-closure
closureOf Str _ = dummy-closure
closureOf Buffer _ = dummy-closure
closureOf (TVar _) _ = dummy-closure
closureOf (Eff _ _) _ = dummy-closure
closureOf (Fix _) _ = dummy-closure

------------------------------------------------------------------------
-- IRCorrectness: The Core Specification
--
-- This matches X86's IRStarResultV structure exactly.
-- Architecture provides this record; Common defines what fields mean.
--
-- Note: Star is provided as a parameter rather than via an interface,
-- since each architecture's Star has slightly different constructor
-- signatures (X86's step* requires halted proof, etc.)
------------------------------------------------------------------------

module IRSpecs
    (M : MachineInterface)
    (Inv : InvariantInterface M)
    (Val : ValidityInterface M Inv)
    (CG : CodeGenInterface M)
    (Star : MachineInterface.Program M → MachineInterface.State M → MachineInterface.State M → Set)
    (ClosureWF : ClosureWFPredicate (MachineInterface.Program M))
    (wf-thunk-capacity : ∀ {E A B : Type} {prog : MachineInterface.Program M} {cp : ℕ}
                           {env : ⟦ E ⟧} {sem : ⟦ A ⟧ → ⟦ B ⟧} →
                         ClosureWF {E} {A} {B} prog cp env sem → ℕ)
    (wf-cap-upper-bound : ∀ {E A B : Type} {prog : MachineInterface.Program M} {cp : ℕ}
                            {env : ⟦ E ⟧} {sem : ⟦ A ⟧ → ⟦ B ⟧} →
                          ClosureWF {E} {A} {B} prog cp env sem → ℕ)
    where

  open MachineInterface M
  open InvariantInterface Inv
  open ValidityInterface Val
  open CodeGenInterface CG

  -- Alias for ClosureWFOutput with the architecture's WF predicate
  ClosureWFOut : Program → Set₁
  ClosureWFOut = ClosureWFOutput ClosureWF

  -- | ApplyWFInput: Everything apply needs from a previous curry
  --
  -- Threading: curry produces → compose threads → apply consumes
  -- Carries: ClosureWF proof, env validity, sufficient capacity
  --
  -- A and B are the closure's domain/codomain types. They are
  -- determined by ClosureTypesOf applied to the IR's input type,
  -- ensuring they match structurally in compose threading.
  --
  -- cl is the closure value this proof describes. In exec-closure-wf,
  -- cl = closureOf B (eval ir x). For apply's input, closureOf gives
  -- proj₁ p, so cl-eq directly bridges runtime and proof values.
  data ApplyWFInput (A B : Type) (prog : Program) (s : State)
                    (cl : Closure A B) : Set₁ where
    no-apply-wf : ApplyWFInput A B prog s cl
    apply-wf : ∀ {E : Type}
      (code-ptr : ℕ) (env : ⟦ E ⟧)
      (semantics : ⟦ A ⟧ → ⟦ B ⟧)
      (closure-addr : ℕ)  -- Address where closure is stored
      -- cl-eq: The closure value matches the WF proof's env/semantics.
      -- For curry, this is refl by computation (eval (curry f) x = record{...}).
      -- Eliminates the runtime-matches-proof bridge postulate.
      (cl-eq : cl ≡ record { env-addr = encode env ; semantics = semantics })
      (wf : ClosureWF {E} {A} {B} prog code-ptr env semantics)
      -- closure-at: Memory layout proof showing code-ptr is at closure-addr+8.
      -- Enables proving code-ptr from ValidAt decomposition = code-ptr from WF.
      (closure-at : ClosureAtS (encode env) code-ptr closure-addr (memory s))
      -- closure-addr-unique: The closure is only valid at closure-addr.
      -- This captures that closures aren't duplicated in memory.
      -- Enables proving apply-closure-addr = closure-addr at apply time.
      (closure-addr-unique : (cl-addr : ℕ) → ValidAt cl cl-addr (memory s) → cl-addr ≡ closure-addr)
      -- env-valid: uses encode env directly (not arbitrary env-addr).
      -- Eliminates the addr-is-encode bridge postulate.
      (env-valid : ValidAt env (encode env) (memory s))
      -- cap: uses the exact formula (not arbitrary cap-needed).
      -- Eliminates the cap-matches bridge postulate.
      (cap : StackCapacity s (apply-overhead + wf-thunk-capacity wf))
      → ApplyWFInput A B prog s cl

  -- | Extract cap-upper-bound from ApplyWFInput
  -- For no-apply-wf, returns 0 (trivially ≤ any ir-stack-requirement)
  -- For apply-wf, returns the wf's cap-upper-bound
  cwf-cap-bound : ∀ {A B : Type} {prog : Program} {s : State} {cl : Closure A B} →
                  ApplyWFInput A B prog s cl → ℕ
  cwf-cap-bound no-apply-wf = 0
  cwf-cap-bound (apply-wf {E} cp env sem cl-addr cl-eq wf _ _ _ _) = wf-cap-upper-bound wf

  -- Preconditions for IR execution
  -- Matches X86's run-*-star-vv preconditions exactly
  record Preconditions {A : Type} (s : State) (x : ⟦ A ⟧)
                       (prefix : Program) (cap-needed : ℕ) : Set₁ where
    field
      pre-halted : halted s ≡ false
      pre-pc : pc s ≡ program-length prefix
      pre-input-valid : ValidAt x (input-value s) (memory s)
      pre-input-is-encode : input-value s ≡ encode x
      pre-stack-inv : StackInvariant s
      pre-capacity : StackCapacity s cap-needed
      pre-frame-inv : FramePtrInvariant s

  -- Core correctness result
  -- Matches X86's IRStarResultV structure
  record IRCorrectness {A B : Type} (ir : IR A B)
      (prog : Program) (s s' : State) (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
    field
      -- Execution
      exec-star : Star prog s s'
      exec-halted : halted s' ≡ false
      exec-pc : pc s' ≡ offset + compile-length ir

      -- Output validity (THE key correctness property)
      exec-output-valid : ValidAt (eval ir x) (output-value s') (memory s')

      -- Output encode equality (for compose threading: f's input-encode from g's output-encode)
      exec-output-is-encode : output-value s' ≡ encode (eval ir x)

      -- Register/state preservation
      exec-saved-regs : SavedRegsPreserved s s'

      -- RSP delta tracking (needed for capacity threading through compose)
      -- rsp s' = rsp s ∸ slots (ir-rsp-delta ir)
      exec-rsp-delta : rsp-delta-slots s s' (ir-rsp-delta ir)

      -- Memory preservation
      exec-heap-preserved : HeapPreserved s s'
      exec-code-preserved : CodePreserved s s'
      exec-frame-preserved : FramePreserved s s'

      -- Invariants maintained
      exec-stack-inv : StackInvariant s'
      exec-capacity : StackCapacity s' (ir-output-capacity ir)
      exec-frame-inv : FramePtrInvariant s'

      -- Closure well-formedness (produced by curry, consumed by apply)
      -- Types come from ClosureTypesOf B (the IR's output type)
      -- cl = closureOf B (eval ir x): the closure from the output value
      exec-closure-wf : ApplyWFInput (ClosureDom B) (ClosureCod B) prog s'
                           (closureOf B (eval ir x))

      -- Bound tracking: the cwf's cap-upper-bound is ≤ ir-stack-requirement
      -- This enables pair/case to derive StackCapacity for cwf at output state:
      -- 1. cwf.cap-upper-bound ≤ ir-stack-requirement ir (this field)
      -- 2. ir-stack-requirement ir ≤ ir-output-capacity ⟨f,g⟩ (by pair output formula)
      -- 3. apply+thunk ≤ cwf.cap-upper-bound (by cwf.cap-in-bound)
      -- 4. So apply+thunk ≤ ir-output-capacity ⟨f,g⟩, enabling capacity-from-larger
      exec-cwf-bound-in-req : cwf-cap-bound exec-closure-wf ≤ ir-stack-requirement ir

  ------------------------------------------------------------------------
  -- Phase Specifications for Composite IR
  --
  -- These match X86's phase result records.
  ------------------------------------------------------------------------

  module PairSpecs {A B C : Type} (f : IR C A) (g : IR C B) where

    -- After setup: registers saved, ready for f
    -- prog is the full program: prefix ++ₚ compile ⟨ f , g ⟩ ++ₚ suffix
    -- offset-f is program-length prefix-f (where f starts)
    record SetupPost (prog : Program) (offset-f : ℕ)
                     (s s₁ : State) (x : ⟦ C ⟧) : Set₁ where
      field
        -- State properties
        setup-halted : halted s₁ ≡ false
        setup-stack-inv : StackInvariant s₁
        setup-input-valid : ValidAt x (input-value s₁) (memory s₁)
        setup-input-is-encode : input-value s₁ ≡ encode x
        setup-capacity : StackCapacity s₁ (ir-stack-requirement f)
        setup-frame-inv : FramePtrInvariant s₁
        -- Execution evidence
        setup-star : Star prog s s₁
        setup-pc : pc s₁ ≡ offset-f
        setup-heap-preserved : HeapPreserved s s₁
        setup-code-preserved : CodePreserved s s₁
        setup-frame-preserved : FramePreserved s s₁

    -- After middle: f's result stored, ready for g
    -- prog is the full program
    -- offset-g is program-length prefix-g (where g starts)
    record MiddlePost (prog : Program) (offset-g : ℕ)
                      (s₁ s₂ s₃ : State) (x : ⟦ C ⟧) (fx : ⟦ A ⟧) : Set₁ where
      field
        -- State properties
        middle-halted : halted s₃ ≡ false
        middle-stack-inv : StackInvariant s₃
        middle-input-valid : ValidAt x (input-value s₃) (memory s₃)
        middle-input-is-encode : input-value s₃ ≡ encode x
        middle-capacity : StackCapacity s₃ (ir-stack-requirement g)
        middle-frame-inv : FramePtrInvariant s₃
        -- Execution evidence
        middle-star : Star prog s₂ s₃
        middle-pc : pc s₃ ≡ offset-g
        middle-heap-preserved : HeapPreserved s₂ s₃
        middle-code-preserved : CodePreserved s₂ s₃
        middle-frame-preserved : FramePreserved s₂ s₃

    -- After cleanup: pair constructed
    -- prog is the full program
    -- offset-end is program-length prefix + compile-length ⟨ f , g ⟩
    record CleanupPost (prog : Program) (offset-end : ℕ)
                       (s s₄ s₅ : State) (x : ⟦ C ⟧)
                       (fx : ⟦ A ⟧) (gx : ⟦ B ⟧) : Set₁ where
      field
        -- State properties
        cleanup-halted : halted s₅ ≡ false
        cleanup-stack-inv : StackInvariant s₅
        cleanup-capacity : StackCapacity s₅ (ir-output-capacity ⟨ f , g ⟩)
        cleanup-output-valid : ValidAt {A * B} (fx , gx) (output-value s₅) (memory s₅)
        cleanup-saved-regs : SavedRegsPreserved s s₅
        cleanup-frame-inv : FramePtrInvariant s₅
        -- Execution evidence
        cleanup-star : Star prog s₄ s₅
        cleanup-pc : pc s₅ ≡ offset-end
        cleanup-rsp-delta : rsp-delta-slots s s₅ (ir-rsp-delta ⟨ f , g ⟩)
        cleanup-heap-preserved : HeapPreserved s₄ s₅
        cleanup-code-preserved : CodePreserved s₄ s₅
        cleanup-frame-preserved : FramePreserved s₄ s₅

  module CurrySpecs {A B C : Type} (f : IR (A * B) C) where

    -- SetupPost includes execution evidence so combine can use it
    -- prog is the full program: prefix ++ₚ compile (curry f) ++ₚ suffix
    -- offset is program-length prefix
    record SetupPost (prog : Program) (offset : ℕ)
                     (s s₁ : State) (x : ⟦ A ⟧) : Set₁ where
      field
        -- State properties
        setup-halted : halted s₁ ≡ false
        setup-stack-inv : StackInvariant s₁
        setup-capacity : StackCapacity s₁ (ir-output-capacity (curry f))
        setup-output-valid : ValidAt {B ⇒ C} (eval (curry f) x) (output-value s₁) (memory s₁)
        setup-saved-regs : SavedRegsPreserved s s₁
        setup-frame-inv : FramePtrInvariant s₁
        -- Execution evidence (for combine to use)
        setup-star : Star prog s s₁
        setup-pc : pc s₁ ≡ offset + compile-length (curry f)
        setup-rsp-delta : rsp-delta-slots s s₁ (ir-rsp-delta (curry f))
        setup-heap-preserved : HeapPreserved s s₁
        setup-code-preserved : CodePreserved s s₁
        setup-frame-preserved : FramePreserved s s₁
        -- Closure environment info (for building ApplyWFInput in curry-combine)
        -- The environment x is valid at its encoding (encode x) in memory.
        -- This comes from pre-input-valid + pre-input-is-encode + heap preservation.
        setup-env-valid : ValidAt x (encode x) (memory s₁)

  module CaseSpecs {A B C : Type} (f : IR A C) (g : IR B C) where

    record DispatchLeftPost (prog : Program) (offset-f : ℕ)
                            (s s₁ : State) (a : ⟦ A ⟧) : Set₁ where
      field
        dispatch-halted : halted s₁ ≡ false
        dispatch-stack-inv : StackInvariant s₁
        dispatch-input-valid : ValidAt a (input-value s₁) (memory s₁)
        dispatch-input-is-encode : input-value s₁ ≡ encode a
        dispatch-capacity : StackCapacity s₁ (ir-stack-requirement f)
        dispatch-frame-inv : FramePtrInvariant s₁
        dispatch-star : Star prog s s₁
        dispatch-pc : pc s₁ ≡ offset-f
        dispatch-heap-preserved : HeapPreserved s s₁
        dispatch-code-preserved : CodePreserved s s₁
        dispatch-frame-preserved : FramePreserved s s₁
        -- Frame setup facts (for cleanup derivation)
        dispatch-frame-setup : FrameSetupInfo s s₁

    record DispatchRightPost (prog : Program) (offset-g : ℕ)
                             (s s₁ : State) (b : ⟦ B ⟧) : Set₁ where
      field
        dispatch-halted : halted s₁ ≡ false
        dispatch-stack-inv : StackInvariant s₁
        dispatch-input-valid : ValidAt b (input-value s₁) (memory s₁)
        dispatch-input-is-encode : input-value s₁ ≡ encode b
        dispatch-capacity : StackCapacity s₁ (ir-stack-requirement g)
        dispatch-frame-inv : FramePtrInvariant s₁
        dispatch-star : Star prog s s₁
        dispatch-pc : pc s₁ ≡ offset-g
        dispatch-heap-preserved : HeapPreserved s s₁
        dispatch-code-preserved : CodePreserved s s₁
        dispatch-frame-preserved : FramePreserved s s₁
        -- Frame setup facts (for cleanup derivation)
        dispatch-frame-setup : FrameSetupInfo s s₁

    -- After cleanup: frame restored, output preserved
    -- prog is the full program
    -- offset-end is program-length prefix + compile-length [ f , g ]
    -- s is the original state (for global saved-regs/rsp-delta)
    -- s₂ is the state after f (or g) runs
    -- s₃ is the state after cleanup
    record CleanupPost (prog : Program) (offset-end : ℕ)
                       (s s₂ s₃ : State) (cx : ⟦ C ⟧) : Set₁ where
      field
        -- State properties
        cleanup-halted : halted s₃ ≡ false
        cleanup-stack-inv : StackInvariant s₃
        cleanup-capacity : StackCapacity s₃ (ir-output-capacity [ f , g ])
        cleanup-output-valid : ValidAt cx (output-value s₃) (memory s₃)
        cleanup-saved-regs : SavedRegsPreserved s s₃
        cleanup-frame-inv : FramePtrInvariant s₃
        -- Execution evidence
        cleanup-star : Star prog s₂ s₃
        cleanup-pc : pc s₃ ≡ offset-end
        cleanup-rsp-delta : rsp-delta-slots s s₃ (ir-rsp-delta [ f , g ])
        -- Local preservation (s₂ → s₃, for chaining in combine)
        cleanup-heap-preserved : HeapPreserved s₂ s₃
        cleanup-code-preserved : CodePreserved s₂ s₃
        cleanup-frame-preserved : FramePreserved s₂ s₃

------------------------------------------------------------------------
-- ClosuresWF: WF for all closures in values of a given type
--
-- This type family computes what WF information is needed for values
-- of each type. Used to thread WF through composition.
--
-- Pattern extracted from RiscV64, generalized for all architectures.
-- Each architecture provides its own ApplyInputWF predicate.
------------------------------------------------------------------------

-- | ApplyInputWF predicate type
-- Each architecture provides a predicate that captures:
--   - code-ptr, env info, semantics, plus arch-specific requirements
-- This is existentially quantified to hide internal details.
ApplyInputWFPredicate : Set → Set₁
ApplyInputWFPredicate Program = Type → Type → Program → Set

-- | ClosuresWF module parameterized by architecture's ApplyInputWF
-- This provides the type family and helper functions.
module ClosuresWFModule {Program : Set} (ApplyInputWF : ApplyInputWFPredicate Program) where

  -- | WF for all closures that might appear in a value of type T
  -- For arrow types: architecture's ApplyInputWF predicate
  -- For products: WF for both components
  -- For sums: WF for both branches (conservative)
  -- For other types: trivial (no closures)
  ClosuresWF : Type → Program → Set
  ClosuresWF Unit prog = ⊤
  ClosuresWF Void prog = ⊤
  ClosuresWF Int prog = ⊤
  ClosuresWF Float prog = ⊤
  ClosuresWF Str prog = ⊤
  ClosuresWF Buffer prog = ⊤
  ClosuresWF (TVar _) prog = ⊤
  ClosuresWF (Eff _ _) prog = ⊤
  ClosuresWF (A * B) prog = ClosuresWF A prog × ClosuresWF B prog
  ClosuresWF (A ⊕ B) prog = ClosuresWF A prog × ClosuresWF B prog
  ClosuresWF (A ⇒[ _ ] B) prog = ApplyInputWF A B prog
  ClosuresWF (Fix F) prog = ⊤  -- Recursive types: assume no closures for now

  -- | Trivial WF for types without closures
  -- IMPORTANT: This function should ONLY be called for types that genuinely
  -- don't contain closures. Arrow types must get their WF from curry's output.
  -- If called with an arrow type, returns an error marker.
  trivialWF : ∀ T prog → ClosuresWF T prog
  trivialWF Unit prog = tt
  trivialWF Void prog = tt
  trivialWF Int prog = tt
  trivialWF Float prog = tt
  trivialWF Str prog = tt
  trivialWF Buffer prog = tt
  trivialWF (TVar _) prog = tt
  trivialWF (Eff _ _) prog = tt
  trivialWF (A * B) prog = trivialWF A prog , trivialWF B prog
  trivialWF (A ⊕ B) prog = trivialWF A prog , trivialWF B prog
  trivialWF (A ⇒[ _ ] B) prog = error-trivialWF-called-with-arrow
    where postulate error-trivialWF-called-with-arrow : ApplyInputWF A B prog
          -- ERROR: Arrow types should get WF from curry's output, not trivialWF!
  trivialWF (Fix F) prog = tt

  -- | Extract WF for first component of a pair
  fstWF : ∀ {A B} {prog} → ClosuresWF (A * B) prog → ClosuresWF A prog
  fstWF (wf-a , _) = wf-a

  -- | Extract WF for second component of a pair
  sndWF : ∀ {A B} {prog} → ClosuresWF (A * B) prog → ClosuresWF B prog
  sndWF (_ , wf-b) = wf-b

  -- | Build WF for a pair from components
  pairWF : ∀ {A B} {prog} → ClosuresWF A prog → ClosuresWF B prog → ClosuresWF (A * B) prog
  pairWF wf-a wf-b = wf-a , wf-b

  -- | Extract WF for apply input: from (A ⇒ B) * A, get the closure's WF
  applyInputWF : ∀ {A B} {prog} → ClosuresWF ((A ⇒ B) * A) prog → ApplyInputWF A B prog
  applyInputWF (wf-closure , _) = wf-closure

  -- | Extract WF for left branch of a sum
  inlWF : ∀ {A B} {prog} → ClosuresWF (A ⊕ B) prog → ClosuresWF A prog
  inlWF (wf-a , _) = wf-a

  -- | Extract WF for right branch of a sum
  inrWF : ∀ {A B} {prog} → ClosuresWF (A ⊕ B) prog → ClosuresWF B prog
  inrWF (_ , wf-b) = wf-b

------------------------------------------------------------------------
-- Summary
--
-- This module defines architecture-independent types that MATCH what
-- X86 actually provides:
--
--   - Preconditions: includes input ValidAt (X86 has this!)
--   - IRCorrectness: matches IRStarResultV fields
--   - Phase specs: match X86's phase result records
--   - ClosuresWF: type family for threading WF through composition
--
-- Key additions from original design:
--   - input-value in MachineInterface (rdi / x0 / a0)
--   - FramePtrInvariant in InvariantInterface (RbpInvariant)
--   - pre-input-valid in Preconditions
--   - StarInterface (each arch provides Star)
--   - ClosuresWFModule for WF threading (from RiscV64)
------------------------------------------------------------------------
