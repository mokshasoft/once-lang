------------------------------------------------------------------------
-- Once.Backend.X86.Correct.PrimContract
--
-- Unified interface for domain compilers (Arith, IO, etc.)
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- A PrimContract bundles:
--   1. Opaque assembly (CCC doesn't parse it)
--   2. A proof that executing it is correct (done in domain compiler's model)
--
-- Key insight: CCC treats primitives as BLACK BOXES.
-- - CCC doesn't need to understand the assembly instructions
-- - CCC only needs to know the INPUT/OUTPUT behavior
-- - The domain compiler (Arith) proves correctness in its own model
--
-- DESIGN: Opaque assembly + effect specification
-- - Assembly: List String (or abstract type) for code emission
-- - Effect: Specification of what the primitive does to state
-- - Proof: Done in domain compiler, trusted at boundary
--
-- This eliminates two postulates:
--   - evalPrim (SemanticBase.agda) - semantics now explicit parameter
--   - run-prim-star-vv (StarBase.agda) - effect now specified by contract
------------------------------------------------------------------------

module Once.Backend.X86.Correct.PrimContract where

open import Once.Type using (Type)
open import Once.SemanticBase using (⟦_⟧)
open import Once.Memory using (Word)
open import Once.Backend.Common.Memory using (Memory; readMem)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.X86.Semantics using (State; readReg)
open Once.Backend.X86.Semantics.State using (halted; pc; regs; memory)
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackCapacityBase using (StackCapacity)

-- For opaque assembly representation
open import Data.String using (String)
open import Data.List using (List; [])

open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _≥_; _+_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Once.Backend.X86.Syntax using (Reg; rax; rdi; r14; r15; rbp; rsp; Program)
open import Once.Backend.X86.Correct.Star using (Star)

------------------------------------------------------------------------
-- PrimEffect: What a primitive does to machine state
------------------------------------------------------------------------

-- | Effect specification: postconditions after executing the primitive
--
-- This is what CCC needs to know - not HOW the primitive works,
-- just WHAT it produces.
--
-- The domain compiler proves these properties hold for its assembly.
-- CCC trusts the specification at the boundary.
--
record PrimEffect {A B : Type} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
                  (prog : Program) (s s' : State) : Set where
  field
    -- Execution trace: machine steps from s to s' following prog
    -- This is the key proof that the assembly actually executes.
    -- Domain compiler (Arith) proves this for its specific instructions.
    effect-star : Star prog s s'

    -- Machine still running after primitive
    effect-halted : halted s' ≡ false

    -- Semantic correctness: result is valid at rax
    -- Domain compiler (Arith) constructs this using valid-int for Int results.
    -- CCC receives this proof without needing to understand the type.
    effect-result-valid : ValidAt (sem x) (readReg (regs s') rax) (memory s')

    -- Register preservation (callee-saved by ABI)
    effect-r14 : readReg (regs s') r14 ≡ readReg (regs s) r14
    effect-r15 : readReg (regs s') r15 ≡ readReg (regs s) r15
    effect-rbp : readReg (regs s') rbp ≡ readReg (regs s) rbp
    effect-rsp : readReg (regs s') rsp ≡ readReg (regs s) rsp

    -- Memory preservation (Ownership model)
    -- Addresses ≥ entry-rsp are not modified (caller's frame, heap, code)
    effect-mem-preserved : ∀ addr → addr ≥ readReg (regs s) rsp →
                           readMem (memory s') addr ≡ readMem (memory s) addr

    -- Invariants preserved
    effect-stack-inv : StackInvariant s'
    effect-rbp-inv : RbpInvariant s'

    -- PC advanced by assembly length
    effect-pc : pc s' ≡ pc s + Data.List.length prog

------------------------------------------------------------------------
-- PrimContract Record
------------------------------------------------------------------------

-- | PrimContract: What a domain compiler must provide
--
-- Parameterized by:
--   A, B  : Input and output types
--   sem   : Semantic function (what the operation computes)
--
-- DESIGN: Opaque assembly + effect specification
-- - prim-assembly: Opaque instruction list (CCC doesn't parse)
-- - prim-effect: What executing the assembly does
-- - The domain compiler proves prim-effect in its own model
--
-- The semantic function is EXPLICIT - no postulated evalPrim needed.
-- Domain compilers (Arith, IO, etc.) provide their own semantics.
--
record PrimContract {A B : Type} (sem : ⟦ A ⟧ → ⟦ B ⟧) : Set where
  field
    ------------------------------------------------------------------------
    -- Compiled output
    ------------------------------------------------------------------------

    -- | The compiled assembly (x86 instructions)
    -- Domain compiler provides actual instructions, CCC emits them directly
    prim-assembly : Program

    -- | Assembly must be non-empty (at least 1 instruction)
    -- This ensures compile-length ir > 0 for all IR terms
    prim-nonempty : Data.List.length prim-assembly ≥ 1

    -- | Stack slots required by this primitive
    prim-stack-requirement : ℕ

    ------------------------------------------------------------------------
    -- Effect specification
    ------------------------------------------------------------------------

    -- | Main correctness: executing the assembly produces correct result
    --
    -- Preconditions:
    --   - Machine not halted
    --   - PC at start of assembly within program
    --   - Input valid at rdi (ValidAt-based interface)
    --   - Stack/Rbp invariants hold
    --   - Sufficient stack capacity
    --
    -- Postconditions (bundled in PrimEffect):
    --   - Execution trace (Star) from s to s'
    --   - Machine still running
    --   - Result valid at rax (ValidAt-based)
    --   - Callee-saved registers preserved
    --   - Memory above entry-rsp preserved
    --   - Invariants preserved
    --   - PC advanced correctly
    --
    -- Note: The domain compiler proves this including the Star trace.
    -- This fully specifies the primitive's behavior - no postulates needed.
    --
    prim-correct : ∀ (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
      -- Preconditions
      halted s ≡ false →
      pc s ≡ Data.List.length prefix →
      ValidAt x (readReg (regs s) rdi) (memory s) →  -- ValidAt-based input
      StackInvariant s →
      StackCapacity s prim-stack-requirement →
      RbpInvariant s →
      -- Postconditions: ∃ final state with correct effect
      let prog = prefix Data.List.++ prim-assembly Data.List.++ suffix
      in ∃[ s' ] PrimEffect sem x prog s s'

------------------------------------------------------------------------
-- Contract Composition Helpers
------------------------------------------------------------------------

-- | Identity primitive: returns input unchanged
id-sem : ∀ {A} → ⟦ A ⟧ → ⟦ A ⟧
id-sem x = x

-- | Compose two semantic functions
compose-sem : ∀ {A B C} → (⟦ B ⟧ → ⟦ C ⟧) → (⟦ A ⟧ → ⟦ B ⟧) → ⟦ A ⟧ → ⟦ C ⟧
compose-sem g f x = g (f x)

------------------------------------------------------------------------
-- Contract Registry (to be populated by domain compilers)
------------------------------------------------------------------------

-- | A registered primitive with its contract
record RegisteredPrim : Set₁ where
  field
    reg-A reg-B : Type
    reg-sem : ⟦ reg-A ⟧ → ⟦ reg-B ⟧
    reg-contract : PrimContract reg-sem

------------------------------------------------------------------------
-- CCC Integration Notes
------------------------------------------------------------------------

-- DESIGN: CCC treats primitives as opaque black boxes.
--
-- At the Prim boundary in MutualIR/CodeGen:
--
-- 1. CodeGen emits prim-assembly directly (actual x86 instructions)
--
-- 2. Correctness uses prim-correct to get PrimEffect:
--    - Input: CCC provides ValidAt x rdi m (from previous computation)
--    - Output: PrimEffect provides:
--      * effect-star: Star execution trace (proves assembly executes)
--      * effect-result-valid: ValidAt (sem x) rax m'
--      * All register/memory preservation proofs
--    - Domain compiler proves ALL of this, including the Star trace.
--
-- 3. For Int results, domain compiler uses valid-int constructor:
--    - Arith compiler knows ⟦ Int ⟧ and encode
--    - Constructs: valid-int refl : ValidAt n n m (when encode is identity)
--    - CCC receives ValidAt proof, never reasons about Int
--
-- When IR has: Prim : (sem : ⟦ A ⟧ → ⟦ B ⟧) → PrimContract sem → IR A B
-- Then:
--   eval (Prim sem _) x = sem x  -- No evalPrim postulate!
--   compile (Prim _ contract) = prim-assembly contract  -- Direct emission
--   run-prim-star-vv: unpack prim-correct  -- No postulate, proven from contract!

------------------------------------------------------------------------
-- X86 Contract Interface
------------------------------------------------------------------------

-- | X86's implementation of ContractInterface using PrimContract
--
-- This allows the IR to be instantiated with X86's proven contracts
-- instead of TrivialContract.
--
-- The instruction type is X86's Instr, and contract-program returns
-- the actual assembly from prim-assembly.
--
open import Once.Backend.ContractInterface using (ContractInterface)
open import Once.Backend.X86.Syntax using (Instr)

X86ContractInterface : ContractInterface Instr
X86ContractInterface = record
  { Contract = PrimContract
  ; contract-program = PrimContract.prim-assembly
  ; contract-nonempty = PrimContract.prim-nonempty
  }
